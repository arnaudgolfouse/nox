use super::{
    bytecode::Instruction, Constant, ParseReturn, ParserError, ParserErrorKind, VariableLocation,
};
use crate::{
    error::Continue,
    lexer::{Assign, Keyword, Operation, Token, TokenKind},
    Position, Range,
};

#[derive(Debug, Clone, Copy, PartialOrd, PartialEq)]
#[repr(u8)]
pub enum Precedence {
    None = 0,
    /// `or`, `xor`
    Or = 2,
    /// `and`
    And = 3,
    /// `==` `!=`
    Equality = 4,
    /// `<` `>` `<=` `>=`
    Comparison = 5,
    /// `+` `-`
    Term = 6,
    /// `*` `/`
    Factor = 7,
    /*/// '^'
    Pow = 8,*/
    /// `%`
    Modulo = 9,
    /// `not` `-`
    Unary = 10,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExpressionType {
    Constant,
    Assign(String, Assign, Range),
    UnaryOp,
    BinaryOp,
    Call,
    Variable,
    Table,
    TableRead,
    TableWrite(Assign),
}

/// Collection of methods for parsing expressions.
///
/// This allow to implement every individual parsing block (constants, variables, ...), while having the default implementation handle putting them together.
pub trait ExpressionParser<'a>: Sized {
    /// Parse a constant.
    fn parse_constant(&mut self, constant: Constant);
    /// Parse a variable name.
    fn parse_variable(
        &mut self,
        variable: String,
        read_only: bool,
    ) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a parenthesised expression.
    ///
    /// The opening `(` token has already been eaten.
    fn parse_grouping(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a lambda.
    ///
    /// The opening `fn` token has already been eaten.
    fn parse_lambda(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a unary operation.
    fn parse_unary(&mut self, operator: Operation) -> Result<(), ParserError<'a>>;
    /// Parse an table.
    ///
    /// The opening `{` token has already been eaten.
    fn parse_braces(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a binary operation.
    ///
    /// `range` is the range of the operator in the text.
    fn parse_binary(&mut self, operator: Operation, range: Range) -> Result<(), ParserError<'a>>;
    /// Parse a function call, e.g. `f(a, 1, 3 + 2)`.
    ///
    /// Assumes we already parsed all the arguments and the parenthesis : All that is left to do is issuing the call itself.
    fn parse_call(&mut self, arg_num: u32) -> Result<(), ParserError<'a>>;
    /// Parse an indexing operation, e.g. `table[x]`
    ///
    /// The opening `[` token has already been eaten.
    fn parse_brackets(&mut self, read_only: bool) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse an dot operation, e.g. `table.x`
    ///
    /// Assumes we already ate the dot (`.`) token.
    fn parse_dot(&mut self, read_only: bool) -> Result<ExpressionType, ParserError<'a>>;
    fn next(&mut self) -> Result<Option<Token>, ParserError<'a>>;
    fn peek(&self) -> Result<Option<&Token>, ParserError<'a>>;
    fn emit_error(
        &self,
        kind: ParserErrorKind,
        continuable: Continue,
        range: Range,
    ) -> ParserError<'a>;
    fn current_position(&self) -> Position;

    /// Parse an expression, with `token` as its first Token.
    ///
    /// Equivalent with `parse_precedence(Precendence::None)`.
    fn parse_expression(
        &mut self,
        token: Option<Token>,
        read_only: bool,
    ) -> Result<ExpressionType, ParserError<'a>> {
        self.parse_precedence(Precedence::None, token, read_only)
    }

    /// Parse an expression with the given precedence, with `prefix_token` as its first Token.
    fn parse_precedence(
        &mut self,
        precedence: Precedence,
        // prefix : '-', 'not', '(', ...
        prefix_token: Option<Token>,
        read_only: bool,
    ) -> Result<ExpressionType, ParserError<'a>> {
        use std::convert::TryFrom;

        let mut expression_type = if let Some(token) = prefix_token {
            match token.kind {
                // fn ...
                TokenKind::Keyword(Keyword::Fn) => self.parse_lambda(),
                // ( ...
                TokenKind::LPar => self.parse_grouping(),
                // - ...
                TokenKind::Op(Operation::Minus) => self
                    .parse_unary(Operation::Minus)
                    .map(|_| ExpressionType::UnaryOp),
                // not ...
                TokenKind::Op(Operation::Not) => self
                    .parse_unary(Operation::Not)
                    .map(|_| ExpressionType::UnaryOp),
                // variable name
                TokenKind::Id(id) => self.parse_variable(id, read_only),
                // table
                TokenKind::LBrace => self.parse_braces(),
                // constant
                kind => match Constant::try_from(kind) {
                    Ok(constant) => {
                        self.parse_constant(constant);
                        Ok(ExpressionType::Constant)
                    }
                    Err(token_kind) => Err(self.emit_error(
                        ParserErrorKind::Unexpected(token_kind),
                        Continue::Stop,
                        token.range,
                    )),
                },
            }?
        } else {
            return Err(self.emit_error(
                ParserErrorKind::ExpectExpression,
                Continue::Stop,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        // infix operations : '+', '*', '/', ... but also 'a.b' and others !
        loop {
            if matches!(expression_type, ExpressionType::Assign(_, _, _)) {
                return Ok(expression_type);
            }
            if let Some(token) = self.peek()? {
                expression_type = match &token.kind {
                    TokenKind::LBracket => {
                        self.next()?;
                        self.parse_brackets(read_only)
                    }
                    TokenKind::Dot => {
                        self.next()?;
                        self.parse_dot(read_only)
                    }
                    TokenKind::Op(op) => {
                        let op = *op;
                        let op_precedence = match op {
                            Operation::Or | Operation::Xor => Precedence::Or,
                            Operation::And => Precedence::And,
                            Operation::Equal | Operation::NEqual => Precedence::Equality,
                            Operation::Less
                            | Operation::More
                            | Operation::LessEq
                            | Operation::MoreEq => Precedence::Comparison,
                            Operation::Plus | Operation::Minus => Precedence::Term,
                            Operation::Multiply | Operation::Divide => Precedence::Factor,
                            Operation::Modulo => Precedence::Modulo,
                            _ => {
                                break;
                            }
                        };
                        if precedence > op_precedence {
                            break;
                        }
                        let range = token.range;
                        self.next()?;
                        let token = self.next()?;
                        self.parse_precedence(op_precedence, token, read_only)?;
                        self.parse_binary(op, range)
                            .map(|_| ExpressionType::BinaryOp)
                    }
                    TokenKind::LPar => {
                        self.next()?;
                        let arg_num = parse_call_internal(self)?;
                        self.parse_call(arg_num).map(|_| ExpressionType::Call)
                    }
                    _ => break,
                }?;
            } else {
                break;
            }
        }

        Ok(expression_type)
    }
}

/// Assumes we already ate the opening `(`.
fn parse_call_internal<'a, P: ExpressionParser<'a>>(
    parser: &mut P,
) -> Result<u32, ParserError<'a>> {
    let mut arg_num = 0;
    loop {
        let next_token = parser.next()?;
        if let Some(ref token) = next_token {
            match token.kind {
                TokenKind::RPar => break,
                _ => {
                    parser.parse_expression(next_token, true)?;
                    arg_num += 1;
                    if let Some(token) = parser.next()? {
                        match token.kind {
                            TokenKind::Comma => {}
                            TokenKind::RPar => break,
                            _ => {
                                return Err(parser.emit_error(
                                    ParserErrorKind::Unexpected(token.kind),
                                    Continue::Stop,
                                    token.range,
                                ))
                            }
                        }
                    } else {
                        return Err(parser.emit_error(
                            ParserErrorKind::Expected(TokenKind::Comma),
                            Continue::Stop,
                            Range::new(parser.current_position(), parser.current_position()),
                        ));
                    }
                }
            }
        } else {
            return Err(parser.emit_error(
                ParserErrorKind::ExpectExpression,
                Continue::Continue,
                Range::new(parser.current_position(), parser.current_position()),
            ));
        }
    }
    Ok(arg_num)
}

/// Implementation of `ExpressionParser` for `Parser`.
impl<'a> ExpressionParser<'a> for super::Parser<'a> {
    fn parse_constant(&mut self, constant: Constant) {
        match constant {
            Constant::Bool(true) => self.emit_instruction_u8(Instruction::PushTrue),
            Constant::Bool(false) => {
                self.emit_instruction_u8(Instruction::PushFalse);
            }
            Constant::Nil => {
                self.emit_instruction_u8(Instruction::PushNil);
            }
            constant => {
                let index = self.code().add_constant(constant);
                self.emit_instruction(Instruction::ReadConstant(index));
            }
        }
    }

    fn parse_variable(
        &mut self,
        variable: String,
        read_only: bool,
    ) -> Result<ExpressionType, ParserError<'a>> {
        if let Some(Token {
            kind: TokenKind::Assign(ass),
            range,
        }) = self.lexer.peek()?
        {
            let (ass, range) = (*ass, *range);
            return if read_only {
                Err(self.emit_error(
                    ParserErrorKind::Unexpected(TokenKind::Assign(ass)),
                    Continue::Stop,
                    range,
                ))
            } else {
                Ok(ExpressionType::Assign(variable, ass, range))
            };
        }

        match self.find_variable(&variable) {
            VariableLocation::Undefined => {
                let index = self.code().add_string(variable);
                self.emit_instruction(Instruction::ReadGlobal(index))
            }
            VariableLocation::Local(index) => {
                self.emit_instruction(Instruction::ReadLocal(index as u32))
            }
            VariableLocation::Global(index) => {
                self.emit_instruction(Instruction::ReadGlobal(index as u32))
            }
            VariableLocation::Captured(index) => {
                self.emit_instruction(Instruction::ReadCaptured(index as u32))
            }
        }

        Ok(ExpressionType::Variable)
    }

    fn parse_grouping(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        let token = self.lexer.next()?;
        let expression_type = self.parse_expression(token, true)?;
        match self.lexer.next()? {
            Some(Token {
                kind: TokenKind::RPar,
                ..
            }) => Ok(expression_type),
            _ => Err(self.emit_error(
                ParserErrorKind::Expected(TokenKind::RPar),
                Continue::Continue,
                self.lexer.current_range(),
            )),
        }
    }

    fn parse_lambda(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        if let Some(Token {
            kind: TokenKind::LPar,
            ..
        }) = self.next()?
        {
        } else {
            return Err(self.emit_error(
                ParserErrorKind::Expected(TokenKind::LPar),
                Continue::Stop,
                Range::new(self.current_position(), self.current_position()),
            ));
        }
        let function = self.parse_prototype(String::from("<closure>"), true)?;
        self.function_stack.push(function);
        loop {
            match self.parse_statements()? {
                ParseReturn::Continue => {}
                ParseReturn::StopClosure => break Ok(ExpressionType::Constant),
                ParseReturn::Stop => {
                    return Err(self.emit_error(
                        ParserErrorKind::Expected(TokenKind::Keyword(Keyword::End)),
                        Continue::Continue,
                        Range::new(self.current_position(), self.current_position()),
                    ))
                }
            }
        }
    }

    fn parse_unary(&mut self, operator: Operation) -> Result<(), ParserError<'a>> {
        let op_line = self.lexer.position.line;
        let token = self.lexer.next()?;
        self.parse_precedence(Precedence::Unary, token, true)?;
        match operator {
            Operation::Minus => self
                .code()
                .emit_instruction_u8(Instruction::Negative, op_line),
            Operation::Not => self.code().emit_instruction_u8(Instruction::Not, op_line),
            _ => {} // technically unreacheable ? meh
        }
        Ok(())
    }

    fn parse_braces(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        let mut elem_num: u32 = 0;
        // TODO : error for 'x = { a = 1, a = 2 }' (double assignement)
        loop {
            if let Some(token) = self.next()? {
                match token.kind {
                    TokenKind::RBrace => break,
                    TokenKind::Id(member) => {
                        elem_num += 1;
                        let member_index = self.code().add_constant(Constant::String(member));
                        self.emit_instruction(Instruction::ReadConstant(member_index));
                        let token = self.next()?;
                        match token {
                            Some(Token {
                                kind: TokenKind::Assign(Assign::Equal),
                                ..
                            }) => {}
                            _ => return Err(self.expected_token(TokenKind::Assign(Assign::Equal))),
                        }

                        let token = self.next()?;
                        self.parse_expression(token, true)?;
                        let token = self.next()?;
                        match token {
                            Some(Token {
                                kind: TokenKind::Comma,
                                ..
                            }) => {}
                            Some(Token {
                                kind: TokenKind::RBrace,
                                ..
                            }) => break,
                            Some(token) => {
                                return Err(self.emit_error(
                                    ParserErrorKind::Unexpected(token.kind),
                                    Continue::Stop,
                                    token.range,
                                ))
                            }
                            None => return Err(self.expected_token(TokenKind::RBrace)),
                        }
                    }
                    _ => {
                        return Err(self.emit_error(
                            ParserErrorKind::Unexpected(token.kind),
                            Continue::Stop,
                            token.range,
                        ))
                    }
                }
            } else {
                return Err(self.expected_token(TokenKind::RBrace));
            }
        }
        self.emit_instruction(Instruction::MakeTable(elem_num));
        Ok(ExpressionType::Table)
    }

    fn parse_binary(&mut self, operator: Operation, range: Range) -> Result<(), ParserError<'a>> {
        let line = range.start.line;

        self.code().emit_instruction_u8(
            match operator {
                Operation::Plus => Instruction::Add,
                Operation::Minus => Instruction::Subtract,
                Operation::Multiply => Instruction::Multiply,
                Operation::Divide => Instruction::Divide,
                Operation::Modulo => Instruction::Modulo,
                // Operation::Pow => self.code.push_instruction(Instruction::Pow,
                Operation::Equal => Instruction::Equal,
                Operation::NEqual => Instruction::NEqual,
                Operation::Less => Instruction::Less,
                Operation::LessEq => Instruction::LessEq,
                Operation::More => Instruction::More,
                Operation::MoreEq => Instruction::MoreEq,
                Operation::Xor => Instruction::Xor,
                _ => Instruction::Add, // technically unreacheable ? meh
            },
            line,
        );
        Ok(())
    }

    fn parse_call(&mut self, arg_num: u32) -> Result<(), ParserError<'a>> {
        self.emit_instruction(Instruction::Call(arg_num));
        Ok(())
    }

    fn parse_brackets(&mut self, read_only: bool) -> Result<ExpressionType, ParserError<'a>> {
        let next_token = self.next()?;
        self.parse_expression(next_token, true)?;
        let range = if let Some(token) = self.next()? {
            match token.kind {
                TokenKind::RBracket => token.range,
                kind => {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(kind),
                        Continue::Stop,
                        token.range,
                    ))
                }
            }
        } else {
            return Err(self.emit_error(
                ParserErrorKind::Expected(TokenKind::RBracket),
                Continue::Continue,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        match self.peek()? {
            Some(Token {
                kind: TokenKind::Assign(ass),
                ..
            }) => {
                let ass = *ass;
                if read_only {
                    Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Assign(ass)),
                        Continue::Stop,
                        range,
                    ))
                } else {
                    Ok(ExpressionType::TableWrite(ass))
                }
            }
            _ => {
                self.code()
                    .emit_instruction_u8(Instruction::ReadTable, range.start.line);
                Ok(ExpressionType::TableRead)
            }
        }
    }

    fn parse_dot(&mut self, read_only: bool) -> Result<ExpressionType, ParserError<'a>> {
        let range = if let Some(token) = self.next()? {
            match token.kind {
                TokenKind::Id(member) => {
                    let member_index = self.code().add_constant(Constant::String(member));
                    self.code().emit_instruction(
                        Instruction::ReadConstant(member_index),
                        token.range.start.line,
                    );

                    token.range
                }
                kind => {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(kind),
                        Continue::Continue,
                        token.range,
                    ));
                }
            }
        } else {
            return Err(self.emit_error(
                ParserErrorKind::ExpectedId,
                Continue::Continue,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        match self.peek()? {
            Some(Token {
                kind: TokenKind::Assign(ass),
                ..
            }) => {
                let ass = *ass;
                if read_only {
                    Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Assign(ass)),
                        Continue::Stop,
                        range,
                    ))
                } else {
                    Ok(ExpressionType::TableWrite(ass))
                }
            }
            _ => {
                self.code()
                    .emit_instruction_u8(Instruction::ReadTable, range.start.line);
                Ok(ExpressionType::TableRead)
            }
        }
    }

    #[inline]
    fn next(&mut self) -> Result<Option<Token>, ParserError<'a>> {
        self.lexer.next().map_err(ParserError::from)
    }

    #[inline]
    fn peek(&self) -> Result<Option<&Token>, ParserError<'a>> {
        self.lexer.peek().map_err(ParserError::from)
    }

    #[inline]
    fn emit_error(
        &self,
        kind: ParserErrorKind,
        continuable: Continue,
        range: Range,
    ) -> ParserError<'a> {
        ParserError {
            kind,
            continuable,
            range,
            source: self.lexer.source.clone(),
        }
    }

    #[inline]
    fn current_position(&self) -> Position {
        self.lexer.position
    }
}
