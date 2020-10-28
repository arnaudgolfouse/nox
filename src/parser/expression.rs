use super::{bytecode::Instruction, Constant, Error, ErrorKind, ParseReturn, VariableLocation};
use crate::{
    error::Continue,
    lexer::{Assign, Keyword, Operation, Token, TokenKind},
    Range,
};

/// Precendence of the various binary operators
#[derive(Debug, Clone, Copy, PartialOrd, PartialEq)]
#[repr(u8)]
pub(super) enum Precedence {
    None = 0,
    /// `or`, `xor`
    Or = 2,
    /// `and`
    And = 3,
    /// `==` `!=`
    Equality = 4,
    /// `<` `>` `<=` `>=`
    Comparison = 5,
    /// `<<`, `>>`
    Shifts = 6,
    /// `+` `-`
    Term = 7,
    /// `*` `/`
    Factor = 8,
    /// `%`
    Modulo = 9,
    /// `^`
    Pow = 10,
    /// `not` `-`
    Unary = 11,
}

/// Type of the expression we just parsed, and/or wether it will be assigned to,
/// so that we can decide if it is valid in a given context.
#[derive(Clone, Debug, PartialEq)]
pub(super) enum ExpressionType {
    /// A constant literal : `1`, `8.2`, `"hello"`, ...
    Constant,
    /// An expression followed by a assignement token.
    ///
    /// The assignement has already been eaten in this case.
    Assign {
        variable: Box<str>,
        assign_type: Assign,
    },
    /// An unary operation : `- ...`, `not ...`
    UnaryOp,
    /// An binary operation : `... + ...`, `... and ...`, ...
    BinaryOp,
    /// A call expression : `...(a, b)`
    Call,
    /// A variable : `x`, `my_variable`
    Variable,
    /// A table literal : `{ x = 5 }`, `{}`, ...
    Table,
    /// A table read operation : `t[5]`, `t.x`, ...
    TableRead,
    /// A table write operation : `t[5] = ...`, `t.x = ...`, ...
    ///
    /// The assignement has already been eaten in this case.
    TableWrite(Assign),
}

impl<'a> super::Parser<'a> {
    /// Parse an expression, with `token` as its first Token.
    ///
    /// Equivalent with `parse_precedence(Precendence::None)`.
    pub(super) fn parse_expression(
        &mut self,
        token: Option<Token>,
        read_only: bool,
    ) -> Result<ExpressionType, Error> {
        self.parse_precedence(Precedence::None, token, read_only)
    }

    /// Parse an expression with the given precedence, with `prefix_token` as
    /// its first Token.
    fn parse_precedence(
        &mut self,
        precedence: Precedence,
        prefix_token: Option<Token>,
        read_only: bool,
    ) -> Result<ExpressionType, Error> {
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
                        ErrorKind::Unexpected(token_kind),
                        Continue::Stop,
                        token.range,
                    )),
                },
            }?
        } else {
            return Err(self.emit_error(
                ErrorKind::ExpectExpression,
                Continue::Stop,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        // infix operations : '+', '*', '/', ... but also 'a.b' and others !
        loop {
            if matches!(expression_type, ExpressionType::Assign{..}) {
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
                            Operation::ShiftLeft | Operation::ShiftRight => Precedence::Shifts,
                            Operation::Plus | Operation::Minus => Precedence::Term,
                            Operation::Multiply | Operation::Divide => Precedence::Factor,
                            Operation::Pow => Precedence::Pow,
                            Operation::Modulo => Precedence::Modulo,
                            _ => {
                                break;
                            }
                        };
                        if precedence >= op_precedence {
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
                        let arg_num = self.parse_call_internal()?;
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

    /// Parse a constant.
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

    /// Parse a variable name.
    pub(super) fn parse_variable(
        &mut self,
        variable: Box<str>,
        read_only: bool,
    ) -> Result<ExpressionType, Error> {
        if let Some(Token {
            kind: TokenKind::Assign(ass),
            range,
            ..
        }) = self.peek()?
        {
            let (ass, range) = (*ass, *range);
            return if read_only {
                Err(self.emit_error(
                    ErrorKind::Unexpected(TokenKind::Assign(ass)),
                    Continue::Stop,
                    range,
                ))
            } else {
                Ok(ExpressionType::Assign {
                    variable,
                    assign_type: ass,
                })
            };
        }

        match self.find_variable(&variable) {
            VariableLocation::Undefined => {
                // TODO : now that we have 'global ...' statements, change this to read a local (aka nil here), as the current logic is very non-intuitive.
                let index = self.code().add_global(variable);
                self.emit_instruction(Instruction::ReadGlobal(index))
            }
            VariableLocation::Local(index) => self.emit_instruction(Instruction::ReadLocal(index)),
            VariableLocation::Global(index) => {
                self.emit_instruction(Instruction::ReadGlobal(index))
            }
            VariableLocation::Captured(index) => {
                self.emit_instruction(Instruction::ReadCaptured(index))
            }
        }

        Ok(ExpressionType::Variable)
    }

    /// Parse a parenthesised expression.
    ///
    /// The opening `(` token has already been eaten.
    fn parse_grouping(&mut self) -> Result<ExpressionType, Error> {
        let token = self.next()?;
        let expression_type = self.parse_expression(token, true)?;
        match self.next()? {
            Some(Token {
                kind: TokenKind::RPar,
                ..
            }) => Ok(expression_type),
            _ => Err(self.emit_error(
                ErrorKind::Expected(TokenKind::RPar),
                Continue::Continue,
                self.current_range(),
            )),
        }
    }

    /// Parse a lambda.
    ///
    /// The opening `fn` token has already been eaten.
    fn parse_lambda(&mut self) -> Result<ExpressionType, Error> {
        if let Some(Token {
            kind: TokenKind::LPar,
            ..
        }) = self.next()?
        {
        } else {
            return Err(self.emit_error(
                ErrorKind::Expected(TokenKind::LPar),
                Continue::Stop,
                Range::new(self.current_position(), self.current_position()),
            ));
        }
        let function = self.parse_prototype(Box::from("<closure>"), true)?;
        self.function_stack.push(function);
        loop {
            match self.parse_statement() {
                Ok(ParseReturn::Continue) => {}
                Ok(ParseReturn::StopClosure) => break Ok(ExpressionType::Constant),
                Ok(ParseReturn::Stop) => {
                    return Err(self.emit_error(
                        ErrorKind::Expected(TokenKind::Keyword(Keyword::End)),
                        Continue::Continue,
                        Range::new(self.current_position(), self.current_position()),
                    ));
                }
                Err(err) => {
                    self.errors.push(err);
                    if self.panic_mode() {
                        break Ok(ExpressionType::Constant);
                    }
                }
            }
        }
    }

    /// Parse a unary operation.
    fn parse_unary(&mut self, operator: Operation) -> Result<(), Error> {
        let op_line = self.current_position().line;
        let token = self.next()?;
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

    /// Parse an table.
    ///
    /// The opening `{` token has already been eaten.
    fn parse_braces(&mut self) -> Result<ExpressionType, Error> {
        let mut elem_num: u32 = 0;
        // easy to check which ones are already used
        let mut element_names_indices = Vec::new();
        loop {
            if let Some(token) = self.next()? {
                match token.kind {
                    TokenKind::RBrace => break,
                    TokenKind::Id(member) => {
                        elem_num += 1;
                        let member_index =
                            self.code().add_constant(Constant::String(member.clone()));
                        if element_names_indices.contains(&member_index) {
                            return Err(self.emit_error(
                                ErrorKind::TableDoubleAssignement(member),
                                Continue::Stop,
                                token.range,
                            ));
                        }
                        element_names_indices.push(member_index);
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
                                    ErrorKind::Unexpected(token.kind),
                                    Continue::Stop,
                                    token.range,
                                ))
                            }
                            None => return Err(self.expected_token(TokenKind::RBrace)),
                        }
                    }
                    _ => {
                        return Err(self.emit_error(
                            ErrorKind::Unexpected(token.kind),
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

    /// Parse a binary operation.
    ///
    /// `range` is the range of the operator in the text.
    fn parse_binary(&mut self, operator: Operation, range: Range) -> Result<(), Error> {
        let line = range.start.line;

        self.code().emit_instruction_u8(
            match operator {
                Operation::Plus => Instruction::Add,
                Operation::Minus => Instruction::Subtract,
                Operation::Multiply => Instruction::Multiply,
                Operation::Divide => Instruction::Divide,
                Operation::Modulo => Instruction::Modulo,
                Operation::Pow => Instruction::Pow,
                Operation::Equal => Instruction::Equal,
                Operation::NEqual => Instruction::NEqual,
                Operation::Less => Instruction::Less,
                Operation::LessEq => Instruction::LessEq,
                Operation::More => Instruction::More,
                Operation::MoreEq => Instruction::MoreEq,
                Operation::And => Instruction::And,
                Operation::Or => Instruction::Or,
                Operation::Xor => Instruction::Xor,
                Operation::ShiftLeft => Instruction::ShiftL,
                Operation::ShiftRight => Instruction::ShiftR,
                Operation::Not => unreachable!(),
            },
            line,
        );
        Ok(())
    }

    /// Parse a function call, e.g. `f(a, 1, 3 + 2)`.
    ///
    /// Assumes we already parsed all the arguments and the parenthesis : All
    /// that is left to do is issuing the call itself.
    fn parse_call(&mut self, arg_num: u32) -> Result<(), Error> {
        self.emit_instruction(Instruction::Call(arg_num));
        Ok(())
    }

    /// Parse an indexing operation, e.g. `table[x]`
    ///
    /// The opening `[` token has already been eaten.
    fn parse_brackets(&mut self, read_only: bool) -> Result<ExpressionType, Error> {
        let next_token = self.next()?;
        self.parse_expression(next_token, true)?;
        let range = if let Some(token) = self.next()? {
            match token.kind {
                TokenKind::RBracket => token.range,
                kind => {
                    return Err(self.emit_error(
                        ErrorKind::Unexpected(kind),
                        Continue::Stop,
                        token.range,
                    ))
                }
            }
        } else {
            return Err(self.emit_error(
                ErrorKind::Expected(TokenKind::RBracket),
                Continue::Continue,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        if let Some(Token {
            kind: TokenKind::Assign(ass),
            ..
        }) = self.peek()?
        {
            let ass = *ass;
            if read_only {
                Err(self.emit_error(
                    ErrorKind::Unexpected(TokenKind::Assign(ass)),
                    Continue::Stop,
                    range,
                ))
            } else {
                Ok(ExpressionType::TableWrite(ass))
            }
        } else {
            self.code()
                .emit_instruction_u8(Instruction::ReadTable, range.start.line);
            Ok(ExpressionType::TableRead)
        }
    }

    /// Parse an dot operation, e.g. `table.x`
    ///
    /// Assumes we already ate the dot (`.`) token.
    fn parse_dot(&mut self, read_only: bool) -> Result<ExpressionType, Error> {
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
                        ErrorKind::Unexpected(kind),
                        Continue::Continue,
                        token.range,
                    ));
                }
            }
        } else {
            return Err(self.emit_error(
                ErrorKind::ExpectedId(None),
                Continue::Continue,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        if let Some(Token {
            kind: TokenKind::Assign(ass),
            ..
        }) = self.peek()?
        {
            let ass = *ass;
            if read_only {
                Err(self.emit_error(
                    ErrorKind::Unexpected(TokenKind::Assign(ass)),
                    Continue::Stop,
                    range,
                ))
            } else {
                Ok(ExpressionType::TableWrite(ass))
            }
        } else {
            self.code()
                .emit_instruction_u8(Instruction::ReadTable, range.start.line);
            Ok(ExpressionType::TableRead)
        }
    }

    /// Assumes we already ate the opening `(`.
    fn parse_call_internal(&mut self) -> Result<u32, Error> {
        let mut arg_num = 0;
        loop {
            let next_token = self.next()?;
            if let Some(ref token) = next_token {
                if token.kind == TokenKind::RPar {
                    break;
                } else {
                    self.parse_expression(next_token, true)?;
                    arg_num += 1;
                    if let Some(token) = self.next()? {
                        match token.kind {
                            TokenKind::Comma => {}
                            TokenKind::RPar => break,
                            _ => {
                                return Err(self.emit_error(
                                    ErrorKind::Unexpected(token.kind),
                                    Continue::Stop,
                                    token.range,
                                ))
                            }
                        }
                    } else {
                        return Err(self.emit_error(
                            ErrorKind::Expected(TokenKind::Comma),
                            Continue::Stop,
                            Range::new(self.current_position(), self.current_position()),
                        ));
                    }
                }
            } else {
                return Err(self.emit_error(
                    ErrorKind::ExpectExpression,
                    Continue::Continue,
                    Range::new(self.current_position(), self.current_position()),
                ));
            }
        }
        Ok(arg_num)
    }
}
