use super::{bytecode::Instruction, Constant, Error, ErrorKind, ParseReturn, VariableLocation};
use crate::{
    error::Continue,
    lexer::{Assign, Keyword, Operation, Token, TokenKind},
};
use std::ops::Range;

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
                self.end_current_range(),
            ));
        };

        // infix operations : '+', '*', '/', ... but also 'a.b' and others !
        loop {
            if matches!(expression_type, ExpressionType::Assign { .. }) {
                return Ok(expression_type);
            }
            match self.peek_transpose()? {
                Some(token) => {
                    expression_type = match &token.kind {
                        TokenKind::LBracket => {
                            self.next().transpose()?;
                            self.parse_brackets(read_only)
                        }
                        TokenKind::Dot => {
                            self.next().transpose()?;
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
                            let range = token.range.clone();
                            self.next().transpose()?;
                            let token = self.next().transpose()?;
                            self.parse_precedence(op_precedence, token, read_only)?;
                            self.parse_binary(op, range);
                            Ok(ExpressionType::BinaryOp)
                        }
                        TokenKind::LPar => {
                            self.next().transpose()?;
                            let arg_num = self.parse_call_internal()?;
                            self.parse_call(arg_num);
                            Ok(ExpressionType::Call)
                        }
                        _ => break,
                    }?;
                }
                None => break,
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
                let index = self.func().chunk.add_constant(constant);
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
        }) = self.peek_transpose()?
        {
            let (ass, range) = (*ass, range.clone());
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
                let index = self.func().chunk.add_global(variable);
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
        let token = self.next().transpose()?;
        let expression_type = self.parse_expression(token, true)?;
        match self.next().transpose()? {
            Some(Token {
                kind: TokenKind::RPar,
                ..
            }) => Ok(expression_type),
            _ => Err(self.emit_error(
                ErrorKind::Expected(TokenKind::RPar),
                Continue::Continue,
                self.next_range.clone(),
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
        }) = self.next().transpose()?
        {
        } else {
            return Err(self.emit_error(
                ErrorKind::Expected(TokenKind::LPar),
                Continue::Stop,
                self.end_current_range(),
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
                        self.end_current_range(),
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
    ///
    /// The operation token has already been eaten.
    fn parse_unary(&mut self, operator: Operation) -> Result<(), Error> {
        let op_pos = self.current_range.start;
        let token = self.next().transpose()?;
        self.parse_precedence(Precedence::Unary, token, true)?;
        match operator {
            Operation::Minus => self
                .func()
                .emit_instruction_u8(Instruction::Negative, op_pos),
            Operation::Not => self.func().emit_instruction_u8(Instruction::Not, op_pos),
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
            if let Some(token) = self.next().transpose()? {
                match token.kind {
                    TokenKind::RBrace => break,
                    TokenKind::Id(member) => {
                        elem_num += 1;
                        let member_index = self
                            .func()
                            .chunk
                            .add_constant(Constant::String(member.clone()));
                        if element_names_indices.contains(&member_index) {
                            return Err(self.emit_error(
                                ErrorKind::TableDoubleAssignement(member),
                                Continue::Stop,
                                token.range,
                            ));
                        }
                        element_names_indices.push(member_index);
                        self.emit_instruction(Instruction::ReadConstant(member_index));
                        let token = self.next().transpose()?;
                        match token {
                            Some(Token {
                                kind: TokenKind::Assign(Assign::Equal),
                                ..
                            }) => {}
                            _ => {
                                return Err(self.expected_token(
                                    TokenKind::Assign(Assign::Equal),
                                    self.end_current_range(),
                                ))
                            }
                        }

                        let token = self.next().transpose()?;
                        self.parse_expression(token, true)?;
                        let token = self.next().transpose()?;
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
                            None => {
                                return Err(self
                                    .expected_token(TokenKind::RBrace, self.end_current_range()))
                            }
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
                return Err(self.expected_token(TokenKind::RBrace, self.end_current_range()));
            }
        }
        self.emit_instruction(Instruction::MakeTable(elem_num));
        Ok(ExpressionType::Table)
    }

    /// Parse a binary operation.
    ///
    /// `range` is the range of the operator in the text.
    ///
    /// # Panics
    ///
    /// Panics if `operator` is not a binary operator.
    fn parse_binary(&mut self, operator: Operation, range: Range<usize>) {
        let pos = range.start;

        self.func().emit_instruction_u8(
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
            pos,
        );
    }

    /// Parse a function call, e.g. `f(a, 1, 3 + 2)`.
    ///
    /// Assumes we already parsed all the arguments and the parenthesis : All
    /// that is left to do is issuing the call itself.
    fn parse_call(&mut self, arg_num: u16) {
        self.emit_instruction(Instruction::Call(arg_num));
    }

    /// Parse an indexing operation, e.g. `table[x]`
    ///
    /// The opening `[` token has already been eaten.
    fn parse_brackets(&mut self, read_only: bool) -> Result<ExpressionType, Error> {
        let next_token = self.next().transpose()?;
        self.parse_expression(next_token, true)?;
        let range = if let Some(token) = self.next().transpose()? {
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
                self.end_current_range(),
            ));
        };

        if let Some(Token {
            kind: TokenKind::Assign(ass),
            ..
        }) = self.peek_transpose()?
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
            self.func()
                .emit_instruction_u8(Instruction::ReadTable, range.start);
            Ok(ExpressionType::TableRead)
        }
    }

    /// Parse an dot operation, e.g. `table.x`
    ///
    /// Assumes we already ate the dot (`.`) token.
    fn parse_dot(&mut self, read_only: bool) -> Result<ExpressionType, Error> {
        let range = if let Some(token) = self.next().transpose()? {
            match token.kind {
                TokenKind::Id(member) => {
                    let member_index = self.func().chunk.add_constant(Constant::String(member));
                    self.func().emit_instruction(
                        Instruction::ReadConstant(member_index),
                        token.range.start,
                    );

                    token.range
                }
                kind => {
                    return Err(self.emit_error(
                        ErrorKind::ExpectedId(Some(kind)),
                        Continue::Stop,
                        token.range,
                    ));
                }
            }
        } else {
            return Err(self.emit_error(
                ErrorKind::ExpectedId(None),
                Continue::Continue,
                self.end_current_range(),
            ));
        };

        if let Some(Token {
            kind: TokenKind::Assign(ass),
            ..
        }) = self.peek_transpose()?
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
            self.func()
                .emit_instruction_u8(Instruction::ReadTable, range.start);
            Ok(ExpressionType::TableRead)
        }
    }

    /// Assumes we already ate the opening `(`.
    fn parse_call_internal(&mut self) -> Result<u16, Error> {
        let mut arg_num: u16 = 0;
        loop {
            let next_token = self.next().transpose()?;
            if let Some(ref token) = next_token {
                if token.kind == TokenKind::RPar {
                    break;
                } else {
                    self.parse_expression(next_token, true)?;
                    arg_num = arg_num.checked_add(1).ok_or_else(|| {
                        self.emit_error(
                            ErrorKind::TooManyFunctionArgs(arg_num as usize + 1),
                            Continue::Stop,
                            self.current_range.clone(),
                        )
                    })?;
                    if let Some(token) = self.next().transpose()? {
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
                            self.end_current_range(),
                        ));
                    }
                }
            } else {
                return Err(self.emit_error(
                    ErrorKind::ExpectExpression,
                    Continue::Continue,
                    self.end_current_range(),
                ));
            }
        }
        Ok(arg_num)
    }
}
