use super::{bytecode::Instruction, Constant, ParserError, ParserErrorKind};
use crate::{
    error::Continue,
    lexer::{Keyword, Operation, Token, TokenKind},
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
    Assign(String),
    UnaryOp,
    BinaryOp,
    Call,
    Variable,
}

/// Collection of methods for parsing expressions.
///
/// This allow to implement every individual parsing block (constants, variables, ...), while having the default implementation handle putting them together.
pub trait ExpressionParser<'a> {
    /// Parse a constant.
    fn parse_constant(&mut self, constant: Constant);
    /// Parse a variable name.
    fn parse_variable(&mut self, variable: String) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a parenthesised expression. The opening `(` token has already been eaten.
    fn parse_grouping(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a lambda. The opening `fn` token has already been eaten.
    fn parse_lambda(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    /// Parse a unary operation.
    fn parse_unary(&mut self, operator: Operation) -> Result<(), ParserError<'a>>;
    /// Parse a binary operation.
    ///
    /// `range` is the range of the operator in the text.
    fn parse_binary(&mut self, operator: Operation, range: Range) -> Result<(), ParserError<'a>>;
    fn parse_call(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn parse_brackets(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn parse_dot(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn next(&mut self) -> Result<Option<Token>, ParserError<'a>>;
    fn peek(&self) -> Result<Option<&Token>, ParserError<'a>>;
    fn emit_error(
        &self,
        kind: ParserErrorKind,
        continuable: Continue,
        range: Range,
    ) -> ParserError<'a>;
    fn current_position(&self) -> Position;

    /// Parse an expression.
    ///
    /// Equivalent with `parse_precedence(Precendence::None)`.
    fn parse_expression(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        self.parse_precedence(Precedence::None)
    }

    /// Parse an expression with the given precedence.
    fn parse_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Result<ExpressionType, ParserError<'a>> {
        use std::convert::TryFrom;

        // prefix : '-', 'not', '(', ...
        let prefix_token = self.next()?;
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
                TokenKind::Id(id) => self.parse_variable(id),
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
            println!("here ?");
            return Err(self.emit_error(
                ParserErrorKind::ExpectExpression,
                Continue::Stop,
                Range::new(self.current_position(), self.current_position()),
            ));
        };

        // infix operations : '+', '*', '/', ... but also 'a.b' and others !
        loop {
            if matches!(expression_type, ExpressionType::Assign(_)) {
                return Ok(expression_type);
            }
            if let Some(token) = self.peek()? {
                expression_type = match &token.kind {
                    TokenKind::LBracket => self.parse_brackets(),
                    TokenKind::Dot => self.parse_dot(),
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
                        self.parse_precedence(op_precedence)?;
                        self.parse_binary(op, range)
                            .map(|_| ExpressionType::BinaryOp)
                    }
                    TokenKind::LPar => self.parse_call(),
                    _ => break,
                }?;
            } else {
                break;
            }
        }

        Ok(expression_type)
    }
}

/// Implementation of `ExpressionParser` for `Parser`.
impl<'a> ExpressionParser<'a> for super::Parser<'a> {
    fn parse_constant(&mut self, constant: Constant) {
        match constant {
            Constant::Bool(true) => self.push_instruction(Instruction::PushTrue),
            Constant::Bool(false) => {
                self.push_instruction(Instruction::PushFalse);
            }
            Constant::Nil => {
                self.push_instruction(Instruction::PushNil);
            }
            constant => {
                let index = self.code.add_constant(constant);
                self.emit_instruction(Instruction::ReadConstant(index));
            }
        }
    }

    fn parse_variable(&mut self, variable: String) -> Result<ExpressionType, ParserError<'a>> {
        if let Some(Token {
            kind: TokenKind::Assign(_),
            ..
        }) = self.lexer.peek()?
        {
            return Ok(ExpressionType::Assign(variable));
        }

        match self.function_stack.last() {
            Some(function) => match function.variable_exists(&variable) {
                Some(index) => self.emit_instruction(Instruction::ReadLocal(index)),
                None => {
                    todo!() // TODO : capture
                }
            },
            None => {
                let index = self.code.add_global(variable);
                self.emit_instruction(Instruction::ReadGlobal(index))
            }
        }

        Ok(ExpressionType::Variable)
    }

    fn parse_grouping(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        let expression_type = self.parse_expression()?;
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
        todo!()
    }

    fn parse_unary(&mut self, operator: Operation) -> Result<(), ParserError<'a>> {
        let op_line = self.lexer.position.line;
        self.parse_precedence(Precedence::Unary)?;
        match operator {
            Operation::Minus => self.code.push_instruction(Instruction::Negative, op_line),
            Operation::Not => self.code.push_instruction(Instruction::Not, op_line),
            _ => {} // technically unreacheable ? meh
        }
        Ok(())
    }

    fn parse_binary(&mut self, operator: Operation, range: Range) -> Result<(), ParserError<'a>> {
        let line = range.start.line;

        match operator {
            Operation::Plus => self.code.push_instruction(Instruction::Add, line),
            Operation::Minus => self.code.push_instruction(Instruction::Subtract, line),
            Operation::Multiply => self.code.push_instruction(Instruction::Multiply, line),
            Operation::Divide => self.code.push_instruction(Instruction::Divide, line),
            Operation::Modulo => self.code.push_instruction(Instruction::Modulo, line),
            // Operation::Pow => self.code.push_instruction(Instruction::Pow, line),
            Operation::Equal => self.code.push_instruction(Instruction::Equal, line),
            Operation::NEqual => self.code.push_instruction(Instruction::NEqual, line),
            Operation::Less => self.code.push_instruction(Instruction::Less, line),
            Operation::LessEq => self.code.push_instruction(Instruction::LessEq, line),
            Operation::More => self.code.push_instruction(Instruction::More, line),
            Operation::MoreEq => self.code.push_instruction(Instruction::MoreEq, line),
            Operation::Xor => self.code.push_instruction(Instruction::Xor, line),
            _ => {} // technically unreacheable ? meh
        }
        Ok(())
    }

    fn parse_call(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        todo!()
    }

    fn parse_brackets(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        todo!()
    }

    fn parse_dot(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        todo!()
    }

    fn next(&mut self) -> Result<Option<Token>, ParserError<'a>> {
        self.lexer.next().map_err(ParserError::from)
    }

    fn peek(&self) -> Result<Option<&Token>, ParserError<'a>> {
        self.lexer.peek().map_err(ParserError::from)
    }

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

    fn current_position(&self) -> Position {
        self.lexer.position
    }
}
