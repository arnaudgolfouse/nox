use super::{bytecode::Instruction, Constant, ParserError, ParserErrorKind};
use crate::{
    error::Continue,
    lexer::{Keyword, Operation, Token, TokenKind},
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

pub enum InfixRule {
    Call,
    Binary,
}

fn get_infix(token: Option<&Token>) -> Option<(InfixRule, Precedence)> {
    if let Some(token) = token {
        match token.kind {
            TokenKind::LPar => Some((InfixRule::Call, Precedence::None)),
            TokenKind::Op(op) => match op {
                Operation::Or | Operation::Xor => Some((InfixRule::Binary, Precedence::Or)),
                Operation::And => Some((InfixRule::Binary, Precedence::And)),
                Operation::Equal | Operation::NEqual => {
                    Some((InfixRule::Binary, Precedence::Equality))
                }
                Operation::Less | Operation::More | Operation::LessEq | Operation::MoreEq => {
                    Some((InfixRule::Binary, Precedence::Comparison))
                }
                Operation::Plus | Operation::Minus => Some((InfixRule::Binary, Precedence::Term)),
                Operation::Multiply | Operation::Divide => {
                    Some((InfixRule::Binary, Precedence::Factor))
                }
                Operation::Modulo => Some((InfixRule::Binary, Precedence::Modulo)),
                Operation::Not => None,
            },
            _ => None,
        }
    } else {
        None
    }
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
    fn parse_binary(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn parse_call(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn parse_brackets(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn parse_dot(&mut self) -> Result<ExpressionType, ParserError<'a>>;
    fn next(&mut self) -> Result<Option<Token>, ParserError<'a>>;
    fn peek(&self) -> Result<Option<&Token>, ParserError<'a>>;
    fn emit_error(&self, kind: ParserErrorKind, continuable: Continue) -> ParserError<'a>;

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

        let prefix_token = self.next()?;
        let mut expression_type = match prefix_token {
            // fn ...
            Some(Token {
                kind: TokenKind::Keyword(Keyword::Fn),
                ..
            }) => self.parse_lambda(),
            // ( ...
            Some(Token {
                kind: TokenKind::LPar,
                ..
            }) => self.parse_grouping(),
            // - ...
            Some(Token {
                kind: TokenKind::Op(Operation::Minus),
                ..
            }) => self
                .parse_unary(Operation::Minus)
                .map(|_| ExpressionType::UnaryOp),
            // not ...
            Some(Token {
                kind: TokenKind::Op(Operation::Not),
                ..
            }) => self
                .parse_unary(Operation::Not)
                .map(|_| ExpressionType::UnaryOp),
            // variable name
            Some(Token {
                kind: TokenKind::Id(id),
                ..
            }) => self.parse_variable(id),
            // constant
            Some(Token { kind, .. }) => match Constant::try_from(kind) {
                Ok(constant) => {
                    self.parse_constant(constant);
                    Ok(ExpressionType::Constant)
                }
                Err(token_kind) => {
                    Err(self.emit_error(ParserErrorKind::Unexpected(token_kind), Continue::Stop))
                }
            },
            None => return Err(self.emit_error(ParserErrorKind::ExpectExpression, Continue::Stop)),
        }?;

        loop {
            if matches!(expression_type, ExpressionType::Assign(_)) {
                return Ok(expression_type);
            }
            expression_type = match self.peek()? {
                Some(Token {
                    kind: TokenKind::LBracket,
                    ..
                }) => self.parse_brackets(),
                Some(Token {
                    kind: TokenKind::Dot,
                    ..
                }) => self.parse_dot(),
                token => {
                    if let Some((infix, infix_precedence)) = get_infix(token) {
                        if precedence > infix_precedence {
                            break;
                        }
                        match infix {
                            InfixRule::Binary => self.parse_binary(),
                            InfixRule::Call => self.parse_call(),
                        }
                    } else {
                        break;
                    }
                }
            }?;
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

    fn parse_binary(&mut self) -> Result<ExpressionType, ParserError<'a>> {
        todo!()
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

    fn emit_error(&self, kind: ParserErrorKind, continuable: Continue) -> ParserError<'a> {
        ParserError {
            kind,
            continuable,
            range: self.lexer.current_range(),
            source: self.lexer.source.clone(),
        }
    }
}
