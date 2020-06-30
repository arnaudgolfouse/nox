pub mod bytecode;
mod expression;

use crate::{
    error::{display_error, Continue},
    lexer::{Assign, Keyword, Lexer, LexerError, LexerErrorKind, TokenKind},
    Range, Source,
};
use bytecode::{Chunk, Constant, Instruction};
use expression::{ExpressionParser, ExpressionType};
use std::fmt;

#[derive(Debug, Clone, Copy)]
enum Scope {
    /// `if` statement. Contains the address of the `Jump` instruction.
    If(usize),
    /// `else` statement. Contains the address of the `Jump` instruction at the end of the `if` block.
    Else(usize),
    /// `while` statement
    While,
    /// `for` statement
    For,
}

#[derive(Default, Debug)]
pub struct Function {
    name: String,
    variables: Vec<String>,
    scopes: Vec<Scope>,
}

impl Function {
    /// This function returns `None` if there is no opened scope in the function
    fn scope(&self) -> Option<Scope> {
        self.scopes.last().copied()
    }

    /// Return the index of the variable if it exists in the function
    fn find_variable(&self, variable: &str) -> Option<u32> {
        for (i, var) in self.variables.iter().enumerate() {
            if var == variable {
                return Some(i as u32);
            }
        }
        None
    }
}

#[derive(Default, Debug)]
pub struct TopLevel {
    variables: String,
    scopes: Vec<Scope>,
}

impl TopLevel {
    /// This function returns `None` if there is no opened scope in the top-level
    fn scope(&self) -> Option<Scope> {
        self.scopes.last().copied()
    }
}

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    code: Chunk,
    errors: Vec<ParserError<'a>>,
    top_level: TopLevel,
    function_stack: Vec<Function>,
}

// fn f()          // -
//     x = none    // - x
//     if true     // - x
//         x = 5   // - x
//         y = 8   // - x y
//     else        // - x y
//         x = 6   // - x y
//         a = 4   // - x y a
//     end         // - x y a
//     z = 8       // - x y a z
// end             // -
impl<'a> Parser<'a> {
    pub fn new(source: Source<'a>) -> Self {
        let chunk_name = source.name().to_owned();
        Self {
            lexer: Lexer::new(source),
            code: Chunk {
                name: chunk_name,
                lines: Vec::new(),
                code: Vec::new(),
                constants: Vec::new(),
                globals: Vec::new(),
                locals_number: 0,
            },
            errors: Vec::new(),
            top_level: TopLevel::default(),
            function_stack: Vec::new(),
        }
    }

    /// emit a new instruction at the current line.
    #[inline(always)]
    fn emit_instruction<Op: bytecode::Operand>(&mut self, instruction: Instruction<Op>) {
        self.code
            .emit_instruction(instruction, self.lexer.position.line)
    }

    /// emit a new u8 instruction at the current line. Same as `emit_instruction::<u8>`.
    #[inline(always)]
    fn push_instruction(&mut self, instruction: Instruction<u8>) {
        self.code
            .push_instruction(instruction, self.lexer.position.line)
    }

    /// Returns the current scope.
    fn scope(&self) -> Option<Scope> {
        match self.function_stack.last() {
            Some(func) => func.scope(),
            None => self.top_level.scope(),
        }
    }

    fn push_scope(&mut self, scope: Scope) {
        if let Some(func) = self.function_stack.last_mut() {
            func.scopes.push(scope)
        } else {
            self.top_level.scopes.push(scope)
        }
    }

    fn pop_scope(&mut self) -> Option<Scope> {
        match self.function_stack.last_mut() {
            Some(func) => func.scopes.pop(),
            None => self.top_level.scopes.pop(),
        }
    }

    pub fn parse_top_level(mut self) -> Result<Chunk, Vec<ParserError<'a>>> {
        loop {
            match self.parse_statements() {
                Err(err) => {
                    self.errors.push(err);
                    if self.panic_mode() {
                        break;
                    }
                }
                Ok(Some(())) => {}
                Ok(None) => break,
            }
        }
        if self.errors.is_empty() {
            Ok(self.code)
        } else {
            Err(self.errors)
        }
    }

    /// advance tokens until we can start to parse a new statement
    ///
    /// If this function returns `true`, no more tokens can be parsed.
    fn panic_mode(&mut self) -> bool {
        #[allow(unused_must_use)]
        loop {
            match self.lexer.peek() {
                Ok(Some(token)) => match token.kind {
                    TokenKind::Keyword(Keyword::Return)
                    | TokenKind::Keyword(Keyword::If)
                    | TokenKind::Keyword(Keyword::While)
                    | TokenKind::Keyword(Keyword::For)
                    | TokenKind::Keyword(Keyword::Fn)
                    | TokenKind::Id(_) => return false,
                    _ => {}
                },
                Ok(None) => return true,
                Err(err) => {
                    self.errors.push(err.into());
                    return false;
                }
            }
            self.lexer.next();
        }
    }

    fn parse_statements(&mut self) -> Result<Option<()>, ParserError<'a>> {
        let first_token = match self.lexer.next()? {
            Some(token) => token,
            None => {
                return if self.scope().is_some() || !self.function_stack.is_empty() {
                    Err(self.emit_error(
                        ParserErrorKind::Expected(TokenKind::Keyword(Keyword::End)),
                        Continue::ContinueWithNewline,
                        Range::new(self.lexer.position, self.lexer.position),
                    ))
                } else {
                    Ok(None)
                }
            }
        };

        match &first_token.kind {
            TokenKind::Keyword(Keyword::Return) => {
                let line = first_token.range.start.line;
                let token = self.next()?;
                self.parse_expression(token, true)?;
                self.code.emit_instruction::<u8>(Instruction::Return, line)
            }
            TokenKind::Keyword(Keyword::End) => {
                if let Some(scope) = self.pop_scope() {
                    match scope {
                        Scope::If(if_address) => self.code.write_jump(
                            Instruction::JumpPopFalse(self.code.code.len() as u32),
                            if_address,
                        ),
                        Scope::Else(else_address) => self.code.write_jump(
                            Instruction::Jump(self.code.code.len() as u32),
                            else_address,
                        ),
                        _ => todo!(),
                    }
                } else if let Some(_function) = self.function_stack.last() {
                    todo!()
                } else {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::End)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            TokenKind::Keyword(Keyword::If) => {
                self.parse_expression(Some(first_token), true)?;
                let if_address = self.code.push_jump();
                self.push_scope(Scope::If(if_address));
            }
            TokenKind::Keyword(Keyword::Else) => {
                if let Some(Scope::If(if_address)) = self.pop_scope() {
                    let else_address = self.code.push_jump();
                    self.push_scope(Scope::Else(else_address));
                    self.code
                        .write_jump(Instruction::JumpPopFalse(self.code.code.len()), if_address);
                } else {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::Else)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            TokenKind::Keyword(Keyword::While) => todo!(),
            TokenKind::Keyword(Keyword::For) => todo!(),
            TokenKind::Id(_) => {
                let range = first_token.range;
                // TODO : make `parse_expression` eat the first token.
                let expression_type = self.parse_expression(Some(first_token), false)?;
                match expression_type {
                    ExpressionType::Assign(var, ass, _) => self.write_variable(var, ass)?,
                    ExpressionType::Call => todo!(),
                    _ => {
                        return Err(self.emit_error(
                            ParserErrorKind::UnexpectedId,
                            Continue::Stop,
                            range,
                        ))
                    }
                }
            }
            _ => {
                return Err(self.emit_error(
                    ParserErrorKind::Unexpected(first_token.kind),
                    Continue::Stop,
                    first_token.range,
                ))
            }
        }

        Ok(Some(()))
    }

    pub fn write_variable(
        &mut self,
        variable: String,
        assignement: Assign,
    ) -> Result<(), ParserError<'a>> {
        match assignement {
            Assign::Equal => {}
            _ => {
                self.parse_variable(variable.clone(), true)?;
            }
        };
        let token = self.lexer.next()?;
        self.parse_expression(token, true)?;
        match assignement {
            Assign::Equal => {}
            Assign::Plus => self.push_instruction(Instruction::Add),
            Assign::Minus => self.push_instruction(Instruction::Subtract),
            Assign::Multiply => self.push_instruction(Instruction::Multiply),
            Assign::Divide => self.push_instruction(Instruction::Divide),
            Assign::Modulo => self.push_instruction(Instruction::Modulo),
        }

        match self.function_stack.last() {
            Some(func) => {
                if let Some(local_index) = func.find_variable(&variable) {
                    self.emit_instruction(Instruction::WriteLocal(local_index))
                } else {
                    // TODO : captures or globals.
                    todo!()
                }
            }
            None => {
                let global_index = self.code.add_global(variable);
                self.emit_instruction(Instruction::WriteGlobal(global_index));
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
pub enum ParserErrorKind {
    Lexer(LexerErrorKind),
    ExpectExpression,
    Expected(TokenKind),
    Unexpected(TokenKind),
    UnexpectedId,
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Lexer(err) => write!(formatter, "{}", err),
            Self::ExpectExpression => formatter.write_str("expected expression"),
            Self::Expected(token) => write!(formatter, "expected '{}'", token),
            Self::Unexpected(token) => write!(formatter, "unexpected token : '{}'", token),
            Self::UnexpectedId => formatter.write_str("unexpected identifier"),
        }
    }
}

#[derive(Debug)]
pub struct ParserError<'a> {
    kind: ParserErrorKind,
    range: Range,
    source: Source<'a>,
    pub continuable: Continue,
}

impl<'a> From<LexerError<'a>> for ParserError<'a> {
    fn from(lexer_error: LexerError<'a>) -> Self {
        Self {
            kind: ParserErrorKind::Lexer(lexer_error.kind),
            range: lexer_error.range,
            source: lexer_error.source,
            continuable: lexer_error.continuable,
        }
    }
}

impl<'a> fmt::Display for ParserError<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        display_error(
            |f| write!(f, "{}", self.kind),
            self.range,
            &self.source,
            false,
            formatter,
        )
    }
}
