pub mod bytecode;
mod expression;

use crate::{
    error::{display_error, Continue},
    lexer::{Assign, Keyword, Lexer, LexerError, LexerErrorKind, Token, TokenKind},
    Range, Source,
};
use bytecode::{Chunk, Constant, Instruction};
use expression::{ExpressionParser, ExpressionType};
use std::fmt;

#[derive(Debug, Clone, Copy)]
enum Scope {
    /// `if` statement. Contains the address of the `JumpPopFalse` instruction.
    If(usize),
    /// `else` statement. Contains the address of the `Jump` instruction at the end of the `if` block.
    Else(usize),
    /// `while` statement
    While,
    /// `for` statement
    For,
}

/// Structure temporary used by the parser to parse a function.
#[derive(Debug)]
struct Function {
    variables: Vec<String>,
    scopes: Vec<Scope>,
    code: Chunk,
    arg_number: u32,
}

impl Function {
    fn new(name: String) -> Self {
        Self {
            variables: Vec::new(),
            scopes: Vec::new(),
            code: Chunk::new(name),
            arg_number: 0,
        }
    }

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
            code: Chunk::new(chunk_name),
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

    /// Emit a `Expected [token]` error at the curretn position, continuable.
    #[inline]
    fn expected_token<T>(&self, kind: TokenKind) -> Result<T, ParserError<'a>> {
        Err(self.emit_error(
            ParserErrorKind::Expected(kind),
            Continue::ContinueWithNewline,
            Range::new(self.lexer.position, self.lexer.position),
        ))
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
                    self.expected_token(TokenKind::Keyword(Keyword::End))
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
                } else if let Some(mut function) = self.function_stack.pop() {
                    self.push_instruction(Instruction::PushNil);
                    self.push_instruction(Instruction::Return);
                    std::mem::swap(&mut self.code, &mut function.code);
                    self.code.functions.push(function.code);
                } else {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::End)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            TokenKind::Keyword(Keyword::If) => {
                let token = self.next()?;
                self.parse_expression(token, true)?;
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
            TokenKind::Keyword(Keyword::Fn) => {
                let mut function = match self.next()? {
                    Some(Token {
                        kind: TokenKind::Id(func_name),
                        ..
                    }) => {
                        match self.next()? {
                            Some(Token {
                                kind: TokenKind::LPar,
                                ..
                            }) => {}
                            token => {
                                return Err(self.emit_error(
                                    ParserErrorKind::Expected(TokenKind::LPar),
                                    Continue::Stop,
                                    if let Some(token) = token {
                                        token.range
                                    } else {
                                        Range::new(self.lexer.position, self.lexer.position)
                                    },
                                ))
                            }
                        };
                        self.parse_prototype(func_name)?
                    }
                    token => {
                        return Err(self.emit_error(
                            ParserErrorKind::ExpectedId,
                            Continue::Stop,
                            if let Some(token) = token {
                                token.range
                            } else {
                                Range::new(self.lexer.position, self.lexer.position)
                            },
                        ))
                    }
                };
                std::mem::swap(&mut self.code, &mut function.code);
                self.function_stack.push(function);
            }
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

    /// Parse a function prototype, e.g. 'fn f(a, b)'
    fn parse_prototype(&mut self, name: String) -> Result<Function, ParserError<'a>> {
        let mut args = Vec::new();
        loop {
            if let Some(token) = self.next()? {
                match token.kind {
                    TokenKind::RPar => break,
                    TokenKind::Id(arg) => {
                        args.push(arg);
                        if let Some(token) = self.next()? {
                            match token.kind {
                                TokenKind::Comma => {}
                                TokenKind::RPar => break,
                                _ => {
                                    return Err(self.emit_error(
                                        ParserErrorKind::Unexpected(token.kind),
                                        Continue::Stop,
                                        token.range,
                                    ))
                                }
                            }
                        } else {
                            return self.expected_token(TokenKind::RPar);
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
                return self.expected_token(TokenKind::RPar);
            }
        }
        self.emit_instruction(Instruction::PushFunction(self.code.functions.len() as u32));
        match self.function_stack.last() {
            Some(func) => {
                if let Some(local_index) = func.find_variable(&name) {
                    self.emit_instruction(Instruction::WriteLocal(local_index))
                } else {
                    // TODO : captures or globals.
                    todo!()
                }
            }
            None => {
                let global_index = self.code.add_global(name.clone());
                self.emit_instruction(Instruction::WriteGlobal(global_index));
            }
        }

        let arg_number = args.len() as _;
        Ok(Function {
            variables: args,
            arg_number,
            scopes: Vec::new(),
            code: Chunk::new(name),
        })
    }
}

#[derive(Debug)]
pub enum ParserErrorKind {
    Lexer(LexerErrorKind),
    ExpectExpression,
    Expected(TokenKind),
    Unexpected(TokenKind),
    ExpectedId,
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
            Self::ExpectedId => formatter.write_str("expected identifier"),
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn errors() {
        // no expression after 'return'
        let parser = Parser::new(Source::TopLevel("return"));
        assert!(parser.parse_top_level().is_err());

        // no 'end' to close this 'if'
        let parser = Parser::new(Source::TopLevel("if true return 0 else return 1"));
        assert!(parser.parse_top_level().is_err());
    }

    #[test]
    fn simple_statements() {
        let parser = Parser::new(Source::TopLevel("return 1"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(1)]);
        assert_eq!(
            chunk.code,
            [Instruction::ReadConstant(0), Instruction::Return]
        );

        let parser = Parser::new(Source::TopLevel("if 1 + 2 return 3 end"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(
            chunk.constants,
            [Constant::Int(1), Constant::Int(2), Constant::Int(3)]
        );
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadConstant(0),
                Instruction::ReadConstant(1),
                Instruction::Add,
                Instruction::JumpPopFalse(6),
                Instruction::ReadConstant(2),
                Instruction::Return
            ]
        );

        let parser = Parser::new(Source::TopLevel(
            "
        if (\"hello\" + \"world\") == \"hello world\"
            return f(2, true)
        else
            return 5 - (f - g)(6) * 8
        end",
        ));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(
            chunk.constants,
            [
                Constant::String("hello".to_owned()),
                Constant::String("world".to_owned()),
                Constant::String("hello world".to_owned()),
                Constant::Int(2),
                Constant::Int(5),
                Constant::Int(6),
                Constant::Int(8),
            ]
        );
        assert_eq!(chunk.globals, [String::from("f"), String::from("g")]);
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadConstant(0),
                Instruction::ReadConstant(1),
                Instruction::Add,
                Instruction::ReadConstant(2),
                Instruction::Equal,
                Instruction::JumpPopFalse(12),
                Instruction::ReadGlobal(0),
                Instruction::ReadConstant(3),
                Instruction::PushTrue,
                Instruction::Call(2),
                Instruction::Return,
                Instruction::Jump(22),
                Instruction::ReadConstant(4),
                Instruction::ReadGlobal(0),
                Instruction::ReadGlobal(1),
                Instruction::Subtract,
                Instruction::ReadConstant(5),
                Instruction::Call(1),
                Instruction::ReadConstant(6),
                Instruction::Multiply,
                Instruction::Subtract,
                Instruction::Return,
            ]
        );
    }

    #[test]
    fn tables() {
        let parser = Parser::new(Source::TopLevel("t = {}"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.globals, [String::from("t")]);
        assert_eq!(
            chunk.code,
            [Instruction::MakeTable(0), Instruction::WriteGlobal(0)]
        );

        let parser = Parser::new(Source::TopLevel("t = { x = 1 + 2, y = \"hello\" }"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(
            chunk.constants,
            [
                Constant::String("x".to_owned()),
                Constant::Int(1),
                Constant::Int(2),
                Constant::String("y".to_owned()),
                Constant::String("hello".to_owned())
            ]
        );
        assert_eq!(chunk.globals, [String::from("t")]);
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadConstant(0),
                Instruction::ReadConstant(1),
                Instruction::ReadConstant(2),
                Instruction::Add,
                Instruction::ReadConstant(3),
                Instruction::ReadConstant(4),
                Instruction::MakeTable(2),
                Instruction::WriteGlobal(0)
            ]
        );
    }

    #[test]
    fn functions() {
        let parser = Parser::new(Source::TopLevel("fn f() return 0 end x = f()"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.globals, [String::from("f"), String::from("x")]);
        assert_eq!(
            chunk.code,
            [
                Instruction::PushFunction(0),
                Instruction::WriteGlobal(0),
                Instruction::ReadGlobal(0),
                Instruction::Call(0),
                Instruction::WriteGlobal(1)
            ]
        );
        assert_eq!(
            chunk.functions[0].code,
            [
                Instruction::ReadConstant(0),
                Instruction::Return,
                Instruction::PushNil,
                Instruction::Return
            ]
        )
    }
}
