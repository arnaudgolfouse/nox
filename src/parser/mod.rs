//! Parser for the nox language.
//!
//! This will generate bytecode from a [Source](../enum.Source.html).
//!
//! # Example
//!
//! ```
//! use nox::{parser::Parser, Source};
//! let parser = Parser::new(Source::TopLevel("x = 5 print(x) return x + 1"));
//! let code = parser.parse_top_level().unwrap();
//! ```

#[cfg(test)]
mod tests;

mod bytecode;
mod expression;

use crate::{
    error::{display_error, Continue},
    lexer::{Assign, Keyword, Lexer, LexerError, LexerErrorKind, Token, TokenKind},
    Range, Source,
};
pub use bytecode::Chunk;
pub(crate) use bytecode::{Constant, Instruction};
use expression::{ExpressionParser, ExpressionType};
use std::fmt;

/// Indicate what to do after successfully parsing a statement.
#[derive(Debug, Clone, Copy)]
enum ParseReturn {
    /// Stop parsing, as there are no more tokens
    Stop,
    /// Stop parsing the current closure
    StopClosure,
    /// Continue parsing
    Continue,
}

#[derive(Debug, Clone, Copy)]
enum EnclosingLoop {
    /// No enclosing loop
    None,
    /// First enclosing loop is a `while`
    While,
    /// First enclosing loop is a `for`
    For,
}

#[derive(Debug, Clone)]
enum Scope {
    /// `if` statement. Contains the address of the `JumpPopFalse` instruction.
    If(usize),
    /// `else` statement. Contains the address of the `Jump` instruction at the
    /// end of the `if` block.
    Else(usize),
    /// `while` statement. Contains the address of the jump instruction.
    While(usize),
    /// `for` statement. Contains the address of the jump instruction, and the
    /// index of the loop variable.
    For(usize, usize),
}

/// Index of a variable, differentiating between local and captured variables.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub(crate) enum LocalOrCaptured {
    /// local variable
    Local(usize),
    /// captured variable
    Captured(usize),
}

impl fmt::Debug for LocalOrCaptured {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Local(index) => write!(formatter, "Local({})", index),
            Self::Captured(index) => write!(formatter, "Captured({})", index),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum VariableLocation {
    Undefined,
    Local(usize),
    Global(usize),
    Captured(usize),
}

/// Structure temporary used by the parser to parse a function.
#[derive(Debug)]
struct Function {
    /// Local variables of this function
    variables: Vec<Box<str>>,
    /// Stack of scopes
    scopes: Vec<Scope>,
    /// Bytecode
    code: Chunk,
    /// Indicate if this function is a closure.
    closure: bool,
}

impl Function {
    fn new_top_level(name: Box<str>) -> Self {
        Self {
            scopes: Vec::new(),
            variables: Vec::new(),
            code: Chunk::new(name),
            closure: false,
        }
    }

    /// This function returns `None` if there is no opened scope in the function
    fn scope(&self) -> Option<&Scope> {
        self.scopes.last()
    }
}

/// Parser for the nox language.
pub struct Parser<'a> {
    /// Associated lexer
    lexer: Lexer<'a>,
    /// Errors encoutered while parsing
    errors: Vec<ParserError<'a>>,
    /// Root function
    top_level: Function,
    /// Nested functions
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
    /// Create a new `Parser` from a `Source`.
    pub fn new(source: Source<'a>) -> Self {
        let name = Box::from(source.name());
        Self {
            lexer: Lexer::new(source),
            errors: Vec::new(),
            top_level: Function::new_top_level(name),
            function_stack: Vec::new(),
        }
    }

    #[inline]
    fn current_range(&self) -> Range {
        Range::new(self.lexer.position, self.lexer.position)
    }

    #[inline]
    fn code(&mut self) -> &mut Chunk {
        if let Some(func) = self.function_stack.last_mut() {
            &mut func.code
        } else {
            &mut self.top_level.code
        }
    }

    /// emit a new instruction at the current line.
    #[inline(always)]
    fn emit_instruction<Op: bytecode::Operand>(&mut self, instruction: Instruction<Op>) {
        let line = self.lexer.position.line;
        self.code().emit_instruction(instruction, line)
    }

    /// emit a new u8 instruction at the current line. Same as `emit_instruction::<u8>`.
    #[inline(always)]
    fn emit_instruction_u8(&mut self, instruction: Instruction<u8>) {
        let line = self.lexer.position.line;
        self.code().emit_instruction_u8(instruction, line)
    }

    /// Emit a `Expected [token]` error at the current position, continuable.
    #[inline]
    fn expected_token(&self, kind: TokenKind) -> ParserError<'a> {
        self.emit_error(
            ParserErrorKind::Expected(kind),
            Continue::Continue,
            self.current_range(),
        )
    }

    /// Returns the current scope.
    fn scope(&self) -> Option<&Scope> {
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

    /// Parse the associated [Source](../enum.Source.html) as a top-level
    /// function.
    ///
    ///
    /// # Panic mode
    ///
    /// If an error is encountered, the parser will enter a 'panic mode', and
    /// try to find another valid statement from which to continue parsing.
    ///
    /// This allow the parser to find multiple errors, although there might be
    /// false positives.
    pub fn parse_top_level(mut self) -> Result<Chunk, Vec<ParserError<'a>>> {
        loop {
            match self.parse_statements() {
                Err(err) => {
                    self.errors.push(err);
                    if self.panic_mode() {
                        break;
                    }
                }
                Ok(ParseReturn::Continue) => {}
                Ok(ParseReturn::Stop) => break,
                Ok(ParseReturn::StopClosure) => {
                    self.errors.push(self.emit_error(
                        ParserErrorKind::EndClosure,
                        Continue::Stop,
                        Range::default(),
                    ));
                    if self.panic_mode() {
                        break;
                    }
                }
            }
        }

        // already handled ???
        /*if !self.function_stack.is_empty() {
            /*self.errors
            .push(self.expected_token(TokenKind::Keyword(Keyword::End)));*/
            Err(self.errors)
        } else*/
        if !self.errors.is_empty() {
            Err(self.errors)
        } else {
            self.top_level.code.locals_number = self.top_level.variables.len() as u32;
            self.top_level
                .code
                .emit_instruction_u8(Instruction::PushNil, self.lexer.position.line);
            self.top_level
                .code
                .emit_instruction_u8(Instruction::Return, self.lexer.position.line);
            Ok(self.top_level.code)
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
                    | TokenKind::Keyword(Keyword::Else)
                    | TokenKind::Keyword(Keyword::While)
                    | TokenKind::Keyword(Keyword::For)
                    | TokenKind::Keyword(Keyword::Fn)
                    | TokenKind::Keyword(Keyword::End)
                    | TokenKind::Keyword(Keyword::Break)
                    | TokenKind::Keyword(Keyword::Continue)
                    | TokenKind::Keyword(Keyword::Global)
                    | TokenKind::Id(_) => return false,
                    _ => {}
                },
                Ok(None) => return true,
                Err(err) => {
                    self.errors.push(err.into());
                }
            }
            self.lexer.next();
        }
    }

    fn parse_statements(&mut self) -> Result<ParseReturn, ParserError<'a>> {
        let first_token = match self.lexer.next()? {
            Some(token) => token,
            None => {
                return if self.scope().is_some() || !self.function_stack.is_empty() {
                    Err(self.expected_token(TokenKind::Keyword(Keyword::End)))
                } else {
                    Ok(ParseReturn::Stop)
                }
            }
        };

        match &first_token.kind {
            TokenKind::Keyword(Keyword::Return) => {
                let line = first_token.range.start.line;
                let token = self.next()?;
                self.parse_expression(token, true)?;
                self.code()
                    .emit_instruction::<u8>(Instruction::Return, line)
            }
            TokenKind::Keyword(Keyword::End) => {
                if let Some(scope) = self.pop_scope() {
                    match scope {
                        Scope::If(if_address) => {
                            let offset = (self.code().code.len() - if_address) as u64;
                            self.code()
                                .write_jump(if_address, Instruction::JumpPopFalse(offset))
                        }
                        Scope::Else(else_address) => {
                            let offset = (self.code().code.len() - else_address) as u64;
                            self.code()
                                .write_jump(else_address, Instruction::Jump(offset))
                        }
                        Scope::While(jump_address) => {
                            self.emit_instruction_u8(Instruction::Continue(0));
                            let jump_destination =
                                self.code().code.len() as u64 - jump_address as u64;
                            self.code().write_jump(
                                jump_address,
                                Instruction::JumpEndWhile(jump_destination),
                            );
                        }
                        Scope::For(jump_address, loop_variable_index) => {
                            self.emit_instruction_u8(Instruction::Continue(1));
                            let jump_destination =
                                self.code().code.len() as u64 - jump_address as u64;
                            self.code().write_jump(
                                jump_address,
                                Instruction::JumpEndFor(jump_destination),
                            );
                            // 'remove' the loop variable
                            match self.function_stack.last_mut() {
                                Some(func) => func.variables[loop_variable_index] = Box::from(""),
                                None => {
                                    self.top_level.variables[loop_variable_index] = Box::from("")
                                }
                            }
                        }
                    }
                } else if let Some(mut function) = self.function_stack.pop() {
                    let line = self.lexer.position.line;
                    function
                        .code
                        .emit_instruction_u8(Instruction::PushNil, line);
                    function.code.emit_instruction_u8(Instruction::Return, line);
                    function.code.locals_number = function.variables.len() as u32;
                    self.code()
                        .functions
                        .push(std::sync::Arc::new(function.code));
                    if function.closure {
                        return Ok(ParseReturn::StopClosure); // weird edge case : we need to stop parsing now and return to the caller (parse_lambda)
                    }
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
                if let Some(token) = self.next()? {
                    match token.kind {
                        TokenKind::Keyword(Keyword::Then) => {}
                        _ => {
                            return Err(self.emit_error(
                                ParserErrorKind::Unexpected(token.kind),
                                Continue::Stop,
                                token.range,
                            ))
                        }
                    }
                } else {
                    return Err(self.expected_token(TokenKind::Keyword(Keyword::Then)));
                }
                let if_address = self.code().push_jump();
                self.push_scope(Scope::If(if_address));
            }
            TokenKind::Keyword(Keyword::Else) => {
                if let Some(Scope::If(if_address)) = self.pop_scope() {
                    let else_address = self.code().push_jump();
                    self.push_scope(Scope::Else(else_address));
                    let offset = (self.code().code.len() - if_address) as u64;
                    self.code()
                        .write_jump(if_address, Instruction::JumpPopFalse(offset));
                } else {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::Else)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            TokenKind::Keyword(Keyword::While) => {
                let prepare_loop = self.code().push_jump();
                let token = self.next()?;
                self.parse_expression(token, true)?;
                // We can subtract 1 because parsing an expression always produces instructions.
                // We NEED to because the offset is from the instruction right AFTER the `PrepareWhile`
                let operand = self.code().code.len() - prepare_loop - 1;
                self.code()
                    .write_jump(prepare_loop, Instruction::PrepareLoop(operand as u64));
                let jump_address = self.code().push_jump();
                self.push_scope(Scope::While(jump_address))
            }
            TokenKind::Keyword(Keyword::For) => {
                // parse the `for` loop variable and the following `in`
                let for_variable = if let Some(token) = self.next()? {
                    match token.kind {
                        TokenKind::Id(variable) => {
                            if let Some(token) = self.next()? {
                                match token.kind {
                                    TokenKind::Keyword(Keyword::In) => {}
                                    _ => {
                                        return Err(self.emit_error(
                                            ParserErrorKind::Unexpected(token.kind),
                                            Continue::Stop,
                                            token.range,
                                        ))
                                    }
                                }
                            } else {
                                return Err(self.emit_error(
                                    ParserErrorKind::Expected(TokenKind::Keyword(Keyword::In)),
                                    Continue::Continue,
                                    self.current_range(),
                                ));
                            }
                            variable
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
                    return Err(self.emit_error(
                        ParserErrorKind::ExpectedId,
                        Continue::Continue,
                        self.current_range(),
                    ));
                };

                let token = self.next()?;
                self.parse_expression(token, true)?;
                let prepare_loop = self.code().push_jump();
                self.emit_instruction_u8(Instruction::DuplicateTop(0));
                self.emit_instruction_u8(Instruction::Call(0));
                let operand = self.code().code.len() - prepare_loop - 1;
                self.code()
                    .write_jump(prepare_loop, Instruction::PrepareLoop(operand as u64));
                let jump_address = self.code().push_jump();
                let index = match self.function_stack.last_mut() {
                    Some(function) => {
                        function.variables.push(for_variable);
                        function.variables.len() - 1
                    }
                    None => {
                        self.top_level.variables.push(for_variable);
                        self.top_level.variables.len() - 1
                    }
                };
                self.emit_instruction(Instruction::WriteLocal(index as u64));
                self.push_scope(Scope::For(jump_address, index))
            }
            TokenKind::Keyword(Keyword::Fn) => {
                let function = match self.peek()? {
                    Some(Token {
                        kind: TokenKind::Id(func_name),
                        ..
                    }) => {
                        let func_name = func_name.clone();
                        self.next()?;
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
                                        self.current_range()
                                    },
                                ))
                            }
                        };
                        let func = self.parse_prototype(func_name.clone(), false)?;
                        self.write_variable(func_name);
                        func
                    }
                    Some(Token {
                        kind: TokenKind::LPar,
                        ..
                    }) => {
                        self.parse_expression(Some(first_token), true)?;
                        return Ok(ParseReturn::Continue);
                    }
                    token => {
                        return Err(self.emit_error(
                            ParserErrorKind::ExpectedId,
                            Continue::Stop,
                            if let Some(token) = token {
                                token.range
                            } else {
                                self.current_range()
                            },
                        ))
                    }
                };
                self.function_stack.push(function);
            }
            TokenKind::Keyword(Keyword::Break) => match self.find_enclosing_loop() {
                EnclosingLoop::While => self.emit_instruction_u8(Instruction::Break(0)),
                EnclosingLoop::For => self.emit_instruction_u8(Instruction::Break(1)),
                EnclosingLoop::None => {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::Break)),
                        Continue::Stop,
                        first_token.range,
                    ))
                }
            },
            TokenKind::Keyword(Keyword::Continue) => match self.find_enclosing_loop() {
                EnclosingLoop::While => self.emit_instruction_u8(Instruction::Continue(0)),
                EnclosingLoop::For => self.emit_instruction_u8(Instruction::Continue(1)),
                EnclosingLoop::None => {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::Continue)),
                        Continue::Stop,
                        first_token.range,
                    ))
                }
            },
            TokenKind::Id(_) => {
                let range = first_token.range;
                let expression_type = self.parse_expression(Some(first_token), false)?;
                match expression_type {
                    ExpressionType::Assign(var, ass, _) => {
                        self.lexer.next()?;
                        self.assign_variable(var, ass)?
                    }
                    ExpressionType::TableWrite(ass) => {
                        self.lexer.next()?;
                        self.assign_table(ass)?
                    }
                    ExpressionType::Call => self.emit_instruction_u8(Instruction::Pop(1)),
                    _ => {
                        let range = Range::new(range.start, self.lexer.previous_position);
                        return if let Some(Token {
                            kind: TokenKind::Assign(_),
                            ..
                        }) = self.lexer.peek()?
                        {
                            Err(self.emit_error(
                                ParserErrorKind::NonAssignable,
                                Continue::Stop,
                                range,
                            ))
                        } else {
                            Err(self.emit_error(
                                ParserErrorKind::UnexpectedExpr,
                                Continue::Stop,
                                range,
                            ))
                        };
                    }
                }
            }
            TokenKind::LPar => {
                self.parse_expression(Some(first_token), true)?;
            }
            _ => {
                return Err(self.emit_error(
                    ParserErrorKind::Unexpected(first_token.kind),
                    Continue::Stop,
                    first_token.range,
                ))
            }
        }

        Ok(ParseReturn::Continue)
    }

    /// Attempt to determine the given variable location relative to the current
    /// function.
    fn find_variable(&mut self, variable: &str) -> VariableLocation {
        // Resolve a captured variable index
        fn find_captured(
            functions: &[Function],
            mut captured_index: LocalOrCaptured,
        ) -> Option<&str> {
            for function in functions.iter().rev() {
                match captured_index {
                    LocalOrCaptured::Local(index) => {
                        return Some(&function.variables[index]);
                    }
                    LocalOrCaptured::Captured(index) => {
                        captured_index = function.code.captures[index];
                    }
                }
            }
            None
        }

        if let Some(func) = self.function_stack.last() {
            // local ?
            // reverse because of for variables.
            for (index, var) in func.variables.iter().enumerate().rev() {
                if var.as_ref() == variable {
                    return VariableLocation::Local(index);
                }
            }

            // already captured ?
            for (index, var_index) in func.code.captures.iter().copied().enumerate() {
                if Some(variable)
                    == find_captured(
                        &self.function_stack[..self.function_stack.len() - 1],
                        var_index,
                    )
                {
                    return VariableLocation::Captured(index);
                }
            }

            // in another function ? Then we must capture the variable a lot of time !
            for (func_index, func) in self.function_stack.iter().enumerate().rev().skip(1) {
                for (index, var) in func.variables.iter().enumerate() {
                    if var.as_ref() == variable {
                        let mut captured_index = LocalOrCaptured::Local(index);
                        // capturing the variable in all subsequent function
                        for function in self.function_stack.iter_mut().skip(func_index + 1) {
                            let next_index = function.code.captures.len();
                            function.code.captures.push(captured_index);
                            captured_index = LocalOrCaptured::Captured(next_index);
                        }
                        return VariableLocation::Captured(match captured_index {
                            LocalOrCaptured::Local(index) | LocalOrCaptured::Captured(index) => {
                                index
                            }
                        });
                    }
                }

                for (index, var_index) in func.code.captures.iter().copied().enumerate() {
                    if find_captured(&self.function_stack[..func_index], var_index)
                        == Some(variable)
                    {
                        let mut captured_index = LocalOrCaptured::Captured(index);
                        // capturing the variable in all subsequent function
                        for function in self.function_stack.iter_mut().skip(func_index + 1) {
                            let next_index = function.code.captures.len();
                            function.code.captures.push(captured_index);
                            captured_index = LocalOrCaptured::Captured(next_index);
                        }
                        return VariableLocation::Captured(match captured_index {
                            LocalOrCaptured::Local(index) | LocalOrCaptured::Captured(index) => {
                                index
                            }
                        });
                    }
                }
            }

            VariableLocation::Undefined
        } else {
            for (index, var) in self.top_level.variables.iter().enumerate().rev() {
                if var.as_ref() == variable {
                    return VariableLocation::Local(index);
                }
            }
            for (index, var) in self.top_level.code.globals.iter().enumerate() {
                if var.as_ref() == variable {
                    return VariableLocation::Global(index);
                }
            }
            VariableLocation::Undefined
        }
    }

    /// Emit the correct instruction to write a variable, assuming everything
    /// else has already been parsed.
    fn write_variable(&mut self, variable: Box<str>) {
        let instruction = match self.find_variable(&variable) {
            VariableLocation::Undefined => match self.function_stack.last_mut() {
                Some(func) => {
                    let index = func.variables.len() as u32;
                    func.variables.push(variable);
                    Instruction::WriteLocal(index)
                }
                None => {
                    let index = self.code().add_string(variable);
                    Instruction::WriteGlobal(index)
                }
            },
            VariableLocation::Local(index) => Instruction::WriteLocal(index as u32),
            VariableLocation::Global(index) => Instruction::WriteGlobal(index as u32),
            VariableLocation::Captured(index) => Instruction::WriteCaptured(index as u32),
        };
        self.emit_instruction(instruction);
    }

    fn assign_variable(
        &mut self,
        variable: Box<str>,
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
            Assign::Plus => self.emit_instruction_u8(Instruction::Add),
            Assign::Minus => self.emit_instruction_u8(Instruction::Subtract),
            Assign::Multiply => self.emit_instruction_u8(Instruction::Multiply),
            Assign::Divide => self.emit_instruction_u8(Instruction::Divide),
            Assign::Modulo => self.emit_instruction_u8(Instruction::Modulo),
        }

        self.write_variable(variable);
        Ok(())
    }

    /// Write a table member
    fn assign_table(&mut self, assignement: Assign) -> Result<(), ParserError<'a>> {
        match assignement {
            Assign::Equal => {}
            _ => {
                self.emit_instruction_u8(Instruction::DuplicateTop(1));
                self.emit_instruction_u8(Instruction::ReadTable);
            }
        }

        let token = self.lexer.next()?;
        self.parse_expression(token, true)?;

        match assignement {
            Assign::Equal => {}
            Assign::Plus => self.emit_instruction_u8(Instruction::Add),
            Assign::Minus => self.emit_instruction_u8(Instruction::Subtract),
            Assign::Multiply => self.emit_instruction_u8(Instruction::Multiply),
            Assign::Divide => self.emit_instruction_u8(Instruction::Divide),
            Assign::Modulo => self.emit_instruction_u8(Instruction::Modulo),
        }

        self.emit_instruction_u8(Instruction::WriteTable);

        Ok(())
    }

    /// Parse a function prototype, e.g. 'fn f(a, b)'
    ///
    /// Assumes the opening `(` has been parsed.
    fn parse_prototype(
        &mut self,
        name: Box<str>,
        closure: bool,
    ) -> Result<Function, ParserError<'a>> {
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
                            return Err(self.expected_token(TokenKind::RPar));
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
                return Err(self.expected_token(TokenKind::RPar));
            }
        }
        let index = self.code().functions.len() as u32;
        self.emit_instruction(Instruction::ReadFunction(index));

        let mut code = Chunk::new(name);
        code.arg_number = args.len() as _;
        Ok(Function {
            variables: args,
            scopes: Vec::new(),
            code,
            closure,
        })
    }

    /// Return `true` if there is an enclosing `while` or `for`.
    fn find_enclosing_loop(&self) -> EnclosingLoop {
        let scopes = match self.function_stack.last() {
            Some(func) => &func.scopes,
            None => &self.top_level.scopes,
        };
        for scope in scopes.iter().rev() {
            match scope {
                Scope::While(_) => return EnclosingLoop::While,
                Scope::For(_, _) => return EnclosingLoop::For,
                _ => {}
            }
        }
        EnclosingLoop::None
    }
}

/*
====================================================
= ERRORS ===========================================
====================================================
*/

#[derive(Debug)]
pub(crate) enum ParserErrorKind {
    Lexer(LexerErrorKind),
    ExpectExpression,
    Expected(TokenKind),
    Unexpected(TokenKind),
    ExpectedId,
    UnexpectedExpr,
    NonAssignable,
    EndClosure,
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Lexer(err) => write!(formatter, "{}", err),
            Self::ExpectExpression => formatter.write_str("expected expression"),
            Self::Expected(token) => write!(formatter, "expected '{}'", token),
            Self::Unexpected(token) => write!(formatter, "unexpected token : '{}'", token),
            Self::UnexpectedExpr => formatter.write_str("unexpected expression"),
            Self::ExpectedId => formatter.write_str("expected identifier"),
            Self::NonAssignable => formatter.write_str("this expression cannot be assigned to"),
            Self::EndClosure => formatter.write_str(
                "This is not an error but an internal hack : you should not be seeing this !",
            ),
        }
    }
}

/// Error emitted during parsing.
#[derive(Debug)]
pub struct ParserError<'a> {
    /// kind of error
    kind: ParserErrorKind,
    /// range of this error in the `Source`
    range: Range,
    /// [Source](../enum.Source.html) of this error
    source: Source<'a>,
    /// Indicate wether adding more tokens might remove this error.
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
            |f| writeln!(f, "{}", self.kind),
            self.range,
            &self.source,
            false,
            formatter,
        )
    }
}
