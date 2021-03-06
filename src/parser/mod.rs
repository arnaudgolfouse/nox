//! Parser for the nox language.
//!
//! This will generate bytecode from a [`Source`].
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
mod serialize;

use self::bytecode::Operand;
use self::expression::ExpressionType;
use crate::{
    error::{display_error, Continue},
    lexer::{self, Assign, Keyword, Lexer, Token, TokenKind},
    Source,
};
use std::{convert::TryInto, fmt, iter::Peekable, ops::Range};

pub use self::bytecode::Chunk;
pub use self::serialize::DeserializeError;

pub(crate) use self::bytecode::{Constant, Instruction};

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
    ///
    /// # Bytecode layout
    ///
    /// Assuming `for <var> in <expression> <statements> end` :
    ///
    /// - `<expression>`
    /// - `PREPARE_LOOP $jump`
    /// - `DUPLICATE_TOP 0`
    /// - `CALL 0`
    /// - `$jump` = `JUMP_END_FOR $end_for` // possible extended instructions
    /// - `<statements>`
    /// - `CONTINUE 0`
    /// - `$end_for`
    For {
        /// Address of the `JUMP_END_FOR` instruction
        jump_address: usize,
        /// Index of the loop variable in the local variables stack
        loop_variable_index: usize,
    },
    /// Dummy scope. Used for continuing parsing even with errors.
    Dummy,
}

/// Index of a variable, differentiating between local and captured variables.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub(crate) enum LocalOrCaptured {
    /// local variable
    Local(u32),
    /// captured variable
    Captured(u32),
}

impl fmt::Debug for LocalOrCaptured {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Local(index) => write!(formatter, "Local({})", index),
            Self::Captured(index) => write!(formatter, "Captured({})", index),
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum VariableLocation {
    Undefined,
    /// index of the variable in the `variables` field of the current function.
    Local(usize),
    /// index of the variable in the `globals` field of the current function.
    Global(usize),
    /// index of the variable in the `code.captures` field of the current
    /// function.
    Captured(usize),
}

/// Structure temporary used by the parser to parse a function.
#[derive(Debug)]
struct Function {
    /// Local variables of this function.
    ///
    /// For the top-level, this store the variables for the `for` loops.
    variables: Vec<Box<str>>,
    /// Variables declared with the `global` keyword.
    ///
    /// Contains the index of the variables in the `strings` field of the
    /// `code`.
    globals: Vec<usize>,
    /// Stack of scopes
    scopes: Vec<Scope>,
    /// Positions where the instruction of `code` were emitted.
    ///
    /// These will be used to construct line information later on.
    positions: Vec<usize>,
    /// Bytecode
    chunk: Chunk,
    /// Indicate if this function is a closure.
    closure: bool,
}

impl Function {
    fn new_top_level(name: Box<str>) -> Self {
        Self {
            scopes: Vec::new(),
            variables: Vec::new(),
            globals: Vec::new(),
            positions: Vec::new(),
            chunk: Chunk::new(name),
            closure: false,
        }
    }

    /// This function returns `None` if there is no opened scope in the function
    fn scope(&self) -> Option<&Scope> {
        self.scopes.last()
    }

    fn emit_instruction<Op: Operand>(&mut self, instruction: Instruction<Op>, position: usize) {
        let (instruction, extended) = instruction.into_u8_instructions();
        for extended in Op::iter_extended(&extended) {
            if let Some(extended) = extended {
                self.emit_instruction_u8(extended, position)
            }
        }
        self.emit_instruction_u8(instruction, position)
    }

    fn emit_instruction_u8(&mut self, instruction: Instruction<u8>, position: usize) {
        self.positions.push(position);
        self.chunk.instructions.push(instruction)
    }

    /// Compute the lines informations for the function's chunk and returns it.
    fn finish_chunk(mut self, source: &str) -> Chunk {
        let char_indices = source.char_indices();
        let mut line = 0;
        let mut positions = self.positions.into_iter();
        let mut next_position = positions.next();
        let mut lines = Vec::new();
        'char_indices: for (pos, c) in char_indices {
            if c == '\n' {
                line += 1;
            }
            loop {
                if let Some(next_pos) = next_position {
                    if next_pos <= pos {
                        if let Some((prev_line, nb)) = lines.last_mut() {
                            if *prev_line == line {
                                *nb += 1
                            } else {
                                lines.push((line, 1))
                            }
                        } else {
                            lines.push((line, 1))
                        }
                        next_position = positions.next();
                    } else {
                        break;
                    }
                } else {
                    break 'char_indices;
                }
            }
        }

        self.chunk.line = lines;
        self.chunk
    }
}

/// Parser for the nox language.
pub struct Parser<'a> {
    /// Holds the source code
    source: Source<'a>,
    /// Associated lexer
    lexer: Peekable<Lexer<'a>>,
    /// Errors encoutered while parsing
    errors: Vec<Error>,
    /// Warnings encoutered while parsing
    warnings: Vec<Warning>,
    /// Root function
    top_level: Function,
    /// Nested functions
    function_stack: Vec<Function>,
    /// Range of the currently parsed Token
    current_range: Range<usize>,
    /// Range of the next token
    next_range: Range<usize>,
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
    /// Create a new `Parser` from a [`Source`].
    pub fn new(source: Source<'a>) -> Self {
        let name = Box::from(source.name());
        Self {
            source: source.clone(),
            lexer: Lexer::new(source).peekable(),
            errors: Vec::new(),
            warnings: Vec::new(),
            top_level: Function::new_top_level(name),
            function_stack: Vec::new(),
            current_range: Range::default(),
            next_range: Range::default(),
        }
    }

    /// Returns the function we are currently parsing.
    #[inline]
    fn func(&mut self) -> &mut Function {
        if let Some(func) = self.function_stack.last_mut() {
            func
        } else {
            &mut self.top_level
        }
    }

    /// Emit a new instruction at the current position.
    #[inline]
    fn emit_instruction<Op: bytecode::Operand>(&mut self, instruction: Instruction<Op>) {
        let pos = self.current_range.start;
        self.func().emit_instruction(instruction, pos)
    }

    /// Emit a new u8 instruction at the current position. Same as
    /// [`emit_instruction::<u8>`](Parser::emit_instruction).
    #[inline]
    fn emit_instruction_u8(&mut self, instruction: Instruction<u8>) {
        let pos = self.current_range.start;
        self.func().emit_instruction_u8(instruction, pos)
    }

    /// Returns the next token (or an error), and log an eventual warning.
    ///
    /// Also update `current_range`, `next_range` with the eventual token/error range.
    #[inline]
    fn next(&mut self) -> Option<Result<Token, Error>> {
        self.current_range = self.next_range.clone();
        let result = match self.lexer.next() {
            Some(Ok(token)) => {
                if let Some(warning) = token.warning {
                    self.emit_warning(WarningKind::Lexer(warning), token.range.clone())
                }
                Some(Ok(token))
            }
            Some(Err(err)) => Some(Err(err.into())),
            None => None,
        };
        self.next_range = if let Some(t) = self.lexer.peek() {
            match t {
                Ok(token) => token.range.clone(),
                Err(err) => err.range.clone(),
            }
        } else {
            self.next_range.end..self.next_range.end
        };

        result
    }

    /// Peek and transpose the lexer, cloning the error if necessary
    #[inline]
    fn peek_transpose(&mut self) -> Result<Option<&Token>, Error> {
        match self.lexer.peek() {
            None => Ok(None),
            Some(Ok(token)) => Ok(Some(token)),
            Some(Err(err)) => Err(err.clone().into()),
        }
    }

    /// Return a range at the end of the current token.
    ///
    /// Intended for use when there are no more tokens.
    #[inline]
    const fn end_current_range(&self) -> Range<usize> {
        self.current_range.end..self.current_range.end
    }

    /// Creates an error.
    #[inline]
    fn emit_error(&self, kind: ErrorKind, continuable: Continue, range: Range<usize>) -> Error {
        Error {
            kind,
            continuable,
            range,
            source: self.source.content().into(),
            source_name: Box::from(self.source.name()),
        }
    }

    /// Add a warning to `warnings`.
    #[inline]
    fn emit_warning(&mut self, kind: WarningKind, range: Range<usize>) {
        self.warnings.push(Warning {
            kind,
            range,
            source: self.source.content().into(),
            source_name: Box::from(self.source.name()),
        })
    }

    /// Emit a `Expected(kind)` error at the given range, continuable.
    #[inline]
    fn expected_token(&self, kind: TokenKind, range: Range<usize>) -> Error {
        self.emit_error(ErrorKind::Expected(kind), Continue::Continue, range)
    }

    /// Returns the current scope.
    fn scope(&self) -> Option<&Scope> {
        match self.function_stack.last() {
            Some(func) => func.scope(),
            None => self.top_level.scope(),
        }
    }

    /// Push a scope in either the current function or the top-level.
    fn push_scope(&mut self, scope: Scope) {
        if let Some(func) = self.function_stack.last_mut() {
            func.scopes.push(scope)
        } else {
            self.top_level.scopes.push(scope)
        }
    }

    /// Pop a scope from either the current function or the top-level.
    fn pop_scope(&mut self) -> Option<Scope> {
        match self.function_stack.last_mut() {
            Some(func) => func.scopes.pop(),
            None => self.top_level.scopes.pop(),
        }
    }

    /// Parse the associated [`Source`] as a top-level
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
    ///
    /// # Errors
    ///
    /// This will return all the `Error` encountered in a vector.
    pub fn parse_top_level(mut self) -> Result<(Chunk, Vec<Warning>), Vec<Error>> {
        loop {
            match self.parse_statement() {
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
                        ErrorKind::EndClosure,
                        Continue::Stop,
                        Range::default(),
                    ));
                    if self.panic_mode() {
                        break;
                    }
                }
            }
        }

        if self.errors.is_empty() {
            self.top_level.chunk.locals_number =
                self.top_level.variables.len().try_into().map_err(|_| {
                    vec![self.emit_error(
                        ErrorKind::TooManyLocalVariables(self.top_level.variables.len()),
                        Continue::Stop,
                        self.current_range.clone(),
                    )]
                })?;
            self.top_level
                .emit_instruction_u8(Instruction::PushNil, self.current_range.end);
            self.top_level
                .emit_instruction_u8(Instruction::Return, self.current_range.end);
            Ok((
                self.top_level.finish_chunk(self.source.content()),
                self.warnings,
            ))
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
                Some(Ok(token)) => match token.kind {
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
                Some(Err(err)) => {
                    self.errors.push(err.clone().into());
                }
                None => return true,
            }
            self.next();
        }
    }

    /// Main parsing function : parse a statement, and returns wether the end
    /// of the current function / the top-level, or an error is encountered.
    fn parse_statement(&mut self) -> Result<ParseReturn, Error> {
        let first_token = match self.next() {
            None => {
                return if self.scope().is_some() || !self.function_stack.is_empty() {
                    Err(self
                        .expected_token(TokenKind::Keyword(Keyword::End), self.next_range.clone()))
                } else {
                    Ok(ParseReturn::Stop)
                }
            }
            Some(token) => token?,
        };

        match &first_token.kind {
            // return <expression>
            TokenKind::Keyword(Keyword::Return) => {
                let pos = first_token.range.start;
                let token = self.next().transpose()?;
                self.parse_expression(token, true)?;
                self.func().emit_instruction_u8(Instruction::Return, pos)
            }
            // <...> end
            TokenKind::Keyword(Keyword::End) => {
                if let Some(scope) = self.pop_scope() {
                    match scope {
                        Scope::Dummy => {}
                        Scope::If(if_address) => {
                            let offset = (self.func().chunk.instructions.len() - if_address) as u64;
                            self.func()
                                .chunk
                                .write_jump(if_address, Instruction::JumpPopFalse(offset))
                        }
                        Scope::Else(else_address) => {
                            let offset =
                                (self.func().chunk.instructions.len() - else_address) as u64;
                            self.func()
                                .chunk
                                .write_jump(else_address, Instruction::Jump(offset))
                        }
                        Scope::While(jump_address) => {
                            self.emit_instruction_u8(Instruction::Continue(0));
                            let jump_destination =
                                self.func().chunk.instructions.len() as u64 - jump_address as u64;
                            self.func().chunk.write_jump(
                                jump_address,
                                Instruction::JumpEndWhile(jump_destination),
                            );
                        }
                        Scope::For {
                            jump_address,
                            loop_variable_index,
                        } => {
                            self.emit_instruction_u8(Instruction::Continue(1));
                            let jump_destination =
                                self.func().chunk.instructions.len() as u64 - jump_address as u64;
                            self.func().chunk.write_jump(
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
                    let pos = self.current_range.start;
                    function.emit_instruction_u8(Instruction::PushNil, pos);
                    function.emit_instruction_u8(Instruction::Return, pos);
                    function.chunk.locals_number =
                        function.variables.len().try_into().map_err(|_| {
                            self.emit_error(
                                ErrorKind::TooManyLocalVariables(function.variables.len()),
                                Continue::Stop,
                                self.current_range.clone(),
                            )
                        })?;
                    let is_closure = function.closure;
                    let new_chunk = function.finish_chunk(self.source.content());
                    self.func()
                        .chunk
                        .functions
                        .push(std::sync::Arc::new(new_chunk));
                    if is_closure {
                        return Ok(ParseReturn::StopClosure); // weird edge case : we need to stop parsing now and return to the caller (parse_lambda)
                    }
                } else {
                    return Err(self.emit_error(
                        ErrorKind::Unexpected(TokenKind::Keyword(Keyword::End)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            // if <expression> then <statements> (<else_stm>)? end
            TokenKind::Keyword(Keyword::If) => {
                let token = self.next().transpose()?;
                self.parse_expression(token, true)?;
                if let Some(token) = self.next().transpose()? {
                    match token.kind {
                        TokenKind::Keyword(Keyword::Then) => {}
                        _ => {
                            return Err(self.emit_error(
                                ErrorKind::Expected(TokenKind::Keyword(Keyword::Then)),
                                Continue::Stop,
                                token.range,
                            ))
                        }
                    }
                } else {
                    return Err(self.expected_token(
                        TokenKind::Keyword(Keyword::Then),
                        self.next_range.clone(),
                    ));
                }
                let if_address = self.func().chunk.push_jump();
                self.push_scope(Scope::If(if_address));
            }
            // <...> else <statements> end
            TokenKind::Keyword(Keyword::Else) => {
                if let Some(Scope::If(if_address)) = self.pop_scope() {
                    let else_address = self.func().chunk.push_jump();
                    self.push_scope(Scope::Else(else_address));
                    let offset = (self.func().chunk.instructions.len() - if_address) as u64;
                    self.func()
                        .chunk
                        .write_jump(if_address, Instruction::JumpPopFalse(offset));
                } else {
                    return Err(self.emit_error(
                        ErrorKind::Unexpected(TokenKind::Keyword(Keyword::Else)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            // while <expression> <statements> end
            TokenKind::Keyword(Keyword::While) => {
                let prepare_loop = self.func().chunk.push_jump();
                let token = self.next().transpose()?;
                self.parse_expression(token, true)?;
                // We **can** subtract 1 because parsing an expression always produces instructions.
                // We **need** to because the offset is from the instruction right AFTER the `PrepareWhile`
                let operand = self.func().chunk.instructions.len() - prepare_loop - 1;
                self.func()
                    .chunk
                    .write_jump(prepare_loop, Instruction::PrepareLoop(operand as u64));
                let jump_address = self.func().chunk.push_jump();
                self.push_scope(Scope::While(jump_address))
            }
            // for <id> in <expression> <statements> end
            // for _ in <expression> <statements> end
            TokenKind::Keyword(Keyword::For) => {
                self.push_scope(Scope::Dummy);
                // parse the `for` loop variable and the following `in`
                // Returns an empty `Box<str>` if the variable is a placeholder.
                let for_variable = if let Some(token) = self.next().transpose()? {
                    match token.kind {
                        TokenKind::Id(_) | TokenKind::Placeholder => {
                            if let Some(token) = self.next().transpose()? {
                                match token.kind {
                                    TokenKind::Keyword(Keyword::In) => {}
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
                                    ErrorKind::Expected(TokenKind::Keyword(Keyword::In)),
                                    Continue::Continue,
                                    self.next_range.clone(),
                                ));
                            }
                            if let TokenKind::Id(variable) = token.kind {
                                variable
                            } else {
                                Box::from("")
                            }
                        }
                        _ => {
                            return Err(self.emit_error(
                                ErrorKind::ExpectedId(Some(token.kind)),
                                Continue::Stop,
                                token.range,
                            ))
                        }
                    }
                } else {
                    return Err(self.emit_error(
                        ErrorKind::ExpectedId(None),
                        Continue::Continue,
                        self.next_range.clone(),
                    ));
                };

                let token = self.next().transpose()?;
                self.parse_expression(token, true)?;
                let prepare_loop = self.func().chunk.push_jump();
                self.emit_instruction_u8(Instruction::DuplicateTop(0));
                self.emit_instruction_u8(Instruction::Call(0));
                let operand = self.func().chunk.instructions.len() - prepare_loop - 1;
                #[allow(clippy::panic)]
                {
                    debug_assert_eq!(operand, 2);
                }
                self.func()
                    .chunk
                    .write_jump(prepare_loop, Instruction::PrepareLoop(operand as u64));
                let jump_address = self.func().chunk.push_jump();
                // the variable will be moved.
                let placeholder = for_variable.is_empty();
                let loop_variable_index = if let Some(function) = self.function_stack.last_mut() {
                    function.variables.push(for_variable);
                    function.variables.len() - 1
                } else {
                    self.top_level.variables.push(for_variable);
                    self.top_level.variables.len() - 1
                };
                if placeholder {
                    self.emit_instruction_u8(Instruction::Pop(1))
                } else {
                    self.emit_instruction(Instruction::WriteLocal(loop_variable_index as u64))
                }
                // pop the dummy scope
                self.pop_scope();
                self.push_scope(Scope::For {
                    jump_address,
                    loop_variable_index,
                })
            }
            // fn <id>((<id>,)*) <statements> end
            TokenKind::Keyword(Keyword::Fn) => {
                let function = match self.peek_transpose()? {
                    // named function
                    Some(Token {
                        kind: TokenKind::Id(func_name),
                        ..
                    }) => {
                        let func_name = func_name.clone();
                        self.next().transpose()?;
                        match self.next().transpose()? {
                            Some(Token {
                                kind: TokenKind::LPar,
                                ..
                            }) => {}
                            _ => {
                                return Err(self.emit_error(
                                    ErrorKind::Expected(TokenKind::LPar),
                                    Continue::Stop,
                                    self.current_range.clone(),
                                ))
                            }
                        };
                        let pos = self.current_range.start;
                        let func = self.parse_prototype(func_name.clone(), false)?;
                        self.write_variable(func_name, pos);
                        func
                    }
                    // anonymous function (lambda)
                    Some(Token {
                        kind: TokenKind::LPar,
                        ..
                    }) => {
                        return self
                            .expression_statement(first_token)
                            .map(|_| ParseReturn::Continue);
                    }
                    token => {
                        let kind = ErrorKind::ExpectedId(token.map(|t| t.kind.clone()));
                        return Err(self.emit_error(kind, Continue::Stop, self.next_range.clone()));
                    }
                };
                self.function_stack.push(function);
            }
            // break
            TokenKind::Keyword(Keyword::Break) => match self.find_enclosing_loop() {
                EnclosingLoop::While => self.emit_instruction_u8(Instruction::Break(0)),
                EnclosingLoop::For => self.emit_instruction_u8(Instruction::Break(1)),
                EnclosingLoop::None => {
                    return Err(self.emit_error(
                        ErrorKind::UnexpectedOutsideLoop(TokenKind::Keyword(Keyword::Break)),
                        Continue::Stop,
                        first_token.range,
                    ))
                }
            },
            // continue
            TokenKind::Keyword(Keyword::Continue) => {
                self.emit_instruction_u8(Instruction::Continue(match self.find_enclosing_loop() {
                    EnclosingLoop::While => 0,
                    EnclosingLoop::For => 1,
                    EnclosingLoop::None => {
                        return Err(self.emit_error(
                            ErrorKind::UnexpectedOutsideLoop(TokenKind::Keyword(Keyword::Continue)),
                            Continue::Stop,
                            first_token.range,
                        ))
                    }
                }))
            }
            // global <id>
            TokenKind::Keyword(Keyword::Global) => {
                let global_start = first_token.range.start;
                if let Some(token) = self.next().transpose()? {
                    match token.kind {
                        TokenKind::Id(variable) => {
                            if self.scope().is_some() {
                                return Err(self.emit_error(
                                    ErrorKind::GlobalNoAtRoot,
                                    Continue::Stop,
                                    global_start..token.range.end,
                                ));
                            }
                            if let Some(func) = self.function_stack.last_mut() {
                                for index in &func.globals {
                                    if variable == func.chunk.globals[*index] {
                                        self.emit_warning(
                                            WarningKind::GlobalAlreadyDefined(variable),
                                            global_start..token.range.end,
                                        );
                                        return Ok(ParseReturn::Continue);
                                    }
                                }
                                for var in &func.variables {
                                    if var.as_ref() == variable.as_ref() {
                                        return Err(self.emit_error(
                                            ErrorKind::AlreadyDeclared(variable),
                                            Continue::Stop,
                                            token.range,
                                        ));
                                    }
                                }
                                let index = func.chunk.add_global(variable);
                                func.globals.push(index as usize)
                            } else {
                                self.emit_warning(
                                    WarningKind::GlobalInTopLevel,
                                    first_token.range.start..token.range.end,
                                )
                            }
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
                        self.next_range.clone(),
                    ));
                }
            }
            // _ = <expression>
            TokenKind::Placeholder => {
                if let Some(token) = self.next().transpose()? {
                    if token.kind == TokenKind::Assign(Assign::Equal) {
                        let token = self.next().transpose()?;
                        self.parse_expression(token, true)?;
                        self.emit_instruction_u8(Instruction::Pop(1));
                    } else {
                        return Err(self.emit_error(
                            ErrorKind::Expected(TokenKind::Assign(Assign::Equal)),
                            Continue::Stop,
                            token.range,
                        ));
                    }
                } else {
                    return Err(self.emit_error(
                        ErrorKind::Expected(TokenKind::Assign(Assign::Equal)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            // x = <expression>
            // x.<id>
            // x((<expression>,)*)
            // x[<expression>]
            TokenKind::Id(_) => self.expression_statement(first_token)?,
            // (<expression>)
            TokenKind::LPar => {
                self.parse_expression(Some(first_token), true)?;
            }
            _ => {
                return Err(self.emit_error(
                    ErrorKind::UnexpectedStartStatement(first_token.kind),
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
                        return Some(&function.variables[index as usize]);
                    }
                    LocalOrCaptured::Captured(index) => {
                        captured_index = function.chunk.captures[index as usize];
                    }
                }
            }
            None
        }

        if let Some(func) = self.function_stack.last() {
            // global ?
            for global_index in &func.globals {
                if func.chunk.globals[*global_index].as_ref() == variable {
                    return VariableLocation::Global(*global_index);
                }
            }

            // local ?
            // reverse because of for variables.
            for (index, var) in func.variables.iter().enumerate().rev() {
                if var.as_ref() == variable {
                    return VariableLocation::Local(index);
                }
            }

            // already captured ?
            for (index, var_index) in func.chunk.captures.iter().copied().enumerate() {
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
                        let mut captured_index = LocalOrCaptured::Local(index.try_into().unwrap());
                        // capturing the variable in all subsequent function
                        for function in self.function_stack.iter_mut().skip(func_index + 1) {
                            let next_index = function.chunk.captures.len();
                            function.chunk.captures.push(captured_index);
                            captured_index =
                                LocalOrCaptured::Captured(next_index.try_into().unwrap());
                        }
                        return VariableLocation::Captured(match captured_index {
                            LocalOrCaptured::Local(index) | LocalOrCaptured::Captured(index) => {
                                index as usize
                            }
                        });
                    }
                }

                for (index, var_index) in func.chunk.captures.iter().copied().enumerate() {
                    if find_captured(&self.function_stack[..func_index], var_index)
                        == Some(variable)
                    {
                        let mut captured_index =
                            LocalOrCaptured::Captured(index.try_into().unwrap());
                        // capturing the variable in all subsequent function
                        for function in self.function_stack.iter_mut().skip(func_index + 1) {
                            let next_index = function.chunk.captures.len();
                            function.chunk.captures.push(captured_index);
                            captured_index =
                                LocalOrCaptured::Captured(next_index.try_into().unwrap());
                        }
                        return VariableLocation::Captured(match captured_index {
                            LocalOrCaptured::Local(index) | LocalOrCaptured::Captured(index) => {
                                index as usize
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
            for (index, var) in self.top_level.chunk.globals.iter().enumerate() {
                if var.as_ref() == variable {
                    return VariableLocation::Global(index);
                }
            }
            VariableLocation::Undefined
        }
    }

    /// Emit the correct instruction to write a variable, assuming everything
    /// else has already been parsed.
    fn write_variable(&mut self, variable: Box<str>, position: usize) {
        let instruction = match self.find_variable(&variable) {
            VariableLocation::Undefined => {
                if let Some(func) = self.function_stack.last_mut() {
                    let index = func.variables.len();
                    func.variables.push(variable);
                    Instruction::WriteLocal(index)
                } else {
                    let index = self.func().chunk.add_global(variable);
                    Instruction::WriteGlobal(index)
                }
            }
            VariableLocation::Local(index) => Instruction::WriteLocal(index),
            VariableLocation::Global(index) => Instruction::WriteGlobal(index),
            VariableLocation::Captured(index) => Instruction::WriteCaptured(index),
        };
        self.func().emit_instruction(instruction, position)
    }

    /// Parse a variable assignement, assuming the variable and the assignement
    /// token have already been parsed.
    fn assign_variable(&mut self, variable: Box<str>, assignement: Assign) -> Result<(), Error> {
        let pos = self.current_range.end;
        if !matches!(assignement, Assign::Equal) {
            self.parse_variable(variable.clone(), true)?;
        }
        let token = self.next().transpose()?;
        self.parse_expression(token, true)?;
        match assignement {
            Assign::Equal => {}
            Assign::Plus => self.emit_instruction_u8(Instruction::Add),
            Assign::Minus => self.emit_instruction_u8(Instruction::Subtract),
            Assign::Multiply => self.emit_instruction_u8(Instruction::Multiply),
            Assign::Divide => self.emit_instruction_u8(Instruction::Divide),
            Assign::Modulo => self.emit_instruction_u8(Instruction::Modulo),
        }

        self.write_variable(variable, pos);
        Ok(())
    }

    /// Parse a table member assignement (such as `t.x = ...` or `t[x] = ...`).
    ///
    /// Assumes that everything up to the assignement token has been parsed, and
    /// that the table field is at the top of the stack.
    fn assign_table(&mut self, assignement: Assign) -> Result<(), Error> {
        if !matches!(assignement, Assign::Equal) {
            self.emit_instruction_u8(Instruction::DuplicateTop(1));
            self.emit_instruction_u8(Instruction::ReadTable);
        }

        let token = self.next().transpose()?;
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
    fn parse_prototype(&mut self, name: Box<str>, closure: bool) -> Result<Function, Error> {
        let mut args = Vec::new();
        loop {
            if let Some(token) = self.next().transpose()? {
                match token.kind {
                    TokenKind::RPar => break,
                    TokenKind::Id(arg) => {
                        args.push(arg);
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
                            return Err(self.expected_token(TokenKind::RPar, token.range));
                        }
                    }
                    _ => {
                        return Err(self.emit_error(
                            ErrorKind::ExpectedId(Some(token.kind)),
                            Continue::Stop,
                            token.range,
                        ));
                    }
                }
            } else {
                return Err(self.expected_token(TokenKind::RPar, self.end_current_range()));
            }
        }
        let index = self.func().chunk.functions.len();
        self.emit_instruction(Instruction::ReadFunction(index));

        let mut chunk = Chunk::new(name);

        chunk.arg_number = args.len().try_into().map_err(|_| {
            self.emit_error(
                ErrorKind::TooManyFunctionArgs(args.len()),
                Continue::Stop,
                self.current_range.clone(),
            )
        })?;
        Ok(Function {
            variables: args,
            globals: Vec::new(),
            scopes: Vec::new(),
            positions: Vec::new(),
            chunk,
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
                Scope::For { .. } => return EnclosingLoop::For,
                _ => {}
            }
        }
        EnclosingLoop::None
    }

    /// Tries to parse an expression in a statement position.
    fn expression_statement(&mut self, first_token: Token) -> Result<(), Error> {
        let start = first_token.range.start;
        let expression_type = self.parse_expression(Some(first_token), false)?;
        let expression_range = start..self.current_range.end;
        match expression_type {
            ExpressionType::Assign {
                variable,
                assign_type,
                ..
            } => {
                self.next().transpose()?;
                self.assign_variable(variable, assign_type)?
            }
            ExpressionType::TableWrite(ass) => {
                self.next().transpose()?;
                self.assign_table(ass)?
            }
            ExpressionType::Call => {
                if matches!(
                    self.lexer.peek(),
                    Some(Ok(Token {
                        kind: TokenKind::Assign(_),
                        ..
                    }))
                ) {
                    return Err(self.emit_error(
                        ErrorKind::NonAssignable,
                        Continue::Stop,
                        expression_range,
                    ));
                }
                self.func().emit_instruction_u8(Instruction::Pop(1), start)
            }
            _ => {
                return if let Some(Token {
                    kind: TokenKind::Assign(_),
                    ..
                }) = self.peek_transpose()?
                {
                    Err(self.emit_error(ErrorKind::NonAssignable, Continue::Stop, expression_range))
                } else {
                    Err(self.emit_error(
                        ErrorKind::UnexpectedExpr,
                        Continue::Stop,
                        expression_range,
                    ))
                };
            }
        }
        Ok(())
    }
}

/*
====================================================
= ERRORS ===========================================
====================================================
*/

/// Kinds of errors emmited by the [`Parser`].
#[derive(Debug, PartialEq)]
enum ErrorKind {
    /// Error emitted by the [`Lexer`]
    Lexer(lexer::ErrorKind),
    /// Expected an expression, found something else or nothing.
    ExpectExpression,
    /// Expected a particular token kind, found something else or nothing.
    Expected(TokenKind),
    /// Encountered an unexpected token kind.
    Unexpected(TokenKind),
    /// Encountered an unexpected token kind instead of the beginning of a
    /// statement.
    UnexpectedStartStatement(TokenKind),
    ///  Encountered 'break' or 'continue' outside of a loop
    UnexpectedOutsideLoop(TokenKind),
    /// Expected an identifier, found something else or nothing.
    ExpectedId(Option<TokenKind>),
    /// Parsed an expression that we realized later was in an incorrect
    /// position.
    UnexpectedExpr,
    /// Tried to assign to a read-only expression (such as `0` or `x + y`).
    NonAssignable,
    /// Tried to end a closure, but the we were at the top-level.
    ///
    /// In theory this error should never be emmited, it is here to catch bugs
    /// in the parser.
    EndClosure,
    /// Tried to write `global x` where `x` was already used as a local
    /// variable.
    AlreadyDeclared(Box<str>),
    /// Tried to declare the same variable twice in a table, e.g.
    /// 't = {a = 1, a = 2 }'
    TableDoubleAssignement(Box<str>),
    /// `global ...` is only authorized at the root of a function
    GlobalNoAtRoot,
    /// A function had too many arguments
    TooManyFunctionArgs(usize),
    /// A function had too local variable
    TooManyLocalVariables(usize),
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Lexer(err) => write!(formatter, "{}", err),
            Self::ExpectExpression => formatter.write_str("expected expression"),
            Self::Expected(token) => write!(formatter, "expected '{}'", token),
            Self::Unexpected(token) | Self::UnexpectedStartStatement(token) => {
                write!(formatter, "unexpected token : '{}'", token)
            }
            Self::UnexpectedOutsideLoop(token) => {
                write!(formatter, "unexpected '{}' outside of loop", token)
            }
            Self::UnexpectedExpr => formatter.write_str("unexpected expression"),
            Self::ExpectedId(token) => {
                formatter.write_str("expected identifier")?;
                if let Some(token) = token {
                    write!(formatter, ", found '{}'", token)
                } else {
                    Ok(())
                }
            }
            Self::NonAssignable => formatter.write_str("this expression cannot be assigned to"),
            Self::EndClosure => formatter.write_str(
                "This is not an error but an internal hack : you should not be seeing this !",
            ),
            Self::AlreadyDeclared(name) => write!(
                formatter,
                "variable '{}' has already been used as a local variable",
                name.as_ref()
            ),
            Self::TableDoubleAssignement(name) => write!(
                formatter,
                "name '{}' is already declared in the table",
                name.as_ref()
            ),
            Self::GlobalNoAtRoot => formatter
                .write_str("'global ...' statements are only authorized at the root of a function"),
            Self::TooManyFunctionArgs(found) => write!(
                formatter,
                "A function cannot have more than {} arguments, found {}",
                u16::MAX,
                found
            ),
            Self::TooManyLocalVariables(found) => write!(
                formatter,
                "A function cannot have more than {} local variables, found {}",
                u32::MAX,
                found
            ),
        }
    }
}

/// Error emitted during parsing.
#[derive(Debug)]
pub struct Error {
    /// kind of error
    kind: ErrorKind,
    /// range of this error in the `Source`
    range: Range<usize>,
    /// Source code of this error
    source: Box<str>,
    /// Name of the `source`
    source_name: Box<str>,
    /// Indicate wether adding more tokens might remove this error.
    pub continuable: Continue,
}

impl Error {
    fn note(&self) -> Option<String> {
        match self.kind {
            ErrorKind::UnexpectedExpr => Some(format!(
                "you can evaluate the expression by wrapping it in parenthesis -> ({})",
                &self.source[self.range.clone()]
            )),
            ErrorKind::UnexpectedStartStatement(_) => Some(String::from("authorized in this position are 'return', 'global', 'if', 'while', 'for', 'fn', an assignement, or a function call")),
            _ => None,
        }
    }
}

impl From<lexer::Error<'_>> for Error {
    fn from(lexer_error: lexer::Error<'_>) -> Self {
        Self {
            kind: ErrorKind::Lexer(lexer_error.kind),
            range: lexer_error.range,
            source: Box::from(lexer_error.source.content()),
            source_name: Box::from(lexer_error.source.name()),
            continuable: lexer_error.continuable,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        writeln!(formatter)?;
        display_error(
            &self.kind,
            self.note(),
            self.range.clone(),
            &self.source,
            &self.source_name,
            false,
            formatter,
        )
    }
}

impl std::error::Error for Error {}

/*
====================================================
= WARNINGS =========================================
====================================================
*/

/// Kind of warning encountered during parsing
#[derive(Clone, Debug)]
enum WarningKind {
    /// Warning from the [`Lexer`]
    Lexer(lexer::Warning),
    /// A `global ...` statement was in the top-level
    GlobalInTopLevel,
    /// Two similar `global ...` were found in the same function.
    GlobalAlreadyDefined(Box<str>),
}

impl fmt::Display for WarningKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Lexer(warning) => write!(formatter, "{}", warning),
            Self::GlobalInTopLevel => {
                formatter.write_str("global statement has no effect at the top level")
            }
            Self::GlobalAlreadyDefined(name) => write!(
                formatter,
                "variable '{}' is already declared as global",
                name
            ),
        }
    }
}

/// Warning emmited during parsing
#[derive(Clone, Debug)]
pub struct Warning {
    /// kind of warning
    kind: WarningKind,
    /// range of this error in the `Source`
    range: Range<usize>,
    /// Source code of this error
    source: Box<str>,
    /// Name of the `source`
    source_name: Box<str>,
}

impl fmt::Display for Warning {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        writeln!(formatter)?;
        display_error::<_, &str>(
            &self.kind,
            None,
            self.range.clone(),
            &self.source,
            &self.source_name,
            true,
            formatter,
        )
    }
}
