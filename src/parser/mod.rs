mod bytecode;
mod expression;

use crate::{
    error::{display_error, Continue},
    lexer::{Assign, Keyword, Lexer, LexerError, LexerErrorKind, Token, TokenKind},
    Range, Source,
};
pub use bytecode::{Chunk, Constant, Instruction};
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
enum Scope {
    /// `if` statement. Contains the address of the `JumpPopFalse` instruction.
    If(usize),
    /// `else` statement. Contains the address of the `Jump` instruction at the
    /// end of the `if` block.
    Else(usize),
    /// `while` statement. Contains the address of the expression, and the
    /// address of the conditional jump instruction.
    While(usize, usize),
    /// `for` statement
    For,
}

#[derive(Debug, Clone, Copy)]
enum VariableLocation {
    Undefined,
    Local(usize),
    Global(usize),
    Captured(usize),
    /// (function index, variable index)
    OtherFunc(usize, usize),
}

/// Structure temporary used by the parser to parse a function.
#[derive(Debug)]
struct Function {
    /// Local variables of this function
    variables: Vec<String>,
    /// Variables that the function captures : the first index is the function's, and the second is the variable's.
    captures: Vec<(usize, usize)>,
    /// Stack of scopes
    scopes: Vec<Scope>,
    /// Bytecode
    code: Chunk,
    /// Indicate if this function is a closure.
    closure: bool,
    /// number of arguments
    arg_number: u32,
}

impl Function {
    /// This function returns `None` if there is no opened scope in the function
    fn scope(&self) -> Option<Scope> {
        self.scopes.last().copied()
    }
}

#[derive(Default, Debug)]
pub struct TopLevel {
    variables: Vec<String>,
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
    fn emit_instruction_u8(&mut self, instruction: Instruction<u8>) {
        self.code
            .emit_instruction_u8(instruction, self.lexer.position.line)
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
                    | TokenKind::Keyword(Keyword::Else)
                    | TokenKind::Keyword(Keyword::While)
                    | TokenKind::Keyword(Keyword::For)
                    | TokenKind::Keyword(Keyword::Fn)
                    | TokenKind::Keyword(Keyword::End)
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

    fn parse_statements(&mut self) -> Result<ParseReturn, ParserError<'a>> {
        let first_token = match self.lexer.next()? {
            Some(token) => token,
            None => {
                return if self.scope().is_some() || !self.function_stack.is_empty() {
                    self.expected_token(TokenKind::Keyword(Keyword::End))
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
                self.code.emit_instruction::<u8>(Instruction::Return, line)
            }
            TokenKind::Keyword(Keyword::End) => {
                if let Some(scope) = self.pop_scope() {
                    match scope {
                        Scope::If(if_address) => self.code.write_jump(
                            if_address,
                            Instruction::JumpPopFalse((self.code.code.len() - if_address) as u64),
                        ),
                        Scope::Else(else_address) => self.code.write_jump(
                            else_address,
                            Instruction::Jump((self.code.code.len() - else_address) as u64),
                        ),
                        Scope::While(expression_address, while_address) => {
                            let mut offset_1 = (self.code.code.len() - while_address + 1) as u64;
                            let mut offset_2 = (self.code.code.len() - expression_address) as u64;
                            bytecode::right_jump_operands(&mut offset_1, &mut offset_2);
                            self.code
                                .write_jump(while_address, Instruction::JumpPopFalse(offset_1));
                            let end_address = self.code.push_jump();
                            self.code
                                .write_jump(end_address, Instruction::JumpBack(offset_2));
                        }
                        _ => todo!(),
                    }
                } else if let Some(mut function) = self.function_stack.pop() {
                    self.emit_instruction_u8(Instruction::PushNil);
                    self.emit_instruction_u8(Instruction::Return);
                    std::mem::swap(&mut self.code, &mut function.code);
                    self.code.functions.push(function.code);
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
                let if_address = self.code.push_jump();
                self.push_scope(Scope::If(if_address));
            }
            TokenKind::Keyword(Keyword::Else) => {
                if let Some(Scope::If(if_address)) = self.pop_scope() {
                    let else_address = self.code.push_jump();
                    self.push_scope(Scope::Else(else_address));
                    self.code.write_jump(
                        if_address,
                        Instruction::JumpPopFalse((self.code.code.len() - if_address) as u64),
                    );
                } else {
                    return Err(self.emit_error(
                        ParserErrorKind::Unexpected(TokenKind::Keyword(Keyword::Else)),
                        Continue::Stop,
                        first_token.range,
                    ));
                }
            }
            TokenKind::Keyword(Keyword::While) => {
                let expression_address = self.code.code.len();
                let token = self.next()?;
                self.parse_expression(token, true)?;
                let while_address = self.code.push_jump();
                self.push_scope(Scope::While(expression_address, while_address))
            }
            TokenKind::Keyword(Keyword::For) => todo!(),
            TokenKind::Keyword(Keyword::Fn) => {
                let mut function = match self.peek()? {
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
                                        Range::new(self.lexer.position, self.lexer.position)
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
    fn find_variable(&self, variable: &str) -> VariableLocation {
        if let Some(func) = self.function_stack.last() {
            // local ?
            for (index, var) in func.variables.iter().enumerate() {
                if var == variable {
                    return VariableLocation::Local(index);
                }
            }

            // already captured ?
            for (index, (func_index, var_index)) in func.captures.iter().copied().enumerate() {
                if self.function_stack[func_index].variables[var_index] == variable {
                    return VariableLocation::Captured(index);
                }
            }

            // in another function ?
            for (func_index, func) in self.function_stack.iter().enumerate().rev().skip(1) {
                for (index, var) in func.variables.iter().enumerate() {
                    if var == variable {
                        return VariableLocation::OtherFunc(func_index, index);
                    }
                }
            }

            VariableLocation::Undefined
        } else {
            for (index, var) in self.top_level.variables.iter().enumerate() {
                if var == variable {
                    return VariableLocation::Global(index);
                }
            }
            VariableLocation::Undefined
        }
    }

    /// Emit the correct instruction to write a variable, assuming everything else has already been parsed.
    fn write_variable(&mut self, variable: String) {
        let instruction = match self.find_variable(&variable) {
            VariableLocation::Undefined => match self.function_stack.last_mut() {
                Some(func) => {
                    let index = func.variables.len() as u32;
                    func.variables.push(variable);
                    Instruction::WriteLocal(index)
                }
                None => {
                    let index = self.code.add_string(variable);
                    Instruction::WriteGlobal(index)
                }
            },
            VariableLocation::Local(index) => Instruction::WriteLocal(index as u32),
            VariableLocation::Global(index) => Instruction::WriteGlobal(index as u32),
            VariableLocation::Captured(index) => Instruction::WriteCaptured(index as u32),
            VariableLocation::OtherFunc(func_index, var_index) => {
                if let Some(func) = self.function_stack.last_mut() {
                    let index = func.captures.len() as u32;
                    func.captures.push((func_index, var_index));
                    Instruction::WriteCaptured(index as u32)
                } else {
                    Instruction::Return // we don't care
                }
            }
        };
        self.emit_instruction(instruction);
    }

    pub fn assign_variable(
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
        name: String,
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
        self.emit_instruction(Instruction::ReadFunction(self.code.functions.len() as u32));

        let arg_number = args.len() as _;
        Ok(Function {
            variables: args,
            captures: Vec::new(),
            arg_number,
            scopes: Vec::new(),
            code: Chunk::new(name),
            closure,
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
                Instruction::JumpPopFalse(3),
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
        assert_eq!(chunk.strings, ["f", "g"]);
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadConstant(0),
                Instruction::ReadConstant(1),
                Instruction::Add,
                Instruction::ReadConstant(2),
                Instruction::Equal,
                Instruction::JumpPopFalse(7),
                Instruction::ReadGlobal(0),
                Instruction::ReadConstant(3),
                Instruction::PushTrue,
                Instruction::Call(2),
                Instruction::Return,
                Instruction::Jump(11),
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
    fn loops() {
        let parser = Parser::new(Source::TopLevel("while x > y x -= 1 end"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(1)]);
        assert_eq!(chunk.strings, ["x", "y"]);
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadGlobal(0),
                Instruction::ReadGlobal(1),
                Instruction::More,
                Instruction::JumpPopFalse(6),
                Instruction::ReadGlobal(0),
                Instruction::ReadConstant(0),
                Instruction::Subtract,
                Instruction::WriteGlobal(0),
                Instruction::JumpBack(8)
            ]
        );

        // while extended operands
        let parser = Parser::new(Source::TopLevel(
            "while x > y
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
            end",
        ));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(1)]);
        assert_eq!(chunk.strings, ["x", "y"]);
        assert_eq!(
            chunk.code[0..5],
            [
                Instruction::ReadGlobal(0),
                Instruction::ReadGlobal(1),
                Instruction::More,
                Instruction::Extended(1),
                Instruction::JumpPopFalse(3),
            ]
        );
        for i in 1..65 {
            assert_eq!(
                chunk.code[(i * 4 + 1)..(i + 1) * 4 + 1],
                [
                    Instruction::ReadGlobal(0),
                    Instruction::ReadConstant(0),
                    Instruction::Subtract,
                    Instruction::WriteGlobal(0),
                ]
            );
        }
        assert_eq!(
            chunk.code[261..],
            [Instruction::Extended(1), Instruction::JumpBack(6)]
        );
    }

    #[test]
    fn tables() {
        let parser = Parser::new(Source::TopLevel("t = {}"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.strings, ["t"]);
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
        assert_eq!(chunk.strings, ["t"]);
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

        let parser = Parser::new(Source::TopLevel("t1[t1.a + f()] -= t2.b[t3[2]]"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(
            chunk.constants,
            [
                Constant::String("a".to_owned()),
                Constant::String("b".to_owned()),
                Constant::Int(2)
            ]
        );
        assert_eq!(
            chunk.strings,
            [
                String::from("t1"),
                String::from("f"),
                String::from("t2"),
                String::from("t3")
            ]
        );
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadGlobal(0),
                Instruction::ReadGlobal(0),
                Instruction::ReadConstant(0),
                Instruction::ReadTable,
                Instruction::ReadGlobal(1),
                Instruction::Call(0),
                Instruction::Add,
                Instruction::DuplicateTop(1),
                Instruction::ReadTable,
                Instruction::ReadGlobal(2),
                Instruction::ReadConstant(1),
                Instruction::ReadTable,
                Instruction::ReadGlobal(3),
                Instruction::ReadConstant(2),
                Instruction::ReadTable,
                Instruction::ReadTable,
                Instruction::Subtract,
                Instruction::WriteTable
            ]
        );
    }

    #[test]
    fn functions() {
        let parser = Parser::new(Source::TopLevel("fn f() return 0 end x = f()"));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.strings, ["f", "x"]);
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadFunction(0),
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
        );

        let parser = Parser::new(Source::TopLevel(
            "
        x = 0
        fn f()
            y = 1
            fn g()
                x = 2
                y = 2
            end
            return g + 1
        end
        ",
        ));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(0)]);
        assert_eq!(chunk.strings, ["x", "f"]);
        assert_eq!(
            chunk.code,
            [
                Instruction::ReadConstant(0),
                Instruction::WriteGlobal(0),
                Instruction::ReadFunction(0),
                Instruction::WriteGlobal(1),
            ]
        );
        assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
        assert!(chunk.functions[0].strings.is_empty());
        assert_eq!(
            chunk.functions[0].code,
            [
                Instruction::ReadConstant(0),
                Instruction::WriteLocal(0),
                Instruction::ReadFunction(0),
                Instruction::WriteLocal(1),
                Instruction::ReadLocal(1),
                Instruction::ReadConstant(0),
                Instruction::Add,
                Instruction::Return,
                Instruction::PushNil,
                Instruction::Return
            ]
        );

        assert_eq!(
            chunk.functions[0].functions[0].constants,
            [Constant::Int(2)]
        );
        assert!(chunk.functions[0].functions[0].strings.is_empty());
        assert_eq!(
            chunk.functions[0].functions[0].code,
            [
                Instruction::ReadConstant(0),
                Instruction::WriteLocal(0),
                Instruction::ReadConstant(0),
                Instruction::WriteCaptured(0),
                Instruction::PushNil,
                Instruction::Return
            ]
        );

        let parser = Parser::new(Source::TopLevel(
            "
            x = fn()
                    y = 1
                    return (fn(a, b) return y + a + b end)(1, 2)
                end
            ",
        ));
        let chunk = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.strings, ["x"]);
        assert_eq!(
            chunk.code,
            [Instruction::ReadFunction(0), Instruction::WriteGlobal(0)]
        );
        assert_eq!(
            chunk.functions[0].code,
            [
                Instruction::ReadConstant(0),
                Instruction::WriteLocal(0),
                Instruction::ReadFunction(0),
                Instruction::ReadConstant(0),
                Instruction::ReadConstant(1),
                Instruction::Call(2),
                Instruction::Return,
                Instruction::PushNil,
                Instruction::Return
            ]
        );
        assert_eq!(
            chunk.functions[0].functions[0].code,
            [
                Instruction::ReadCaptured(0),
                Instruction::ReadLocal(0),
                Instruction::ReadLocal(1),
                Instruction::Add,
                Instruction::Add,
                Instruction::Return,
                Instruction::PushNil,
                Instruction::Return
            ]
        );
    }
}
