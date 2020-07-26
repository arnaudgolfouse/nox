//! Lexer for the nox language.

#[cfg(test)]
mod tests;

mod token;

use crate::{
    error::{display_error, Continue},
    Position, Range, Source,
};
pub use token::{Assign, Keyword, Operation, Token, TokenKind};

use std::{
    convert::TryFrom,
    fmt::{self, Debug, Display},
    iter::Peekable,
    str::Chars,
};

/// Transform a [Source](../enum.Source.html) into [Token](struct.Token.html)s
pub struct Lexer<'a> {
    /// Source code for this lexer
    pub(crate) source: Source<'a>,
    /// Iterator over the `source`'s chars
    iterator: Peekable<Chars<'a>>,
    /// Next token, pre-parsed
    next_token: Result<Option<Token>, LexerError<'a>>,
    /// Start position of the current token
    current_start: Position,
    /// Current position on the source
    pub(crate) position: Position,
    /// Position of the next token in the source
    next_position: Position,
    /// Position of the previous token in the source
    pub(crate) previous_position: Position,
}

impl<'a> Lexer<'a> {
    /// Creates a new `Lexer` from a `Source`.
    pub fn new(source: Source<'a>) -> Self {
        let mut lexer = Self {
            iterator: source.content().chars().peekable(),
            next_token: Ok(None),
            current_start: Position::default(),
            position: Position::default(),
            next_position: Position::default(),
            previous_position: Position::default(),
            source,
        };
        lexer.next_token = lexer.advance();
        lexer
    }

    /// Creates a new `Lexer` from a `str`.
    pub fn top_level(source: &'a str) -> Self {
        let mut lexer = Self {
            iterator: source.chars().peekable(),
            next_token: Ok(None),
            current_start: Position::default(),
            position: Position::default(),
            next_position: Position::default(),
            previous_position: Position::default(),
            source: Source::TopLevel(source),
        };
        lexer.next_token = lexer.advance();
        lexer
    }

    pub(crate) fn current_range(&self) -> Range {
        Range::new(self.current_start, self.position)
    }

    /// emit an error at the currently parsed token
    fn emit_error(&self, kind: LexerErrorKind, continuable: Continue) -> LexerError<'a> {
        LexerError {
            kind,
            range: self.current_range(),
            source: self.source.clone(),
            continuable,
        }
    }

    /// emit an error at the current position
    fn emit_error_at_position(
        &self,
        kind: LexerErrorKind,
        continuable: Continue,
    ) -> LexerError<'a> {
        LexerError {
            kind,
            range: Range::new(self.next_position, self.next_position),
            source: self.source.clone(),
            continuable,
        }
    }

    /// Parse the attached `Source` into a vector of `Token`s.
    ///
    /// # Errors
    ///
    /// See [LexerErrorKind](enum.LexerErrorKind.html)
    ///
    /// # Examples
    ///
    /// ```
    /// use nox::lexer::{Lexer, TokenKind, Operation};
    /// let mut lexer = Lexer::top_level("def f(a, b) a + b * 4.1");
    /// let mut tokens = lexer.tokens().unwrap();
    /// assert_eq!(TokenKind::Float(4.1), tokens.pop().unwrap().kind);
    /// assert_eq!(TokenKind::Op(Operation::Multiply), tokens.pop().unwrap().kind);
    /// assert_eq!(TokenKind::Id("b".to_owned()), tokens.pop().unwrap().kind);
    /// ```
    pub fn tokens(&mut self) -> Result<Vec<Token>, LexerError<'a>> {
        let mut result = Vec::new();
        while let Some(token) = self.next()? {
            result.push(token)
        }

        Ok(result)
    }

    /// Advance to the next token
    fn advance(&mut self) -> Result<Option<Token>, LexerError<'a>> {
        // skip whitespace
        #[allow(unused_assignments)]
        let mut next_char = ' ';
        loop {
            match self.next_char() {
                Some('\n') => (),
                Some(c) if c.is_whitespace() => (),
                None => {
                    return Ok(None);
                }
                Some(c) => {
                    next_char = c;
                    break;
                }
            }
        }
        self.current_start = self.position;

        let token = match next_char {
            '(' => TokenKind::LPar,
            ')' => TokenKind::RPar,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '.' => TokenKind::Dot,
            ',' => TokenKind::Comma,
            ';' => TokenKind::SemiColon,
            c if c.is_alphanumeric() || c == '_' => {
                let word = self.identifier(next_char);
                match word.as_str() {
                    "and" => TokenKind::Op(Operation::And),
                    "or" => TokenKind::Op(Operation::Or),
                    "xor" => TokenKind::Op(Operation::Xor),
                    "not" => TokenKind::Op(Operation::Not),
                    "_" => TokenKind::Placeholder,
                    s => {
                        if let Ok(keyword) = Keyword::try_from(s) {
                            TokenKind::Keyword(keyword)
                        } else if !c.is_numeric() {
                            TokenKind::Id(word)
                        } else if word.starts_with("0b") {
                            self.parse_base(&word[2..], 2)?
                        } else if word.starts_with("0x") {
                            self.parse_base(&word[2..], 16)?
                        } else if word.starts_with("0o") {
                            self.parse_base(&word[2..], 8)?
                        } else {
                            self.parse_base(&word, 10)?
                        }
                    }
                }
            }
            '"' => TokenKind::Str(self.string('"')?),
            '\'' => TokenKind::Str(self.string('\'')?),
            '=' | '<' | '>' | '+' | '-' | '*' | '/' | '%' => self.op_or_equal(next_char),
            '!' => match self.iterator.peek() {
                Some('=') => {
                    self.next_char();
                    TokenKind::Op(Operation::NEqual)
                }
                _ => TokenKind::Exclamation,
            },
            '^' => TokenKind::Op(Operation::Pow),
            c => return Err(self.emit_error(LexerErrorKind::UnknownCharacter(c), Continue::Stop)),
        };

        Ok(Some(Token {
            kind: token,
            range: Range {
                start: self.current_start,
                end: self.position,
            },
        }))
    }

    /// Parse the next `Token` in the text. If there is no more text to process, returns `None`.
    ///
    /// # Errors
    ///
    /// See [LexerErrorKind](enum.LexerErrorKind.html)
    ///
    /// # Examples
    ///
    /// ```
    /// use nox::lexer::{Lexer, TokenKind, Operation};
    ///
    /// let source = "3 * \"hello\" ^ 2";
    /// let tokens = [
    ///     TokenKind::Int(3),
    ///     TokenKind::Op(Operation::Multiply),
    ///     TokenKind::Str("hello".to_owned()),
    ///     TokenKind::Op(Operation::Pow),
    ///     TokenKind::Int(2),
    /// ];
    /// let mut lexer = Lexer::top_level(source);
    /// for token in tokens.iter() {
    ///     assert_eq!(token, &lexer.next().unwrap().unwrap().kind);
    /// }
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<Token>, LexerError<'a>> {
        let mut token = Ok(None);
        std::mem::swap(&mut token, &mut self.next_token);
        // the real meat of the function is in `advance`
        self.next_token = self.advance();
        token
    }

    /// Peek at the next token.
    ///
    /// This function acts as `next`, but does not advance the iterator.
    ///
    /// # Errors
    ///
    /// See [LexerErrorKind](enum.LexerErrorKind.html)
    ///
    /// # Examples
    ///
    /// ```
    /// use nox::lexer::{Lexer, TokenKind, Operation};
    ///
    /// let source = "3 * \"hello\"";
    /// let tokens = [
    ///     TokenKind::Int(3),
    ///     TokenKind::Op(Operation::Multiply),
    ///     TokenKind::Op(Operation::Multiply),
    ///     TokenKind::Str("hello".to_owned()),
    /// ];
    /// let mut lexer = Lexer::top_level(source);
    /// assert_eq!(tokens[0], lexer.next().unwrap().unwrap().kind);
    /// assert_eq!(tokens[1], lexer.peek().unwrap().unwrap().kind);
    /// assert_eq!(tokens[2], lexer.next().unwrap().unwrap().kind);
    /// assert_eq!(tokens[3], lexer.next().unwrap().unwrap().kind);
    /// ```
    pub fn peek(&self) -> Result<Option<&Token>, LexerError<'a>> {
        match &self.next_token {
            Ok(next_token) => Ok(next_token.as_ref()),
            Err(err) => Err(err.clone()),
        }
    }

    fn parse_base(&mut self, s: &str, base: u32) -> Result<TokenKind, LexerError<'a>> {
        let result = match i64::from_str_radix(s, base) {
            Ok(i) => i,
            Err(err) => return Err(self.emit_error(LexerErrorKind::Parsei64(err), Continue::Stop)),
        };
        // if there is a '.', this is a floating-point number
        let next_char = self.iterator.peek();
        match next_char {
            Some('.') => {
                if base != 10 {
                    return Err(
                        self.emit_error(LexerErrorKind::NumberUnexpectedDot(base), Continue::Stop)
                    );
                }
                self.next_char();
                match self.next_char() {
                    Some(c) => {
                        let float_part = self.identifier(c);
                        self.number_float(&float_part, result)
                    }
                    None => Err(self.emit_error(
                        LexerErrorKind::ExpectedCharacterAfter('.'),
                        Continue::Continue,
                    )),
                }
            }
            _ => Ok(TokenKind::Int(result)),
        }
    }

    fn number_float(&mut self, s: &str, int_part: i64) -> Result<TokenKind, LexerError<'a>> {
        let s = {
            let mut temp = ".".to_owned();
            temp.push_str(s);
            temp
        };
        let float_part = match s.parse::<f64>() {
            Ok(f) => f,
            Err(err) => return Err(self.emit_error(LexerErrorKind::Parsef64(err), Continue::Stop)),
        };
        // if there is a '.', throw an error
        match self.iterator.peek() {
            Some('.') => Err(self
                .emit_error_at_position(LexerErrorKind::NumberUnexpectedDot(10), Continue::Stop)),
            _ => Ok(TokenKind::Float(int_part as f64 + float_part)),
        }
    }

    /// Will make a string out of all the next characters, until `matching_character`.
    fn string(&mut self, matching_character: char) -> Result<String, LexerError<'a>> {
        let mut result = String::new();
        loop {
            let next_char = match self.next_char() {
                None => {
                    return Err(self.emit_error(
                        LexerErrorKind::IncompleteString(matching_character),
                        Continue::Continue,
                    ))
                }
                Some(c) => c,
            };
            if next_char == matching_character {
                break;
            } else {
                result.push(next_char)
            }
        }

        Ok(result)
    }

    /// Parse all the following letters/numbers as part of an identifier, until a whitespace character is met.
    fn identifier(&mut self, first_letter: char) -> String {
        let mut result = String::with_capacity(1);
        result.push(first_letter);

        loop {
            match self.iterator.peek() {
                Some(c) if c.is_alphanumeric() || *c == '_' => {
                    if let Some(c) = self.next_char() {
                        result.push(c)
                    }
                }
                _ => break,
            }
        }

        result
    }

    /// Parse an operator, and eventually make it an assignement.
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// assert_eq!(lexer.op_or_equal('+'), TokenKind::Op(Operation::Plus));
    /// lexer = Lexer::top_level("=");
    /// assert_eq!(lexer.op_or_equal('+'), TokenKind::Assign(Assign::Plus));
    /// ```
    fn op_or_equal(&mut self, op: char) -> TokenKind {
        match self.iterator.peek() {
            Some('=') => {
                self.next_char();
                match op {
                    '=' => TokenKind::Op(Operation::Equal),
                    '<' => TokenKind::Op(Operation::LessEq),
                    '>' => TokenKind::Op(Operation::MoreEq),
                    '+' => TokenKind::Assign(Assign::Plus),
                    '-' => TokenKind::Assign(Assign::Minus),
                    '*' => TokenKind::Assign(Assign::Multiply),
                    '/' => TokenKind::Assign(Assign::Divide),
                    '%' => TokenKind::Assign(Assign::Modulo),
                    _ => unreachable!(),
                }
            }
            _ => match op {
                '=' => TokenKind::Assign(Assign::Equal),
                '<' => TokenKind::Op(Operation::Less),
                '>' => TokenKind::Op(Operation::More),
                '+' => TokenKind::Op(Operation::Plus),
                '-' => TokenKind::Op(Operation::Minus),
                '*' => TokenKind::Op(Operation::Multiply),
                '/' => TokenKind::Op(Operation::Divide),
                '%' => TokenKind::Op(Operation::Modulo),
                _ => unreachable!(),
            },
        }
    }

    /// Gives next char with side-effects : it skips whitespace and advance the position.
    fn next_char(&mut self) -> Option<char> {
        self.previous_position = self.position;
        self.position = self.next_position;
        match self.iterator.next() {
            None => None,
            Some('\n') => {
                self.next_position.line += 1;
                Some('\n')
            }
            Some('#') => {
                while let Some(c) = self.iterator.next() {
                    if c == '\n' {
                        self.next_position = Position {
                            column: 0,
                            line: self.next_position.line + 1,
                        };
                        return Some('\n');
                    }
                }

                None
            }
            Some(c) => {
                self.next_position.column += 1;
                Some(c)
            }
        }
    }
}

/// Kind of errors returned by the lexer
#[derive(Debug, PartialEq, Clone)]
pub enum LexerErrorKind {
    /// A number was malformed because in contained a dot where it should'nt.
    ///
    /// For example, floating point numbers are not supported in base 16, so parsing '0x2.1' will trigger this error.
    NumberUnexpectedDot(u32),
    /// Unknown character.
    ///
    /// This include emoji and some unrecognised non-alphanumeric character (`$` for example).
    UnknownCharacter(char),
    /// Expected a character, but the input was over
    ExpectedCharacterAfter(char),
    /// Missing ending character in a string
    IncompleteString(char),
    /// Error while parsing an integer
    Parsei64(std::num::ParseIntError),
    /// Error while parsing a float
    Parsef64(std::num::ParseFloatError),
}

impl Display for LexerErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::NumberUnexpectedDot(base) => {
                if *base == 10 {
                    write!(formatter, "unexpected dot")
                } else {
                    write!(
                        formatter,
                        "floating-point numbers are not supported for base {}",
                        base
                    )
                }
            }
            Self::UnknownCharacter(c) => write!(formatter, "unknown character : '{}'", c),
            Self::ExpectedCharacterAfter(c) => {
                write!(formatter, "expected character after '{}'", c)
            }
            Self::IncompleteString(c) => write!(formatter, "expected {} to end the string", c),
            Self::Parsei64(err) => write!(formatter, "{}", err),
            Self::Parsef64(err) => write!(formatter, "{}", err),
        }
    }
}

/// A lexer error.
///
/// Contains its kind, as well as other information such as the position of the error in the input
/// text.
///
/// This can be used as such, but it is often preferable to convert it to [Error](../struct.Error.html),
/// which has nicer formatting.
#[derive(Debug, Clone)]
pub struct LexerError<'a> {
    pub(crate) kind: LexerErrorKind,
    pub(crate) range: Range,
    pub(crate) source: Source<'a>,
    pub(crate) continuable: Continue,
}

impl<'a> fmt::Display for LexerError<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let display_message = |formatter: &mut fmt::Formatter| write!(formatter, "{}", self.kind);
        display_error(display_message, self.range, &self.source, false, formatter)
    }
}
