//! Lexer for the nox language.

#[cfg(test)]
mod tests;

mod num_parser;
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
    next_token: Result<Option<Token>, Error<'a>>,
    /// Start position of the current token
    current_start: Position,
    /// End position of the current token
    pub(crate) current_end: Position,
    /// Start position of the previous token
    pub(crate) previous_start: Position,
    /// End position of the previous token
    pub(crate) previous_end: Position,
    /// Current position on the source
    pub(crate) position: Position,
    /// Next position in the source
    next_position: Position,
}

impl<'a> Lexer<'a> {
    /// Creates a new `Lexer` from a `Source`.
    pub fn new(source: Source<'a>) -> Self {
        let mut lexer = Self {
            iterator: source.content().chars().peekable(),
            next_token: Ok(None),
            current_start: Position::default(),
            current_end: Position::default(),
            previous_start: Position::default(),
            previous_end: Position::default(),
            position: Position::default(),
            next_position: Position::default(),
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
            current_end: Position::default(),
            previous_start: Position::default(),
            previous_end: Position::default(),
            position: Position::default(),
            next_position: Position::default(),
            source: Source::TopLevel(source),
        };
        lexer.next_token = lexer.advance();
        lexer
    }

    /// emit an error at the currently parsed token
    fn emit_error(&self, kind: ErrorKind, continuable: Continue) -> Error<'a> {
        Error {
            kind,
            range: Range::new(self.current_start, self.position),
            source: self.source.clone(),
            continuable,
        }
    }

    /// Parse the attached `Source` into a vector of `Token`s.
    ///
    /// # Errors
    ///
    /// See [`ErrorKind`](enum.ErrorKind.html)
    ///
    /// # Examples
    ///
    /// ```
    /// use nox::lexer::{Lexer, TokenKind, Operation};
    /// let mut lexer = Lexer::top_level("def f(a, b) a + b * 4.1");
    /// let mut tokens = lexer.tokens().unwrap();
    /// assert_eq!(TokenKind::Float(4.1), tokens.pop().unwrap().kind);
    /// assert_eq!(TokenKind::Op(Operation::Multiply), tokens.pop().unwrap().kind);
    /// assert_eq!(TokenKind::Id("b".into()), tokens.pop().unwrap().kind);
    /// ```
    pub fn tokens(&mut self) -> Result<Vec<Token>, Error<'a>> {
        let mut result = Vec::new();
        while let Some(token) = self.next()? {
            result.push(token)
        }

        Ok(result)
    }

    /// Advance to the next token
    fn advance(&mut self) -> Result<Option<Token>, Error<'a>> {
        self.previous_start = self.current_start;
        self.previous_end = self.current_end;
        // skip whitespace
        #[allow(unused_assignments)]
        let mut next_char = ' ';
        loop {
            match self.next_char_skip_comment() {
                Some(c) if c.is_whitespace() => {}
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

        let mut warning = None;
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
            c if c.is_ascii_digit() => {
                use num_parser::{parse_number, IntOrFloat};

                let number =
                    self.eat_while(c, |c| c.is_ascii_alphanumeric() || c == '_' || c == '.');

                parse_number(&number)
                    .map(|(int_or_float, warn)| {
                        warning = warn;
                        match int_or_float {
                            IntOrFloat::Int(i) => TokenKind::Int(i),
                            IntOrFloat::Float(f) => TokenKind::Float(f),
                        }
                    })
                    .map_err(|err| self.emit_error(ErrorKind::NumberError(err), Continue::Stop))?
            }
            c if c.is_alphabetic() || c == '_' => {
                let word = self.eat_while(c, |c| c.is_alphanumeric() || c == '_');
                match word.as_ref() {
                    "and" => TokenKind::Op(Operation::And),
                    "or" => TokenKind::Op(Operation::Or),
                    "xor" => TokenKind::Op(Operation::Xor),
                    "not" => TokenKind::Op(Operation::Not),
                    "inf" => TokenKind::Float(f64::INFINITY),
                    "NaN" => TokenKind::Float(f64::NAN),
                    "_" => TokenKind::Placeholder,
                    s => {
                        if let Ok(keyword) = Keyword::try_from(s) {
                            TokenKind::Keyword(keyword)
                        } else {
                            TokenKind::Id(word)
                        }
                    }
                }
            }
            '"' => TokenKind::Str(match self.string('"') {
                Ok(ok) => ok,
                Err(err) => return Err(self.string_error('"', err)),
            }),
            '\'' => TokenKind::Str(match self.string('\'') {
                Ok(ok) => ok,
                Err(err) => return Err(self.string_error('\'', err)),
            }),
            '=' | '<' | '>' | '+' | '-' | '*' | '/' | '%' => self.op_or_equal(next_char),
            '!' => match self.iterator.peek() {
                Some('=') => {
                    self.next_char();
                    TokenKind::Op(Operation::NEqual)
                }
                _ => TokenKind::Exclamation,
            },
            '^' => TokenKind::Op(Operation::Pow),
            c => return Err(self.emit_error(ErrorKind::UnknownCharacter(c), Continue::Stop)),
        };

        self.current_end = self.position;
        Ok(Some(Token {
            kind: token,
            range: Range {
                start: self.current_start,
                end: self.current_end,
            },
            warning,
        }))
    }

    /// Parse the next `Token` in the text. If there is no more text to process, returns `None`.
    ///
    /// # Errors
    ///
    /// See [`ErrorKind`](enum.ErrorKind.html)
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
    ///     TokenKind::Str("hello".into()),
    ///     TokenKind::Op(Operation::Pow),
    ///     TokenKind::Int(2),
    /// ];
    /// let mut lexer = Lexer::top_level(source);
    /// for token in tokens.iter() {
    ///     assert_eq!(token, &lexer.next().unwrap().unwrap().kind);
    /// }
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<Token>, Error<'a>> {
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
    /// See [`ErrorKind`](enum.ErrorKind.html)
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
    ///     TokenKind::Str("hello".into()),
    /// ];
    /// let mut lexer = Lexer::top_level(source);
    /// assert_eq!(tokens[0], lexer.next().unwrap().unwrap().kind);
    /// assert_eq!(tokens[1], lexer.peek().unwrap().unwrap().kind);
    /// assert_eq!(tokens[2], lexer.next().unwrap().unwrap().kind);
    /// assert_eq!(tokens[3], lexer.next().unwrap().unwrap().kind);
    /// ```
    pub fn peek(&self) -> Result<Option<&Token>, Error<'a>> {
        match &self.next_token {
            Ok(next_token) => Ok(next_token.as_ref()),
            Err(err) => Err(err.clone()),
        }
    }

    /// Will make a string out of all the next characters, until
    /// `matching_character`.
    fn string(&mut self, matching_character: char) -> Result<Box<str>, Error<'a>> {
        let mut result = String::new();
        loop {
            let next_char = match self.next_char() {
                None => {
                    return Err(self.emit_error(
                        ErrorKind::IncompleteString(matching_character),
                        Continue::Continue,
                    ))
                }
                Some('\\') => {
                    let c = match self.next_char() {
                        Some(c) => c,
                        None => {
                            return Err(self.emit_error(
                                ErrorKind::IncompleteString(matching_character),
                                Continue::Stop,
                            ))
                        }
                    };
                    let start_pos = self.position;
                    match c {
                        '\\' => '\\',
                        '\'' => '\'',
                        '\"' => '\"',
                        '0' => '\0',
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        // ohhh boy, unicode
                        // ;)
                        // this is the same as in rust : \u{code}
                        'u' => {
                            match self.next_char() {
                                Some('{') => {}
                                c => {
                                    return Err(Error {
                                        kind: ErrorKind::ExpectedFound('{', c),
                                        continuable: Continue::Stop,
                                        source: self.source.clone(),
                                        range: Range::new(start_pos, self.position),
                                    })
                                }
                            }
                            let mut code_point = String::new();
                            loop {
                                if let Some(c) = self.next_char() {
                                    match c {
                                        '}' => break,
                                        c if c == matching_character => {
                                            return Err(Error {
                                                kind: ErrorKind::ExpectedFound(
                                                    '}',
                                                    Some(matching_character),
                                                ),
                                                source: self.source.clone(),
                                                continuable: Continue::Stop,
                                                range: Range::new(start_pos, self.position),
                                            })
                                        }
                                        _ => code_point.push(c),
                                    }
                                } else {
                                    return Err(self.emit_error(
                                        ErrorKind::IncompleteString(matching_character),
                                        Continue::Stop,
                                    ));
                                }
                            }
                            match u32::from_str_radix(&code_point, 16) {
                                Ok(code) => match std::char::from_u32(code) {
                                    Some(c) => c,
                                    None => {
                                        return Err(Error {
                                            source: self.source.clone(),
                                            continuable: Continue::Stop,
                                            kind: ErrorKind::InvalidCodePoint(code),
                                            range: Range::new(start_pos, self.position),
                                        })
                                    }
                                },
                                Err(err) => {
                                    return Err(Error {
                                        source: self.source.clone(),
                                        continuable: Continue::Stop,
                                        kind: ErrorKind::Parseint(err),
                                        range: Range::new(start_pos, self.position),
                                    })
                                }
                            }
                        }
                        c if c == matching_character => c,
                        _ => {
                            return Err(Error {
                                kind: ErrorKind::UnknownEscape(c),
                                continuable: Continue::Stop,
                                source: self.source.clone(),
                                range: Range::new(start_pos, self.position),
                            })
                        }
                    }
                }
                Some(c) => {
                    if c == matching_character {
                        break;
                    } else {
                        c
                    }
                }
            };
            result.push(next_char)
        }

        Ok(result.into_boxed_str())
    }

    /// If an error is encountered in a string, we go to the end of said string
    /// before reporting it.
    fn string_error(&mut self, matching_character: char, error: Error<'a>) -> Error<'a> {
        loop {
            match self.next_char() {
                Some(c) if c == matching_character => break,
                Some(_) => {}
                None => break,
            }
        }
        error
    }

    /// Consume and collect all characters that match `predicate`.
    fn eat_while<F>(&mut self, first_char: char, predicate: F) -> Box<str>
    where
        F: Fn(char) -> bool,
    {
        let mut result = String::new();
        result.push(first_char);

        while let Some(c) = self.iterator.peek().copied() {
            if predicate(c) {
                result.push(c);
                self.next_char();
            } else {
                break;
            }
        }

        result.into_boxed_str()
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
            Some('<') if op == '<' => {
                self.next_char();
                TokenKind::Op(Operation::ShiftLeft)
            }
            Some('>') if op == '>' => {
                self.next_char();
                TokenKind::Op(Operation::ShiftRight)
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

    /// Gives next char and advance the position.
    ///
    /// It will skips commentary, and return the newline.
    fn next_char_skip_comment(&mut self) -> Option<char> {
        self.position = self.next_position;
        match self.iterator.next() {
            None => None,
            Some('\n') => {
                self.next_position = Position {
                    column: 0,
                    line: self.next_position.line + 1,
                };
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

    /// Gives next char and advance the position.
    fn next_char(&mut self) -> Option<char> {
        self.position = self.next_position;
        match self.iterator.next() {
            None => None,
            Some('\n') => {
                self.next_position.line += 1;
                Some('\n')
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
pub enum ErrorKind {
    /// Unknown character.
    ///
    /// This include emoji and some unrecognised non-alphanumeric character (`$`
    /// for example).
    UnknownCharacter(char),
    /// Expected a character, but the input was over
    ExpectedCharacterAfter(char),
    /// Expected the first character, found the second or nothing
    ExpectedFound(char, Option<char>),
    /// Expected a digit, found something else.
    ExpectedDigit(char),
    /// Missing ending character in a string
    IncompleteString(char),
    /// Unknown escape character in a string
    UnknownEscape(char),
    /// Invalid UTF8 code point in string.
    ///
    /// Emmitted with "\u{code}"
    InvalidCodePoint(u32),
    /// Error while parsing an integer in `\u{...}`
    Parseint(std::num::ParseIntError),
    /// Error while parsing a number
    NumberError(num_parser::NumberError),
}

impl Display for ErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::UnknownCharacter(c) => write!(formatter, "unknown character : '{}'", c),
            Self::ExpectedCharacterAfter(c) => {
                write!(formatter, "expected character after '{}'", c)
            }
            Self::ExpectedFound(expected, found) => write!(
                formatter,
                "expected '{}', found {}",
                expected,
                match found {
                    Some(c) => format!("'{}'", c),
                    None => "nothing".to_owned(),
                }
            ),
            Self::ExpectedDigit(c) => write!(formatter, "expected a digit, found {}", c),
            Self::IncompleteString(c) => write!(formatter, "expected {} to end the string", c),
            Self::UnknownEscape(c) => {
                write!(formatter, "unknown escape sequence in string : '\\{}'", c)
            }
            Self::InvalidCodePoint(c) => write!(formatter, "invalid utf8 code point : '{:x}'", c),
            Self::Parseint(err) => write!(formatter, "{}", err),
            Self::NumberError(err) => write!(formatter, "{}", err),
        }
    }
}

/// A lexer error.
///
/// Contains its kind, as well as other information such as the position of the
/// error in the input text.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub(crate) kind: ErrorKind,
    pub(crate) range: Range,
    pub(crate) source: Source<'a>,
    pub(crate) continuable: Continue,
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        // we need a displayable type, i32 will do
        display_error::<_, i32>(
            &self.kind,
            None,
            self.range,
            self.source.content(),
            self.source.name(),
            false,
            formatter,
        )
    }
}

impl std::error::Error for Error<'_> {}

/// Kind of warnings returned by the lexer
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Warning {
    /// A float had excessive precision, and some digits were ignored.
    ExcessiveFloatPrecision,
}

impl fmt::Display for Warning {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ExcessiveFloatPrecision => {
                formatter.write_str("float have an excessive precision : some digits are ignored")
            }
        }
    }
}
