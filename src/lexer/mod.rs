//! Lexer for the nox language.

#[cfg(test)]
mod tests;

mod num_parser;
mod token;

pub use token::{Assign, Keyword, Operation, Token, TokenKind};

use crate::{
    error::{display_error, Continue},
    Source,
};
use std::{
    fmt::{self, Debug, Display},
    ops::Range,
};
use token::RawToken;

pub struct Lexer<'source> {
    source: Source<'source>,
    lexer: logos::Lexer<'source, RawToken>,
}

impl<'source> Lexer<'source> {
    pub fn new(source: Source<'source>) -> Self {
        let lexer = logos::Lexer::new(source.content());
        Self { source, lexer }
    }

    pub fn top_level(source: &'source str) -> Self {
        Self {
            source: Source::TopLevel(source),
            lexer: logos::Lexer::new(source),
        }
    }
}

impl<'source> Iterator for Lexer<'source> {
    type Item = Result<Token, Error<'source>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_token = self.lexer.next()?;
        let range = self.lexer.span();
        let mut warning = None;

        let kind = match next_token {
            RawToken::EqualEqual => TokenKind::Op(Operation::Equal),
            RawToken::NEqual => TokenKind::Op(Operation::NEqual),
            RawToken::Less => TokenKind::Op(Operation::Less),
            RawToken::LessEq => TokenKind::Op(Operation::LessEq),
            RawToken::More => TokenKind::Op(Operation::More),
            RawToken::MoreEq => TokenKind::Op(Operation::MoreEq),
            RawToken::Plus => TokenKind::Op(Operation::Plus),
            RawToken::Minus => TokenKind::Op(Operation::Minus),
            RawToken::Multiply => TokenKind::Op(Operation::Multiply),
            RawToken::Divide => TokenKind::Op(Operation::Divide),
            RawToken::Modulo => TokenKind::Op(Operation::Modulo),
            RawToken::Pow => TokenKind::Op(Operation::Pow),
            RawToken::Or => TokenKind::Op(Operation::Or),
            RawToken::And => TokenKind::Op(Operation::And),
            RawToken::Xor => TokenKind::Op(Operation::Xor),
            RawToken::Not => TokenKind::Op(Operation::Not),
            RawToken::ShiftLeft => TokenKind::Op(Operation::ShiftLeft),
            RawToken::ShiftRight => TokenKind::Op(Operation::ShiftRight),
            RawToken::Equal => TokenKind::Assign(Assign::Equal),
            RawToken::PlusEqual => TokenKind::Assign(Assign::Plus),
            RawToken::MinusEqual => TokenKind::Assign(Assign::Minus),
            RawToken::MultiplyEqual => TokenKind::Assign(Assign::Multiply),
            RawToken::DivideEqual => TokenKind::Assign(Assign::Divide),
            RawToken::ModuloEqual => TokenKind::Assign(Assign::Modulo),
            RawToken::Fn => TokenKind::Keyword(Keyword::Fn),
            RawToken::Global => TokenKind::Keyword(Keyword::Global),
            RawToken::If => TokenKind::Keyword(Keyword::If),
            RawToken::Then => TokenKind::Keyword(Keyword::Then),
            RawToken::Else => TokenKind::Keyword(Keyword::Else),
            RawToken::For => TokenKind::Keyword(Keyword::For),
            RawToken::In => TokenKind::Keyword(Keyword::In),
            RawToken::While => TokenKind::Keyword(Keyword::While),
            RawToken::End => TokenKind::Keyword(Keyword::End),
            RawToken::Break => TokenKind::Keyword(Keyword::Break),
            RawToken::Continue => TokenKind::Keyword(Keyword::Continue),
            RawToken::Return => TokenKind::Keyword(Keyword::Return),
            RawToken::True => TokenKind::Keyword(Keyword::True),
            RawToken::False => TokenKind::Keyword(Keyword::False),
            RawToken::Nil => TokenKind::Keyword(Keyword::Nil),
            RawToken::LPar => TokenKind::LPar,
            RawToken::RPar => TokenKind::RPar,
            RawToken::LBracket => TokenKind::LBracket,
            RawToken::RBracket => TokenKind::RBracket,
            RawToken::LBrace => TokenKind::LBrace,
            RawToken::RBrace => TokenKind::RBrace,
            RawToken::Dot => TokenKind::Dot,
            RawToken::Comma => TokenKind::Comma,
            RawToken::SemiColon => TokenKind::SemiColon,
            RawToken::Exclamation => TokenKind::Exclamation,
            RawToken::Interrogation => TokenKind::Interrogation,
            RawToken::Placeholder => TokenKind::Placeholder,
            RawToken::Number => {
                use num_parser::{parse_number, IntOrFloat};

                let number = &self.source.content()[range.clone()];
                match parse_number(number) {
                    Ok((int_or_float, warn)) => {
                        warning = warn;
                        match int_or_float {
                            IntOrFloat::Int(i) => TokenKind::Int(i),
                            IntOrFloat::Float(f) => TokenKind::Float(f),
                        }
                    }
                    Err(err) => {
                        return Some(Err(Error {
                            kind: ErrorKind::NumberError(err),
                            range,
                            source: self.source.clone(),
                            continuable: Continue::Stop,
                        }))
                    }
                }
            }
            RawToken::Str => {
                let range = range.clone();
                match parse_string(
                    self.source.content().as_bytes()[range.start] as char,
                    range,
                    self.source.clone(),
                ) {
                    Ok(boxed_str) => TokenKind::Str(boxed_str),
                    Err(err) => return Some(Err(err)),
                }
            }
            RawToken::Id => TokenKind::Id(self.source.content()[range.clone()].into()),
            RawToken::Error => match self.source.content().as_bytes().get(range.start) {
                Some(c) if *c == b'\'' || *c == b'"' => {
                    match parse_string(*c as char, range.clone(), self.source.clone()) {
                        Ok(string) => TokenKind::Str(string),
                        Err(err) => return Some(Err(err)),
                    }
                }
                _ => {
                    return Some(Err(Error {
                        kind: ErrorKind::UnknownToken,
                        range,
                        source: self.source.clone(),
                        continuable: Continue::Stop,
                    }))
                }
            },
        };
        Some(Ok(Token {
            kind,
            range,
            warning,
        }))
    }
}

/// Escape the characters in a string, and return an owned version.
fn parse_string(
    matching_character: char,
    string_range: Range<usize>,
    source: Source<'_>,
) -> Result<Box<str>, Error<'_>> {
    /// Helper structure to parse a string
    struct StringParser<'source> {
        string_range: Range<usize>,
        position: usize,
        source: Source<'source>,
        chars: std::str::Chars<'source>,
    }

    impl Iterator for StringParser<'_> {
        type Item = char;

        fn next(&mut self) -> Option<Self::Item> {
            let c = self.chars.next()?;
            self.position += c.len_utf8();
            Some(c)
        }
    }

    impl<'source> StringParser<'source> {
        /// Emit an error in the string
        fn error(
            &self,
            kind: ErrorKind,
            range: Range<usize>,
            continuable: Continue,
        ) -> Error<'source> {
            Error {
                kind,
                range: (self.string_range.start + range.start)
                    ..(self.string_range.start + range.end),
                source: self.source.clone(),
                continuable,
            }
        }
    }

    // remove the string delimiters

    let chars = match source
        .content()
        .get(string_range.start + 1..string_range.end.saturating_sub(1))
    {
        Some(source_interior) => {
            let last_char = source
                .content()
                .as_bytes()
                .get(string_range.end.saturating_sub(1))
                .copied()
                .map(|c| c as char);
            match last_char {
                Some(c) if c == matching_character => {} // ok here
                _ => {
                    return Err(Error {
                        kind: ErrorKind::IncompleteString(matching_character),
                        range: string_range.end.saturating_sub(1)..string_range.end,
                        source,
                        continuable: Continue::Continue, // no fear
                    });
                }
            }
            source_interior.chars()
        }
        None => {
            return Err(Error {
                kind: ErrorKind::IncompleteString(matching_character),
                range: string_range.end.saturating_sub(1)..string_range.end,
                source,
                continuable: Continue::Continue, // no fear
            });
        }
    };
    let mut string_parser = StringParser {
        string_range,
        // 1 bc we don't take the string delimiter
        position: 1,
        source,
        chars,
    };

    let mut result = String::new();

    while let Some(c) = string_parser.next() {
        let next_char = if c == '\\' {
            let start_escape_pos = string_parser.position;
            let c = match string_parser.next() {
                Some(c) => c,
                None => {
                    return Err(string_parser.error(
                        ErrorKind::IncompleteString(matching_character),
                        0..0,
                        Continue::Continue,
                    ))
                }
            };
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
                    let lbrace_pos = string_parser.position;
                    match string_parser.next() {
                        Some('{') => {}
                        c => {
                            return Err(string_parser.error(
                                ErrorKind::ExpectedFound('{', c),
                                lbrace_pos..string_parser.position,
                                Continue::Stop,
                            ))
                        }
                    }
                    let mut code_point = String::new();
                    let start_code_point_pos = string_parser.position;
                    loop {
                        if let Some(c) = string_parser.next() {
                            match c {
                                '}' => break,
                                c if c == matching_character => {
                                    return Err(string_parser.error(
                                        ErrorKind::ExpectedFound('}', Some(matching_character)),
                                        string_parser.position..string_parser.position + 1,
                                        Continue::Stop,
                                    ))
                                }
                                _ => code_point.push(c),
                            }
                        } else {
                            return Err(string_parser.error(
                                ErrorKind::IncompleteString(matching_character),
                                0..string_parser.position,
                                Continue::Stop,
                            ));
                        }
                    }
                    let end_code_point_pos = string_parser.position.saturating_sub(1);
                    // TODO : plug our own (very simple !) int parser here
                    match u32::from_str_radix(&code_point, 16) {
                        Ok(code) => match std::char::from_u32(code) {
                            Some(c) => c,
                            None => {
                                return Err(string_parser.error(
                                    ErrorKind::InvalidCodePoint(code),
                                    start_code_point_pos..end_code_point_pos,
                                    Continue::Stop,
                                ))
                            }
                        },
                        Err(err) => {
                            return Err(string_parser.error(
                                ErrorKind::Parseint(err),
                                start_code_point_pos..end_code_point_pos,
                                Continue::Stop,
                            ));
                        }
                    }
                }
                c if c == matching_character => c,
                _ => {
                    return Err(string_parser.error(
                        ErrorKind::UnknownEscape(c),
                        start_escape_pos..string_parser.position,
                        Continue::Stop,
                    ))
                }
            }
        } else {
            c
        };
        result.push(next_char);
    }

    Ok(result.into_boxed_str())
}

/// Kind of errors returned by the [`Lexer`]
#[derive(Debug, PartialEq, Clone)]
pub enum ErrorKind {
    /// The parsed token does not correspond to any known token.
    UnknownToken,
    /// Expected the first character, found the second or nothing
    ExpectedFound(char, Option<char>),
    /// Missing ending character in a string
    IncompleteString(char),
    /// Unknown escape character in a string
    UnknownEscape(char),
    /// Invalid UTF8 code point in string.
    ///
    /// Emmitted by `"\u{code}"` if `code` is invalid.
    InvalidCodePoint(u32),
    /// Error while parsing an integer in `\u{...}`
    Parseint(std::num::ParseIntError),
    /// Error while parsing a number
    NumberError(num_parser::NumberError),
}

impl Display for ErrorKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnknownToken => formatter.write_str("unknown token"),
            Self::ExpectedFound(expected, found) => write!(
                formatter,
                "expected '{}', found {}",
                expected,
                match found {
                    Some(c) => format!("'{}'", c),
                    None => "nothing".to_owned(),
                }
            ),
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

/// A [`Lexer`] error.
///
/// Contains its [kind](ErrorKind), as well as other information such as the
/// position of the error in the input text.
#[derive(Debug, Clone)]
pub struct Error<'a> {
    pub(crate) kind: ErrorKind,
    pub(crate) range: Range<usize>,
    pub(crate) source: Source<'a>,
    pub(crate) continuable: Continue,
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        // we need a displayable type, i32 will do
        display_error::<_, i32>(
            &self.kind,
            None,
            self.range.clone(),
            self.source.content(),
            self.source.name(),
            false,
            formatter,
        )
    }
}

impl std::error::Error for Error<'_> {}

/// Kind of warnings returned by the [`Lexer`]
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
