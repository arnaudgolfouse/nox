use crate::Range;
use std::{
    convert,
    fmt::{self, Display, Write},
};

/// Binary and unary operators
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Operation {
    /// `==`
    Equal,
    /// `!=`
    NEqual,
    /// `<`
    Less,
    /// `<=`
    LessEq,
    /// `>`
    More,
    /// `>=`
    MoreEq,
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Multiply,
    /// `/`
    Divide,
    /// `%`
    Modulo,
    /// `or`
    Or,
    /// `and`
    And,
    /// `xor`
    Xor,
    /// `not`
    Not,
}

impl Operation {
    /// Returns `true` if this operator can be unary
    pub fn is_unary(self) -> bool {
        match self {
            Self::Minus | Self::Not => true,
            _ => false,
        }
    }

    /// Returns `true` if this operator can be binary
    pub fn is_binary(self) -> bool {
        match self {
            Self::Not => false,
            _ => true,
        }
    }
}

impl Display for Operation {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Operation::Equal => formatter.write_str("=="),
            Operation::NEqual => formatter.write_str("!="),
            Operation::Less => formatter.write_char('<'),
            Operation::LessEq => formatter.write_str("<="),
            Operation::More => formatter.write_char('>'),
            Operation::MoreEq => formatter.write_str(">="),
            Operation::Plus => formatter.write_char('+'),
            Operation::Minus => formatter.write_char('-'),
            Operation::Multiply => formatter.write_char('*'),
            Operation::Divide => formatter.write_char('/'),
            Operation::Modulo => formatter.write_char('%'),
            Operation::And => formatter.write_str("and"),
            Operation::Or => formatter.write_str("or"),
            Operation::Xor => formatter.write_str("xor"),
            Operation::Not => formatter.write_str("not"),
        }
    }
}

/// Assignation symbols
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Assign {
    /// `=`
    Equal,
    /// `+=`
    Plus,
    /// `-=`
    Minus,
    /// `*=`
    Multiply,
    /// `/=`
    Divide,
    /// `%=`
    Modulo,
}

/// Keywords of the language
///
/// # Remark
///
/// `and`, `or`, `xor` and `not`, while technically keywords, are found under the
/// [Operation](enum.Operation.html) enum.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Keyword {
    /// `fn`
    Fn,
    /// `if`
    If,
    /// `then`
    Then,
    /// `else`
    Else,
    /// `for`
    For,
    /// `in`
    In,
    /// `while`
    While,
    /// `end`
    End,
    /// `continue`
    Continue,
    /// `break`
    Break,
    /// `return`
    Return,
    /// `true`
    True,
    /// `false`
    False,
    /// `nil`
    Nil,
}

impl Display for Keyword {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Fn => formatter.write_str("fn"),
            Self::If => formatter.write_str("if"),
            Self::Then => formatter.write_str("then"),
            Self::Else => formatter.write_str("else"),
            Self::For => formatter.write_str("for"),
            Self::In => formatter.write_str("in"),
            Self::While => formatter.write_str("while"),
            Self::End => formatter.write_str("end"),
            Self::Continue => formatter.write_str("continue"),
            Self::Break => formatter.write_str("break"),
            Self::Return => formatter.write_str("return"),
            Self::True => formatter.write_str("true"),
            Self::False => formatter.write_str("false"),
            Self::Nil => formatter.write_str("nil"),
        }
    }
}

impl convert::TryFrom<&str> for Keyword {
    type Error = ();
    fn try_from(word: &str) -> Result<Self, <Self as convert::TryFrom<&str>>::Error> {
        match word {
            "fn" => Ok(Self::Fn),
            "if" => Ok(Self::If),
            "then" => Ok(Self::Then),
            "else" => Ok(Self::Else),
            "for" => Ok(Self::For),
            "in" => Ok(Self::In),
            "while" => Ok(Self::While),
            "end" => Ok(Self::End),
            "continue" => Ok(Self::Continue),
            "break" => Ok(Self::Break),
            "return" => Ok(Self::Return),
            "true" => Ok(Self::True),
            "false" => Ok(Self::False),
            "nil" => Ok(Self::Nil),
            _ => Err(()),
        }
    }
}

/// Kind of token encountered. This can be an operator, a keyword, a variable
/// name...
#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    Keyword(Keyword),
    /// `(`
    LPar,
    /// `)`
    RPar,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `.`
    Dot,
    /// `,`
    Comma,
    /// `;`
    SemiColon,
    /// `!`
    Exclamation,
    /// `?`
    Interrogation,
    Assign(Assign),
    Placeholder,
    Int(i64),
    Float(f64),
    Str(String),
    Op(Operation),
    Id(String),
}

impl TokenKind {
    /// Returns `true` is `self` is a number, a string or a boolean
    pub fn is_constant(&self) -> bool {
        match self {
            Self::Int(_) | Self::Float(_) | Self::Str(_) => true,
            Self::Keyword(keyword) => match keyword {
                Keyword::Nil | Keyword::True | Keyword::False => true,
                _ => false,
            },
            _ => false,
        }
    }
}

impl Display for TokenKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Keyword(keyword) => Display::fmt(keyword, formatter),
            Self::LPar => formatter.write_char('('),
            Self::RPar => formatter.write_char(')'),
            Self::LBracket => formatter.write_char('['),
            Self::RBracket => formatter.write_char(']'),
            Self::LBrace => formatter.write_char('{'),
            Self::RBrace => formatter.write_char('}'),
            Self::Dot => formatter.write_char('.'),
            Self::Comma => formatter.write_char(','),
            Self::SemiColon => formatter.write_char(';'),
            Self::Exclamation => formatter.write_char('!'),
            Self::Interrogation => formatter.write_char('?'),
            Self::Assign(a) => match a {
                Assign::Equal => formatter.write_char('='),
                Assign::Plus => formatter.write_str("+="),
                Assign::Minus => formatter.write_str("-="),
                Assign::Multiply => formatter.write_str("*="),
                Assign::Divide => formatter.write_str("/="),
                Assign::Modulo => formatter.write_str("%="),
            },
            Self::Placeholder => formatter.write_str("_"),
            Self::Int(i) => write!(formatter, "{}", i),
            Self::Float(f) => write!(formatter, "{:?}", f),
            Self::Str(s) => write!(formatter, "{:?}", s),
            Self::Op(op) => op.fmt(formatter),
            Self::Id(id) => write!(formatter, "{}", id),
        }
    }
}

/// Token returned by a [Lexer](struct.Lexer.html)
#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    /// kind of token.
    pub kind: TokenKind,
    /// start and end of the token in the source text.
    pub range: Range,
}
