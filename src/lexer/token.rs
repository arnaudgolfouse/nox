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
    /// `^`
    Pow,
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
            Operation::Pow => formatter.write_char('^'),
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

macro_rules! keywords {
    (
        $(#[$doc:meta])*
        pub enum $K:ident {
            $(
                $(#[$keyword_doc:meta])*
                $keyword:ident => $name:literal,
            )*
        }
    ) => {
$(#[$doc])*
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum $K {
    $(
        $(#[$keyword_doc])*
        $keyword,
    )*
}

impl Display for $K {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            $(
                Self::$keyword => formatter.write_str($name),
            )*
        }
    }
}

impl convert::TryFrom<&str> for $K {
    type Error = ();
    fn try_from(word: &str) -> Result<Self, <Self as convert::TryFrom<&str>>::Error> {
        match word {
            $(
                $name => Ok(Self::$keyword),
            )*
            _ => Err(()),
        }
    }
}
    };
}

keywords! {
/// Keywords of the language
///
/// # Remark
///
/// `and`, `or`, `xor` and `not`, while technically keywords, are found under the
/// [Operation](enum.Operation.html) enum.
pub enum Keyword {
    /// `fn`
    Fn => "fn",
    /// `global`
    Global => "global",
    /// `if`
    If => "if",
    /// `then`
    Then => "then",
    /// `else`
    Else => "else",
    /// `for`
    ///
    /// Start a `for` loop
    For => "for",
    /// `in`
    In => "in",
    /// `while`
    ///
    /// Start a `while` loop
    While => "while",
    /// `end`
    ///
    /// End the current `fn`, `if`, `else`, `while`, or `for` block.
    End => "end",
    /// `break`
    ///
    /// Break out of the current loop
    Break => "break",
    /// `continue`
    ///
    /// Skip to the next iteration of the current loop
    Continue => "continue",
    /// `return`
    ///
    /// Return from the currently executing code
    Return => "return",
    /// `true`
    ///
    /// Boolean constant `true`
    True => "true",
    /// `false`
    ///
    /// Boolean constant `false`
    False => "false",
    /// `nil`
    ///
    /// Constant `nil`
    Nil => "nil",
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
    Str(Box<str>),
    Op(Operation),
    Id(Box<str>),
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
