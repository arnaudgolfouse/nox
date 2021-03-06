use super::Warning;
use logos::Logos;
use std::{
    convert,
    fmt::{self, Write},
    ops::Range,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Logos)]
pub(super) enum RawToken {
    // Operations
    #[token("==")]
    EqualEqual,
    #[token("!=")]
    NEqual,
    #[token("<")]
    Less,
    #[token("<=")]
    LessEq,
    #[token(">")]
    More,
    #[token(">=")]
    MoreEq,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Multiply,
    #[token("/")]
    Divide,
    #[token("%")]
    Modulo,
    #[token("^")]
    Pow,
    #[token("or")]
    Or,
    #[token("and")]
    And,
    #[token("xor")]
    Xor,
    #[token("not")]
    Not,
    #[token("<<")]
    ShiftLeft,
    #[token(">>")]
    ShiftRight,

    // Assignements
    #[token("=")]
    Equal,
    #[token("+=")]
    PlusEqual,
    #[token("-=")]
    MinusEqual,
    #[token("*=")]
    MultiplyEqual,
    #[token("/=")]
    DivideEqual,
    #[token("%=")]
    ModuloEqual,

    // Keywords
    #[token("fn")]
    Fn,
    #[token("global")]
    Global,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("while")]
    While,
    #[token("end")]
    End,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("return")]
    Return,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("nil")]
    Nil,

    // Punctuation
    #[token("(")]
    LPar,
    #[token(")")]
    RPar,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(".")]
    Dot,
    #[token(",")]
    Comma,
    #[token(";")]
    SemiColon,
    #[token("!")]
    Exclamation,
    #[token("?")]
    Interrogation,

    // Others
    #[token("_")]
    Placeholder,

    #[regex(r"[0-9][0-9a-zA-Z_]*(\.[0-9a-zA-Z_]*)?")]
    Number,
    #[regex(r#"("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*')"#)]
    Str,
    #[regex("[a-zA-Z_][0-9a-zA-Z_]*")]
    Id,

    #[error]
    #[regex(r"([\s]+|#[^\n]*)", logos::skip)]
    Error,
}

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
    /// <<
    ShiftLeft,
    /// >>
    ShiftRight,
}

impl Operation {
    /// Returns [`true`] if this operator can be unary
    pub const fn is_unary(self) -> bool {
        matches!(self, Self::Minus | Self::Not)
    }

    /// Returns [`true`] if this operator can be binary
    pub const fn is_binary(self) -> bool {
        !(matches!(self, Self::Not))
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Equal => formatter.write_str("=="),
            Self::NEqual => formatter.write_str("!="),
            Self::Less => formatter.write_char('<'),
            Self::LessEq => formatter.write_str("<="),
            Self::More => formatter.write_char('>'),
            Self::MoreEq => formatter.write_str(">="),
            Self::Plus => formatter.write_char('+'),
            Self::Minus => formatter.write_char('-'),
            Self::Multiply => formatter.write_char('*'),
            Self::Divide => formatter.write_char('/'),
            Self::Modulo => formatter.write_char('%'),
            Self::Pow => formatter.write_char('^'),
            Self::And => formatter.write_str("and"),
            Self::Or => formatter.write_str("or"),
            Self::Xor => formatter.write_str("xor"),
            Self::Not => formatter.write_str("not"),
            Self::ShiftLeft => formatter.write_str("<<"),
            Self::ShiftRight => formatter.write_str(">>"),
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
/// [`Operation`] enum.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Keyword {
    /// `fn`
    ///
    /// Starts a function
    Fn,
    /// `global`
    ///
    /// Declare a variable in a function as global.
    Global,
    /// `if`
    If,
    /// `then`
    Then,
    /// `else`
    Else,
    /// `for`
    ///
    /// Start a `for` loop
    For,
    /// `in`
    In,
    /// `while`
    ///
    /// Start a `while` loop
    While,
    /// `end`
    ///
    /// End the current `fn`, `if`, `else`, `while`, or `for` block.
    End,
    /// `break`
    ///
    /// Break out of the current loop
    Break,
    /// `continue`
    ///
    /// Skip to the next iteration of the current loop
    Continue,
    /// `return`
    ///
    /// Return from the currently executing code
    Return,
    /// `true`
    ///
    /// Boolean constant `true`
    True,
    /// `false`
    ///
    /// Boolean constant `false`
    False,
    /// `nil`
    ///
    /// Constant `nil`
    Nil,
}

impl fmt::Display for Keyword {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(match self {
            Self::Fn => "fn",
            Self::Global => "global",
            Self::If => "if",
            Self::Then => "then",
            Self::Else => "else",
            Self::For => "for",
            Self::In => "in",
            Self::While => "while",
            Self::End => "end",
            Self::Break => "break",
            Self::Continue => "continue",
            Self::Return => "return",
            Self::True => "true",
            Self::False => "false",
            Self::Nil => "nil",
        })
    }
}

impl convert::TryFrom<&str> for Keyword {
    type Error = ();
    fn try_from(word: &str) -> Result<Self, <Self as convert::TryFrom<&str>>::Error> {
        match word {
            "fn" => Ok(Self::Fn),
            "global" => Ok(Self::Global),
            "if" => Ok(Self::If),
            "then" => Ok(Self::Then),
            "else" => Ok(Self::Else),
            "for" => Ok(Self::For),
            "in" => Ok(Self::In),
            "while" => Ok(Self::While),
            "end" => Ok(Self::End),
            "break" => Ok(Self::Break),
            "continue" => Ok(Self::Continue),
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
    /// `_`
    Placeholder,
    /// integer literal
    Int(i64),
    /// float literal
    Float(f64),
    /// string literal
    Str(Box<str>),
    Op(Operation),
    /// identifier
    Id(Box<str>),
}

impl TokenKind {
    /// Returns `true` is `self` is a number, a string or a boolean
    pub const fn is_constant(&self) -> bool {
        match self {
            Self::Int(_) | Self::Float(_) | Self::Str(_) => true,
            Self::Keyword(keyword) => {
                matches!(keyword, Keyword::Nil | Keyword::True | Keyword::False)
            }
            _ => false,
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Keyword(keyword) => fmt::Display::fmt(keyword, formatter),
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

/// Token returned by a [`Lexer`](super::Lexer)
#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    /// kind of token.
    pub kind: TokenKind,
    /// start and end of the token in the source text.
    pub range: Range<usize>,
    /// Eventual warning.
    pub warning: Option<Warning>,
}
