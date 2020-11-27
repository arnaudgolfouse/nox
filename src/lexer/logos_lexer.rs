use super::{Assign, Error, Keyword, Operation, TokenKind, Warning};
use logos::Logos;
use std::ops::Range;

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

    #[regex(r"[0-9][0-9a-zA-Z_]*(?:\.[0-9a-zA-Z_]*)")]
    Number,
    #[regex(r#"("(?:[^"\\]|\\.)*"|'(?:[^'\\]|\\.)*')"#)]
    Str,
    #[regex("[a-zA-Z_][0-9a-zA-Z_]*")]
    Id,

    #[regex("#[^\n]*")]
    Comment,

    #[error]
    #[regex(r"[\s]+", logos::skip)]
    Error,
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

pub(super) struct Tokenizer<'source> {
    lexer: logos::Lexer<'source, RawToken>,
}

impl<'source> Iterator for Tokenizer<'source> {
    type Item = Result<Token, Error<'source>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_token = self.lexer.next()?;
        let span = self.lexer.span();
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
                todo!()
            }
            RawToken::Str => {
                todo!()
            }
            RawToken::Id => {
                todo!()
            }
            RawToken::Comment => {
                todo!()
            }
            RawToken::Error => {
                todo!()
            }
        };
        Some(Ok(Token {
            kind,
            range: span,
            warning,
        }))
    }
}
