use super::*;
use num_parser::{Base, NumberError};

#[test]
fn errors() {
    // multiple dots
    assert_eq!(
        Lexer::top_level("3.1.2").next().unwrap_err().kind,
        LexerErrorKind::NumberError(NumberError::NumberUnexpectedDot)
    );
    // unrecognised character
    assert_eq!(
        Lexer::top_level("😬").next().unwrap_err().kind,
        LexerErrorKind::UnknownCharacter('😬')
    );
    // incomplete string
    assert_eq!(
        Lexer::top_level("'hello world").next().unwrap_err().kind,
        LexerErrorKind::IncompleteString('\'')
    );
    // overflow error
    assert_eq!(
        Lexer::top_level("999999999999999999999")
            .next()
            .unwrap_err()
            .kind,
        LexerErrorKind::NumberError(NumberError::Overflow)
    );
    // invalid digit
    assert_eq!(
        Lexer::top_level("0xg").next().unwrap_err().kind,
        LexerErrorKind::NumberError(NumberError::Invalid('g', Base::Hexadecimal))
    );
    assert_eq!(
            Lexer::top_level("0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001").next().unwrap(),
            Some(Token {
                kind: TokenKind::Float(0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001),
                range: Range::new(Position::default(), Position::new(181, 0))
            })
        );
}

#[test]
fn strings() {
    // normal string
    assert_eq!(
        Lexer::top_level(r#""hello world!""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("hello world!".into())
    );
    // escape "
    assert_eq!(
        Lexer::top_level(r#""hello'\" world""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("hello'\" world".into()),
        "failed to escape \""
    );
    // escape utf-8
    assert_eq!(
        Lexer::top_level(r#""\u{0052}\u{75}\u{73}\u{74} \u{1f609}""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("Rust 😉".into()),
        "failed to escape utf-8"
    );
    // standart escapes
    assert_eq!(
        Lexer::top_level(r#""hello#\r\nworld!\\\0""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("hello#\r\nworld!\\\0".into())
    );
}
