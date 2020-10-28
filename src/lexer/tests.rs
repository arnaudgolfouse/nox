use super::*;
use num_parser::{Base, NumberError};

#[test]
fn errors() {
    // multiple dots
    assert_eq!(
        Lexer::top_level("3.1.2").next().unwrap().unwrap_err().kind,
        ErrorKind::NumberError(NumberError::NumberUnexpectedDot)
    );
    // unrecognised character
    assert_eq!(
        Lexer::top_level("😬").next().unwrap().unwrap_err().kind,
        ErrorKind::UnknownCharacter('😬')
    );
    // incomplete string
    assert_eq!(
        Lexer::top_level("'hello world")
            .next()
            .unwrap()
            .unwrap_err()
            .kind,
        ErrorKind::IncompleteString('\'')
    );
    // overflow error
    assert_eq!(
        Lexer::top_level("999999999999999999999")
            .next()
            .unwrap()
            .unwrap_err()
            .kind,
        ErrorKind::NumberError(NumberError::Overflow)
    );
    // invalid digit
    assert_eq!(
        Lexer::top_level("0xg").next().unwrap().unwrap_err().kind,
        ErrorKind::NumberError(NumberError::Invalid('g', Base::Hexadecimal))
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

#[test]
fn numbers() {
    assert_eq!(
        Lexer::top_level("0.000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_001").next().unwrap().unwrap().kind,
        TokenKind::Float(0.000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_000_001));
}
