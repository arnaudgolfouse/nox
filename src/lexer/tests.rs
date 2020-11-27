use super::*;
use num_parser::{Base, NumberError};

#[test]
fn errors() {
    // unrecognised characters and tokens
    assert_eq!(
        Lexer::top_level("😬").next().unwrap().unwrap_err().kind,
        ErrorKind::UnknownToken
    );
    assert_eq!(
        Lexer::top_level("&").next().unwrap().unwrap_err().kind,
        ErrorKind::UnknownToken
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
    // invalid digits
    for digit in 'g'..='z' {
        let mut source = "0x".to_owned();
        source.push(digit);
        assert_eq!(
            Lexer::top_level(&source).next().unwrap().unwrap_err().kind,
            ErrorKind::NumberError(NumberError::Invalid(digit, Base::Hexadecimal))
        );
    }
    for digit in ('a'..='z').chain('8'..='9') {
        let mut source = "0o".to_owned();
        source.push(digit);
        assert_eq!(
            Lexer::top_level(&source).next().unwrap().unwrap_err().kind,
            ErrorKind::NumberError(NumberError::Invalid(digit, Base::Octal))
        );
    }
    for digit in ('a'..='z').chain('2'..='9') {
        let mut source = "0b".to_owned();
        source.push(digit);
        assert_eq!(
            Lexer::top_level(&source).next().unwrap().unwrap_err().kind,
            ErrorKind::NumberError(NumberError::Invalid(digit, Base::Binary))
        );
    }
    for digit in 'a'..='z' {
        // gives a floating-point number !
        if digit != 'e' {
            let mut source = "12".to_owned();
            source.push(digit);
            assert_eq!(
                Lexer::top_level(&source).next().unwrap().unwrap_err().kind,
                ErrorKind::NumberError(NumberError::Invalid(digit, Base::Decimal))
            );
        }
    }
}

#[test]
fn strings() {
    // normal string
    assert_eq!(
        Lexer::top_level(
            r#"
        "hello world!"
        "#
        )
        .next()
        .unwrap()
        .unwrap()
        .kind,
        TokenKind::Str("hello world!".into())
    );
    // escape "
    assert_eq!(
        Lexer::top_level(
            r#"
        "hello'\" world"
        "#
        )
        .next()
        .unwrap()
        .unwrap()
        .kind,
        TokenKind::Str("hello'\" world".into()),
        "failed to escape \""
    );
    // escape utf-8
    assert_eq!(
        Lexer::top_level(
            r#"
        "\u{0052}\u{75}\u{73}\u{74} \u{1f609}"
        "#
        )
        .next()
        .unwrap()
        .unwrap()
        .kind,
        TokenKind::Str("Rust 😉".into()),
        "failed to escape utf-8"
    );
    // standart escapes + no commentary in strings
    assert_eq!(
        Lexer::top_level(
            r#"
        "hello#\r\nworld!\\\0"
        "#
        )
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
