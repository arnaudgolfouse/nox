use super::*;

#[test]
fn errors() {
    // multiple dots
    assert!(matches!(
        Lexer::top_level("3.1.2").next().unwrap_err().kind,
        LexerErrorKind::NumberUnexpectedDot(10)
    ));
    // dot in hexadecimal
    // TODO : Lua support this, maybe we should too ?
    assert!(matches!(
        Lexer::top_level("0x5fa.2").next().unwrap_err().kind,
        LexerErrorKind::NumberUnexpectedDot(16)
    ));
    // unrecognised character
    assert!(matches!(
        Lexer::top_level("😬").next().unwrap_err().kind,
        LexerErrorKind::UnknownCharacter(_)
    ));
    // incomplete string
    assert!(matches!(
        Lexer::top_level("'hello world").next().unwrap_err().kind,
        LexerErrorKind::IncompleteString(_)
    ));
    // i64 error
    assert!(matches!(
        Lexer::top_level("999999999999999999999")
            .next()
            .unwrap_err()
            .kind,
        LexerErrorKind::Parseint(_)
    ));
    // TODO : the Rust parser is not very good with this error, make a custom one.
    assert!(matches!(
        Lexer::top_level("0xg").next().unwrap_err().kind,
        LexerErrorKind::Parseint(_)
    ));
    // f64 error
    assert!(matches!(
            // yeah 😅
            // TODO : resolve this, make it 1.0 ?
            Lexer::top_level("0.999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999").next().unwrap_err().kind,
            LexerErrorKind::Parsefloat(_)
        ));
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
    assert_eq!(
        Lexer::top_level(r#""hello'\" world""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("hello'\" world".to_owned())
    );
    assert_eq!(
        Lexer::top_level(r#""\u{0052}\u{75}\u{73}\u{74} \u{1f609}""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("Rust 😉".to_owned())
    );

    assert_eq!(
        Lexer::top_level(r#""hello#\r\nworld!\\\0""#)
            .next()
            .unwrap()
            .unwrap()
            .kind,
        TokenKind::Str("hello#\r\nworld!\\\0".to_owned())
    );
}
