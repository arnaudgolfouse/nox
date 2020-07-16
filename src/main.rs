use nox2::{parser::Parser, Source};

fn main() {
    let parser = Parser::new(Source::TopLevel(
        r#"
    # comment !
    return (3 != -4.6) * not do43do(8.2, "9") + "fn + 5" / "z"(東京.bye, 5[4 + 9](8).b.c) == 5"#,
    ));
    parser.parse_top_level().unwrap();
}
