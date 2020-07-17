use nox2::{parser::Parser, Source};

fn main() {
    let parser = Parser::new(Source::TopLevel(
        r#"
    # comment !
    fn f()
        return 5
    end
    return (3 != -4.6) * not do43do(8.2, "9") + "fn + 5" / "z"(héllœ.bye, (5+4)(8).b[c + 8]) == 5"#,
    ));
    match parser.parse_top_level() {
        Ok(chunk) => println!("{}", chunk),
        Err(err) => {
            for err in err {
                println!("{}", err)
            }
        }
    }
}
