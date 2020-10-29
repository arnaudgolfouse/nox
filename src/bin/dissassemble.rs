use nox::{parser::Parser, Source};

fn main() -> Result<(), Vec<nox::parser::Error>> {
    let source = get_source();

    let parser = Parser::new(Source::TopLevel(&source));
    let chunk = parser.parse_top_level()?.0;
    println!("{}", chunk);

    Ok(())
}

fn get_source() -> String {
    const FOR_LOOPS_NUMBER: usize = 10000;
    let mut source = String::with_capacity(FOR_LOOPS_NUMBER * "for i in range(0, 1)\nend\n".len());
    for _ in 0..FOR_LOOPS_NUMBER {
        source.push_str("for i in range(0, 1)\n");
    }
    source.push_str("x = i\n");
    for _ in 0..FOR_LOOPS_NUMBER {
        source.push_str("end\n");
    }
    source.push_str("return x");
    source
}
