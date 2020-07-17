use crate::parser::{Parser, ParserError};

pub mod gc;
pub mod values;

pub struct RuntimeError {}

#[derive(Default)]
pub struct VM;

impl VM {
    pub fn new() -> Self {
        Self
    }

    pub fn parse_top_level<'a>(&mut self, source: &'a str) -> Result<(), Vec<ParserError<'a>>> {
        let parser = Parser::new(crate::Source::TopLevel(source));
        let chunk = parser.parse_top_level()?;
        println!("{}", chunk);
        Ok(())
    }
}
