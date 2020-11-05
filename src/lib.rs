//! Nox language interpreter
//!
//! This documentation covers the internal of the parser and the runtime : it
//! does not describe how to actually use the nox language.
//!
//! # Structure
//!
//! The process is made out of three major steps :
//! - Lexing : A [Lexer](./lexer/struct.Lexer.html) turns the source code into
//! [Tokens](./lexer/struct.Token.html).
//! - Parsing : A [Parser](./parser/struct.Parser.html) turns source code into
//! bytecode (It includes a `Lexer` internally).
//! - Running : A [Virtual Machine](./runtime/struct.VM.html) runs the bytecode.
//!
//! # Features
//!
//! - Benchmarks can be run by activating the `bench` feature :
//! `cargo bench --bench *** --features bench`.
#![cfg_attr(not(test), warn(clippy::panic))]
#![warn(unreachable_pub)]

mod error;
pub mod lexer;
pub mod libraries;
pub mod parser;
pub mod runtime;

pub use error::Continue;

use std::fmt;

/// Source of the code given to the interpreter.
#[derive(Debug, Clone)]
pub enum Source<'a> {
    /// Source code originated from a file
    File { name: String, content: &'a str },
    /// Source code was directly given to the interpreter (e.g. via a REPL)
    TopLevel(&'a str),
}

impl<'a> Source<'a> {
    /// Actual source code
    pub const fn content(&self) -> &'a str {
        match self {
            Self::File { content, .. } | Self::TopLevel(content) => content,
        }
    }

    /// Name of the source.
    ///
    /// Will return `"top-level"` if the Source is `TopLevel`.
    pub fn name(&self) -> &str {
        match self {
            Self::File { name, .. } => name,
            Self::TopLevel(_) => "top-level",
        }
    }
}

/// Position in the source code
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct Position {
    pub column: u32,
    pub line: u32,
}

impl Position {
    pub const fn new(column: u32, line: u32) -> Self {
        Self { column, line }
    }

    /// Return the position to the left of `self` (or `self` if `self.column` = 0).
    pub fn left(self) -> Self {
        Self {
            line: self.line,
            column: self.column.saturating_sub(1),
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(formatter, "{}:{}", self.line, self.column)
    }
}

/// A range of positions in the source code
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

impl Range {
    pub const fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    /// Returns a subslice of the given `source` corresponding to the range,
    /// removing line skips.
    pub fn substr(self, source: &str) -> String {
        let mut first_line = true;
        let mut col_start = 0;
        let mut col_end = 0;

        let mut result = String::new();

        for (line_index, line) in source
            .lines()
            .enumerate()
            .take(self.end.line as usize + 1)
            .skip(self.start.line as usize)
        {
            let mut chars = line.chars();
            if first_line {
                first_line = false;
                loop {
                    if col_start >= self.start.column as usize {
                        break;
                    }
                    match chars.next() {
                        None => break,
                        Some(c) => {
                            col_start += c.len_utf8();
                        }
                    }
                }
                col_end = col_start;
            }
            for c in chars {
                result.push(c);
                if line_index == self.end.line as usize {
                    if col_end >= self.end.column as usize {
                        break;
                    } else {
                        col_end += c.len_utf8();
                    }
                }
            }
        }

        result
    }
}

impl fmt::Display for Range {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(formatter, "{}..{}", self.start, self.end)
    }
}
