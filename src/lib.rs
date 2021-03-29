//! Nox language interpreter
//!
//! This documentation covers the internal of the parser and the runtime : it
//! does not describe how to actually use the nox language.
//!
//! # Structure
//!
//! The process is made out of three major steps :
//! - Lexing : A [`Lexer`](lexer::Lexer) turns the source code into
//! [`Tokens`](lexer::Token).
//! - Parsing : A [`Parser`](parser::Parser) turns source code into
//! bytecode (It includes a `Lexer` internally).
//! - Running : A [`Virtual Machine`](runtime::VM) runs the bytecode.
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

pub use self::error::Continue;

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
    /// Will return `"top-level"` if the Source is [`TopLevel`](Source::TopLevel).
    pub fn name(&self) -> &str {
        match self {
            Self::File { name, .. } => name,
            Self::TopLevel(_) => "top-level",
        }
    }
}
