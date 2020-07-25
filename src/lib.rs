//! Nox language interpreter
//!
//! # Features
//!
//! The `check` feature, enabled by default, enables checks on various
//! operations internal to the VM. It is mainly used in case there is a bug in
//! the VM, or if you fed custom bytecode to the VM. Disabling it may improve
//! performances.
//! 
//! ## Note
//! 
//! At the moment, it seems that unchecked run perform **worse** that the 
//! checked ones. They do result in smaller binaries though.

mod error;
pub mod lexer;
pub mod libraries;
pub mod parser;
pub mod vm;

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
    pub fn content(&self) -> &'a str {
        match self {
            Self::File { content, .. } => content,
            Self::TopLevel(content) => content,
        }
    }

    /// Name of the source.
    ///
    /// Will return `"top-level"` if the Source is `TopLevel`.
    pub fn name(&self) -> &str {
        match self {
            Self::File { name, .. } => &name,
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
    pub fn new(column: u32, line: u32) -> Self {
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
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }
}

impl fmt::Display for Range {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(formatter, "{}..{}", self.start, self.end)
    }
}
