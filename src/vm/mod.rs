//! Runtime of the nox language.
//!
//! Contains the [Virtual Machine](struct.VM.html), the
//! [Garbage Collector](./gc/struct.GC.html) and the
//! [Foreign Functions Interface](./ffi/index.html).

pub mod ffi;
pub mod gc;
mod values;

#[cfg(test)]
mod tests;

#[cfg(not(feature = "check"))]
mod unchecked_run;
#[cfg(not(feature = "check"))]
pub use unchecked_run::*;

#[cfg(feature = "check")]
mod run;
#[cfg(feature = "check")]
pub use run::*;

use crate::{
    error::Continue,
    parser::{Chunk, Constant, Instruction, Parser, ParserError},
    Source,
};
use gc::GC;
use std::{collections::HashMap, fmt, sync::Arc};
use values::OperationError;
pub use values::Value;

#[derive(Default, Debug)]
struct CallFrame {
    /// Code of this function
    chunk: Arc<Chunk>,
    /// `ip` to return to
    previous_ip: usize,
    /// start of the local variables in the `stack`
    local_start: usize,
    /// start of the captured variables in the `stack`
    captured_start: usize,
    /// Stack of loop addresses used in `Continue` and `Break`
    loop_addresses: Vec<(usize, usize)>,
}

/// The Nox Virtual Machine
#[derive(Default, Debug)]
pub struct VM {
    /// Currently executing code
    chunk: Arc<Chunk>,
    /// Instruction pointer
    ip: usize,
    /// Stack for local variables
    stack: Vec<Value>,
    /// Global variables
    global_variables: HashMap<String, Value>,
    /// Stack of call information
    call_frames: Vec<CallFrame>,
    /// Stack of loop addresses used in `Continue` and `Break`
    loop_addresses: Vec<(usize, usize)>,
    /// Garbage collector
    gc: GC,
}

impl VM {
    pub fn new() -> Self {
        Self::default()
    }

    /// Completely reset the VM.
    ///
    /// Semantically equivalent to dropping and recreating the VM, but keep some
    /// of the allocated memory.
    pub fn reset(&mut self) {
        self.partial_reset();
        for (_, mut value) in self.global_variables.drain() {
            value.unroot()
        }
        self.gc.mark_and_sweep();
        #[cfg(test)]
        assert_eq!(self.gc.allocated, 0);
    }

    /// Similar to `reset`, but keep the global variables, the GC and the curent
    /// chunk.
    pub fn partial_reset(&mut self) {
        self.ip = 0;
        for mut value in self.stack.drain(..) {
            value.unroot()
        }
        self.call_frames.clear();
        self.loop_addresses.clear();
        self.gc.mark_and_sweep();
    }

    /// Load and parse a text `source` in the top-level for execution.
    pub fn parse_top_level<'a>(&mut self, source: &'a str) -> Result<(), VMError<'a>> {
        self.partial_reset();
        let parser = Parser::new(crate::Source::TopLevel(source));
        self.chunk = Arc::new(parser.parse_top_level()?);
        Ok(())
    }

    /// Load and parse a `source` file or `str` in the top-level for execution.
    pub fn parse_source<'a>(&mut self, source: Source<'a>) -> Result<(), VMError<'a>> {
        self.partial_reset();
        let parser = Parser::new(source);
        self.chunk = Arc::new(parser.parse_top_level()?);
        Ok(())
    }

    /// Load a raw chunk of bytecode in the top-level for execution.
    pub fn load(&mut self, chunk: Chunk) {
        self.partial_reset();
        self.chunk = Arc::new(chunk);
    }

    /// Load the library as a table in the global variables.
    pub fn import(&mut self, library: ffi::Library) -> Result<(), VMError> {
        if self.global_variables.contains_key(&library.name) {
            return Err(VMError::Runtime {
                kind: RuntimeError::NameAlreadyDefined(library.name),
                line: 0,
            });
        }
        let mut library_table = self.gc.new_table();
        library_table.root();
        if let Some(library_table) = library_table.as_table_mut() {
            for (name, value) in library.variables {
                self.gc
                    .add_table_element(library_table, Value::String(name), value);
            }
        }
        self.global_variables.insert(library.name, library_table);
        Ok(())
    }

    /// Load all objects in the library as global variables.
    pub fn import_all(&mut self, library: ffi::Library) -> Result<(), VMError> {
        for (name, value) in library.variables {
            if self.global_variables.contains_key(&name) {
                return Err(VMError::Runtime {
                    kind: RuntimeError::NameAlreadyDefined(name),
                    line: 0,
                });
            }
            self.global_variables.insert(name, value);
        }
        Ok(())
    }

    /// Run the VM on the currently stored code.
    ///
    /// # Return
    ///
    /// If a `return` statement is encountered on the top-level, it's value is
    /// returned.
    ///
    /// Else, if the machine exhausts all code without encountering `return`,
    /// `Value::Nil` is returned.
    ///
    /// # Examples
    ///
    /// **Example 1**
    /// ```
    /// # use nox2::vm::{VM, Value};
    /// let mut vm = VM::new();
    /// vm.parse_top_level(
    /// "
    /// t = { x = 5, y = 6 }
    /// if t.x < t.y then
    ///     t.y -= 4
    /// else
    ///     return t.x + t.y
    /// end
    /// return t.x * t.y
    /// ").unwrap();
    ///
    /// assert_eq!(vm.run().unwrap(), Value::Int(10));
    /// ```
    /// **Example 2**
    /// ```
    /// # use nox2::vm::{VM, Value};
    /// let mut vm = VM::new();
    /// vm.parse_top_level(
    /// "
    /// fn f()
    ///     x = 5
    ///     fn g(a)
    ///         x += a
    ///         return x
    ///     end
    ///     return g
    /// end
    ///
    /// f = f()
    ///
    /// f(1)
    /// x = f(-60.5)
    ///
    /// return x
    /// ").unwrap();
    ///
    /// assert_eq!(vm.run().unwrap(), Value::Float(-54.5));
    /// ```
    pub fn run<'a>(&mut self) -> Result<Value, VMError<'a>> {
        // for variables
        for _ in 0..self.chunk.locals_number {
            self.stack.push(Value::Nil)
        }
        let kind = match self.run_internal() {
            Ok(ok) => return Ok(ok),
            Err(err) => err,
        };
        match kind {
            VMErrorKind::Runtime(err) => Err(VMError::Runtime {
                kind: err,
                line: self.chunk().get_line(self.ip),
            }),
            #[cfg(feature = "check")]
            VMErrorKind::Internal(err) => Err(VMError::Internal {
                kind: err,
                line: self.chunk().get_line(self.ip),
            }),
        }
    }

    /// Currently executing instructions
    #[inline]
    fn code(&self) -> &Vec<Instruction<u8>> {
        match self.call_frames.last() {
            Some(frame) => &frame.chunk.code,
            None => &self.chunk.code,
        }
    }

    /// Currently executing Chunk
    #[inline]
    fn chunk(&self) -> &Chunk {
        match self.call_frames.last() {
            Some(frame) => &frame.chunk,
            None => &self.chunk,
        }
    }

    /// Returns a reference to the current function's local variables.
    #[inline]
    fn local_vars(&self) -> &[Value] {
        match self.call_frames.last() {
            Some(frame) => &self.stack[frame.local_start..frame.captured_start],
            // all the stack for loop variables
            None => &self.stack[..],
        }
    }

    /// Returns a reference to the current function's captured variables.
    #[inline]
    fn captured_vars(&self) -> &[Value] {
        match self.call_frames.last() {
            Some(frame) => &self.stack[frame.captured_start..],
            None => &[],
        }
    }

    /// Returns a mutable reference to the current function's local variables.
    #[inline]
    fn local_vars_mut(&mut self) -> &mut [Value] {
        match self.call_frames.last() {
            Some(frame) => &mut self.stack[frame.local_start..frame.captured_start],
            // all the stack for loop variables
            None => &mut self.stack[..],
        }
    }

    /// Returns a mutable reference to the current function's captured variables.
    #[inline]
    fn captured_vars_mut(&mut self) -> &mut [Value] {
        match self.call_frames.last() {
            Some(frame) => &mut self.stack[frame.captured_start..],
            None => &mut [],
        }
    }
}

impl Drop for VM {
    fn drop(&mut self) {
        for mut value in self.stack.drain(..) {
            value.unroot()
        }
        for (_, mut value) in self.global_variables.drain() {
            value.unroot()
        }
    }
}

/*
====================================================
= ERRORS ===========================================
====================================================
*/

#[derive(Debug)]
pub enum RuntimeError {
    OperationError(OperationError),
    NotATable(String),
    NotAFunction(String),
    InvalidArgNumber(u32, u64),
    /// Error emitted by a Rust function
    RustFunction(String),
    /// Trying to import an already defined library
    NameAlreadyDefined(String),
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::OperationError(err) => fmt::Display::fmt(err, formatter),
            Self::NotATable(value) => write!(formatter, "{} is not a table", value),
            Self::NotAFunction(value) => write!(formatter, "{} is not a function", value),
            Self::InvalidArgNumber(expected, got) => write!(
                formatter,
                "invalid number of arguments : expected {}, got {}",
                expected, got
            ),
            Self::RustFunction(err) => write!(formatter, "{}", err),
            Self::NameAlreadyDefined(name) => {
                write!(formatter, "library name '{}' is already defined", name)
            }
        }
    }
}

impl<'a> VMError<'a> {
    pub fn continuable(&self) -> Continue {
        match self {
            Self::Runtime { .. } => Continue::Stop,
            #[cfg(feature = "check")]
            Self::Internal { .. } => Continue::Stop,
            Self::Parser(err) => {
                let mut continable = Continue::Continue;
                for err in err {
                    if err.continuable == Continue::Stop {
                        continable = Continue::Stop;
                        break;
                    }
                }
                continable
            }
        }
    }
}

impl<'a> From<Vec<ParserError<'a>>> for VMError<'a> {
    fn from(err: Vec<ParserError<'a>>) -> Self {
        Self::Parser(err)
    }
}

impl From<RuntimeError> for VMErrorKind {
    fn from(err: RuntimeError) -> Self {
        Self::Runtime(err)
    }
}

impl<'a> fmt::Display for VMError<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use colored::Colorize;
        match self {
            Self::Runtime { kind, line } => writeln!(
                formatter,
                "{} line {} :\n{}",
                "error".red().bold(),
                line + 1,
                kind
            ),
            #[cfg(feature = "check")]
            Self::Internal { kind, line } => {
                writeln!(
                    formatter,
                    "{} line {} :\n{}",
                    "INTERNAL ERROR".red().bold(),
                    line + 1,
                    kind
                )?;
                writeln!(formatter)?;
                writeln!(
                    formatter,
                    "{}",
                    "!!! THIS ERROR IS INTERNAL TO THE VIRTUAL MACHINE AND INDICATE A FAULTY BYTECODE : PLEASE REPORT IT !!!".red().bold(),
                )
            }
            Self::Parser(err) => {
                for err in err {
                    fmt::Display::fmt(err, formatter)?;
                    writeln!(formatter)?;
                }
                Ok(())
            }
        }
    }
}
