//! Runtime of the nox language.
//!
//! Contains the [`Virtual Machine`](VM), the
//! [`Garbage Collector`](gc::GC) and the
//! [`Foreign Functions Interface`](ffi).

pub mod ffi;
pub mod gc;
mod values;

#[cfg(test)]
mod tests;

mod run;

use crate::{
    error::Continue,
    parser::{self, Chunk, Constant, Instruction, Parser},
    Source,
};
use gc::GC;
use std::{collections::HashMap, error, fmt, marker::PhantomData, sync::Arc};
pub use values::Value;
use values::{OperationError, RValue};

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
    global_variables: HashMap<Box<str>, Value>,
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
        self.global_variables.clear();
        self.gc.mark_and_sweep();
        #[cfg(test)]
        assert_eq!(self.gc.allocated, 0);
    }

    /// Similar to [`reset`](VM::reset), but keep the global variables, the GC
    /// and the current chunk.
    pub fn partial_reset(&mut self) {
        self.ip = 0;
        self.stack.clear();
        self.call_frames.clear();
        self.loop_addresses.clear();
    }

    /// Load and parse a text `source` in the top-level for execution.
    ///
    /// # Errors
    ///
    /// Any parsing error is converted to [`VMError`] and returned.
    pub fn parse_top_level(&mut self, source: &str) -> Result<Vec<parser::Warning>, VMError> {
        self.partial_reset();
        let parser = Parser::new(crate::Source::TopLevel(source));
        let (chunk, warnings) = parser.parse_top_level()?;
        self.chunk = Arc::new(chunk);
        Ok(warnings)
    }

    /// Load and parse a `source` file or `str` in the top-level for execution.
    ///
    /// # Errors
    ///
    /// Any parsing error is converted to [`VMError`] and returned.
    pub fn parse_source(&mut self, source: Source) -> Result<Vec<parser::Warning>, VMError> {
        self.partial_reset();
        let parser = Parser::new(source);
        let (chunk, warnings) = parser.parse_top_level()?;
        self.chunk = Arc::new(chunk);
        Ok(warnings)
    }

    /// Load a raw chunk of bytecode in the top-level for execution.
    pub fn load(&mut self, chunk: Chunk) {
        self.partial_reset();
        self.chunk = Arc::new(chunk);
    }

    /// Load the library as a table in the global variables.
    ///
    /// # Errors
    ///
    /// If the name of the library tries to replace an already defined
    /// global variable, [`RuntimeError::NameAlreadyDefined`] is emitted.
    pub fn import(&mut self, library: ffi::Library) -> Result<(), VMError> {
        if self.global_variables.contains_key(&library.name) {
            return Err(VMError::Runtime {
                kind: RuntimeError::NameAlreadyDefined(library.name),
                position: 0,
                unwind_message: String::new(),
            });
        }
        let mut library_table = self.gc.new_table();
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
    ///
    /// # Errors
    ///
    /// If one of the symbols of the library tries to replace an already defined
    /// global variable, [`RuntimeError::NameAlreadyDefined`] is emitted.
    pub fn import_all(&mut self, library: ffi::Library) -> Result<(), VMError> {
        for (name, value) in library.variables {
            if self.global_variables.contains_key(&name) {
                return Err(VMError::Runtime {
                    kind: RuntimeError::NameAlreadyDefined(name),
                    position: 0,
                    unwind_message: String::new(),
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
    /// [`Value::Nil`] is returned.
    ///
    /// # Examples
    ///
    /// **Example 1**
    /// ```
    /// # use nox::runtime::{VM, Value};
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
    /// # use nox::runtime::{VM, Value};
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
    ///
    /// # Errors
    ///
    /// See [`VMError`].
    pub fn run(&mut self) -> Result<RValue, VMError> {
        // for variables
        for _ in 0..self.chunk.locals_number {
            self.stack.push(Value::Nil)
        }
        match self.run_internal() {
            Ok(()) => {
                let return_value = self.stack.pop().unwrap_or(Value::Nil);
                self.partial_reset();
                Ok(self.make_rvalue(return_value))
            }
            Err(err) => Err(self.make_error(err)),
        }
    }

    /// Construct a `VMError` from a `VMErrorKind` (by doing stack
    /// unwinding).
    fn make_error(&mut self, error: VMErrorKind) -> VMError {
        match error {
            VMErrorKind::Runtime(err) => {
                let err = self.unwind(err);
                self.gc.mark_and_sweep();
                err
            }
            VMErrorKind::Interfacing(err) => {
                self.partial_reset();
                VMError::Interfacing {
                    kind: err,
                    position: self.chunk().get_pos(self.ip),
                }
            }
            VMErrorKind::Internal(err) => {
                self.partial_reset();
                VMError::Internal {
                    kind: err,
                    position: self.chunk().get_pos(self.ip),
                }
            }
        }
    }

    /// Push a value onto the stack.
    ///
    /// # Safety
    ///
    /// The value **must** originate from this `VM`.
    pub unsafe fn push<'a>(&'a mut self, value: RValue<'a>) {
        // no need to root since `value` will never be dropped.
        self.stack.push(value.into_raw())
    }

    /// Pop a value from the stack
    pub fn pop(&mut self) -> Option<RValue> {
        match self.stack.pop() {
            None => None,
            // additional root here
            Some(value) => Some(self.make_rvalue(value)),
        }
    }

    /// Return the entire stack as a slice.
    pub fn stack(&self) -> &[Value] {
        &self.stack
    }

    /// Inspect the last element of the stack.
    pub fn last(&self) -> Option<&Value> {
        self.stack.last()
    }

    /// Return the element at `index` if it is in bounds.
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.stack.get(index)
    }

    /// Make a `RValue` out of a regular value.
    fn make_rvalue(&self, value: Value) -> RValue {
        RValue(value, PhantomData::default())
    }

    /// Currently executing instructions
    #[inline]
    fn code(&self) -> &Vec<Instruction<u8>> {
        match self.call_frames.last() {
            Some(frame) => &frame.chunk.code,
            None => &self.chunk.code,
        }
    }

    /// Currently executing `Chunk`
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

    /// Create an unwind message for a runtime error.
    ///
    /// This will pop every call frame, but keep anything below.
    fn unwind(&mut self, error: RuntimeError) -> VMError {
        let mut unwind_message = String::new();
        let position = self.chunk().get_pos(self.ip.saturating_sub(1));
        while let Some(frame) = self.call_frames.pop() {
            self.unwind_frame(&frame, &mut unwind_message);
        }
        VMError::Runtime {
            kind: error,
            position,
            unwind_message,
        }
    }

    /// Log the unwinding of one frame in the given string.
    fn unwind_frame(&mut self, frame: &CallFrame, unwind_message: &mut String) {
        unwind_message.push_str(&format!(
            "  line {:<6} -> {}(",
            self.chunk().get_pos(frame.previous_ip.saturating_sub(1)) + 1,
            frame.chunk.name
        ));
        // captured
        for _ in self.stack.drain(frame.captured_start..) {}
        // locals (but not args)
        for _ in self
            .stack
            .drain(frame.local_start + frame.chunk.arg_number as usize..)
        {}
        // arguments
        if let Some(args) = frame.chunk.arg_number.checked_sub(1) {
            for value in self
                .stack
                .drain(frame.local_start..frame.local_start + args as usize)
            {
                unwind_message.push_str(&format!("{:#}, ", value));
            }
            // last argument
            if let Some(value) = self.stack.pop() {
                unwind_message.push_str(&format!("{:#}", value));
            }
        }
        // function
        self.stack.pop();
        unwind_message.push_str(")\n");
    }

    /// If a string is at the `nb_args`-th position in the `stack`, make a
    /// function out of it and calls it with `nb_args` arguments, pushing the
    /// result at the top of the stack.
    ///
    /// # Errors
    ///
    /// [`InterfacingError::NotAString`] is returned if the stack is incorrectly
    /// setup.
    pub fn str_call(&mut self, nb_args: usize) -> Result<Vec<parser::Warning>, VMError> {
        let func_index = match self.stack.len().checked_sub(nb_args + 1) {
            None => return Err(self.make_error(InterfacingError::IncorrectStackIndex(0).into())),
            Some(index) => index,
        };
        match self.stack.get_mut(func_index) {
            None => Err(self.make_error(InterfacingError::IncorrectStackIndex(func_index).into())),
            Some(func) => match func {
                Value::String(s) => {
                    let parser = Parser::new(Source::TopLevel(s.as_ref()));
                    let (code, warnings) = parser.parse_top_level()?;
                    let function = self.gc.new_function(Arc::new(code), Vec::new());
                    *func = function;
                    self.call_internal(nb_args)
                        .map_err(|err| self.make_error(err))?;
                    Ok(warnings)
                }
                value => {
                    let value_str = format!("{}", value);
                    Err(self.make_error(InterfacingError::NotAString(value_str).into()))
                }
            },
        }
    }

    /// Interpret the stack as `nb_args` arguments with a function below.
    ///
    /// This will prepare the `VM` for the function and call it, and then push
    /// the result on top of the stack.
    ///
    /// # Errors
    ///
    /// See [`VMError`].
    pub fn call(&mut self, nb_args: usize) -> Result<(), VMError> {
        self.call_internal(nb_args)
            .map_err(|err| self.make_error(err))
    }

    /// Interpret the stack as `nb_args` arguments with a function below.
    ///
    /// This will prepare the `VM` for the function and call it.
    fn call_internal(&mut self, nb_args: usize) -> Result<(), VMErrorKind> {
        let local_start = self
            .stack
            .len()
            .checked_sub(nb_args)
            .ok_or(InternalError::EmptyStack)?;
        let mut function = self
            .stack
            .get(local_start - 1)
            .ok_or(InternalError::EmptyStack)?
            .clone();

        let func = if let Some(function) = function.as_function_mut() {
            function
        } else if let Value::RustFunction(ref function) = function {
            match function.0.borrow_mut()(&mut self.stack[local_start..]) {
                Ok(value) => {
                    for _ in self.stack.drain(local_start - 1..) {}
                    self.stack.push(value);
                }
                Err(err) => return Err(RuntimeError::RustFunction(err).into()),
            }
            return Ok(());
        } else {
            return Err(RuntimeError::NotAFunction(format!("{}", function)).into());
        };

        if nb_args != func.0.arg_number {
            return Err(RuntimeError::InvalidArgNumber(func.0.arg_number, nb_args).into());
        }

        for _ in 0..(func.0.locals_number - nb_args as usize) {
            self.stack.push(Value::Nil)
        }

        let captured_start = self.stack.len();
        for captured in func.1 {
            let captured = (captured as &Value).clone();
            self.stack.push(captured);
        }

        self.call_frames.push(CallFrame {
            chunk: func.0.clone(),
            previous_ip: self.ip,
            local_start,
            captured_start,
            loop_addresses: Vec::new(),
        });

        self.ip = 0;

        self.run_internal()
    }
}

impl Drop for VM {
    fn drop(&mut self) {
        self.stack.clear();
        self.global_variables.clear();
    }
}

/*
====================================================
= ERRORS ===========================================
====================================================
*/

/// Error thrown by the [`VM`] at runtime.
#[derive(Debug)]
pub enum RuntimeError {
    /// Invalid unary or binary operation
    OperationError(OperationError),
    /// A table operation (read or write) was attempted on a value that is not a
    /// table.
    NotATable(String),
    /// A call operation was attempted on a value that is not a function.
    NotAFunction(String),
    /// A function received an incorrect number of arguments
    InvalidArgNumber(usize, usize),
    /// Error emitted by a Rust function
    RustFunction(String),
    /// Trying to import an already defined library
    NameAlreadyDefined(Box<str>),
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

impl error::Error for RuntimeError {}

#[derive(Debug)]
pub enum InterfacingError {
    /// The given index does not exists in the stack
    IncorrectStackIndex(usize),
    /// The stack does not contains enough elements for the operation
    NotEnoughStackElements,
    /// A string operation (usually `str_call`) was attempted on a value that was
    /// not a string.
    NotAString(String),
}

impl fmt::Display for InterfacingError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::IncorrectStackIndex(index) => {
                write!(formatter, "index {} is out of bounds", index)
            }
            Self::NotEnoughStackElements => {
                formatter.write_str("the stack does not contains enough elements for the operation")
            }
            Self::NotAString(value) => write!(formatter, "{} is not a string", value),
        }
    }
}

impl error::Error for InterfacingError {}

impl From<InterfacingError> for VMErrorKind {
    fn from(err: InterfacingError) -> Self {
        Self::Interfacing(err)
    }
}

impl From<RuntimeError> for VMErrorKind {
    fn from(err: RuntimeError) -> Self {
        Self::Runtime(err)
    }
}

#[derive(Debug)]
pub(super) enum VMErrorKind {
    Internal(InternalError),
    Runtime(RuntimeError),
    Interfacing(InterfacingError),
}

/// Error internally thrown by the [`VM`].
///
/// Such errors *should* not happen in theory. If they do, that means there is a
/// bug in the [`VM`] or [`Parser`].
#[derive(Debug)]
pub enum InternalError {
    /// The instruction pointer was out of bounds : the first number is the
    /// value of the instruction pointer, and the second is the length of the
    /// instruction vector.
    InstructionPointerOOB(usize, usize),
    /// The instruction pointer is sent out of bounds by the contained offset.
    /// The boolean indicate whether the offset is positive ([`true`]) or
    /// negative ([`false`])
    JumpOob(usize, bool),
    /// An element was requested from the `stack` but it was empty.
    EmptyStack,
    /// Various instruction errors. Most of the time this is caused by an
    /// incorrect `Read-` or `Write-` instruction operand.
    InvalidOperand(Instruction<usize>),
    /// A `Break` or `Continue` instruction was encountered outside of a loop.
    ///
    /// If [`true`], `break`, else `continue`.
    BreakOrContinueOutsideLoop(bool),
}

impl fmt::Display for InternalError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::InstructionPointerOOB(ptr, max_ptr) => write!(
                formatter,
                "!!! instruction pointer '{}' is out of bounds for chunk of len {} !!!",
                ptr, max_ptr
            ),
            Self::JumpOob(jump_address, forward) => {
                if *forward {
                    write!(
                        formatter,
                        "!!! jump offset {} is out of bounds !!!",
                        jump_address
                    )
                } else {
                    write!(
                        formatter,
                        "!!! jump offset -{} is out of bounds !!!",
                        jump_address
                    )
                }
            }
            Self::EmptyStack => formatter.write_str("!!! empty stack !!!"),
            Self::InvalidOperand(instruction) => write!(
                formatter,
                "!!! incorrect instruction : '{:?}'  !!!",
                instruction
            ),
            Self::BreakOrContinueOutsideLoop(b) => write!(
                formatter,
                "unexpected {} outside or a 'while' or 'for' loop",
                if *b { "break" } else { "continue" }
            ),
        }
    }
}

impl From<InternalError> for VMErrorKind {
    fn from(err: InternalError) -> Self {
        Self::Internal(err)
    }
}

impl error::Error for InternalError {}

/// Various errors thrown by the Virtual Machine.
#[derive(Debug)]
pub enum VMError {
    /// Internal error : indicate a bug in the VM
    Internal {
        kind: InternalError,
        position: usize,
    },
    /// Error encountered at runtime
    Runtime {
        kind: RuntimeError,
        position: usize,
        unwind_message: String,
    },
    /// Error encountered while interfacing with Rust
    Interfacing {
        kind: InterfacingError,
        position: usize,
    },
    /// Error(s) encountered while parsing
    Parser(Vec<parser::Error>),
}

impl<'a> VMError {
    pub fn continuable(&self) -> Continue {
        match self {
            Self::Runtime { .. } | Self::Interfacing { .. } | Self::Internal { .. } => {
                Continue::Stop
            }
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

impl<'a> From<Vec<parser::Error>> for VMError {
    fn from(err: Vec<parser::Error>) -> Self {
        Self::Parser(err)
    }
}

impl<'a> fmt::Display for VMError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use colored::Colorize;
        match self {
            Self::Runtime {
                kind,
                position,
                unwind_message,
            } => {
                if !unwind_message.is_empty() {
                    writeln!(formatter, "stack trace :\n{}", unwind_message)?;
                }
                writeln!(
                    formatter,
                    "{} pos {} :\n{}",
                    "error".red().bold(),
                    position,
                    kind
                )
            }
            Self::Interfacing { kind, position } => writeln!(
                formatter,
                "{} pos {} :\n{}",
                "error".red().bold(),
                position,
                kind
            ),
            Self::Internal { kind, position } => {
                writeln!(
                    formatter,
                    "{} pos {} :\n{}",
                    "INTERNAL ERROR".red().bold(),
                    position,
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

impl error::Error for VMError {}
