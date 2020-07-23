pub mod ffi;
pub mod gc;
mod values;

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
    chunk: Arc<Chunk>,
    previous_ip: usize,
    local_start: usize,
    captured_start: usize,
}

#[derive(Default, Debug)]
pub struct VM {
    /// Currently executing code
    chunk: Arc<Chunk>,
    /// Instruction pointer
    ip: usize,
    /// Stack for local variables
    stack: Vec<Value>,
    /// Stack for temporary variables
    tmp_stack: Vec<Value>,
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
        Self {
            ..Default::default()
        }
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
        self.gc.mark_and_sweep()
    }

    // Similar to `reset`, but keep the global variables and the GC.
    fn partial_reset(&mut self) {
        self.chunk = Arc::new(Chunk::default());
        self.ip = 0;
        for mut value in self.stack.drain(..) {
            value.unroot()
        }
        for mut value in self.tmp_stack.drain(..) {
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

    /// Load and parse a `source` file or top-level in the top-level for
    /// execution.
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
            VMErrorKind::Internal(err) => Err(VMError::Internal {
                kind: err,
                line: self.chunk().get_line(self.ip),
            }),
        }
    }

    #[inline]
    fn code(&self) -> &Vec<Instruction<u8>> {
        match self.call_frames.last() {
            Some(frame) => &frame.chunk.code,
            None => &self.chunk.code,
        }
    }

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
            Some(frame) => &self.stack[frame.local_start..],
            // all the stack for loop variables
            None => &self.stack[..],
        }
    }

    /// Returns a reference to the current function's local variables.
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
            Some(frame) => &mut self.stack[frame.local_start..],
            // all the stack for loop variables
            None => &mut self.stack[..],
        }
    }

    /// Returns a mutable reference to the current function's local variables.
    #[inline]
    fn captured_vars_mut(&mut self) -> &mut [Value] {
        match self.call_frames.last() {
            Some(frame) => &mut self.stack[frame.captured_start..],
            None => &mut [],
        }
    }

    /// Read the instruction pointer, resolving any `Instruction::Extended`.
    ///
    /// # Errors
    ///
    /// An error is emitted is the instruction pointer is out of bounds.
    fn read_ip(&mut self) -> Result<(Instruction<u8>, u64), VMErrorKind> {
        let mut operand = 0;
        let opcode =
            loop {
                match self.code().get(self.ip).copied().ok_or_else(|| {
                    InternalError::InstructionPointerOOB(self.ip, self.code().len())
                })? {
                    // extended operand
                    Instruction::Extended(extended) => {
                        operand += extended as u64;
                        operand <<= 8;
                        self.ip += 1;
                    }
                    instruction => {
                        operand += instruction.operand().unwrap_or(0) as u64;
                        self.ip += 1;
                        break instruction;
                    }
                };
            };
        Ok((opcode, operand))
    }

    /// Pop and unroot a value from the `tmp_stack`.
    ///
    /// If `rooted` is `true`, the value will NOT be unrooted.
    #[inline]
    fn pop_tmp(&mut self, rooted: bool) -> Result<Value, VMErrorKind> {
        let mut value = self.tmp_stack.pop().ok_or(InternalError::EmptyStack)?;
        if !rooted {
            value.unroot();
        }
        Ok(value)
    }

    /// Read a value at `index` from the `stack`.
    ///
    /// The returned value will have an additional root.
    #[inline]
    fn read_local(&mut self, index: usize) -> Result<Value, VMErrorKind> {
        Ok(unsafe {
            let mut local = self
                .local_vars()
                .get(index)
                .ok_or(InternalError::IncorrectInstruction(Instruction::ReadLocal(
                    index as u64,
                )))?
                .duplicate();
            local.root();
            local
        })
    }

    /// Read a `value` at `index` in the `stack`.
    ///
    /// The previous value will be unrooted.
    fn write_local(&mut self, index: usize, value: Value) -> Result<(), VMErrorKind> {
        let old_value =
            self.local_vars_mut()
                .get_mut(index)
                .ok_or(InternalError::IncorrectInstruction(
                    Instruction::WriteLocal(index as u64),
                ))?;
        old_value.unroot();
        *old_value = value;
        Ok(())
    }

    /// Root and write the given global value, unrooting any potential previous
    /// value.
    #[inline]
    fn write_global(&mut self, name: String, global: Value) {
        if let Some(mut value) = self.global_variables.insert(name, global) {
            value.unroot()
        }
    }

    /// Jump to the specified destination.
    ///
    /// # Return
    ///
    /// - `Ok(())` if `destination` was in bounds, or if `destination == self.code().len()`. (will be handled at the next iteration of the `run` loop).
    /// - `Err(InternalError::JumpOob)` else.
    #[inline]
    fn jump_to(&mut self, destination: usize) -> Result<(), VMErrorKind> {
        if destination > self.code().len() {
            Err(InternalError::JumpOob(destination, true).into())
        } else {
            self.ip = destination;
            Ok(())
        }
    }

    /// Read a function from the current code's `functions`.
    ///
    /// This will take care of capturing variables, and the returned function
    /// will be rooted.
    fn read_function(&mut self, operand: u64) -> Result<Value, VMErrorKind> {
        use crate::parser::LocalOrCaptured;

        let function = self
            .chunk()
            .functions
            .get(operand as usize)
            .ok_or(InternalError::IncorrectInstruction(
                Instruction::ReadFunction(operand),
            ))?
            .clone();

        // Capture variables
        let mut captured = Vec::new();
        for captured_index in function.captures.iter() {
            match captured_index {
                LocalOrCaptured::Local(index) => {
                    let to_capture = unsafe {
                        self.local_vars_mut()
                            .get_mut(*index)
                            .ok_or(InternalError::IncorrectInstruction(Instruction::ReadLocal(
                                *index as u64,
                            )))?
                            .duplicate()
                    };
                    let to_capture = self.gc.new_captured(to_capture);
                    captured.push(unsafe { to_capture.duplicate() });
                    *self.local_vars_mut().get_mut(*index).ok_or(
                        InternalError::IncorrectInstruction(Instruction::ReadLocal(*index as u64)),
                    )? = to_capture;
                }
                LocalOrCaptured::Captured(index) => {
                    let to_capture = self.captured_vars_mut().get_mut(*index).ok_or(
                        InternalError::IncorrectInstruction(Instruction::ReadLocal(*index as u64)),
                    )?;
                    captured.push(unsafe { to_capture.duplicate() })
                }
            }
        }

        Ok(self.gc.new_function(function, captured))
    }

    fn run_internal(&mut self) -> Result<Value, VMErrorKind> {
        loop {
            if self.ip == self.code().len() {
                return Ok(Value::Nil);
            }
            let (opcode, operand) = self.read_ip()?;
            //println!("instruction = {} {}", opcode.name(), operand);
            match opcode {
                Instruction::Return => {
                    if let Some(frame) = self.call_frames.pop() {
                        for mut value in self.stack.drain(frame.local_start..) {
                            value.unroot()
                        }
                        self.ip = frame.previous_ip;
                        match self.tmp_stack.last_mut() {
                            Some(return_value) => return_value.decapture(),
                            None => return Err(InternalError::EmptyStack.into()),
                        }
                    } else if let Some(value) = self.tmp_stack.pop() {
                        return Ok(value);
                    } else {
                        return Err(InternalError::EmptyStack.into());
                    }
                }
                Instruction::Equal => {
                    let value_1 = self.pop_tmp(false)?;
                    let value_2 = self.pop_tmp(false)?;
                    self.tmp_stack.push(Value::Bool(value_1 == value_2))
                }
                Instruction::NEqual => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    self.tmp_stack.push(Value::Bool(value_1 != value_2))
                }
                Instruction::Less => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.less(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::LessEq => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.less_eq(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::More => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.more(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::MoreEq => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.more_eq(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Add => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.add(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Subtract => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.subtract(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Multiply => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.multiply(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Divide => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.divide(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Modulo => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.modulo(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Pow => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.pow(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::And => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.and(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Or => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.or(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Xor => {
                    let value_2 = self.pop_tmp(false)?;
                    let value_1 = self.pop_tmp(false)?;
                    let new_value = value_1.xor(value_2)?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Negative => {
                    let value = self.pop_tmp(false)?;
                    let new_value = value.negative()?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::Not => {
                    let value = self.pop_tmp(false)?;
                    let new_value = value.not()?;
                    self.tmp_stack.push(new_value)
                }
                Instruction::PushNil => self.tmp_stack.push(Value::Nil),
                Instruction::PushTrue => self.tmp_stack.push(Value::Bool(true)),
                Instruction::PushFalse => self.tmp_stack.push(Value::Bool(false)),
                Instruction::ReadTable => {
                    let key = self.pop_tmp(false)?;
                    let table = self.pop_tmp(false)?;
                    if let Some(table) = table.as_table() {
                        let mut value = table
                            .get(&key)
                            .map(|value| unsafe { value.duplicate() })
                            .unwrap_or(Value::Nil);
                        value.root();
                        self.tmp_stack.push(value)
                    } else {
                        return Err(RuntimeError::NotATable(format!("{}", table)).into());
                    }
                }
                Instruction::WriteTable => {
                    let value = self.pop_tmp(false)?;
                    let key = self.pop_tmp(false)?;
                    let mut table = self.pop_tmp(false)?;
                    if let Some(table) = table.as_table_mut() {
                        self.gc.add_table_element(table, key, value);
                    } else {
                        return Err(RuntimeError::NotATable(format!("{}", table)).into());
                    }
                }
                Instruction::ReadFunction(_) => {
                    let function = self.read_function(operand)?;
                    self.tmp_stack.push(function);
                }
                Instruction::ReadConstant(_) => self.tmp_stack.push(
                    self.chunk()
                        .constants
                        .get(operand as usize)
                        .cloned()
                        .unwrap_or(Constant::Nil)
                        .into(),
                ),
                Instruction::ReadGlobal(_) => {
                    let name = self.chunk().globals.get(operand as usize).ok_or(
                        InternalError::IncorrectInstruction(Instruction::ReadGlobal(operand)),
                    )?;
                    let mut value = self
                        .global_variables
                        .get(name)
                        .map(|value| unsafe { value.duplicate() })
                        .unwrap_or(Value::Nil);
                    value.root();
                    self.tmp_stack.push(value)
                }
                Instruction::WriteGlobal(_) => {
                    let name = self
                        .chunk
                        .globals
                        .get(operand as usize)
                        .ok_or(InternalError::IncorrectInstruction(
                            Instruction::ReadGlobal(operand),
                        ))?
                        .clone();
                    let global = self.pop_tmp(true)?;
                    self.write_global(name, global)
                }
                Instruction::ReadLocal(_) => {
                    let local = self.read_local(operand as usize)?;
                    self.tmp_stack.push(local)
                }
                Instruction::WriteLocal(_) => {
                    let local = self.pop_tmp(true)?;
                    self.write_local(operand as usize, local)?
                }
                Instruction::ReadCaptured(_) => {
                    let mut captured = unsafe {
                        self.captured_vars()
                            .get(operand as usize)
                            .ok_or(InternalError::IncorrectInstruction(
                                Instruction::ReadCaptured(operand),
                            ))?
                            .duplicate()
                    };
                    captured.root();
                    self.tmp_stack.push(captured)
                }
                Instruction::WriteCaptured(_) => {
                    let var = self.pop_tmp(true)?;
                    let captured = self.captured_vars_mut().get_mut(operand as usize).ok_or(
                        InternalError::IncorrectInstruction(Instruction::ReadCaptured(operand)),
                    )?;
                    if let Some(value) = captured.as_captured_mut() {
                        *value = var;
                    }
                }
                Instruction::Pop(_) => {
                    for _ in 0..operand {
                        self.pop_tmp(false)?;
                    }
                }
                // NOTE FOR JUMPS : We need to add/subtract 1 because we are on the instruction AFTER the jump.
                Instruction::Jump(_) => self.jump_to(operand as usize + self.ip - 1)?,
                Instruction::JumpTrue(_) => {
                    if self.tmp_stack.last().ok_or(InternalError::EmptyStack)? == &Value::Bool(true)
                    {
                        self.jump_to(operand as usize + self.ip - 1)?
                    }
                }
                Instruction::JumpFalse(_) => {
                    if self.tmp_stack.last().ok_or(InternalError::EmptyStack)?
                        == &Value::Bool(false)
                    {
                        self.jump_to(operand as usize + self.ip - 1)?
                    }
                }
                Instruction::JumpPopFalse(_) => {
                    if self.pop_tmp(false)? == Value::Bool(false) {
                        self.jump_to(operand as usize + self.ip - 1)?
                    }
                }
                Instruction::JumpEndWhile(_) => {
                    let value = self.pop_tmp(false)?;
                    if value == Value::Bool(false) {
                        self.loop_addresses.pop();
                        self.jump_to(operand as usize + self.ip - 1)?
                    }
                }
                Instruction::JumpEndFor(_) => {
                    if self.tmp_stack.last() == Some(&Value::Nil) {
                        self.pop_tmp(false)?;
                        // address of the loop variable, since this instruction is always followed by `WriteLocal(loop_index)`.
                        {
                            let ip_before = self.ip;
                            let (_, operand) = self.read_ip()?;
                            match self.local_vars_mut().get_mut(operand as usize) {
                                Some(value) => {
                                    value.unroot();
                                    *value = Value::Nil;
                                }
                                None => {
                                    return Err(InternalError::InvalidOperand(
                                        Instruction::WriteLocal(operand),
                                    )
                                    .into())
                                }
                            }
                            self.ip = ip_before;
                        }
                        self.loop_addresses.pop();
                        self.jump_to(operand as usize + self.ip - 1)?;
                        self.pop_tmp(false)?;
                    }
                }
                Instruction::Break(_) => {
                    let (_, jump_address) = self
                        .loop_addresses
                        .last()
                        .ok_or(InternalError::BreakOrContinueOutsideLoop(true))?;
                    match operand {
                        0 => self.tmp_stack.push(Value::Bool(false)),
                        1 => self.tmp_stack.push(Value::Nil),
                        _ => {
                            return Err(
                                InternalError::InvalidOperand(Instruction::Break(operand)).into()
                            )
                        }
                    }
                    self.ip = *jump_address;
                }
                Instruction::Continue(_) => {
                    let (expr_address, _) = self
                        .loop_addresses
                        .last()
                        .ok_or(InternalError::BreakOrContinueOutsideLoop(false))?;
                    self.ip = *expr_address
                }
                Instruction::PrepareLoop(_) => {
                    let expr_address = self.ip;
                    let jump_address = expr_address + operand as usize;
                    self.loop_addresses.push((expr_address, jump_address))
                }
                Instruction::Call(_) => {
                    let local_start = self.stack.len();
                    for arg in self.tmp_stack.drain(
                        (self
                            .tmp_stack
                            .len()
                            .checked_sub(operand as usize)
                            .ok_or(InternalError::EmptyStack)?)..,
                    ) {
                        self.stack.push(arg);
                    }

                    let mut function = self.pop_tmp(false)?;

                    let function = match function.as_function_mut() {
                        Some(function) => function,
                        None => {
                            use std::ops::DerefMut;
                            if let Value::RustFunction(function) = function {
                                let function = function.clone();
                                let mut function = function.0.borrow_mut();
                                match function.deref_mut()(&mut self.stack[local_start..]) {
                                    Ok(mut value) => {
                                        value.root();
                                        self.tmp_stack.push(value);
                                        for mut value in self.stack.drain(local_start..) {
                                            value.unroot()
                                        }
                                    }
                                    Err(err) => return Err(RuntimeError::RustFunction(err).into()),
                                }
                                continue;
                            } else {
                                return Err(
                                    RuntimeError::NotAFunction(format!("{}", function)).into()
                                );
                            }
                        }
                    };

                    if operand != function.0.arg_number as u64 {
                        return Err(
                            RuntimeError::InvalidArgNumber(function.0.arg_number, operand).into(),
                        );
                    }

                    for _ in 0..(function.0.locals_number - operand as u32) {
                        self.stack.push(Value::Nil)
                    }

                    let captured_start = self.stack.len();
                    for captured in function.1 {
                        let mut captured = unsafe { captured.duplicate() };
                        captured.root();
                        self.stack.push(captured);
                    }

                    self.call_frames.push(CallFrame {
                        chunk: function.0.clone(),
                        previous_ip: self.ip,
                        local_start,
                        captured_start,
                    });

                    self.ip = 0;
                }
                Instruction::MakeTable(_) => {
                    let mut new_table = self.gc.new_table();
                    if let Some(table) = new_table.as_table_mut() {
                        for _ in 0..operand {
                            let value = self.pop_tmp(false)?;
                            let key = self.pop_tmp(false)?;
                            self.gc.add_table_element(table, key, value);
                        }
                    }
                    self.tmp_stack.push(new_table)
                }
                Instruction::DuplicateTop(_) => {
                    // bound-checking ahead
                    let index_start = match self.tmp_stack.len().checked_sub(operand as usize + 1) {
                        Some(index_start) => index_start,
                        None => return Err(InternalError::EmptyStack.into()),
                    };
                    for index in index_start..self.tmp_stack.len() {
                        // we already did the bound-check !
                        let mut duplicate =
                            unsafe { self.tmp_stack.get_unchecked(index).duplicate() };
                        duplicate.root();
                        self.tmp_stack.push(duplicate)
                    }
                }
                // unreacheable : already consumed at the beginning of the loop
                Instruction::Extended(_) => unreachable!(),
            }
        }
    }
}

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

#[derive(Debug)]
pub enum InternalError {
    InstructionPointerOOB(usize, usize),
    JumpOob(usize, bool),
    EmptyStack,
    IncorrectInstruction(Instruction<u64>),
    /// if `true`, `break`, else `continue`.
    BreakOrContinueOutsideLoop(bool),
    InvalidOperand(Instruction<u64>),
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
                        "!!! jump address -{} is out of bounds !!!",
                        jump_address
                    )
                } else {
                    write!(
                        formatter,
                        "!!! jump address {} is out of bounds !!!",
                        jump_address
                    )
                }
            }
            Self::EmptyStack => formatter.write_str("!!! empty stack !!!"),
            Self::IncorrectInstruction(instruction) => write!(
                formatter,
                "!!! incorrect instruction : '{:?}'  !!!",
                instruction
            ),
            Self::BreakOrContinueOutsideLoop(b) => write!(
                formatter,
                "unexpected {} outside or a 'while' or 'for' loop",
                if *b { "break" } else { "continue" }
            ),
            Self::InvalidOperand(instruction) => write!(
                formatter,
                "!!! invalid operand for instruction '{}' : '{}'  !!!",
                instruction.name(),
                instruction.operand().unwrap()
            ),
        }
    }
}

#[derive(Debug)]
pub enum VMError<'a> {
    Internal { kind: InternalError, line: usize },
    Runtime { kind: RuntimeError, line: usize },
    Parser(Vec<ParserError<'a>>),
}

impl<'a> VMError<'a> {
    pub fn continuable(&self) -> Continue {
        match self {
            Self::Runtime { .. } | Self::Internal { .. } => Continue::Stop,
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

#[derive(Debug)]
enum VMErrorKind {
    Internal(InternalError),
    Runtime(RuntimeError),
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

impl From<InternalError> for VMErrorKind {
    fn from(err: InternalError) -> Self {
        Self::Internal(err)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operations() {
        let mut vm = VM::new();
        vm.parse_top_level(
            "
            x = 5                  # x = 5
            y = x + 1              # y = 6
            z = y * x + 8 - 2 % 2  # z = 38
            return (z + 5) * -0.5  # return -21.5
        ",
        )
        .unwrap();

        assert_eq!(vm.run().unwrap(), Value::Float(-21.5));
    }

    #[test]
    fn tables() {
        let mut vm = VM::new();
        vm.parse_top_level(
            "
            t = { x = 5, y = 6 }
            t.y -= 4
            return t.x * t.y
        ",
        )
        .unwrap();

        assert_eq!(vm.run().unwrap(), Value::Int(10));
    }

    #[test]
    fn control_flow() {
        let mut vm = VM::new();
        vm.parse_top_level(
            "
            x = 5
            y = 6
            if x > y then
                if true then
                    return x + y
                end
            else
                if not not not false then
                    y -= 2
                else
                    y += 2
                end
            end
            return y",
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(4));

        let mut vm = VM::new();
        vm.parse_top_level(
            "
            y = 1
            x = 64
            while x > y
                x -= 5
            end
            return x",
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(-1));

        // testing extended instructions
        let mut vm = VM::new();
        vm.parse_top_level(
            "
            total = 0
            y = 1
            x = 64
            while x > y
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
            end
            total += x
            x = 64
            while x > y
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                if x == 0 then
                    break
                end
            end
            total += x
            x = 64
            while x > y
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                if x == 0 then
                    continue
                end
            end
            total += x
            return total
            ",
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(0));

        let mut vm = VM::new();
        vm.parse_top_level(
            "
            x1 = 0
            x2 = 1
            i = 5
            while true
                i -= 1
                x = x1 + x2
                x1 = x2
                x2 = x
                if i <= 0 then
                    break
                end
            end
            return x2",
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(8));
    }

    #[test]
    fn for_loop() {
        let mut vm = VM::new();
        vm.parse_top_level(
            "
            fn range(a, b)
                it = a
                fn iter()
                    if it == b then
                        return nil
                    else
                        it += 1
                        return it - 1
                    end
                end
                return iter
            end
            x = 0
            for i in range(1, 4)
                while i != 0
                    i -= 1
                    x += 1
                end
            end
            return x
            ",
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(6));
    }

    #[test]
    fn errors() {
        let mut vm = VM::new();
        assert!(vm.parse_top_level("0 = x",).is_err());
        vm.parse_top_level("x.a = 7").unwrap();
        assert!(vm.run().is_err());
        vm.reset();
        vm.parse_top_level("x[789] = 9").unwrap();
        assert!(vm.run().is_err());
    }
}
