use super::*;

impl VM {
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

    /// Pop and unroot a value from the `stack`.
    ///
    /// If `rooted` is `true`, the value will NOT be unrooted.
    #[inline]
    fn pop_stack(&mut self, rooted: bool) -> Result<Value, VMErrorKind> {
        let mut value = self.stack.pop().ok_or(InternalError::EmptyStack)?;
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
        Ok({
            let mut local = unsafe {
                self.local_vars()
                    .get(index)
                    .ok_or(InternalError::InvalidOperand(Instruction::ReadLocal(
                        index as u64,
                    )))?
                    .duplicate()
            };
            local.root();
            local
        })
    }

    /// Write a `value` at `index` in the `stack`.
    ///
    /// The previous value will be unrooted.
    fn write_local(&mut self, index: usize, value: Value) -> Result<(), VMErrorKind> {
        let old_value =
            self.local_vars_mut()
                .get_mut(index)
                .ok_or(InternalError::InvalidOperand(Instruction::WriteLocal(
                    index as u64,
                )))?;
        old_value.unroot();
        *old_value = value;
        Ok(())
    }

    /// Root and write the given global value, unrooting any potential previous
    /// value.
    #[inline]
    fn write_global(&mut self, name: Box<str>, global: Value) {
        if let Some(mut value) = if global == Value::Nil {
            self.global_variables.remove(&name)
        } else {
            self.global_variables.insert(name, global)
        } {
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
        if destination >= self.code().len() {
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
            .ok_or(InternalError::InvalidOperand(Instruction::ReadFunction(
                operand,
            )))?
            .clone();

        // Capture variables
        let mut captured = Vec::new();
        for captured_index in function.captures.iter() {
            match captured_index {
                LocalOrCaptured::Local(index) => {
                    let to_capture = unsafe {
                        self.local_vars_mut()
                            .get_mut(*index)
                            .ok_or(InternalError::InvalidOperand(Instruction::ReadLocal(
                                *index as u64,
                            )))?
                            .duplicate()
                    };
                    let to_capture = self.gc.new_captured(to_capture);
                    captured.push(unsafe { to_capture.duplicate() });
                    *self.local_vars_mut().get_mut(*index).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadLocal(*index as u64)),
                    )? = to_capture;
                }
                LocalOrCaptured::Captured(index) => {
                    let to_capture = self.captured_vars_mut().get_mut(*index).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadLocal(*index as u64)),
                    )?;
                    captured.push(unsafe { to_capture.duplicate() })
                }
            }
        }

        Ok(self.gc.new_function(function, captured))
    }

    /// Return the (eventual) closest loop address for the current function
    fn loop_address(&self, break_or_continue: bool) -> Result<(usize, usize), InternalError> {
        match self.call_frames.last() {
            Some(function) => &function.loop_addresses,
            None => &self.loop_addresses,
        }
        .last()
        .copied()
        .ok_or(InternalError::BreakOrContinueOutsideLoop(break_or_continue))
    }

    /// Push a loop address for the current function
    fn push_loop_address(&mut self, addresses: (usize, usize)) {
        match self.call_frames.last_mut() {
            Some(function) => function.loop_addresses.push(addresses),
            None => self.loop_addresses.push(addresses),
        }
    }

    /// Pop a loop address for the current function
    fn pop_loop_address(&mut self) {
        match self.call_frames.last_mut() {
            Some(function) => function.loop_addresses.pop(),
            None => self.loop_addresses.pop(),
        };
    }

    /// Pop two values from the stack and applies the given operation.
    fn binary_op(
        &mut self,
        op: impl Fn(Value, Value) -> Result<Value, OperationError>,
    ) -> Result<(), VMErrorKind> {
        let value_2 = self.pop_stack(false)?;
        let value_1 = self.pop_stack(false)?;
        let new_value = op(value_1.captured_value(), value_2.captured_value())?;
        self.stack.push(new_value);
        Ok(())
    }

    pub(super) fn run_internal(&mut self) -> Result<Value, VMErrorKind> {
        loop {
            let (opcode, operand) = self.read_ip()?;
            match opcode {
                Instruction::Return => {
                    if let Some(frame) = self.call_frames.pop() {
                        for mut value in self
                            .stack
                            .drain(frame.local_start - 1..self.stack.len() - 1)
                        {
                            value.unroot()
                        }
                        self.ip = frame.previous_ip;
                        match self.stack.last_mut() {
                            Some(return_value) => return_value.decapture(),
                            None => return Err(InternalError::EmptyStack.into()),
                        }
                    } else if let Some(value) = self.stack.pop() {
                        return Ok(value);
                    } else {
                        return Err(InternalError::EmptyStack.into());
                    }
                }
                Instruction::Equal => {
                    let value_1 = self.pop_stack(false)?;
                    let value_2 = self.pop_stack(false)?;
                    self.stack.push(Value::Bool(value_1 == value_2))
                }
                Instruction::NEqual => {
                    let value_2 = self.pop_stack(false)?;
                    let value_1 = self.pop_stack(false)?;
                    self.stack.push(Value::Bool(value_1 != value_2))
                }
                Instruction::Less => self.binary_op(Value::less)?,
                Instruction::LessEq => self.binary_op(Value::less_eq)?,
                Instruction::More => self.binary_op(Value::more)?,
                Instruction::MoreEq => self.binary_op(Value::more_eq)?,
                Instruction::Add => self.binary_op(Value::add)?,
                Instruction::Subtract => self.binary_op(Value::subtract)?,
                Instruction::Multiply => self.binary_op(Value::multiply)?,
                Instruction::Divide => self.binary_op(Value::divide)?,
                Instruction::Modulo => self.binary_op(Value::modulo)?,
                Instruction::Pow => self.binary_op(Value::pow)?,
                Instruction::And => self.binary_op(Value::and)?,
                Instruction::Or => self.binary_op(Value::or)?,
                Instruction::Xor => self.binary_op(Value::xor)?,
                Instruction::ShiftL => self.binary_op(Value::shift_left)?,
                Instruction::ShiftR => self.binary_op(Value::shift_right)?,
                Instruction::Negative => {
                    let value = self.pop_stack(false)?;
                    let new_value = value.negative()?;
                    self.stack.push(new_value)
                }
                Instruction::Not => {
                    let value = self.pop_stack(false)?;
                    let new_value = value.not()?;
                    self.stack.push(new_value)
                }
                Instruction::PushNil => self.stack.push(Value::Nil),
                Instruction::PushTrue => self.stack.push(Value::Bool(true)),
                Instruction::PushFalse => self.stack.push(Value::Bool(false)),
                Instruction::ReadTable => {
                    let key = self.pop_stack(false)?;
                    let table = self.pop_stack(false)?;
                    if let Some(table) = table.as_table() {
                        let mut value = table
                            .get(&key)
                            .map(|value| unsafe { value.duplicate() })
                            .unwrap_or(Value::Nil);
                        value.root();
                        self.stack.push(value)
                    } else {
                        return Err(RuntimeError::NotATable(format!("{}", table)).into());
                    }
                }
                Instruction::WriteTable => {
                    let value = self.pop_stack(false)?;
                    let key = self.pop_stack(false)?;
                    let mut table = self.pop_stack(false)?;
                    if let Some(table) = table.as_table_mut() {
                        if value == Value::Nil {
                            self.gc.remove_table_element(table, &key);
                        } else {
                            self.gc.add_table_element(table, key, value);
                        }
                    } else {
                        return Err(RuntimeError::NotATable(format!("{}", table)).into());
                    }
                }
                Instruction::ReadFunction(_) => {
                    let function = self.read_function(operand)?;
                    self.stack.push(function);
                }
                Instruction::ReadConstant(_) => self.stack.push(
                    self.chunk()
                        .constants
                        .get(operand as usize)
                        .cloned()
                        .unwrap_or(Constant::Nil)
                        .into(),
                ),
                Instruction::ReadGlobal(_) => {
                    let name = self.chunk().globals.get(operand as usize).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadGlobal(operand)),
                    )?;
                    let mut value = self
                        .global_variables
                        .get(name)
                        .map(|value| unsafe { value.duplicate() })
                        .unwrap_or(Value::Nil);
                    value.root();
                    self.stack.push(value)
                }
                Instruction::WriteGlobal(_) => {
                    let name = self
                        .chunk
                        .globals
                        .get(operand as usize)
                        .ok_or(InternalError::InvalidOperand(Instruction::ReadGlobal(
                            operand,
                        )))?
                        .clone();
                    let global = self.pop_stack(true)?;
                    self.write_global(name, global)
                }
                Instruction::ReadLocal(_) => {
                    let local = self.read_local(operand as usize)?;
                    self.stack.push(local)
                }
                Instruction::WriteLocal(_) => {
                    let local = self.pop_stack(true)?;
                    self.write_local(operand as usize, local)?
                }
                Instruction::ReadCaptured(_) => {
                    let mut captured = unsafe {
                        self.captured_vars()
                            .get(operand as usize)
                            .ok_or(InternalError::InvalidOperand(Instruction::ReadCaptured(
                                operand,
                            )))?
                            .duplicate()
                    };
                    captured.root();
                    self.stack.push(captured)
                }
                Instruction::WriteCaptured(_) => {
                    let var = self.pop_stack(true)?;
                    let captured = self.captured_vars_mut().get_mut(operand as usize).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadCaptured(operand)),
                    )?;
                    if let Some(value) = captured.as_captured_mut() {
                        *value = var;
                    }
                }
                Instruction::Pop(_) => {
                    for _ in 0..operand {
                        self.pop_stack(false)?;
                    }
                }
                // NOTE FOR JUMPS : We need to add/subtract 1 because we are on the instruction AFTER the jump.
                Instruction::Jump(_) => self.jump_to(operand as usize + self.ip - 1)?,
                Instruction::JumpPopFalse(_) => {
                    if self.pop_stack(false)? == Value::Bool(false) {
                        self.jump_to(operand as usize + self.ip - 1)?
                    }
                }
                Instruction::JumpEndWhile(_) => {
                    let value = self.pop_stack(false)?;
                    if value == Value::Bool(false) {
                        self.pop_loop_address();
                        self.jump_to(operand as usize + self.ip - 1)?
                    }
                }
                Instruction::JumpEndFor(_) => {
                    if self.stack.last() == Some(&Value::Nil) {
                        self.pop_stack(false)?;
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
                        self.pop_loop_address();
                        self.jump_to(operand as usize + self.ip - 1)?;
                        self.pop_stack(false)?;
                    }
                }
                Instruction::Break(_) => {
                    let (_, jump_address) = self.loop_address(true)?;
                    match operand {
                        0 => self.stack.push(Value::Bool(false)),
                        1 => self.stack.push(Value::Nil),
                        _ => {
                            return Err(
                                InternalError::InvalidOperand(Instruction::Break(operand)).into()
                            )
                        }
                    }
                    self.ip = jump_address;
                }
                Instruction::Continue(_) => {
                    let (expr_address, _) = self.loop_address(false)?;
                    self.ip = expr_address
                }
                Instruction::PrepareLoop(_) => {
                    let expr_address = self.ip;
                    let jump_address = expr_address + operand as usize;
                    self.push_loop_address((expr_address, jump_address));
                }
                Instruction::Call(_) => {
                    let local_start = self
                        .stack
                        .len()
                        .checked_sub(operand as usize)
                        .ok_or(InternalError::EmptyStack)?;
                    let mut function = unsafe {
                        self.stack
                            .get(local_start - 1)
                            .ok_or(InternalError::EmptyStack)?
                            .duplicate()
                    };

                    let func = match function.as_function_mut() {
                        Some(function) => function,
                        None => {
                            use std::ops::DerefMut;
                            if let Value::RustFunction(function) = function {
                                let function = function.clone();
                                let mut function = function.0.borrow_mut();
                                match function.deref_mut()(&mut self.stack[local_start..]) {
                                    Ok(mut value) => {
                                        value.root();
                                        for mut value in self.stack.drain(local_start - 1..) {
                                            value.unroot()
                                        }
                                        self.stack.push(value);
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

                    if operand != func.0.arg_number as u64 {
                        return Err(
                            RuntimeError::InvalidArgNumber(func.0.arg_number, operand).into()
                        );
                    }

                    for _ in 0..(func.0.locals_number - operand as u32) {
                        self.stack.push(Value::Nil)
                    }

                    let captured_start = self.stack.len();
                    for captured in func.1 {
                        let mut captured = unsafe { captured.duplicate() };
                        captured.root();
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
                }
                Instruction::MakeTable(_) => {
                    let mut new_table = self.gc.new_table();
                    if let Some(table) = new_table.as_table_mut() {
                        for _ in 0..operand {
                            let value = self.pop_stack(false)?;
                            let key = self.pop_stack(false)?;
                            self.gc.add_table_element(table, key, value);
                        }
                    }
                    self.stack.push(new_table)
                }
                Instruction::DuplicateTop(_) => {
                    // bound-checking ahead
                    let index_start = match self.stack.len().checked_sub(operand as usize + 1) {
                        Some(index_start) => index_start,
                        None => return Err(InternalError::EmptyStack.into()),
                    };
                    for index in index_start..self.stack.len() {
                        // we already did the bound-check !
                        let mut duplicate = unsafe { self.stack.get_unchecked(index).duplicate() };
                        duplicate.root();
                        self.stack.push(duplicate)
                    }
                }
                // unreacheable : already consumed at the beginning of the loop
                Instruction::Extended(_) => unreachable!(),
            }
        }
    }
}

#[derive(Debug)]
pub(super) enum VMErrorKind {
    Internal(InternalError),
    Runtime(RuntimeError),
}

/// Error internally thrown by the VM.
///
/// Such errors *should* not happen in theory. If they do, that means there is a
/// bug in the VM or parser.
#[derive(Debug)]
pub enum InternalError {
    /// The instruction pointer was out of bounds : the first number is the
    /// value of the instruction pointer, and the second is the length of the
    /// instruction vector.
    InstructionPointerOOB(usize, usize),
    /// The instruction pointer is sent out of bounds by the contained offset.
    /// The boolean indicate whether the offset is positive (`true`) or negative
    /// (`false`)
    JumpOob(usize, bool),
    /// An element was requested from the `stack` but it was empty.
    EmptyStack,
    /// Various instruction errors. Most of the time this is caused by an
    /// incorrect `Read-` or `Write-` instruction operand.
    InvalidOperand(Instruction<u64>),
    /// A `Break` or `Continue` instruction was encountered outside of a loop.
    ///
    /// If `true`, `break`, else `continue`.
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

/// Various errors thrown by the Virtual Machine.
#[derive(Debug)]
pub enum VMError<'a> {
    /// Internal error : indicate a bug in the VM
    Internal { kind: InternalError, line: usize },
    /// Error encountered at runtime
    Runtime {
        kind: RuntimeError,
        line: usize,
        unwind_message: String,
    },
    /// Error(s) encountered while parsing
    Parser(Vec<ParserError<'a>>),
}

impl From<InternalError> for VMErrorKind {
    fn from(err: InternalError) -> Self {
        Self::Internal(err)
    }
}
