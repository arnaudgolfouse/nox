use super::{
    Constant, Instruction, InternalError, OperationError, RuntimeError, VMErrorKind, Value, VM,
};

impl VM {
    /// Read the instruction pointer, resolving any `Instruction::Extended`.
    ///
    /// # Errors
    ///
    /// An error is emitted is the instruction pointer is out of bounds.
    fn read_ip(&mut self) -> Result<(Instruction<u8>, usize), VMErrorKind> {
        let mut operand = 0;
        let opcode =
            loop {
                match self.code().get(self.ip).copied().ok_or_else(|| {
                    InternalError::InstructionPointerOOB(self.ip, self.code().len())
                })? {
                    // extended operand
                    Instruction::Extended(extended) => {
                        operand += extended as usize;
                        operand <<= std::mem::size_of::<usize>();
                        self.ip += 1;
                    }
                    instruction => {
                        operand += instruction.operand().unwrap_or(0) as usize;
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
    pub(super) fn pop_stack(&mut self) -> Result<Value, VMErrorKind> {
        self.stack
            .pop()
            .ok_or(VMErrorKind::Internal(InternalError::EmptyStack))
    }

    /// Read a value at `index` from the `stack`.
    ///
    /// The returned value will have an additional root.
    #[inline]
    fn read_local(&mut self, index: usize) -> Result<Value, VMErrorKind> {
        Ok({
            self.local_vars()
                .get(index)
                .ok_or(InternalError::InvalidOperand(Instruction::ReadLocal(index)))?
                .clone()
        })
    }

    /// Write a `value` at `index` in the `stack`.
    ///
    /// The previous value will be unrooted.
    fn write_local(&mut self, index: usize, value: Value) -> Result<(), VMErrorKind> {
        *self
            .local_vars_mut()
            .get_mut(index)
            .ok_or(InternalError::InvalidOperand(Instruction::WriteLocal(
                index,
            )))? = value;
        Ok(())
    }

    /// Root and write the given global value, unrooting any potential previous
    /// value.
    #[inline]
    fn write_global(&mut self, name: Box<str>, global: Value) {
        if global == Value::Nil {
            self.global_variables.remove(&name)
        } else {
            self.global_variables.insert(name, global)
        };
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
    fn read_function(&mut self, operand: usize) -> Result<Value, VMErrorKind> {
        use crate::parser::LocalOrCaptured;

        let function = self
            .chunk()
            .functions
            .get(operand)
            .ok_or(InternalError::InvalidOperand(Instruction::ReadFunction(
                operand,
            )))?
            .clone();

        // Capture variables
        let mut captured = Vec::new();
        for captured_index in &function.captures {
            match captured_index {
                LocalOrCaptured::Local(index) => {
                    let to_capture = self
                        .local_vars_mut()
                        .get_mut(*index)
                        .ok_or(InternalError::InvalidOperand(Instruction::ReadLocal(
                            *index,
                        )))?
                        .clone();
                    let to_capture = self.gc.new_captured(to_capture);
                    captured.push(to_capture.clone());
                    *self.local_vars_mut().get_mut(*index).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadLocal(*index)),
                    )? = to_capture;
                }
                LocalOrCaptured::Captured(index) => {
                    let to_capture = self.captured_vars_mut().get_mut(*index).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadLocal(*index)),
                    )?;
                    captured.push(to_capture.clone())
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
        op: fn(Value, Value) -> Result<Value, OperationError>,
    ) -> Result<(), VMErrorKind> {
        let value_2 = self.pop_stack()?;
        let value_1 = self.pop_stack()?;
        let new_value = op(value_1.captured_value(), value_2.captured_value())?;
        // new_value is not collectable, so there is no need to root it
        self.stack.push(new_value);
        Ok(())
    }

    pub(super) fn run_internal(&mut self) -> Result<(), VMErrorKind> {
        loop {
            let (opcode, operand) = self.read_ip()?;
            match opcode {
                Instruction::Return => {
                    if let Some(frame) = self.call_frames.pop() {
                        for _ in self
                            .stack
                            .drain(frame.local_start - 1..self.stack.len() - 1)
                        {
                        }
                        self.ip = frame.previous_ip;
                        match self.stack.last_mut() {
                            Some(return_value) => return_value.decapture(),
                            None => return Err(InternalError::EmptyStack.into()),
                        }
                    }
                    return Ok(());
                }
                Instruction::Equal => {
                    let value_1 = self.pop_stack()?;
                    let value_2 = self.pop_stack()?;
                    self.stack.push(Value::Bool(value_1 == value_2))
                }
                Instruction::NEqual => {
                    let value_2 = self.pop_stack()?;
                    let value_1 = self.pop_stack()?;
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
                    let value = self.pop_stack()?;
                    let new_value = value.negative()?;
                    self.stack.push(new_value)
                }
                Instruction::Not => {
                    let value = self.pop_stack()?;
                    let new_value = value.not()?;
                    self.stack.push(new_value)
                }
                Instruction::PushNil => self.stack.push(Value::Nil),
                Instruction::PushTrue => self.stack.push(Value::Bool(true)),
                Instruction::PushFalse => self.stack.push(Value::Bool(false)),
                Instruction::ReadTable => {
                    let key = self.pop_stack()?;
                    let table = self.pop_stack()?;
                    if let Some(table) = table.as_table() {
                        let value = table
                            .get(key.as_nodrop_ref())
                            .map_or(Value::Nil, |value| (value as &Value).clone());
                        self.stack.push(value)
                    } else {
                        return Err(RuntimeError::NotATable(format!("{}", table)).into());
                    }
                }
                Instruction::WriteTable => {
                    let value = self.pop_stack()?;
                    let key = self.pop_stack()?;
                    let mut table = self.pop_stack()?;
                    if let Some(table) = table.as_table_mut() {
                        if value == Value::Nil {
                            self.gc.remove_table_element(table, key.as_nodrop_ref());
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
                        .get(operand)
                        .cloned()
                        .unwrap_or(Constant::Nil)
                        .into(),
                ),
                Instruction::ReadGlobal(_) => {
                    let name =
                        self.chunk()
                            .globals
                            .get(operand)
                            .ok_or(InternalError::InvalidOperand(Instruction::ReadGlobal(
                                operand,
                            )))?;
                    let value = self
                        .global_variables
                        .get(name)
                        .map_or(Value::Nil, |value| (value as &Value).clone());
                    self.stack.push(value)
                }
                Instruction::WriteGlobal(_) => {
                    let name = self
                        .chunk
                        .globals
                        .get(operand)
                        .ok_or(InternalError::InvalidOperand(Instruction::ReadGlobal(
                            operand,
                        )))?
                        .clone();
                    let global = self.pop_stack()?;
                    self.write_global(name, global)
                }
                Instruction::ReadLocal(_) => {
                    let local = self.read_local(operand)?;
                    self.stack.push(local)
                }
                Instruction::WriteLocal(_) => {
                    let local = self.pop_stack()?;
                    self.write_local(operand, local)?
                }
                Instruction::ReadCaptured(_) => {
                    let captured = self
                        .captured_vars()
                        .get(operand)
                        .ok_or(InternalError::InvalidOperand(Instruction::ReadCaptured(
                            operand,
                        )))?
                        .clone();
                    self.stack.push(captured)
                }
                Instruction::WriteCaptured(_) => {
                    let var = self.pop_stack()?;
                    let captured = self.captured_vars_mut().get_mut(operand).ok_or(
                        InternalError::InvalidOperand(Instruction::ReadCaptured(operand)),
                    )?;
                    if let Some(value) = captured.as_captured_mut() {
                        *value = var;
                    }
                }
                Instruction::Pop(_) => {
                    for _ in 0..operand {
                        self.pop_stack()?;
                    }
                }
                // NOTE FOR JUMPS : We need to add/subtract 1 because we are on the instruction AFTER the jump.
                Instruction::Jump(_) => self.jump_to(operand + self.ip - 1)?,
                Instruction::JumpPopFalse(_) => {
                    if self.pop_stack()? == Value::Bool(false) {
                        self.jump_to(operand + self.ip - 1)?
                    }
                }
                Instruction::JumpEndWhile(_) => {
                    let value = self.pop_stack()?;
                    if value == Value::Bool(false) {
                        self.pop_loop_address();
                        self.jump_to(operand + self.ip - 1)?
                    }
                }
                Instruction::JumpEndFor(_) => {
                    if self.stack.last() == Some(&Value::Nil) {
                        self.pop_stack()?;
                        // address of the loop variable, since this instruction is always followed by `WriteLocal(loop_index)`.
                        {
                            let ip_before = self.ip;
                            let (_, local_index) = self.read_ip()?;
                            match self.local_vars_mut().get_mut(local_index) {
                                Some(value) => {
                                    *value = Value::Nil;
                                }
                                None => {
                                    return Err(InternalError::InvalidOperand(
                                        Instruction::WriteLocal(local_index),
                                    )
                                    .into())
                                }
                            }
                            self.ip = ip_before;
                        }
                        self.pop_loop_address();
                        self.jump_to(operand + self.ip - 1)?;
                        self.pop_stack()?;
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
                    let jump_address = expr_address + operand;
                    self.push_loop_address((expr_address, jump_address));
                }
                Instruction::Call(_) => {
                    self.call_internal(operand)?;
                }
                Instruction::MakeTable(_) => {
                    let mut new_table = self.gc.new_table();
                    if let Some(table) = new_table.as_table_mut() {
                        for _ in 0..operand {
                            let value = self.pop_stack()?;
                            let key = self.pop_stack()?;
                            self.gc.add_table_element(table, key, value);
                        }
                    }
                    self.stack.push(new_table)
                }
                Instruction::DuplicateTop(_) => {
                    // bound-checking ahead
                    let index_start = match self.stack.len().checked_sub(operand + 1) {
                        Some(index_start) => index_start,
                        None => return Err(InternalError::EmptyStack.into()),
                    };
                    for index in index_start..self.stack.len() {
                        // we already did the bound-check !
                        let duplicate = unsafe { self.stack.get_unchecked(index) }.clone();
                        self.stack.push(duplicate)
                    }
                }
                // unreacheable : already consumed at the beginning of the loop
                Instruction::Extended(_) => unreachable!(),
            }
        }
    }
}
