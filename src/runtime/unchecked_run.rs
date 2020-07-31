use super::*;

impl VM {
    /// Read the instruction pointer, resolving any `Instruction::Extended`.
    ///
    /// # Note
    ///
    /// No bound-checking is done to see if the instruction pointer is out of
    /// bounds
    #[inline]
    fn read_ip(&mut self) -> (Instruction<u8>, u64) {
        let mut operand = 0;
        let opcode = loop {
            match *unsafe { self.code().get_unchecked(self.ip) } {
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
        (opcode, operand)
    }

    /// Pop and unroot a value from the `stack`.
    ///
    /// If `rooted` is `true`, the value will NOT be unrooted.
    #[inline]
    fn pop_tmp(&mut self, rooted: bool) -> Value {
        // TODO : replace this with `unreacheable` once it is stabilized
        let mut value = self.stack.pop().unwrap_or(Value::Nil);
        if !rooted {
            value.unroot();
        }
        value
    }

    /// Read a value at `index` from the `stack`.
    ///
    /// The returned value will have an additional root.
    #[inline]
    fn read_local(&mut self, index: usize) -> Value {
        let mut local = unsafe { self.local_vars().get_unchecked(index).duplicate() };
        local.root();
        local
    }

    /// Read a `value` at `index` in the `stack`.
    ///
    /// The previous value will be unrooted.
    fn write_local(&mut self, index: usize, value: Value) {
        let old_value = unsafe { self.local_vars_mut().get_unchecked_mut(index) };
        old_value.unroot();
        *old_value = value;
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
    /// # Note
    ///
    /// No bound-checking is done
    #[inline]
    fn jump_to(&mut self, destination: usize) {
        self.ip = destination;
    }

    /// Read a function from the current code's `functions`.
    ///
    /// This will take care of capturing variables, and the returned function
    /// will be rooted.
    fn read_function(&mut self, operand: u64) -> Value {
        use crate::parser::LocalOrCaptured;

        let function = unsafe {
            self.chunk()
                .functions
                .get_unchecked(operand as usize)
                .clone()
        };

        // Capture variables
        let mut captured = Vec::new();
        for captured_index in function.captures.iter() {
            match captured_index {
                LocalOrCaptured::Local(index) => {
                    let to_capture =
                        unsafe { self.local_vars_mut().get_unchecked_mut(*index).duplicate() };
                    let to_capture = self.gc.new_captured(to_capture);
                    captured.push(unsafe { to_capture.duplicate() });
                    unsafe {
                        *self.local_vars_mut().get_unchecked_mut(*index) = to_capture;
                    }
                }
                LocalOrCaptured::Captured(index) => {
                    let to_capture = unsafe { self.captured_vars_mut().get_unchecked_mut(*index) };
                    captured.push(unsafe { to_capture.duplicate() })
                }
            }
        }

        self.gc.new_function(function, captured)
    }

    /// Return the closest loop address for the current function
    fn loop_address(&self) -> (usize, usize) {
        match self.call_frames.last() {
            Some(function) => &function.loop_addresses,
            None => &self.loop_addresses,
        }
        .last()
        .copied()
        .unwrap_or((0, 0))
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

    pub(super) fn run_internal(&mut self) -> Result<Value, VMErrorKind> {
        loop {
            let (opcode, operand) = self.read_ip();
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
                            None => {} // TODO : unreacheable
                        }
                    } else if let Some(value) = self.stack.pop() {
                        return Ok(value);
                    } else {
                        // TODO : unreacheable
                    }
                }
                Instruction::Equal => {
                    let value_1 = self.pop_tmp(false);
                    let value_2 = self.pop_tmp(false);
                    self.stack.push(Value::Bool(value_1 == value_2))
                }
                Instruction::NEqual => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    self.stack.push(Value::Bool(value_1 != value_2))
                }
                Instruction::Less => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.less(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::LessEq => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.less_eq(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::More => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.more(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::MoreEq => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.more_eq(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Add => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.add(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Subtract => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.subtract(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Multiply => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.multiply(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Divide => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.divide(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Modulo => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.modulo(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Pow => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.pow(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::And => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.and(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Or => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.or(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Xor => {
                    let value_2 = self.pop_tmp(false);
                    let value_1 = self.pop_tmp(false);
                    let new_value = value_1.xor(value_2)?;
                    self.stack.push(new_value)
                }
                Instruction::Negative => {
                    let value = self.pop_tmp(false);
                    let new_value = value.negative()?;
                    self.stack.push(new_value)
                }
                Instruction::Not => {
                    let value = self.pop_tmp(false);
                    let new_value = value.not()?;
                    self.stack.push(new_value)
                }
                Instruction::PushNil => self.stack.push(Value::Nil),
                Instruction::PushTrue => self.stack.push(Value::Bool(true)),
                Instruction::PushFalse => self.stack.push(Value::Bool(false)),
                Instruction::ReadTable => {
                    let key = self.pop_tmp(false);
                    let table = self.pop_tmp(false);
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
                    let value = self.pop_tmp(false);
                    let key = self.pop_tmp(false);
                    let mut table = self.pop_tmp(false);
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
                    let function = self.read_function(operand);
                    self.stack.push(function);
                }
                Instruction::ReadConstant(_) => self.stack.push(unsafe {
                    self.chunk()
                        .constants
                        .get_unchecked(operand as usize)
                        .clone()
                        .into()
                }),
                Instruction::ReadGlobal(_) => {
                    let name = unsafe { self.chunk().globals.get_unchecked(operand as usize) };
                    let mut value = self
                        .global_variables
                        .get(name)
                        .map(|value| unsafe { value.duplicate() })
                        .unwrap_or(Value::Nil);
                    value.root();
                    self.stack.push(value)
                }
                Instruction::WriteGlobal(_) => {
                    let name =
                        unsafe { self.chunk.globals.get_unchecked(operand as usize).clone() };
                    let global = self.pop_tmp(true);
                    self.write_global(name, global)
                }
                Instruction::ReadLocal(_) => {
                    let local = self.read_local(operand as usize);
                    self.stack.push(local)
                }
                Instruction::WriteLocal(_) => {
                    let local = self.pop_tmp(true);
                    self.write_local(operand as usize, local)
                }
                Instruction::ReadCaptured(_) => {
                    let mut captured = unsafe {
                        self.captured_vars()
                            .get_unchecked(operand as usize)
                            .duplicate()
                    };
                    captured.root();
                    self.stack.push(captured)
                }
                Instruction::WriteCaptured(_) => {
                    let var = self.pop_tmp(true);
                    let captured =
                        unsafe { self.captured_vars_mut().get_unchecked_mut(operand as usize) };
                    if let Some(value) = captured.as_captured_mut() {
                        *value = var;
                    }
                }
                Instruction::Pop(_) => {
                    for _ in 0..operand {
                        self.pop_tmp(false);
                    }
                }
                // NOTE FOR JUMPS : We need to add/subtract 1 because we are on the instruction AFTER the jump.
                Instruction::Jump(_) => self.jump_to(operand as usize + self.ip - 1),
                Instruction::JumpPopFalse(_) => {
                    if self.pop_tmp(false) == Value::Bool(false) {
                        self.jump_to(operand as usize + self.ip - 1)
                    }
                }
                Instruction::JumpEndWhile(_) => {
                    let value = self.pop_tmp(false);
                    if value == Value::Bool(false) {
                        self.pop_loop_address();
                        self.jump_to(operand as usize + self.ip - 1)
                    }
                }
                Instruction::JumpEndFor(_) => {
                    if self.stack.last() == Some(&Value::Nil) {
                        self.pop_tmp(false);
                        // address of the loop variable, since this instruction is always followed by `WriteLocal(loop_index)`.
                        {
                            let ip_before = self.ip;
                            let (_, operand) = self.read_ip();
                            {
                                let value = unsafe {
                                    self.local_vars_mut().get_unchecked_mut(operand as usize)
                                };
                                value.unroot();
                                *value = Value::Nil;
                            }
                            self.ip = ip_before;
                        }
                        self.pop_loop_address();
                        self.jump_to(operand as usize + self.ip - 1);
                        self.pop_tmp(false);
                    }
                }
                Instruction::Break(_) => {
                    let (_, jump_address) = self.loop_address();
                    if operand == 0 {
                        self.stack.push(Value::Bool(false))
                    } else {
                        self.stack.push(Value::Nil)
                    }
                    self.ip = jump_address;
                }
                Instruction::Continue(_) => {
                    let (expr_address, _) = self.loop_address();
                    self.ip = expr_address
                }
                Instruction::PrepareLoop(_) => {
                    let expr_address = self.ip;
                    let jump_address = expr_address + operand as usize;
                    self.push_loop_address((expr_address, jump_address))
                }
                Instruction::Call(_) => {
                    let local_start = self.stack.len() - operand as usize;
                    let mut function =
                        unsafe { self.stack.get_unchecked(local_start - 1).duplicate() };

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
                            let value = self.pop_tmp(false);
                            let key = self.pop_tmp(false);
                            self.gc.add_table_element(table, key, value);
                        }
                    }
                    self.stack.push(new_table)
                }
                Instruction::DuplicateTop(_) => {
                    let index_start = self.stack.len() - operand as usize - 1;
                    for index in index_start..self.stack.len() {
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
    Runtime(RuntimeError),
}

#[derive(Debug)]
pub enum VMError<'a> {
    Runtime { kind: RuntimeError, line: usize },
    Parser(Vec<ParserError<'a>>),
}
