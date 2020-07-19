pub mod gc;
pub mod values;

use crate::{
    error::Continue,
    parser::{Chunk, Constant, Instruction, Parser, ParserError},
};
use gc::GC;
use std::{collections::HashMap, fmt, sync::Arc};
use values::Value;

#[derive(Default, Debug)]
struct CallFrame {
    previous_code: Arc<Chunk>,
    start: usize,
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
    call_frames: Vec<CallFrame>,
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
        self.chunk = Arc::new(Chunk::default());
        self.ip = 0;
        for mut value in self.stack.drain(..) {
            value.unroot()
        }
        for mut value in self.tmp_stack.drain(..) {
            value.unroot()
        }
        for (_, mut value) in self.global_variables.drain() {
            value.unroot()
        }
        self.call_frames.clear();
    }

    pub fn parse_top_level<'a>(&mut self, source: &'a str) -> Result<(), VMError<'a>> {
        let parser = Parser::new(crate::Source::TopLevel(source));
        self.chunk = Arc::new(parser.parse_top_level()?);
        self.ip = 0;
        for mut value in self.stack.drain(..) {
            value.unroot()
        }
        for mut value in self.tmp_stack.drain(..) {
            value.unroot()
        }
        self.call_frames.clear();
        Ok(())
    }

    #[inline]
    fn current_frame_start(&self) -> usize {
        self.call_frames
            .last()
            .map(|frame| frame.start)
            .unwrap_or(0)
    }

    #[inline]
    fn code(&self) -> &Vec<Instruction<u8>> {
        &self.chunk.code
    }

    /// Read the instruction pointer, resolving any `Instruction::Extended`.
    ///
    /// # Errors
    ///
    /// An error is emitted is the instruction pointer is out of bounds.
    fn read_ip<'a>(&mut self) -> Result<(Instruction<u8>, u64), VMError<'a>> {
        let mut operand = 0;
        let opcode =
            loop {
                match self.code().get(self.ip).copied().ok_or_else(|| {
                    RuntimeError::InstructionPointerOOB(self.ip, self.code().len())
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
    fn pop_tmp<'a>(&mut self, rooted: bool) -> Result<Value, VMError<'a>> {
        let mut value = self.tmp_stack.pop().ok_or(RuntimeError::EmptyStack)?;
        if !rooted {
            value.unroot();
        }
        Ok(value)
    }

    /// Read a value at `index` from the `stack`.
    #[inline]
    fn read_local<'a>(&self, index: usize) -> Result<Value, VMError<'a>> {
        Ok(self
            .stack
            .get(index)
            .ok_or(RuntimeError::IncorrectInstruction(Instruction::ReadLocal(
                index as u64,
            )))?
            .clone())
    }

    /// Read a `value` at `index` in the `stack`.
    ///
    /// The previous value will be unrooted.
    fn write_local<'a>(&mut self, index: usize, value: Value) -> Result<(), VMError<'a>> {
        let old_value = self
            .stack
            .get_mut(index)
            .ok_or(RuntimeError::IncorrectInstruction(Instruction::ReadLocal(
                index as u64,
            )))?;
        old_value.unroot();
        *old_value = value;
        Ok(())
    }

    /// Root and write the given global value, unrooting any potential previous
    /// value.
    #[inline]
    fn write_global(&mut self, name: String, mut global: Value) {
        global.root();
        if let Some(mut value) = self.global_variables.insert(name, global) {
            value.unroot()
        }
    }

    /// Jump to the specified destination.
    ///
    /// # Return
    ///
    /// - `Ok(None)` if `destination` was in bounds.
    /// - `Ok(Some(Value::Nil))` if `destination == self.code().len()`.
    /// - `Err(RuntimeError::JumpOob)` else.
    #[inline]
    fn jump_to<'a>(&mut self, destination: usize) -> Result<Option<Value>, VMError<'a>> {
        let code_len = self.code().len();
        match destination {
            destination if destination < code_len => {
                Err(RuntimeError::JumpOob(destination, true).into())
            }
            _ if destination == code_len => Ok(Some(Value::Nil)),
            _ => {
                self.ip = destination;
                Ok(None)
            }
        }
    }

    pub fn run<'a>(&mut self) -> Result<Value, VMError<'a>> {
        loop {
            if self.ip == self.code().len() {
                return Ok(Value::Nil);
            }
            let (opcode, operand) = self.read_ip()?;
            match opcode {
                Instruction::Return => {
                    if let Some(frame) = self.call_frames.pop() {
                        for mut value in self.stack.drain(frame.start..) {
                            value.unroot()
                        }
                    } else if let Some(value) = self.tmp_stack.pop() {
                        return Ok(value);
                    } else {
                        return Err(RuntimeError::EmptyStack.into());
                    }
                }
                Instruction::Equal => {
                    let value_1 = self.pop_tmp(false)?;
                    let value_2 = self.pop_tmp(false)?;
                    self.tmp_stack.push(Value::Bool(value_1 == value_2))
                }
                Instruction::NEqual => {
                    let value_1 = self.pop_tmp(false)?;
                    let value_2 = self.pop_tmp(false)?;
                    self.tmp_stack.push(Value::Bool(value_1 != value_2))
                }
                Instruction::Less => todo!(),
                Instruction::LessEq => todo!(),
                Instruction::More => todo!(),
                Instruction::MoreEq => todo!(),
                Instruction::Add => todo!(),
                Instruction::Subtract => todo!(),
                Instruction::Multiply => todo!(),
                Instruction::Divide => todo!(),
                Instruction::Modulo => todo!(),
                Instruction::Pow => todo!(),
                Instruction::And => todo!(),
                Instruction::Or => todo!(),
                Instruction::Xor => todo!(),
                Instruction::Negative => todo!(),
                Instruction::Not => todo!(),
                Instruction::PushNil => self.tmp_stack.push(Value::Nil),
                Instruction::PushTrue => self.tmp_stack.push(Value::Bool(true)),
                Instruction::PushFalse => self.tmp_stack.push(Value::Bool(false)),
                Instruction::ReadTable => todo!(),
                Instruction::WriteTable => todo!(),
                Instruction::ReadFunction(_) => todo!(),
                Instruction::ReadConstant(_) => self.tmp_stack.push(
                    self.chunk
                        .constants
                        .get(operand as usize)
                        .cloned()
                        .unwrap_or(Constant::Nil)
                        .into(),
                ),
                Instruction::ReadGlobal(_) => {
                    let name = self.chunk.strings.get(operand as usize).ok_or(
                        RuntimeError::IncorrectInstruction(Instruction::ReadGlobal(operand)),
                    )?;
                    let mut value = self
                        .global_variables
                        .get(name)
                        .cloned()
                        .unwrap_or(Value::Nil);
                    value.root();
                    self.tmp_stack.push(value)
                }
                Instruction::WriteGlobal(_) => {
                    let name = self
                        .chunk
                        .strings
                        .get(operand as usize)
                        .ok_or(RuntimeError::IncorrectInstruction(Instruction::ReadGlobal(
                            operand,
                        )))?
                        .clone();
                    let global = self.pop_tmp(false)?;
                    self.write_global(name, global)
                }
                Instruction::ReadLocal(_) => {
                    let local = self.read_local(operand as usize + self.current_frame_start())?;
                    self.tmp_stack.push(local)
                }
                Instruction::WriteLocal(_) => {
                    let local = self.pop_tmp(true)?;
                    self.write_local(operand as usize + self.current_frame_start(), local)?
                }
                Instruction::ReadCaptured(_) => todo!(),
                Instruction::WriteCaptured(_) => todo!(),
                Instruction::Pop(_) => {
                    for _ in 0..operand {
                        self.pop_tmp(false)?;
                    }
                }
                Instruction::Jump(_) => {
                    if let Some(value) = self.jump_to(operand as usize + self.ip)? {
                        return Ok(value);
                    }
                }
                Instruction::JumpTrue(_) => {
                    if self.tmp_stack.last().ok_or(RuntimeError::EmptyStack)? == &Value::Bool(true)
                    {
                        if let Some(value) = self.jump_to(operand as usize + self.ip)? {
                            return Ok(value);
                        }
                    }
                }
                Instruction::JumpFalse(_) => {
                    if self.tmp_stack.last().ok_or(RuntimeError::EmptyStack)? == &Value::Bool(false)
                    {
                        if let Some(value) = self.jump_to(operand as usize + self.ip)? {
                            return Ok(value);
                        }
                    }
                }
                Instruction::JumpPopTrue(_) => {
                    if self.pop_tmp(false)? == Value::Bool(true) {
                        if let Some(value) = self.jump_to(operand as usize + self.ip)? {
                            return Ok(value);
                        }
                    }
                }
                Instruction::JumpPopFalse(_) => {
                    if self.pop_tmp(false)? == Value::Bool(false) {
                        if let Some(value) = self.jump_to(operand as usize + self.ip)? {
                            return Ok(value);
                        }
                    }
                }
                Instruction::JumpBack(_) => match self.ip.checked_sub(operand as usize) {
                    Some(destination) => self.ip = destination,
                    None => {
                        return Err(RuntimeError::JumpOob(operand as usize - self.ip, false).into())
                    }
                },
                Instruction::Call(_) => todo!(),
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
                Instruction::DuplicateTop(_) => todo!(),
                // unreacheable : already consumed at the beginning of the loop
                Instruction::Extended(_) => unreachable!(),
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum RuntimeError {
    InstructionPointerOOB(usize, usize),
    JumpOob(usize, bool),
    EmptyStack,
    IncorrectInstruction(Instruction<u64>),
}

impl fmt::Display for RuntimeError {
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
        }
    }
}

pub struct VMError<'a> {
    kind: VMErrorKind<'a>,
    continuable: Continue,
}

#[derive(Debug)]
pub enum VMErrorKind<'a> {
    Runtime(RuntimeError),
    Parser(Vec<ParserError<'a>>),
}

impl<'a> From<Vec<ParserError<'a>>> for VMError<'a> {
    fn from(err: Vec<ParserError<'a>>) -> Self {
        let continuable = err
            .last()
            .map(|err| err.continuable)
            .unwrap_or(Continue::Continue);
        Self {
            kind: VMErrorKind::Parser(err),
            continuable,
        }
    }
}

impl<'a> From<RuntimeError> for VMError<'a> {
    fn from(err: RuntimeError) -> Self {
        Self {
            kind: VMErrorKind::Runtime(err),
            continuable: Continue::Stop,
        }
    }
}

impl<'a> fmt::Display for VMError<'a> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match &self.kind {
            VMErrorKind::Runtime(err) => fmt::Display::fmt(err, formatter),
            VMErrorKind::Parser(err) => {
                for err in err {
                    fmt::Display::fmt(err, formatter)?
                }
                Ok(())
            }
        }
    }
}

impl<'a> VMError<'a> {
    pub fn continuable(&self) -> Continue {
        self.continuable
    }
}
