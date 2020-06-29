use crate::lexer::TokenKind;
use std::{convert::TryFrom, fmt, mem::size_of};

/// Helper trait : this should not be derived by any actual type other than u8, u16, usize... (which is already done in this library).
#[doc(hidden)]
pub trait Operand: Sized + Default + Copy {
    /// data for the `Extended` instructions. In theory, this is `[Option<u8>; n]`.
    type Extended;
    /// Return the operand and the slice of (eventual) extended operands.
    fn extended(self) -> (u8, <Self as Operand>::Extended);
    /// Return an iterator over the (eventual) extended operands.
    fn iter_extended(
        extended: &<Self as Operand>::Extended,
    ) -> std::iter::Copied<std::slice::Iter<Option<Instruction<u8>>>>;
}

/// implement `Operand` for integer types
macro_rules! implement_integer_operand {
    ($($t:ty)*) => {
        $(
        impl Operand for $t {
            type Extended = [Option<Instruction<u8>>; size_of::<$t>() - 1];
            fn extended(mut self) -> (u8, <Self as Operand>::Extended) {
                let u8_part = (self & 0xff) as u8;
                self = self.rotate_right(8);
                let mut extended = [None; size_of::<$t>() - 1];
                for i in 0..extended.len() {
                    let byte = (self & 0xff) as u8;
                    if byte != 0 {
                        extended[i] = Some(Instruction::Extended(byte));
                    }
                    self = self.rotate_right(8);
                }
                (u8_part, extended)
            }

            fn iter_extended(extended: &<Self as Operand>::Extended) -> std::iter::Copied<std::slice::Iter<Option<Instruction<u8>>>> {
                extended.into_iter().copied()
            }
        }
        )*
    };
}

implement_integer_operand!(u8 u16 u32 u64 usize);

/// Bytecode instructions
///
/// # Notes
///
/// This structure is generic over the argument type to facilitate parsing (where instructions can
/// have up to u32 operands). Only the `u8` variant will effectively be used at the end.
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Instruction<Op: Operand> {
    /// Return from the current function
    ///
    /// This leaves the stack unchanged.
    Return,
    /// Equality test (`==`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    Equal,
    /// Inequality test (`!=`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    NEqual,
    /// Inferior test (`<`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    Less,
    /// Inferior or equal test (`<=`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    LessEq,
    /// Superior test (`>`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    More,
    /// Superior or equal test (`>=`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    MoreEq,
    /// Addition (`+`)
    ///
    /// Pop two values from the stack, add them and push the result.
    Add,
    /// Subtraction (`-`)
    ///
    /// Pop two values from the stack, subtract on with the other, and push the result.
    Subtract,
    /// Multiplication (`*`)
    ///
    /// Pop two values from the stack, multiply them and push the result.
    Multiply,
    /// Division (`/`)
    ///
    /// Pop two values from the stack, divide of with the other, and push the result.
    Divide,
    /// Modulo (`%`)
    ///
    /// Pop two values from the stack, take one modulo the other,and push the result.
    Modulo,
    /// Power (`^`)
    ///
    /// Pop two values from the stack, take one to the power of the other, and push the
    /// result.
    Pow,
    /// `or`
    ///
    /// Pop two values from the stack, 'or' them, and push the result.
    Or,
    /// `and`
    ///
    /// Pop two values from the stack, 'and' them, and push the result.
    And,
    /// `xor`
    ///
    /// Pop two values from the stack, 'xor' them, and push the result.
    Xor,
    /// Negation (-)
    ///
    /// Pop one value from the stack, negate it, and push it back.
    Negative,
    /// Logical negation (not)
    ///
    /// Pop one value from the stack, negate it logically, and push it back.
    Not,
    /// Push `nil` on the stack.
    PushNil,
    /// Push `true` on the stack.
    PushTrue,
    /// Push `false` on the stack.
    PushFalse,
    /// Push a constant on the stack.
    ///
    /// The constant is designated by its index in the `constants` field of the chunk.
    ReadConstant(Op),
    /// Push a global on the stack.
    ///
    /// The global's name is designated by its index in the `globals` field of the chunk.
    ReadGlobal(Op),
    /// Write a global variable.
    ///
    /// Pop the variable at the top of the stack, and write it at the global name, designated by its
    /// index in the `globals` field of the chunk.
    WriteGlobal(Op),
    /// Push a local on the stack.
    ///
    /// The local is designated by its index in the stack.
    ReadLocal(Op),
    /// Write a local variable.
    ///
    /// Pop the variable at the top of the stack, and write it at the given index in the stack.
    WriteLocal(Op),
    ReadCaptured(Op),
    WriteCaptured(Op),
    /// Pop the indicated number of values from the stack.
    Pop(Op),
    /// Raw jump
    ///
    /// Jump at the specified index in the instructions vector.
    Jump(Op),
    /// Conditional jump
    ///
    /// Jump at the specified index in the instructions vector if `true` is at the top of the stack.
    JumpTrue(Op),
    /// Conditional jump
    ///
    /// Jump at the specified index in the instructions vector if `true` is at the top of the stack, and pops the top of the stack.
    JumpPopTrue(Op),
    /// Call a function.
    ///
    /// This interprets the top of the stack as the function, and the `operand` following values
    /// as the arguments.
    Call(Op),
    /// Argument extension
    ///
    /// Allow for instructions with u16 / u24 / u32 operands : this always precede the concerned
    /// instruction.
    Extended(Op),
}

impl<Op: Operand> Instruction<Op> {
    pub fn operand(self) -> Option<Op> {
        use Instruction::*;
        match self {
            Return | Equal | NEqual | Less | LessEq | More | MoreEq | Add | Subtract | Multiply
            | Divide | Modulo | Pow | Or | And | Xor | Negative | Not | PushNil | PushTrue
            | PushFalse => None,
            ReadConstant(operand)
            | ReadGlobal(operand)
            | WriteGlobal(operand)
            | ReadLocal(operand)
            | WriteLocal(operand)
            | ReadCaptured(operand)
            | WriteCaptured(operand)
            | Pop(operand)
            | Jump(operand)
            | JumpTrue(operand)
            | JumpPopTrue(operand)
            | Call(operand)
            | Extended(operand) => Some(operand),
        }
    }

    /// Returns the printable name of the instruction.
    pub fn name(self) -> &'static str {
        match self {
            Self::Return => "RETURN",
            Self::Equal => "EQUAL",
            Self::NEqual => "NEQUAL",
            Self::Less => "LESS",
            Self::LessEq => "LESS_EQ",
            Self::More => "MORE",
            Self::MoreEq => "MORE_EQ",
            Self::Add => "ADD",
            Self::Subtract => "SUBTRACT",
            Self::Multiply => "MULTIPLY",
            Self::Divide => "DIVIDE",
            Self::Modulo => "MODULO",
            Self::Pow => "POW",
            Self::Or => "OR",
            Self::And => "AND",
            Self::Xor => "XOR",
            Self::Negative => "NEGATIVE",
            Self::Not => "NOT",
            Self::PushNil => "PUSH_NIL",
            Self::PushTrue => "PUSH_TRUE",
            Self::PushFalse => "PUSH_FALSE",
            Self::ReadConstant(_) => "READ_CONSTANT",
            Self::ReadGlobal(_) => "READ_GLOBAL",
            Self::ReadLocal(_) => "WRITE_GLOBAL",
            Self::WriteGlobal(_) => "READ_LOCAL",
            Self::WriteLocal(_) => "WRITE_LOCAL",
            Self::ReadCaptured(_) => "READ_CAPTURED",
            Self::WriteCaptured(_) => "WRITE_CAPTURED",
            Self::Pop(_) => "POP",
            Self::Jump(_) => "JUMP",
            Self::JumpTrue(_) => "JUMP_TRUE",
            Self::JumpPopTrue(_) => "JUMP_POP_TRUE",
            Self::Call(_) => "CALL",
            Self::Extended(_) => "EXTENDED",
        }
    }

    /// Convert this instruction into a `u8` instruction, and the eventual extended operands.
    pub fn into_u8(self) -> (Instruction<u8>, Op::Extended) {
        let (operand, extended) = self.operand().unwrap_or_default().extended();

        use Instruction::*;
        (
            match self {
                Return => Return,
                Equal => Equal,
                NEqual => NEqual,
                Less => Less,
                LessEq => LessEq,
                More => More,
                MoreEq => MoreEq,
                Add => Add,
                Subtract => Subtract,
                Multiply => Multiply,
                Divide => Divide,
                Modulo => Modulo,
                Pow => Pow,
                Or => Or,
                And => And,
                Xor => Xor,
                Negative => Negative,
                Not => Not,
                PushNil => PushNil,
                PushTrue => PushTrue,
                PushFalse => PushFalse,
                ReadConstant(_) => ReadConstant(operand),
                ReadGlobal(_) => ReadGlobal(operand),
                WriteGlobal(_) => WriteGlobal(operand),
                ReadLocal(_) => ReadLocal(operand),
                WriteLocal(_) => WriteLocal(operand),
                ReadCaptured(_) => ReadCaptured(operand),
                WriteCaptured(_) => WriteCaptured(operand),
                Pop(_) => Pop(operand),
                Jump(_) => Jump(operand),
                JumpTrue(_) => JumpTrue(operand),
                JumpPopTrue(_) => JumpPopTrue(operand),
                Call(_) => Call(operand),
                Extended(_) => Extended(operand),
            },
            extended,
        )
    }
}

/// Constants of a program
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Nil,
    Int(i64),
    Bool(bool),
    Float(f64),
    String(String),
}

impl TryFrom<TokenKind> for Constant {
    type Error = TokenKind;
    fn try_from(token_kind: TokenKind) -> Result<Self, TokenKind> {
        use crate::lexer::Keyword;
        match token_kind {
            TokenKind::Int(i) => Ok(Constant::Int(i)),
            TokenKind::Float(f) => Ok(Constant::Float(f)),
            TokenKind::Str(s) => Ok(Constant::String(s)),
            TokenKind::Keyword(Keyword::True) => Ok(Constant::Bool(true)),
            TokenKind::Keyword(Keyword::False) => Ok(Constant::Bool(false)),
            TokenKind::Keyword(Keyword::Nil) => Ok(Constant::Nil),
            _ => Err(token_kind),
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Nil => formatter.write_str("nil"),
            Self::Int(i) => write!(formatter, "{}", i),
            Self::Bool(b) => write!(formatter, "{}", b),
            Self::Float(f) => write!(formatter, "{}", f),
            Self::String(s) => write!(formatter, "{:?}", s),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Chunk {
    /// Name of this chunk
    pub name: String,
    /// Vector of line information for the instructions
    pub lines: Vec<(u32, u32)>,
    /// bytecode instructions
    pub code: Vec<Instruction<u8>>,
    /// Constants associated with the chunk
    pub constants: Vec<Constant>,
    /// Global names associated with the chunk
    pub globals: Vec<String>,
    /// Number of locals needed when loading the function
    pub locals_number: u16,
}

impl Chunk {
    /// Emit the new instruction.
    ///
    /// Multiple `u8` instructions will actually be emmited if the operand is bigger than `u8::MAX`.
    pub fn emit_instruction<Op: Operand>(&mut self, instruction: Instruction<Op>, line: u32) {
        let (instruction, extended) = instruction.into_u8();
        for extended in Op::iter_extended(&extended) {
            if let Some(extended) = extended {
                self.push_instruction(extended, line)
            }
        }
        self.push_instruction(instruction, line)
    }

    /// Directly push an instruction.
    ///
    /// If you want to use bigger operands than `u8`, consider using `emit_instruction` instead.
    pub fn push_instruction(&mut self, instruction: Instruction<u8>, line: u32) {
        match self.lines.last_mut() {
            Some((l, nb)) if *l == line => *nb += 1,
            _ => self.lines.push((line, 1)),
        }

        self.code.push(instruction)
    }

    /// Add a constant to the Chunk, and return it's index for future reference.
    pub fn add_constant(&mut self, constant: Constant) -> u32 {
        self.constants.push(constant);
        self.constants.len() as u32 - 1
    }

    /// Add a global to the Chunk, and return it's index for future reference.
    pub fn add_global(&mut self, global: String) -> u32 {
        for (i, glob) in self.globals.iter().enumerate() {
            if global == *glob {
                return i as u32;
            }
        }
        self.globals.push(global);
        self.globals.len() as u32 - 1
    }

    /// push an instruction (presumed to be a JUMP), and return its index in the bytecode for future modification
    pub fn push_jump(&mut self) -> usize {
        self.code.push(Instruction::Jump(0));
        self.code.len() - 1
    }

    /// Write the (now known) operand at the given index.
    ///
    /// This function can be quite inneficient, as instruction bigger than `u8::MAX` will shift the entire code to make room for extended instructions.
    pub fn write_jump<Op: Operand>(&mut self, instruction: Instruction<Op>, mut address: usize) {
        // wow there cowboy !
        let initial_instruction = &mut self.code[address];
        assert_eq!(initial_instruction, &Instruction::Jump(0));
        let (instruction, extended) = instruction.into_u8();
        *initial_instruction = instruction;
        for extended in Op::iter_extended(&extended) {
            if let Some(extended) = extended {
                self.code.insert(address, extended);
                address += 1
            }
        }
    }

    fn fmt_instruction(
        &self,
        instruction: Instruction<u8>,
        extended: Option<u32>,
        formatter: &mut fmt::Formatter,
    ) -> Result<(), fmt::Error> {
        let operand = instruction
            .operand()
            .map(|op| op as u32 + extended.unwrap_or(0));
        write!(formatter, "{:<14}    ", instruction.name())?;
        let operand_value = match instruction {
            Instruction::ReadConstant(_) => {
                format!("{}", self.constants[operand.unwrap() as usize])
            }
            Instruction::ReadGlobal(_) => self.globals[operand.unwrap() as usize].clone(),
            _ => String::new(),
        };
        let operand = if let Some(operand) = instruction.operand() {
            format!("{}", operand)
        } else {
            String::new()
        };

        write!(formatter, "{:<10} {}", operand, operand_value)
    }
}

impl fmt::Display for Chunk {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        println!("{} :", self.name);
        print!(" - constants : [");
        for constant in &self.constants[..self.constants.len().saturating_sub(1)] {
            print!("{}, ", constant)
        }
        if let Some(last) = self.constants.last() {
            print!("{}", last)
        }
        println!("]");
        println!(" - {} locals", self.locals_number);
        println!();
        formatter
            .write_str("line       index      opcode            operand    operand value\n\n")?;
        let mut lines = self.lines.iter();
        let mut current_line = match lines.next() {
            Some(line) => line,
            None => return Ok(()),
        };
        let mut lines_acc = 0;
        let mut extended = None;
        for (i, inst) in self.code.iter().enumerate() {
            if lines_acc == 0 {
                write!(formatter, "{:<10} ", current_line.0)
            } else {
                formatter.write_str("|          ")
            }?;
            write!(formatter, "{:<10} ", i)?;
            match inst {
                Instruction::Extended(extend) => {
                    extended = Some((extended.unwrap_or(0) << 8) + *extend as u32);
                    self.fmt_instruction(*inst, None, formatter)?;
                }
                _ => {
                    self.fmt_instruction(*inst, extended, formatter)?;
                    extended = None;
                }
            }
            writeln!(formatter)?;
            lines_acc += 1;
            if lines_acc == current_line.1 {
                current_line = lines.next().unwrap_or(&(0, 0));
                lines_acc = 0
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn extended_conversion() {
        let x: u8 = 5;
        assert_eq!(x.extended(), (x, []));

        let x: u16 = (4 << 8) + 2;
        assert_eq!(x.extended(), (2, [Some(Instruction::Extended(4))]));

        let x: u32 = (102 << 24) + (6 << 8) + 84;
        assert_eq!(
            x.extended(),
            (
                84,
                [
                    Some(Instruction::Extended(6)),
                    None,
                    Some(Instruction::Extended(102))
                ]
            )
        );
    }
}
