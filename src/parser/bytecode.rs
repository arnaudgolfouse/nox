use super::LocalOrCaptured;
use crate::lexer::TokenKind;
use std::{convert::TryFrom, fmt, iter, mem::size_of, slice, sync::Arc};

/// Helper trait : this should not be derived by any actual type other than u8,
/// u16, usize... (which is already done in this library).
#[doc(hidden)]
pub trait Operand: fmt::Display + Sized + Default + Copy + std::cmp::PartialOrd {
    /// data for the `Extended` instructions. In theory, this is `[Option<u8>; n]`.
    type Extended: fmt::Debug;
    /// Return the operand and the slice of (eventual) extended operands.
    fn extended(self) -> (u8, <Self as Operand>::Extended);
    /// Return an iterator over the (eventual) extended operands.
    fn iter_extended(
        extended: &<Self as Operand>::Extended,
    ) -> iter::Copied<slice::Iter<Option<Instruction<u8>>>>;
}

/// implement [`Operand`] for integer types
macro_rules! implement_integer_operand {
    ($($t:ty)*) => {
        $(
        impl Operand for $t {
            type Extended = [Option<Instruction<u8>>; size_of::<Self>() - 1];

            fn extended(mut self) -> (u8, <Self as Operand>::Extended) {
                let u8_part = (self & 0xff) as u8;
                self = self.checked_shr(8).unwrap_or(0);
                let mut extended = [None; size_of::<Self>() - 1];
                for extended in &mut extended {
                    if self == 0 {
                        break
                    }
                    let byte = (self & 0xff) as u8;
                    *extended = Some(Instruction::Extended(byte));
                    self = self.checked_shr(8).unwrap_or(0);
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

/// This macro helps implementing methods on [`Instruction`] easily.
macro_rules! instructions {
    (
        $(
            $(#[$code1_doc:meta])*
            $code1:ident => $name1:literal,
        )*
        ---
        $(
            $(#[$code2_doc:meta])*
            $code2:ident(Op) => $name2:literal,
        )*
    ) => {
/// Bytecode instructions
///
/// # Notes
///
/// This structure is generic over the argument type to facilitate parsing
/// (where instructions can have up to [`u32`] operands). Only the [`u8`]
/// variant will effectively be used at the end.
#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Instruction<Op: Operand> {
    $(
        $(#[$code1_doc])*
        $code1,
    )*
    $(
        $(#[$code2_doc])*
        $code2(Op),
    )*
}

impl<Op: Operand> fmt::Debug for Instruction<Op> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            $(
                Self::$code1 => formatter.write_str(stringify!($code1)),
            )*
            $(
                Self::$code2(operand) => {
                    write!(formatter, stringify!($code2))?;
                    write!(formatter, "({})", operand)
                }
            )*
        }
    }
}

impl<Op: Operand> Instruction<Op> {
    /// Return `Some(operand)` if an operand is associated with this
    /// instruction, else it returns [`None`].
    pub fn operand(self) -> Option<Op> {
        match self {
            $(
                Self::$code1 => None,
            )*
            $(
                Self::$code2(operand) => Some(operand),
            )*
        }
    }

    /// Returns the printable name of the instruction.
    pub fn name(self) -> &'static str {
        match self {
            $(
                Self::$code1 => $name1,
            )*
            $(
                Self::$code2(_) => $name2,
            )*
        }
    }

    /// Convert this instruction into a [`u8`] instruction, and the eventual
    /// extended operands.
    pub fn into_u8(self) -> (Instruction<u8>, Op::Extended) {
        let (operand, extended) = self.operand().unwrap_or_default().extended();

        (
            match self {
                $(
                    Self::$code1 => Instruction::$code1,
                )*
                $(
                    Self::$code2(_) => Instruction::$code2(operand),
                )*
            },
            extended,
        )
    }
}
    };
}

instructions! {
    /// Return from the current function
    ///
    /// This pops a call frame, including all its variables (local and captured)
    Return => "RETURN",
    /// Equality test (`==`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    Equal => "EQUAL",
    /// Inequality test (`!=`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    NEqual => "NOT_EQUAL",
    /// Inferior test (`<`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    Less => "LESS",
    /// Inferior or equal test (`<=`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    LessEq => "LESS_EQ",
    /// Superior test (`>`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    More => "MORE",
    /// Superior or equal test (`>=`)
    ///
    /// Pop two values from the stack, compare them and push the result.
    MoreEq => "MORE_EQ",
    /// Addition (`+`)
    ///
    /// Pop two values from the stack, add them and push the result.
    Add => "ADD",
    /// Subtraction (`-`)
    ///
    /// Pop two values from the stack, subtract on with the other, and push the
    /// result.
    Subtract => "SUBTRACT",
    /// Multiplication (`*`)
    ///
    /// Pop two values from the stack, multiply them and push the result.
    Multiply => "MULTIPLY",
    /// Division (`/`)
    ///
    /// Pop two values from the stack, divide of with the other, and push the
    /// result.
    Divide => "DIVIDE",
    /// Modulo (`%`)
    ///
    /// Pop two values from the stack, take one modulo the other,and push the
    /// result.
    Modulo => "MODULO",
    /// Power (`^`)
    ///
    /// Pop two values from the stack, take one to the power of the other, and
    /// push the result.
    Pow => "POW",
    /// `or`
    ///
    /// Pop two values from the stack, 'or' them, and push the result.
    Or => "OR",
    /// `and`
    ///
    /// Pop two values from the stack, 'and' them, and push the result.
    And => "AND",
    /// `xor`
    ///
    /// Pop two values from the stack, 'xor' them, and push the result.
    Xor => "XOR",
    /// `<<`
    ///
    /// Pop two values from the stack, shift the first by the second, and push
    /// the result.
    ShiftL => "SHL",
    /// `>>`
    ///
    /// Pop two values from the stack, shift the first by the second, and push
    /// the result.
    ShiftR => "SHR",
    /// Negation (-)
    ///
    /// Pop one value from the stack, negate it, and push it back.
    Negative => "NEG",
    /// Logical negation (not)
    ///
    /// Pop one value from the stack, negate it logically, and push it back.
    Not => "NOT",
    /// Push `nil` on the stack.
    PushNil => "PUSH_NIL",
    /// Push `true` on the stack.
    PushTrue => "PUSH_TRUE",
    /// Push `false` on the stack.
    PushFalse => "PUSH_FALSE",
    /// Read a table element
    ///
    /// The key is at the top of the stack, and the table right behind it.
    ReadTable => "READ_TABLE",
    /// Write a table element
    ///
    /// The element to write is at the top of the stack, then the key, and
    /// then the table.
    WriteTable => "WRITE_TABLE",
    ---
    /// Push a function on the stack.
    ///
    /// The function is designated by its index in the `functions` field of the
    /// chunk.
    ReadFunction(Op) => "READ_FUNCTION",
    /// Push a constant on the stack.
    ///
    /// The constant is designated by its index in the `constants` field of the
    /// chunk.
    ReadConstant(Op) => "READ_CONSTANT",
    /// Push a global on the stack.
    ///
    /// The global's name is designated by its index in the `globals` field of
    /// the chunk.
    ReadGlobal(Op) => "READ_GLOBAL",
    /// Write a global variable.
    ///
    /// Pop the variable at the top of the stack, and write it at the global
    /// name, designated by its index in the `globals` field of the chunk.
    WriteGlobal(Op) => "WRITE_GLOBAL",
    /// Push a local variable on the stack.
    ///
    /// The local is designated by its index in the `locals` part of the stack.
    ReadLocal(Op) => "READ_LOCAL",
    /// Write a local variable.
    ///
    /// Pop the variable at the top of the stack, and write it at the given
    /// index in the `locals` part of the stack.
    WriteLocal(Op) => "WRITE_LOCAL",
    /// Push a captured variable on the stack.
    ///
    /// The captured is designated by its index in the `captured` part of the
    /// stack.
    ReadCaptured(Op) => "READ_CAPTURED",
    /// Write a captured variable.
    ///
    /// Pop the variable at the top of the stack, and write it at the given
    /// index in the `captured` part of the stack.
    WriteCaptured(Op) => "WRITE_CAPTURED",
    /// Pop the indicated number of values from the stack.
    Pop(Op) => "POP",
    /// Raw jump
    ///
    /// Jump the specified offset in the instructions vector.
    Jump(Op) => "JUMP",
    /// Conditional jump
    ///
    /// Pop the top of the stack, and jump the specified offset in the
    /// instructions vector if it is `false`.
    JumpPopFalse(Op) => "JUMP_POP_FALSE",
    /// Conditional jump
    ///
    /// Pop the top of the stack, and if it is `false`, jump the specified
    /// offset in the instructions vector and pop an element of `loop_addresses`.
    JumpEndWhile(Op) => "JUMP_END_WHILE",
    /// Conditional jump
    ///
    /// Pop the top of the stack, and if it is `nil`, jump the specified
    /// offset in the instructions vector, pop an element of `loop_addresses`,
    /// pop the top of the stack (the function), and 'clear' (unroots) the
    /// loop variable.
    JumpEndFor(Op) => "JUMP_END_FOR",
    /// Break for the closest enclosing loop.
    ///
    /// If `Op == 0`, this is a `while` loop, else this is a `for` loop.
    ///
    /// No changes to the stack : This will use the stored loop address.
    Break(Op) => "BREAK",
    /// Break for the closest enclosing loop.
    ///
    /// If `Op == 0`, this is a `while` loop, else this is a `for` loop.
    ///
    /// No changes to the stack : This will use the stored loop address.
    Continue(Op) => "CONTINUE",
    /// Prepare for a `while` or `for` loop by storing addresses.
    ///
    /// The operand is an offset to the position of the jump.
    ///
    /// The current address will be stored, as well as the address of the jump.
    PrepareLoop(Op) => "PREPARE_LOOP",
    /// Call a function.
    ///
    /// This interprets the `operand` last values of the stack as the
    /// arguments, and the following value as the function.
    Call(Op) => "CALL",
    /// Creates a new table and pushes it on the stack.
    ///
    /// This will use 2*Op elements of the stack to make this table (pair by
    /// pair).
    MakeTable(Op) => "MAKE_TABLE",
    /// Duplicate the first `Op+1` elements of the stack.
    DuplicateTop(Op) => "DUPLICATE_TOP",
    /// Argument extension
    ///
    /// Allow for instructions with u16 / u24 / u32 operands : this always
    /// precede the concerned instruction.
    Extended(Op) => "EXTENDED",
}

/// Constants of a program
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Nil,
    Int(i64),
    Bool(bool),
    Float(f64),
    String(Box<str>),
}

impl TryFrom<TokenKind> for Constant {
    type Error = TokenKind;
    fn try_from(token_kind: TokenKind) -> Result<Self, TokenKind> {
        use crate::lexer::Keyword;
        match token_kind {
            TokenKind::Int(i) => Ok(Self::Int(i)),
            TokenKind::Float(f) => Ok(Self::Float(f)),
            TokenKind::Str(s) => Ok(Self::String(s)),
            TokenKind::Keyword(Keyword::True) => Ok(Self::Bool(true)),
            TokenKind::Keyword(Keyword::False) => Ok(Self::Bool(false)),
            TokenKind::Keyword(Keyword::Nil) => Ok(Self::Nil),
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

/// Chunk of code.
///
/// This structure contains all the necessary informations to run a function,
/// including its code but also constants, other functions, global variables
/// names...
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Chunk {
    /// Name of this chunk
    pub(crate) name: Box<str>,
    /// Vector of position information for the instructions
    pub(crate) positions: Vec<(usize, u32)>,
    /// bytecode instructions
    pub(crate) code: Vec<Instruction<u8>>,
    /// Number of arguments for this function (0 is top-level)
    pub(crate) arg_number: usize,
    /// Constants associated with the chunk
    pub(crate) constants: Vec<Constant>,
    /// Global names associated with the chunk
    pub(crate) globals: Vec<Box<str>>,
    /// Number of locals needed when loading the function
    pub(crate) locals_number: usize,
    /// Captured variables from this function's parent.
    pub(crate) captures: Vec<LocalOrCaptured>,
    /// functions inside this chunk
    pub(crate) functions: Vec<Arc<Chunk>>,
}

impl Chunk {
    /// Create a new Chunk with the name `name`.
    pub(super) fn new(name: Box<str>) -> Self {
        Self {
            name,
            positions: Vec::new(),
            code: Vec::new(),
            arg_number: 0,
            constants: Vec::new(),
            globals: Vec::new(),
            locals_number: 0,
            captures: Vec::new(),
            functions: Vec::new(),
        }
    }

    /// Return the name of this chunk.
    pub const fn name(&self) -> &str {
        &self.name
    }

    /// Emit the new instruction.
    ///
    /// Multiple [`u8`] instructions will actually be emmited if the operand is
    /// bigger than [`u8::MAX`].
    pub(super) fn emit_instruction<Op: Operand>(
        &mut self,
        instruction: Instruction<Op>,
        position: usize,
    ) {
        let (instruction, extended) = instruction.into_u8();
        for extended in Op::iter_extended(&extended) {
            if let Some(extended) = extended {
                self.emit_instruction_u8(extended, position)
            }
        }
        self.emit_instruction_u8(instruction, position)
    }

    /// Directly push an instruction.
    ///
    /// If you want to use bigger operands than [`u8`], consider using
    /// [`emit_instruction`](Chunk::emit_instruction) instead.
    pub(super) fn emit_instruction_u8(&mut self, instruction: Instruction<u8>, position: usize) {
        match self.positions.last_mut() {
            Some((pos, nb)) if *pos == position => *nb += 1,
            _ => self.positions.push((position, 1)),
        }

        self.code.push(instruction)
    }

    /// Add a constant to the `Chunk`, and return its index for future
    /// reference.
    pub(super) fn add_constant(&mut self, constant: Constant) -> usize {
        if let Some((index, _)) = self
            .constants
            .iter()
            .enumerate()
            .find(|(_, cst)| **cst == constant)
        {
            return index;
        }

        self.constants.push(constant);
        self.constants.len() - 1
    }

    /// Add a global to the `Chunk`, and return its index for future reference.
    pub(super) fn add_global(&mut self, global: Box<str>) -> usize {
        if let Some((index, _)) = self
            .globals
            .iter()
            .enumerate()
            .find(|(_, glob)| **glob == global)
        {
            return index;
        }

        self.globals.push(global);
        self.globals.len() - 1
    }

    /// push a dummy `Jump(0)` instruction, and returns its index in the bytecode
    /// for future modification
    pub(super) fn push_jump(&mut self) -> usize {
        self.code.push(Instruction::Jump(0));
        self.code.len() - 1
    }

    /// Write the (now known) operand at the given index.
    ///
    /// This function can be quite inneficient, as operands bigger than
    /// [`u8::MAX`] will shift a lot of code to make room for extended
    /// instructions.
    pub(super) fn write_jump(&mut self, address: usize, instruction: Instruction<u64>) {
        let initial_instruction = &mut self.code[address];
        // wow there cowboy !
        #[allow(clippy::panic)]
        {
            debug_assert_eq!(*initial_instruction, Instruction::Jump(0))
        }
        let (instruction, extended) = instruction.into_u8();
        *initial_instruction = instruction;
        for extended in extended.iter().copied().flatten() {
            self.code.insert(address, extended);
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
            .map(|op| u32::from(op) + extended.unwrap_or(0));
        write!(formatter, "{:<14}    ", instruction.name())?;
        let operand_value = match instruction {
            Instruction::ReadConstant(_) => {
                format!("{}", self.constants[operand.unwrap_or_default() as usize]).into_boxed_str()
            }
            Instruction::ReadGlobal(_) | Instruction::WriteGlobal(_) => {
                self.globals[operand.unwrap_or_default() as usize].clone()
            }
            Instruction::ReadFunction(_) => self.functions[operand.unwrap_or_default() as usize]
                .name
                .clone(),
            _ => Box::from(""),
        };
        let operand = if let Some(operand) = instruction.operand() {
            format!("{}", operand)
        } else {
            String::new()
        };

        write!(formatter, "{:<10} {}", operand, operand_value)
    }

    /// Get the position for the instruction at `index`, or the last position.
    ///
    /// This function will iterate on the whole bytecode to find the correct
    /// position, making it potentially costly.
    pub fn get_pos(&self, index: usize) -> usize {
        let mut pos_index = 0;
        for (pos, nb) in self.positions.iter().copied() {
            if pos_index + nb as usize >= index {
                return pos as usize;
            }
            pos_index += nb as usize;
        }

        self.positions.last().map_or(0, |(pos, _)| *pos) as usize
    }
}

impl fmt::Display for Chunk {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(formatter, "{} :", self.name)?;
        write!(formatter, " - constants : [")?;
        for constant in &self.constants[..self.constants.len().saturating_sub(1)] {
            write!(formatter, "{}, ", constant)?
        }
        if let Some(last) = self.constants.last() {
            write!(formatter, "{}", last)?
        }
        writeln!(formatter, "]")?;
        writeln!(formatter, " - globals : {:?}", self.globals)?;
        write!(formatter, " - functions : [")?;
        for function in &self.functions[..self.functions.len().saturating_sub(1)] {
            write!(formatter, "{}, ", function.name)?
        }
        if let Some(last) = self.functions.last() {
            write!(formatter, "{}", last.name)?
        }
        writeln!(formatter, "]")?;
        writeln!(formatter, " - {} locals", self.locals_number)?;
        writeln!(formatter)?;
        formatter
            .write_str("pos        index      opcode            operand    operand value\n\n")?;
        let mut positions = self.positions.iter();
        let mut current_position = match positions.next() {
            Some(position) => position,
            None => return Ok(()),
        };
        let mut positions_acc = 0;
        let mut extended = None;
        for (i, inst) in self.code.iter().enumerate() {
            if positions_acc == 0 {
                write!(formatter, "{:<10} ", current_position.0)
            } else {
                formatter.write_str("|          ")
            }?;
            write!(formatter, "{:<10} ", i)?;
            if let Instruction::Extended(extend) = inst {
                extended = Some((extended.unwrap_or(0) << 8) + u32::from(*extend));
                self.fmt_instruction(*inst, None, formatter)?;
            } else {
                self.fmt_instruction(*inst, extended, formatter)?;
                extended = None;
            }
            writeln!(formatter)?;
            positions_acc += 1;
            if positions_acc == current_position.1 {
                current_position = positions.next().unwrap_or(&(0, 0));
                positions_acc = 0
            }
        }

        for function in &self.functions {
            writeln!(
                formatter,
                "\n================================================================"
            )?;
            writeln!(formatter, "{}", function)?;
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

        let y: u16 = (4 << 8) + 2;
        assert_eq!(y.extended(), (2, [Some(Instruction::Extended(4))]));

        let z: u32 = (102 << 24) + (6 << 8) + 84;
        assert_eq!(
            z.extended(),
            (
                84,
                [
                    Some(Instruction::Extended(6)),
                    Some(Instruction::Extended(0)),
                    Some(Instruction::Extended(102))
                ]
            )
        );
    }
}
