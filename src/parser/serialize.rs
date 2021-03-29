//! Serialization of a `Chunk` into a binary format.
//!
//! # Note
//! This is not that efficient: in fact, storing source code is lighter 🙃

use super::{bytecode::*, LocalOrCaptured};
use std::{mem::size_of, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, thiserror::Error)]
pub enum DeserializeError {
    #[error("End of buffer input, but the chunk is incomplete")]
    EndOfInput,
    #[error("Unexpected byte: {0}")]
    UnexpectedByte(u8),
    #[error("Length does not fit in `usize`: {0}")]
    DoesNotFitInUsize(u64),
    #[error("An incorrect utf8 byte sequence was found: {0:?}")]
    IncorrectChar([u8; 4]),
}

impl Chunk {
    /// Efficiently serialize this chunk in the given `buffer`.
    ///
    /// # Notes
    /// - All sizes represent the **number of elements**, not byte length.
    /// - Sizes are encoded with `u64`.
    /// - All number on multiple bytes are encoded using `to_le_bytes`.
    pub fn serialize(&self, buffer: &mut Vec<u8>) {
        use serialize::*;

        serialize_str(&self.name, buffer);
        serialize_positions(&self.line, buffer);
        serialize_code(&self.instructions, buffer);
        buffer.extend(&self.arg_number.to_le_bytes());
        serialize_constants(&self.constants, buffer);
        serialize_globals(&self.globals, buffer);
        buffer.extend(&self.locals_number.to_le_bytes());
        serialize_captures(&self.captures, buffer);
        buffer.extend(&(self.functions.len() as u64).to_le_bytes());
        for function in &self.functions {
            function.serialize(buffer)
        }
    }

    pub fn deserialize(mut buffer: &[u8]) -> Result<Self, DeserializeError> {
        Self::deserialize_internal(&mut buffer)
    }

    fn deserialize_internal(buffer: &mut &[u8]) -> Result<Self, DeserializeError> {
        use deserialize::*;

        let name = deserialize_str(buffer)?;
        let positions = deserialize_positions(buffer)?;
        let code = deserialize_code(buffer)?;
        let arg_number = deserialize_u16(buffer)?;
        let constants = deserialize_constants(buffer)?;
        let globals = deserialize_globals(buffer)?;
        let locals_number = deserialize_u32(buffer)?;
        let captures = deserialize_captures(buffer)?;

        let functions_len = deserialize_len(buffer)?;
        let mut functions = Vec::with_capacity(functions_len);
        for _ in 0..functions_len {
            functions.push(Arc::new(Self::deserialize_internal(buffer)?))
        }

        Ok(Self {
            name,
            line: positions,
            instructions: code,
            arg_number,
            constants,
            globals,
            locals_number,
            captures,
            functions,
        })
    }
}

#[allow(clippy::module_inception)]
mod serialize {
    use super::*;

    /// Serialize `s` as a null-terminated string in the given `buffer`.
    pub(super) fn serialize_str(s: &str, buffer: &mut Vec<u8>) {
        buffer.extend(s.as_bytes());
        buffer.push(0);
    }

    pub(super) fn serialize_positions(positions: &[(u64, u32)], buffer: &mut Vec<u8>) {
        buffer.extend(&(positions.len() as u64).to_le_bytes());
        buffer.reserve(positions.len() * (size_of::<u64>() + size_of::<u32>()));
        for (pos, nb) in positions {
            buffer.extend(&pos.to_le_bytes());
            buffer.extend(&nb.to_le_bytes());
        }
    }

    /// Serialize the `code` vector in the given `buffer`.
    ///
    /// Instructions take as much space as they need (so an instruction without
    /// operand take 1 byte).
    pub(super) fn serialize_code(code: &[Instruction<u8>], buffer: &mut Vec<u8>) {
        buffer.extend(&(code.len() as u64).to_le_bytes());
        for instruction in code.iter().copied() {
            buffer.push(instruction.discriminant());
            if let Some(operand) = instruction.operand() {
                buffer.push(operand);
            }
        }
    }

    pub(super) fn serialize_constants(constants: &[Constant], buffer: &mut Vec<u8>) {
        buffer.extend(&(constants.len() as u64).to_le_bytes());
        for constant in constants {
            match constant {
                Constant::Nil => {
                    buffer.push(0);
                }
                Constant::Int(x) => {
                    buffer.push(1);
                    buffer.extend(&x.to_le_bytes());
                }
                Constant::Bool(x) => {
                    buffer.push(2);
                    buffer.push(if *x { 1 } else { 0 });
                }
                Constant::Float(x) => {
                    buffer.push(3);
                    buffer.extend(&x.to_le_bytes());
                }
                Constant::String(x) => {
                    buffer.push(4);
                    serialize_str(x, buffer)
                }
            }
        }
    }

    pub(super) fn serialize_globals(globals: &[Box<str>], buffer: &mut Vec<u8>) {
        buffer.extend(&(globals.len() as u64).to_le_bytes());
        for global in globals {
            serialize_str(global, buffer)
        }
    }

    pub(super) fn serialize_captures(captures: &[LocalOrCaptured], buffer: &mut Vec<u8>) {
        buffer.extend(&(captures.len() as u64).to_le_bytes());
        for capture in captures {
            match capture {
                LocalOrCaptured::Local(idx) => {
                    buffer.push(0);
                    buffer.extend(&idx.to_le_bytes())
                }
                LocalOrCaptured::Captured(idx) => {
                    buffer.push(1);
                    buffer.extend(&idx.to_le_bytes())
                }
            }
        }
    }
}

#[allow(clippy::module_inception)]
mod deserialize {
    use super::*;
    use std::convert::TryInto;

    fn deserialize_u8(buffer: &mut &[u8]) -> Result<u8, DeserializeError> {
        match buffer.split_first() {
            Some((byte, new_buffer)) => {
                *buffer = new_buffer;
                Ok(*byte)
            }
            None => Err(DeserializeError::EndOfInput),
        }
    }

    pub(super) fn deserialize_u16(buffer: &mut &[u8]) -> Result<u16, DeserializeError> {
        const SIZE: usize = std::mem::size_of::<u16>();
        let length_le_bytes = buffer.get(0..SIZE).ok_or(DeserializeError::EndOfInput)?;
        let len = u16::from_le_bytes(
            length_le_bytes
                .try_into()
                .map_err(|_| DeserializeError::EndOfInput)?,
        );
        *buffer = buffer.get(SIZE..).ok_or(DeserializeError::EndOfInput)?;
        Ok(len)
    }

    pub(super) fn deserialize_u32(buffer: &mut &[u8]) -> Result<u32, DeserializeError> {
        const SIZE: usize = std::mem::size_of::<u32>();
        let length_le_bytes = buffer.get(0..SIZE).ok_or(DeserializeError::EndOfInput)?;
        let len = u32::from_le_bytes(
            length_le_bytes
                .try_into()
                .map_err(|_| DeserializeError::EndOfInput)?,
        );
        *buffer = buffer.get(SIZE..).ok_or(DeserializeError::EndOfInput)?;
        Ok(len)
    }

    fn deserialize_u64(buffer: &mut &[u8]) -> Result<u64, DeserializeError> {
        const SIZE: usize = std::mem::size_of::<u64>();
        let length_le_bytes = buffer.get(0..SIZE).ok_or(DeserializeError::EndOfInput)?;
        let len = u64::from_le_bytes(
            length_le_bytes
                .try_into()
                .map_err(|_| DeserializeError::EndOfInput)?,
        );
        *buffer = buffer.get(SIZE..).ok_or(DeserializeError::EndOfInput)?;
        Ok(len)
    }

    #[inline]
    pub(super) fn deserialize_len(buffer: &mut &[u8]) -> Result<usize, DeserializeError> {
        let len = deserialize_u64(buffer)?;
        len.try_into()
            .map_err(|_| DeserializeError::DoesNotFitInUsize(len))
    }

    /// Deserialize a null-terminated string stored in `buffer`.
    pub(super) fn deserialize_str(buffer: &mut &[u8]) -> Result<Box<str>, DeserializeError> {
        let mut result = String::new();
        let bytes = buffer.iter().copied();
        let mut char_buffer = [0u8; 4];
        let mut char_buffer_idx = 0;
        for byte in bytes {
            if byte == 0 {
                if char_buffer_idx != 0 {
                    return Err(DeserializeError::IncorrectChar(char_buffer));
                }
                break;
            } else {
                char_buffer[char_buffer_idx] = byte;
                if byte & 0b1000_0000 == 0 {
                    result.push(match std::char::from_u32(u32::from_ne_bytes(char_buffer)) {
                        Some(c) => c,
                        None => return Err(DeserializeError::IncorrectChar(char_buffer)),
                    });
                    char_buffer_idx = 0;
                    char_buffer = [0; 4];
                } else {
                    char_buffer_idx = (char_buffer_idx + 1) % 4;
                }
            }
        }
        *buffer = &buffer[result.len() + 1..];
        Ok(result.into())
    }

    pub(super) fn deserialize_positions(
        buffer: &mut &[u8],
    ) -> Result<Vec<(u64, u32)>, DeserializeError> {
        let len = deserialize_len(buffer)?;
        let mut result = Vec::with_capacity(len);
        for _ in 0..len {
            let pos = deserialize_u64(buffer)?;
            let nb = deserialize_u32(buffer)?;
            result.push((pos, nb))
        }
        Ok(result)
    }

    pub(super) fn deserialize_code(
        buffer: &mut &[u8],
    ) -> Result<Vec<Instruction<u8>>, DeserializeError> {
        let len = deserialize_len(buffer)?;
        let mut result = Vec::with_capacity(len);
        for _ in 0..len {
            let discriminant = deserialize_u8(buffer)?;
            let operand = buffer.first().copied();
            let instruction = Instruction::from_raw(discriminant, operand.unwrap_or_default())
                .map_err(|_| DeserializeError::UnexpectedByte(discriminant))?;
            if instruction.operand().is_some() {
                if let Some((_, new_buffer)) = buffer.split_first() {
                    *buffer = new_buffer
                } else {
                    return Err(DeserializeError::EndOfInput);
                }
            }
            result.push(instruction)
        }
        Ok(result)
    }

    pub(super) fn deserialize_constants(
        buffer: &mut &[u8],
    ) -> Result<Vec<Constant>, DeserializeError> {
        let len = deserialize_len(buffer)?;
        let mut result = Vec::with_capacity(len);
        for _ in 0..len {
            result.push(match deserialize_u8(buffer)? {
                0 => Constant::Nil,
                1 => Constant::Int(i64::from_le_bytes(deserialize_u64(buffer)?.to_le_bytes())),
                2 => {
                    let b = deserialize_u8(buffer)?;
                    Constant::Bool(match b {
                        0 => false,
                        1 => true,
                        _ => return Err(DeserializeError::UnexpectedByte(b)),
                    })
                }
                3 => Constant::Float(f64::from_le_bytes(deserialize_u64(buffer)?.to_le_bytes())),
                4 => Constant::String(deserialize_str(buffer)?),
                byte => return Err(DeserializeError::UnexpectedByte(byte)),
            })
        }
        Ok(result)
    }

    pub(super) fn deserialize_globals(
        buffer: &mut &[u8],
    ) -> Result<Vec<Box<str>>, DeserializeError> {
        let len = deserialize_len(buffer)?;
        let mut result = Vec::with_capacity(len);
        for _ in 0..len {
            result.push(deserialize_str(buffer)?)
        }
        Ok(result)
    }

    pub(super) fn deserialize_captures(
        buffer: &mut &[u8],
    ) -> Result<Vec<LocalOrCaptured>, DeserializeError> {
        let len = deserialize_len(buffer)?;
        let mut result = Vec::with_capacity(len);
        for _ in 0..len {
            let local_or_captured = deserialize_u8(buffer)?;
            let idx = deserialize_u32(buffer)?;
            result.push(match local_or_captured {
                0 => LocalOrCaptured::Local(idx),
                1 => LocalOrCaptured::Captured(idx),
                _ => return Err(DeserializeError::UnexpectedByte(local_or_captured)),
            })
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Chunk, Parser, Source};

    #[test]
    fn serialize_and_back() {
        const SOURCE: &str = r#"
if ("hello" + "world") == "hello world" then
    return f(2, true)
else
    return 5 - (f - g)(6) * 8
end"#;
        let parser = Parser::new(Source::TopLevel(SOURCE));
        let (chunk, _) = parser.parse_top_level().unwrap();
        let mut buffer = Vec::new();
        chunk.serialize(&mut buffer);
        let new_chunk = Chunk::deserialize(buffer.as_slice()).unwrap();
        assert_eq!(chunk, new_chunk);
    }

    #[test]
    fn serialize_with_nested_functions() {
        const SOURCE: &str = r#"
fn say_hello(name)
    println("hello ", name)
    return 0
end
name = "Alice"
say_hello(name)
name = "Bob"
say_hello(name)
say_hello("Celine")
"#;
        let parser = Parser::new(Source::TopLevel(SOURCE));
        let (chunk, _) = parser.parse_top_level().unwrap();
        let mut buffer = Vec::new();
        chunk.serialize(&mut buffer);
        println!(
            "SOURCE.len() = {}, buffer.len() = {}",
            SOURCE.len(),
            buffer.len()
        );
        let new_chunk = Chunk::deserialize(buffer.as_slice()).unwrap();
        assert_eq!(chunk, new_chunk);
    }
}
