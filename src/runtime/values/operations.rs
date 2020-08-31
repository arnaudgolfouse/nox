//! Module for the binary and unary operations on values.

use super::{
    super::{gc::CollectableObject, RuntimeError, VMErrorKind},
    Value,
};
use crate::lexer::Operation;
use std::{
    convert::TryFrom,
    fmt,
    hash::{Hash, Hasher},
};

#[derive(Debug)]
pub enum OperationError {
    Binary(Operation, Value, Value),
    Unary(Operation, Value),
}

impl fmt::Display for OperationError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Binary(opcode, v1, v2) => write!(
                formatter,
                "invalid binary operation '{}' between {:#} and {:#}",
                opcode, v1, v2
            ),
            Self::Unary(opcode, v) => write!(
                formatter,
                "invalid unary operation '{}' for {:#}",
                opcode, v
            ),
        }
    }
}

impl From<OperationError> for RuntimeError {
    fn from(err: OperationError) -> Self {
        Self::OperationError(err)
    }
}

impl From<OperationError> for VMErrorKind {
    fn from(err: OperationError) -> Self {
        RuntimeError::OperationError(err).into()
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        // 'de-capture' the variables
        if let Some(x1) = self.as_captured() {
            return if let Some(x2) = other.as_captured() {
                x1 == x2
            } else {
                x1 == other
            };
        }
        if let Some(x2) = other.as_captured() {
            return self == x2;
        }
        // do the actual comparison (impossible to have captured variables now !)
        match self {
            Self::Nil => matches!(other, Self::Nil),
            Self::Bool(x1) => match other {
                Self::Bool(x2) => x1 == x2,
                _ => false,
            },
            Self::Int(x1) => match other {
                Self::Int(x2) => x1 == x2,
                _ => false,
            },
            Self::Float(x1) => match other {
                Self::Float(x2) => x1 == x2,
                _ => false,
            },
            Self::String(x1) => match other {
                Self::String(x2) => x1 == x2,
                _ => false,
            },
            // only pointer equality now
            Self::Collectable(ptr1) => match other {
                Self::Collectable(ptr2) => ptr1 == ptr2,
                _ => false,
            },
            Self::RustFunction(_) => false,
        }
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        match self {
            Self::Nil => 0.hash(hasher),
            Self::Bool(b) => b.hash(hasher),
            Self::Int(i) => i.hash(hasher),
            Self::Float(f) => (*f).to_bits().hash(hasher),
            Self::String(s) => s.hash(hasher),
            Self::Collectable(ptr) => match &unsafe { ptr.as_ref() }.object {
                CollectableObject::Captured(value) => value.hash(hasher),
                _ => ptr.hash(hasher),
            },
            // two RustFunction's are never equal, so we don't really care about what is hashed
            Self::RustFunction(func) => func.0.as_ptr().hash(hasher),
        }
    }
}

impl Value {
    /// Add the two values together, returning a new value if it worked.
    ///
    /// The new value will not be garbage collected.
    ///
    /// # Errors
    ///
    /// If the two values can't be added, `OperationError(+, self, other)` is
    /// returned.
    pub(crate) fn add(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 + i2)),
                Value::Float(f) => Ok(Value::Float(i1 as f64 + f)),
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Float(f2) => Ok(Value::Float(f1 + f2)),
                Value::Int(i) => Ok(Value::Float(i as f64 + f1)),
                _ => Err((self, other)),
            },
            Value::String(ref s1) => match other {
                Value::String(ref s2) => {
                    Ok(Value::String(format!("{}{}", s1, s2).into_boxed_str()))
                }
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Plus, s, o))
    }

    pub(crate) fn subtract(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 - i2)),
                Value::Float(f) => Ok(Value::Float(i1 as f64 - f)),
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Float(f2) => Ok(Value::Float(f1 - f2)),
                Value::Int(i) => Ok(Value::Float(f1 - i as f64)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Minus, s, o))
    }

    pub(crate) fn multiply(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 * i2)),
                Value::Float(f) => Ok(Value::Float(i1 as f64 * f)),
                Value::String(ref s) => match usize::try_from(i1) {
                    Ok(i1) => Ok(Value::String(s.repeat(i1).into_boxed_str())),
                    Err(_) => Err((self, other)),
                },
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Float(f2) => Ok(Value::Float(f1 * f2)),
                Value::Int(i) => Ok(Value::Float(i as f64 * f1)),
                _ => Err((self, other)),
            },
            Value::String(ref s) => match other {
                Value::Int(i) => match usize::try_from(i) {
                    Ok(i) => Ok(Value::String(s.repeat(i).into_boxed_str())),
                    Err(_) => Err((self, other)),
                },
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Multiply, s, o))
    }

    pub(crate) fn divide(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 / i2)),
                Value::Float(f) => Ok(Value::Float(i1 as f64 / f)),
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Float(f2) => Ok(Value::Float(f1 / f2)),
                Value::Int(i) => Ok(Value::Float(f1 / i as f64)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Divide, s, o))
    }

    pub(crate) fn modulo(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 % i2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Modulo, s, o))
    }

    pub(crate) fn pow(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int((i1 as f64).powf(i2 as f64) as i64)),
                Value::Float(f) => Ok(Value::Float((i1 as f64).powf(f))),
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Int(i) => Ok(Value::Float(f1.powf(i as f64))),
                Value::Float(f2) => Ok(Value::Float(f1.powf(f2))),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Pow, s, o))
    }

    pub(crate) fn less(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Bool(i1 < i2)),
                Value::Float(f) => Ok(Value::Bool((i1 as f64) < f)),
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Float(f2) => Ok(Value::Bool(f1 < f2)),
                Value::Int(i) => Ok(Value::Bool(f1 < (i as f64))),
                _ => Err((self, other)),
            },
            Value::String(ref s1) => match other {
                Value::String(ref s2) => Ok(Value::Bool(s1 < s2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Less, s, o))
    }

    pub(crate) fn less_eq(self, other: Value) -> Result<Value, OperationError> {
        match self.more(other)? {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => unreachable!(),
        }
    }

    pub(crate) fn more(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Bool(i1 > i2)),
                Value::Float(f) => Ok(Value::Bool((i1 as f64) > f)),
                _ => Err((self, other)),
            },
            Value::Float(f1) => match other {
                Value::Float(f2) => Ok(Value::Bool(f1 > f2)),
                Value::Int(i) => Ok(Value::Bool(f1 > (i as f64))),
                _ => Err((self, other)),
            },
            Value::String(ref s1) => match other {
                Value::String(ref s2) => Ok(Value::Bool(s1 > s2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::More, s, o))
    }

    pub(crate) fn more_eq(self, other: Value) -> Result<Value, OperationError> {
        match self.less(other)? {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => unreachable!(),
        }
    }

    pub(crate) fn and(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Bool(b1) => match other {
                Value::Bool(b2) => Ok(Value::Bool(b1 && b2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::And, s, o))
    }

    pub(crate) fn or(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Bool(b1) => match other {
                Value::Bool(b2) => Ok(Value::Bool(b1 || b2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Or, s, o))
    }

    pub(crate) fn xor(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Bool(b1) => match other {
                Value::Bool(b2) => Ok(Value::Bool(b1 ^ b2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::Xor, s, o))
    }

    pub(crate) fn shift_left(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 << i2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::ShiftLeft, s, o))
    }

    pub(crate) fn shift_right(self, other: Value) -> Result<Value, OperationError> {
        match self {
            Value::Int(i1) => match other {
                Value::Int(i2) => Ok(Value::Int(i1 >> i2)),
                _ => Err((self, other)),
            },
            _ => Err((self, other)),
        }
        .map_err(|(s, o)| OperationError::Binary(Operation::ShiftRight, s, o))
    }

    pub(crate) fn negative(mut self) -> Result<Value, OperationError> {
        self = self.captured_value();
        match self {
            Value::Int(i) => Ok(Value::Int(-i)),
            Value::Float(f) => Ok(Value::Float(-f)),
            _ => Err(OperationError::Unary(Operation::Minus, self)),
        }
    }

    pub(crate) fn not(mut self) -> Result<Value, OperationError> {
        self = self.captured_value();
        match self {
            Value::Bool(b) => Ok(Value::Bool(!b)),
            _ => Err(OperationError::Unary(Operation::Not, self)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn hash_and_eq() {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        let v1 = Value::String("x".into());
        let v2 = Value::String("x".into());
        assert_eq!(v1, v2);
        assert_eq!(v1.hash(&mut hasher), v2.hash(&mut hasher));
        let v1 = Value::Int(8);
        let v2 = Value::Int(8);
        assert_eq!(v1, v2);
        assert_eq!(v1.hash(&mut hasher), v2.hash(&mut hasher));
        let v1 = Value::Float(1.25);
        let v2 = Value::Float(1.25);
        assert_eq!(v1, v2);
        assert_eq!(v1.hash(&mut hasher), v2.hash(&mut hasher));
    }
}
