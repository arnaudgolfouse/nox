mod operations;
mod rust_value;

use super::{
    ffi::RustFunction,
    gc::{Collectable, CollectableObject},
};
use crate::parser::{Chunk, Constant};
pub use operations::OperationError;
pub use rust_value::RValue;
use std::{collections::HashMap, fmt, ptr::NonNull, sync::Arc};

/// A value that a variable can take in nox.
pub enum Value {
    /// `nil` value
    Nil,
    /// Boolean
    Bool(bool),
    /// Integer
    Int(i64),
    /// Floating-point number
    Float(f64),
    /// Heap-allocated string
    ///
    /// TODO : make this a collectable value ?
    String(String),
    /// Collectable value
    Collectable(NonNull<Collectable>),
    /// External Rust function
    RustFunction(RustFunction),
}

impl fmt::Debug for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Nil => formatter.write_str("Nil"),
            Self::Bool(b) => write!(formatter, "Bool({})", b),
            Self::Int(i) => write!(formatter, "Int({})", i),
            Self::Float(f) => write!(formatter, "Float({})", f),
            Self::String(s) => write!(formatter, "String({:?})", s),
            Self::Collectable(ptr) => {
                if formatter.alternate() {
                    write!(formatter, "Collectable({:#?})", unsafe { ptr.as_ref() })
                } else {
                    write!(formatter, "Collectable({:?})", ptr)
                }
            }
            Self::RustFunction(func) => write!(formatter, "RustFunction({:?})", func),
        }
    }
}

impl From<Constant> for Value {
    fn from(constant: Constant) -> Self {
        match constant {
            Constant::Nil => Self::Nil,
            Constant::Bool(b) => Self::Bool(b),
            Constant::Int(i) => Self::Int(i),
            Constant::Float(f) => Self::Float(f),
            Constant::String(s) => Self::String(s),
        }
    }
}

impl Eq for Value {}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Nil => formatter.write_str("nil"),
            Self::Bool(b) => fmt::Display::fmt(b, formatter),
            Self::Int(i) => fmt::Display::fmt(i, formatter),
            Self::Float(f) => fmt::Display::fmt(f, formatter),
            Self::String(s) => fmt::Display::fmt(s, formatter),
            Self::Collectable(col) => fmt::Display::fmt(unsafe { col.as_ref() }, formatter),
            Self::RustFunction(_) => formatter.write_str("<function>"),
        }
    }
}

impl Value {
    /// Clones the value.
    ///
    /// `Value` does not implement `Clone`, as cloning semantics are tied to
    /// the [garbage collector](../gc/struct.GC.html). This method is provided
    /// to get a raw copy of a value.
    ///
    /// # Safety
    ///
    /// If the value is collectable, this function yields a new pointer to the
    /// same value. It must then be ensured that this pointer remains valid.
    pub(super) unsafe fn duplicate(&self) -> Self {
        match self {
            Self::Nil => Self::Nil,
            Self::Bool(b) => Self::Bool(*b),
            Self::Int(i) => Self::Int(*i),
            Self::Float(f) => Self::Float(*f),
            Self::String(s) => Self::String(s.clone()),
            Self::Collectable(ptr) => Self::Collectable(*ptr),
            Self::RustFunction(func) => Self::RustFunction(func.clone()),
        }
    }

    /// Clones a vector of values.
    ///
    /// # Safety
    ///
    /// If values in the vector are collectable, this function yields new
    /// pointers to the same values. It must then be ensured that these pointers
    /// remains valid.
    pub unsafe fn duplicate_vec(values: &[Self]) -> Vec<Self> {
        let mut new_vec = Vec::with_capacity(values.len());
        for value in values {
            new_vec.push(value.duplicate())
        }
        new_vec
    }

    /// Add a root to this value if it is collectable.
    #[inline]
    pub(super) fn root(&mut self) {
        if let Self::Collectable(obj) = self {
            unsafe { obj.as_mut() }.root()
        }
    }

    /// Remove a root to this value if it is collectable.
    ///
    /// # Panics
    ///
    /// This function will panic if the number of roots is already `0`.
    #[inline]
    pub(super) fn unroot(&mut self) {
        if let Self::Collectable(obj) = self {
            unsafe { obj.as_mut() }.unroot()
        }
    }

    #[inline]
    pub(super) fn as_collectable(&self) -> Option<&Collectable> {
        match self {
            Self::Collectable(ptr) => Some(unsafe { ptr.as_ref() }),
            _ => None,
        }
    }

    /// Return `Some` if the value is a captured value.
    pub(super) fn as_captured(&self) -> Option<&Value> {
        match self {
            Self::Collectable(ptr) => match &unsafe { &ptr.as_ref() }.object {
                CollectableObject::Captured(value) => Some(value),
                _ => None,
            },
            _ => None,
        }
    }

    /// Return `Some` if the value is a captured value.
    pub(super) fn as_captured_mut(&mut self) -> Option<&mut Value> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Captured(value) => Some(value),
                _ => None,
            },
            _ => None,
        }
    }

    /// Return `self` if it is not captured, or the inner value of `self`
    fn captured_value(self) -> Value {
        match self {
            Self::Collectable(ptr) => {
                let captured = unsafe { &ptr.as_ref().object };
                match captured {
                    CollectableObject::Captured(value) => unsafe { value.duplicate() },
                    _ => self,
                }
            }
            _ => self,
        }
    }

    /// Return `self` if it is not captured, or the inner value of `self`
    pub fn captured_value_ref(&self) -> &Value {
        match self {
            Self::Collectable(ptr) => {
                let captured = unsafe { &ptr.as_ref().object };
                match captured {
                    CollectableObject::Captured(value) => value,
                    _ => self,
                }
            }
            _ => self,
        }
    }

    /// If `self` is a captured variable, change `self` into its captured value
    /// and unroot the capture, root the internal value.
    ///
    /// If `self` is not collectable, this will clone the value. Else it will
    /// just clone the pointer.
    pub(super) fn decapture(&mut self) {
        let mut value = match self.as_captured() {
            Some(value) => unsafe { value.duplicate() },
            None => return,
        };
        value.root();
        self.unroot();
        *self = value;
    }

    pub(super) fn as_table(&self) -> Option<&HashMap<Value, Value>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &ptr.as_ref().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn as_table_mut(&mut self) -> Option<&mut HashMap<Value, Value>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn as_function_mut(&mut self) -> Option<(&mut Arc<Chunk>, &mut Vec<Value>)> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Function {
                    chunk,
                    captured_variables,
                } => Some((chunk, captured_variables)),
                _ => None,
            },
            _ => None,
        }
    }
}
