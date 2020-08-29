mod operations;
mod rust_value;

use super::{
    ffi::RustFunction,
    gc::{Collectable, CollectableObject},
};
use crate::parser::{Chunk, Constant};
pub use operations::OperationError;
pub use rust_value::RValue;
use std::{
    collections::HashMap,
    fmt,
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::Arc,
};

/// A value that a variable can take in nox.
///
/// This value will be unrooted as it is dropped ; as such, all creation of a
/// `Value` **must** root it if it is collectable.
///
/// This means a `Value` will *always* have at least one root.
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
    String(Box<str>),
    /// Collectable value
    Collectable(NonNull<Collectable>),
    /// External Rust function
    RustFunction(RustFunction),
}

impl Drop for Value {
    fn drop(&mut self) {
        if let Self::Collectable(obj) = self {
            unsafe { obj.as_mut().unroot() }
        }
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Self::Nil => Self::Nil,
            Self::Bool(b) => Self::Bool(*b),
            Self::Int(i) => Self::Int(*i),
            Self::Float(f) => Self::Float(*f),
            Self::String(s) => Self::String(s.clone()),
            Self::Collectable(ptr) => {
                let mut new = Self::Collectable(*ptr);
                new.root();
                new
            }
            Self::RustFunction(func) => Self::RustFunction(func.clone()),
        }
    }
}

/// This is the version of `Value` that won't be unrooted on drop.
///
/// As such, its use is reserved for the internal of GC objects.
///
/// A `NoDropValue` *can* have 0 roots, but then it **must** be referenced by a
/// rooted object, or be ready to be collected.
#[derive(Hash, PartialEq, Eq)]
pub struct NoDropValue(pub ManuallyDrop<Value>);

impl Clone for NoDropValue {
    fn clone(&self) -> Self {
        NoDropValue(ManuallyDrop::new(match self.0.deref() {
            Value::Nil => Value::Nil,
            Value::Bool(b) => Value::Bool(*b),
            Value::Int(i) => Value::Int(*i),
            Value::Float(f) => Value::Float(*f),
            Value::String(s) => Value::String(s.clone()),
            Value::Collectable(ptr) => Value::Collectable(*ptr),
            Value::RustFunction(func) => Value::RustFunction(func.clone()),
        }))
    }
}

impl Deref for NoDropValue {
    type Target = Value;
    fn deref(&self) -> &<Self as std::ops::Deref>::Target {
        self.0.deref()
    }
}

impl DerefMut for NoDropValue {
    fn deref_mut(&mut self) -> &mut <Self as std::ops::Deref>::Target {
        self.0.deref_mut()
    }
}

impl fmt::Debug for NoDropValue {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.deref(), formatter)
    }
}

impl NoDropValue {
    pub const fn new(value: Value) -> Self {
        Self(ManuallyDrop::new(value))
    }

    pub const fn into_inner(self) -> Value {
        ManuallyDrop::into_inner(self.0)
    }

    pub fn as_ref(&self) -> &Value {
        self.deref()
    }
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
            Self::String(s) => {
                if formatter.alternate() {
                    fmt::Debug::fmt(s, formatter)
                } else {
                    fmt::Display::fmt(s, formatter)
                }
            }
            Self::Collectable(col) => fmt::Display::fmt(unsafe { col.as_ref() }, formatter),
            Self::RustFunction(_) => formatter.write_str("<function>"),
        }
    }
}

impl Value {
    /// Clones the value, but does not add a root.
    ///
    /// # Safety
    ///
    /// If the value is collectable, this function yields a new pointer to the
    /// same value. It must then be ensured that this pointer remains valid.
    /*pub(super) unsafe fn duplicate(&self) -> Self {
        match self {
            Self::Nil => Self::Nil,
            Self::Bool(b) => Self::Bool(*b),
            Self::Int(i) => Self::Int(*i),
            Self::Float(f) => Self::Float(*f),
            Self::String(s) => Self::String(s.clone()),
            Self::Collectable(ptr) => Self::Collectable(*ptr),
            Self::RustFunction(func) => Self::RustFunction(func.clone()),
        }
    }*/

    /// Add a root to this value if it is collectable.
    #[inline]
    pub(super) fn root(&mut self) {
        if let Self::Collectable(obj) = self {
            unsafe { obj.as_mut() }.root()
        }
    }

    /// Remove a root to this value if it is collectable.
    ///
    /// # Safety
    ///
    /// If the root count reaches `0` via this function, the value **must** no
    /// be ready to be collected (aka there is a rooted object referencing this).
    ///
    /// # Panics
    ///
    /// This function will panic if the number of roots is already `0`.
    #[inline]
    pub(super) unsafe fn unroot(&mut self) {
        if let Self::Collectable(obj) = self {
            obj.as_mut().unroot()
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
    pub(super) fn captured_value(self) -> Value {
        match self {
            Self::Collectable(ptr) => {
                let captured = unsafe { &ptr.as_ref().object };
                match captured {
                    CollectableObject::Captured(value) => value.deref().clone(),
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
        if let Some(value) = self.as_captured() {
            *self = value.clone();
        }
    }

    pub(super) fn as_table(&self) -> Option<&HashMap<NoDropValue, NoDropValue>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &ptr.as_ref().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn as_table_mut(&mut self) -> Option<&mut HashMap<NoDropValue, NoDropValue>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn as_function_mut(&mut self) -> Option<(&mut Arc<Chunk>, &mut Vec<NoDropValue>)> {
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

    /// Transform `self` into its no-drop version.
    pub(super) const fn into_nodrop(self) -> NoDropValue {
        NoDropValue::new(self)
    }

    pub(super) const fn from_nodrop(value: NoDropValue) -> Self {
        value.into_inner()
    }
}
