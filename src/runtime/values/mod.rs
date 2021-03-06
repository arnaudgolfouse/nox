mod operations;
mod rust_value;

use super::{
    ffi::RustFunction,
    gc::{Collectable, CollectableObject},
};
use crate::parser::{Chunk, Constant};
use std::{
    collections::HashMap,
    fmt,
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::Arc,
};

pub(super) use self::operations::OperationError;
pub(super) use self::rust_value::RValue;

/// A value that a variable can take in nox.
///
/// This value will be unrooted as it is dropped ; as such, all creation of a
/// `Value` **must** root it if it is [collectable](Value::Collectable).
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
                let mut new_ptr = *ptr;
                unsafe { new_ptr.as_mut() }.root();
                Self::Collectable(new_ptr)
            }
            Self::RustFunction(func) => Self::RustFunction(func.clone()),
        }
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
    // ===============
    // GC manipulation
    // ===============

    /// Remove a root to this value if it is collectable.
    ///
    /// # Safety
    ///
    /// If the root count reaches `0` via this function, the value **must** not
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

    /// Return [`Some`] with the inner value if `self` is a captured variable.
    pub(super) fn as_captured(&self) -> Option<&Self> {
        match self {
            Self::Collectable(ptr) => match &unsafe { &ptr.as_ref() }.object {
                CollectableObject::Captured(value) => Some(value),
                _ => None,
            },
            _ => None,
        }
    }

    /// Return [`Some`] with the inner value if `self` is a captured variable.
    pub(super) fn as_captured_mut(&mut self) -> Option<&mut Self> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Captured(value) => Some(value),
                _ => None,
            },
            _ => None,
        }
    }

    /// Return `self` if it is not captured, or the inner value of `self`
    pub(super) fn captured_value(self) -> Self {
        match self {
            Self::Collectable(ptr) => {
                let captured = unsafe { &ptr.as_ref().object };
                match captured {
                    CollectableObject::Captured(value) => (value as &Value).clone(),
                    _ => self,
                }
            }
            _ => self,
        }
    }

    /// Return `self` if it is not captured, or the inner value of `self`
    pub fn captured_value_ref(&self) -> &Self {
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

    /// If `self` is a captured variable, change `self` into its captured value.
    pub(super) fn decapture(&mut self) {
        if let Some(value) = self.as_captured() {
            // note that the root count takes care of itself : the cloning add a
            // root to the internal value, and the original is then dropped and
            // loses a root.
            *self = value.clone();
        }
    }

    // ================
    // Safe conversions
    // ================

    /// Try to cast `self` as a [`table`](CollectableObject::Table).
    ///
    /// Returns [`None`] if the cast is not possible.
    pub(super) fn as_table(&self) -> Option<&HashMap<NoDropValue, NoDropValue>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &ptr.as_ref().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }

    /// Try to cast `self` as a mutable [`table`](CollectableObject::Table).
    ///
    /// Returns [`None`] if the cast is not possible.
    pub(super) fn as_table_mut(&mut self) -> Option<&mut HashMap<NoDropValue, NoDropValue>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }

    /// Try to cast `self` as a mutable [`Function`](CollectableObject::Function).
    ///
    /// Returns [`None`] if the cast is not possible.
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

    /// Interpret `self` as a [`NoDropValue`] reference.
    ///
    /// This is safe, as the `NoDropValue`'s lifetime will be tied to `self`,
    /// and the method for cloning a `NoDropValue` is unsafe.
    #[inline]
    pub(super) fn as_nodrop_ref(&self) -> &NoDropValue {
        unsafe { &*(self as *const Self as *const NoDropValue) }
    }

    // ==================
    // Unsafe conversions
    // ==================
    //
    // Not useful yet, but we may use this with typed intructions at some point.

    /*

    /// Assume that `self` is a **non-captured** [`Int`].
    ///
    /// # Safety
    ///
    /// If `self` is not literally an [`Int`], behaviour is undefined.
    ///
    /// [`Int`]: (Value::Int)
    unsafe fn assume_int(self) -> i64 {
        if let Value::Int(i) = self {
            i
        } else {
            std::hint::unreachable_unchecked()
        }
    }

    /// Assume that `self` is a **non-captured** [`Float`].
    ///
    /// # Safety
    ///
    /// If `self` is not literally an [`Float`], behaviour is undefined.
    ///
    /// [`Float`]: (Value::Float)
    unsafe fn assume_float(self) -> f64 {
        if let Value::Float(f) = self {
            f
        } else {
            std::hint::unreachable_unchecked()
        }
    }

    */
}

//=================================
//========== NoDropValue ==========
//=================================

/// This is the version of [`Value`] that won't be unrooted on drop.
///
/// As such, its use is reserved for the internal of GC objects.
///
/// A `NoDropValue` *can* have 0 roots, but then it **must** be referenced by a
/// rooted object, or be ready to be collected.
#[derive(Hash, PartialEq, Eq)]
pub struct NoDropValue(ManuallyDrop<Value>);

impl Deref for NoDropValue {
    type Target = Value;
    fn deref(&self) -> &<Self as std::ops::Deref>::Target {
        &self.0
    }
}

impl DerefMut for NoDropValue {
    fn deref_mut(&mut self) -> &mut <Self as std::ops::Deref>::Target {
        &mut self.0
    }
}

impl fmt::Debug for NoDropValue {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self as &Value, formatter)
    }
}

impl NoDropValue {
    /// Creates a new `NoDropValue` wrapper from a [`Value`].
    ///
    /// # Safety
    ///
    /// This will unroot `value` once : as such, this should only be used in the
    /// internals of [`GC`](super::gc::GC), when we borrow `GC` mutably, to
    /// avoid collections.
    pub(super) unsafe fn new(mut value: Value) -> Self {
        value.unroot();
        Self(ManuallyDrop::new(value))
    }

    /// Acts like an unsafe `clone` method for `NoDropValue`.
    ///
    /// # Safety
    ///
    /// This will duplicate `self`, which is in itself a kind of lifetime
    /// extension (if `self`'s lifetime was constrained in any way).
    ///
    /// As such, it is reserved for the internals of [`GC`](super::gc::GC),
    /// when we borrow `GC` mutably, to avoid collections.
    ///
    /// Users of this method **must** ensure that the new value will not be
    /// collected and then used.
    pub(super) unsafe fn duplicate(&self) -> Self {
        Self(ManuallyDrop::new(match self.0.deref() {
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
