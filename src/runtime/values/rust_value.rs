//! TODO This module will disappear in time.
//!
//! Indeed this approach is likely inherently unsafe : instead only
//! non-collectable values should be directly manipulable ; Others should only
//! be manipulated through the VM.
//!
//! Lua does this very well : this should be taken as a model.
//!
//! # Example
//!
//! The following code is definitively NOT safe :
//! ```no_run
//! use nox::runtime::VM;
//!
//! let mut vm = VM::new();
//! let mut other_vm = VM::new();
//! let table = {
//!     vm.parse_top_level("return { x = 0 }").unwrap();
//!     vm.run().unwrap()
//! };
//! other_vm.push(table);
//! ```

use super::Value;
use std::{fmt, marker::PhantomData, ops::Deref};

/// Value given to a Rust program.
///
/// This is a representation of a [Value](./enum.Value.html) that can be safely
/// manipulated from a Rust program : It will not be garbage collected a long as
/// it is alive.
///
/// It's lifetime is tied to the VM from which it was issued.
///
/// A `RValue<'static>` can be obtained if the value is not collectable.
#[repr(transparent)]
pub struct RValue<'a>(
    pub(crate) Value,
    pub(crate) PhantomData<&'a crate::runtime::VM>,
);

impl fmt::Debug for RValue<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(self as &Value, formatter)
    }
}

impl fmt::Display for RValue<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self as &Value, formatter)
    }
}

impl PartialEq<RValue<'_>> for RValue<'_> {
    fn eq(&self, other: &RValue) -> bool {
        self as &Value == other as &Value
    }
}

impl PartialEq<Value> for RValue<'_> {
    fn eq(&self, other: &Value) -> bool {
        self as &Value == other
    }
}

impl PartialEq<RValue<'_>> for Value {
    fn eq(&self, other: &RValue<'_>) -> bool {
        self == other as &Self
    }
}

impl Deref for RValue<'_> {
    type Target = Value;
    fn deref(&self) -> &<Self as Deref>::Target {
        &self.0
    }
}

impl<'a> RValue<'a> {
    /// Access the inner `Value`
    pub(crate) fn into_raw(self) -> Value {
        self.0
    }

    /// Remove the lifetime dependency if the contained value is not collectable.
    ///
    /// # Errors
    ///
    /// If the value is collectable, it is returned in the `Err` variant.
    pub fn into_static(self) -> Result<RValue<'static>, Self> {
        match self.0 {
            Value::Nil | Value::Bool(_) | Value::Int(_) | Value::Float(_) | Value::String(_) => {
                Ok(RValue(self.0, PhantomData))
            }
            _ => Err(self),
        }
    }
}
