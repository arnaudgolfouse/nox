use super::*;
use std::{cell::UnsafeCell, convert::TryFrom, marker::PhantomData, ops::Deref};

/// Value given to a Rust program.
///
/// This is a representation of a [Value](./enum.Value.html) that can be safely
/// manipulated from a Rust program : It is thread safe (**note** : not yet !)
/// and will not be garbage collected a long as it is alive.
///
/// It's lifetime is tied to the VM from which it was issued.
///
/// a `RValue<'static>` can be created from any non-collectable `Value` via
/// `try_from`
#[repr(transparent)]
pub struct RValue<'a>(pub(crate) UnsafeCell<Value>, pub(crate) PhantomData<&'a ()>);

impl fmt::Debug for RValue<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Debug::fmt(&self.0, formatter)
    }
}

impl fmt::Display for RValue<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self.deref(), formatter)
    }
}

impl PartialEq<RValue<'_>> for RValue<'_> {
    fn eq(&self, other: &RValue) -> bool {
        self.deref() == other.deref()
    }
}

impl PartialEq<Value> for RValue<'_> {
    fn eq(&self, other: &Value) -> bool {
        self.deref() == other
    }
}

impl<'a> Drop for RValue<'a> {
    fn drop(&mut self) {
        unsafe { &mut *self.0.get() }.unroot()
    }
}

impl Deref for RValue<'_> {
    type Target = Value;
    fn deref(&self) -> &<Self as Deref>::Target {
        unsafe { &*self.0.get() }
    }
}

impl TryFrom<Value> for RValue<'static> {
    type Error = ();
    fn try_from(value: Value) -> Result<Self, <Self as TryFrom<Value>>::Error> {
        match value {
            Value::Nil | Value::Bool(_) | Value::Int(_) | Value::Float(_) | Value::String(_) => {
                Ok(RValue(UnsafeCell::new(value), PhantomData))
            }
            _ => Err(()),
        }
    }
}

impl<'a> RValue<'a> {
    /// Access the inner `Value`
    ///
    /// # Safety
    ///
    /// `self` still has the RValue root : it must be ensured that the value is
    /// appropriately unrooted
    pub(crate) unsafe fn into_raw(self) -> Value {
        std::mem::transmute(self) // oof !!!
    }
}
