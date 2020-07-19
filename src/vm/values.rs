use super::gc::{Collectable, CollectableObject};
use crate::parser::Constant;
use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    ptr::NonNull,
};

#[derive(Clone, Debug)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Collectable(NonNull<Collectable>),
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
            Self::Collectable(_) => {
                if let Some(x1) = self.as_collectable() {
                    if let Some(x2) = self.as_collectable() {
                        x1 == x2
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }
}

impl Eq for Value {}

impl Hash for Value {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        match self {
            Self::Nil => 0.hash(hasher),
            Self::Bool(b) => b.hash(hasher),
            Self::Int(i) => i.hash(hasher),
            Self::Float(f) => (*f).to_bits().hash(hasher),
            Self::String(s) => s.hash(hasher),
            Self::Collectable(ptr) => ptr.hash(hasher),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Self::Nil => formatter.write_str("nil"),
            Self::Bool(b) => fmt::Display::fmt(b, formatter),
            Self::Int(i) => fmt::Display::fmt(i, formatter),
            Self::Float(f) => fmt::Display::fmt(f, formatter),
            Self::String(s) => fmt::Display::fmt(s, formatter),
            Self::Collectable(col) => fmt::Display::fmt(unsafe { col.as_ref() }, formatter),
        }
    }
}

impl Value {
    #[inline]
    pub fn root(&mut self) {
        if let Self::Collectable(obj) = self {
            unsafe { obj.as_mut() }.root()
        }
    }

    #[inline]
    pub fn unroot(&mut self) {
        if let Self::Collectable(obj) = self {
            unsafe { obj.as_mut() }.unroot()
        }
    }

    #[inline]
    pub fn as_collectable(&self) -> Option<&Collectable> {
        match self {
            Self::Collectable(ptr) => Some(unsafe { ptr.as_ref() }),
            _ => None,
        }
    }

    /// Return `Some` if the value is not collectable, or if it is a captured
    /// value.
    pub fn as_captured(&self) -> Option<&Value> {
        match self {
            Self::Collectable(ptr) => match &unsafe { &ptr.as_ref() }.object {
                CollectableObject::Captured(value) => Some(value),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn as_table_mut(&mut self) -> Option<&mut HashMap<Value, Value>> {
        match self {
            Self::Collectable(ptr) => match unsafe { &mut ptr.as_mut().object } {
                CollectableObject::Table(table) => Some(table),
                _ => None,
            },
            _ => None,
        }
    }
}
