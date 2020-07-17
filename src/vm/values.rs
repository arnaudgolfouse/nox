use super::gc::{Collectable, CollectableObject};
use std::{
    collections::HashMap,
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

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
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
            Self::Collectable(x1) => match other {
                Self::Collectable(x2) => x1 == x2,
                _ => false,
            },
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
