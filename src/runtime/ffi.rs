//! Foreign Functions Interface

use super::Value;
use std::{
    fmt::Debug,
    sync::{Arc, Mutex},
};

/// Representation of a Rust function in nox.
///
/// The function receives a slice of values for its arguments, and returns a custom
/// [`String`] error, or a single [`Value`].
///
/// It is thread-safe.
#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct RustFunction(Arc<Mutex<dyn FnMut(&mut [Value]) -> Result<Value, String>>>);

impl RustFunction {
    /// Call the `RustFunction` with the given values.
    pub fn call(&self, args: &mut [Value]) -> Result<Value, String> {
        self.0.lock().unwrap()(args)
    }

    pub(crate) fn as_ptr(&self) -> *const Mutex<dyn FnMut(&mut [Value]) -> Result<Value, String>> {
        Arc::as_ptr(&self.0)
    }
}

impl PartialEq for RustFunction {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl Debug for RustFunction {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        formatter.write_str("RustFunction")
    }
}

impl<F> From<F> for Value
where
    F: 'static + FnMut(&mut [Value]) -> Result<Value, String>,
{
    fn from(value: F) -> Self {
        Self::RustFunction(RustFunction(Arc::new(Mutex::new(value))))
    }
}

/// Library regrouping external objects.
///
/// This can be loaded into the current top-level via the [`import`] and
/// [`import_all`] methods of the `VM`.
///
/// [`import`]: super::VM::import
/// [`import_all`]: super::VM::import_all
#[derive(Debug)]
pub struct Library {
    pub(super) name: Box<str>,
    pub(super) variables: Vec<(Box<str>, Value)>,
}

impl Library {
    /// Creates a new empty library
    pub fn new<Name: Into<Box<str>>>(name: Name) -> Self {
        Self {
            name: name.into(),
            variables: Vec::new(),
        }
    }

    /// Add an integer constant to the library
    pub fn add_int<Name: Into<Box<str>>>(&mut self, name: Name, i: i64) {
        self.variables.push((name.into(), Value::Int(i)))
    }

    /// Add a float constant to the library
    pub fn add_float<Name: Into<Box<str>>>(&mut self, name: Name, f: f64) {
        self.variables.push((name.into(), Value::Float(f)))
    }

    /// Add a string constant to the library
    pub fn add_string<Name: Into<Box<str>>, S: Into<Box<str>>>(&mut self, name: Name, s: S) {
        self.variables.push((name.into(), Value::String(s.into())))
    }

    /// Add a Rust function to the library
    pub fn add_function<Name: Into<Box<str>>, F>(&mut self, function_name: Name, function: F)
    where
        F: FnMut(&mut [Value]) -> Result<Value, String> + 'static,
    {
        self.variables
            .push((function_name.into(), Value::from(function)))
    }
}
