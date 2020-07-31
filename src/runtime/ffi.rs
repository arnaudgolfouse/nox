//! Foreign Functions Interface

use super::Value;
use std::{cell::RefCell, fmt::Debug, sync::Arc};

/// Representation of a Rust function in nox.
///
/// The function receives a slice of values for its arguments.
///
/// it is able to return a custom `String` error, or a single `Value`.
#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct RustFunction(pub Arc<RefCell<dyn FnMut(&mut [Value]) -> Result<Value, String>>>);

impl PartialEq for RustFunction {
    fn eq(&self, _: &RustFunction) -> bool {
        false
    }
}

impl Debug for RustFunction {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        formatter.write_str("RustFunction")
    }
}

impl<F: 'static + FnMut(&mut [Value]) -> Result<Value, String>> From<F> for Value {
    fn from(value: F) -> Self {
        Self::RustFunction(RustFunction(Arc::new(RefCell::new(value))))
    }
}

/// Library regrouping external objects.
///
/// This can be loaded into the current top-level via the
/// [import](../struct.VM.html#method.import) and
/// [import_all](../struct.VM.html#method.import_all) functions of the `VM`.
#[derive(Debug)]
pub struct Library {
    pub(crate) name: Box<str>,
    pub(crate) variables: Vec<(Box<str>, Value)>,
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
        for<'a> F: FnMut(&mut [Value]) -> Result<Value, String> + 'static,
    {
        self.variables
            .push((function_name.into(), Value::from(function)))
    }
}
