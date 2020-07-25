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
    pub(crate) name: String,
    pub(crate) variables: Vec<(String, Value)>,
}

impl Library {
    /// Creates a new empty library
    pub fn new(name: String) -> Self {
        Self {
            name,
            variables: Vec::new(),
        }
    }

    /// Add an integer constant to the library
    pub fn add_int<S: ToString>(&mut self, name: S, i: i64) {
        self.variables.push((name.to_string(), Value::Int(i)))
    }

    /// Add a float constant to the library
    pub fn add_float<S: ToString>(&mut self, name: S, f: f64) {
        self.variables.push((name.to_string(), Value::Float(f)))
    }

    /// Add a string constant to the library
    pub fn add_string<S: ToString>(&mut self, name: S, s: String) {
        self.variables.push((name.to_string(), Value::String(s)))
    }

    /// Add a Rust function to the library
    pub fn add_function<S: ToString, F>(&mut self, function_name: S, function: F)
    where
        for<'a> F: FnMut(&mut [Value]) -> Result<Value, String> + 'static,
    {
        self.variables
            .push((function_name.to_string(), Value::from(function)))
    }
}
