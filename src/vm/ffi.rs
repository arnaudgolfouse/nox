use super::Value;
use std::{cell::RefCell, fmt::Debug, rc::Rc};

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct RustFunction(pub Rc<RefCell<dyn FnMut(&mut [Value]) -> Result<Value, String>>>);

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
        Self::RustFunction(RustFunction(Rc::new(RefCell::new(value))))
    }
}

#[derive(Debug)]
pub struct Library {
    pub(crate) name: String,
    pub(crate) variables: Vec<(String, Value)>,
}

impl Library {
    pub fn new(name: String) -> Self {
        Self {
            name,
            variables: Vec::new(),
        }
    }

    pub fn add_int<S: ToString>(&mut self, name: S, i: i64) {
        self.variables.push((name.to_string(), Value::Int(i)))
    }

    pub fn add_float<S: ToString>(&mut self, name: S, f: f64) {
        self.variables.push((name.to_string(), Value::Float(f)))
    }

    pub fn add_function<S: ToString, F>(&mut self, function_name: S, function: F)
    where
        for<'a> F: FnMut(&mut [Value]) -> Result<Value, String> + 'static,
    {
        self.variables
            .push((function_name.to_string(), Value::from(function)))
    }
}
