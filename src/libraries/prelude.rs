use crate::vm::Value;

pub fn range(args: &mut [Value]) -> Result<Value, String> {
    if args.len() != 2 {
        return Err(format!(
            "<range> : incorrect number of arguments : expected 2, got {}",
            args.len()
        ));
    }
    let from = match unsafe { args.get_unchecked(0) }.captured_value_ref() {
        Value::Int(n) => *n,
        value => return Err(format!("<range> : invalid value : {}", value)),
    };
    let to = match unsafe { args.get_unchecked(1) }.captured_value_ref() {
        Value::Int(n) => *n,
        value => return Err(format!("<range> : invalid value : {}", value)),
    };
    if to < from {
        return Ok(Value::from(|_: &mut [Value]| Ok(Value::Nil)));
    }
    let mut x = from;
    let iterator = move |_: &mut [Value]| {
        if x == to {
            Ok(Value::Nil)
        } else {
            x += 1;
            Ok(Value::Int(x - 1))
        }
    };
    Ok(Value::from(iterator))
}

pub fn letters(args: &mut [Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err(format!(
            "<letters> : incorrect number of arguments : expected 1, got {}",
            args.len()
        ));
    }
    let string: Vec<char> = match unsafe { args.get_unchecked(0) }.captured_value_ref() {
        Value::String(s) => s,
        value => return Err(format!("<letters> : invalid value : {}", value)),
    }
    .chars()
    .collect();
    let mut string = string.into_iter();
    let letters = move |_: &mut [Value]| {
        Ok(match string.next() {
            None => Value::Nil,
            Some(c) => {
                let mut res = String::with_capacity(1);
                res.push(c);
                Value::String(res)
            }
        })
    };
    Ok(Value::from(letters))
}

pub fn print(args: &mut [Value]) -> Result<Value, String> {
    for arg in args {
        print!("{}", arg)
    }
    Ok(Value::Nil)
}

pub fn println(args: &mut [Value]) -> Result<Value, String> {
    for arg in args {
        print!("{}", arg)
    }
    println!();
    Ok(Value::Nil)
}

pub fn to_string(args: &mut [Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err(format!(
            "<to_string> : incorrect number of arguments : expected 1, got {}",
            args.len()
        ));
    }
    let string = match unsafe { args.get_unchecked(0) }.captured_value_ref() {
        Value::String(s) => s.clone(),
        Value::Int(i) => i.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        v => {
            return Err(format!(
                "<to_string> : impossible to convert '{}' to str",
                v
            ))
        }
    };
    Ok(Value::String(string))
}

pub fn to_int(args: &mut [Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err(format!(
            "<to_int> : incorrect number of arguments : expected 1, received {}",
            args.len()
        ));
    }
    let int = match unsafe { args.get_unchecked(0) }.captured_value_ref() {
        Value::String(s) => match i64::from_str_radix(&s, 10) {
            Ok(i) => i,
            Err(err) => return Err(err.to_string()),
        },
        Value::Int(i) => *i,
        Value::Float(f) => f.floor() as i64,
        Value::Bool(b) => *b as i64,
        v => return Err(format!("<to_int> : impossible to convert '{}' to int", v)),
    };
    Ok(Value::Int(int))
}