use crate::runtime::Value;

/// Takes two `Int` arguments `a` and `b`, and creates an iterator from `a`
/// (included) to `b` (excluded).
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

/// Takes a single `String` argument, and creates an iterator over its letters.
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
            Some(c) => Value::String(Box::from(c.encode_utf8(&mut [0; 4]) as &str)),
        })
    };
    Ok(Value::from(letters))
}

/// Print the given arguments
pub fn print(args: &mut [Value]) -> Result<Value, String> {
    for arg in args {
        print!("{}", arg)
    }
    Ok(Value::Nil)
}

/// Print the given arguments and a newline.
pub fn println(args: &mut [Value]) -> Result<Value, String> {
    for arg in args {
        print!("{}", arg)
    }
    println!();
    Ok(Value::Nil)
}

/// Takes a single argument, and tries to convert it to a `String`.
pub fn to_string(args: &mut [Value]) -> Result<Value, String> {
    if args.len() != 1 {
        return Err(format!(
            "<to_string> : incorrect number of arguments : expected 1, got {}",
            args.len()
        ));
    }
    let string = match unsafe { args.get_unchecked(0) }.captured_value_ref() {
        Value::String(s) => return Ok(Value::String(s.clone())),
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
    Ok(Value::String(string.into_boxed_str()))
}

/// Takes a single argument, and tries to convert it to a `Int`.
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
