mod prelude;

use crate::vm::ffi::Library;

pub fn prelude() -> Library {
    let mut prelude = Library::new("std_prelude".to_owned());
    prelude.add_function("range", prelude::range);
    prelude.add_function("letters", prelude::letters);
    prelude.add_function("print", prelude::print);
    prelude.add_function("println", prelude::println);
    prelude.add_function("to_string", prelude::to_string);
    prelude.add_function("to_int", prelude::to_int);
    prelude
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::{Value, VM};

    #[test]
    fn test_case() {
        let mut vm = VM::new();
        vm.import_all(prelude()).unwrap();
        vm.parse_top_level(
            "
            x = 0
            for i in range(1, 4)
                while i != 0
                    i -= 1
                    x += 1
                end
            end
            return x
            ",
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(6));

        let mut vm = VM::new();
        vm.import_all(prelude()).unwrap();
        vm.parse_top_level(
            r#"
            x = ""
            for c in letters("hello world !")
                if c == "o" or c == "e" then
                    x += c
                end
            end
            return x
            "#,
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::String("eoo".to_string()));

        let mut vm = VM::new();
        vm.import_all(prelude()).unwrap();
        vm.parse_top_level(
            r#"
            a = to_string(54)   # "54"
            b = to_string(8.61) # "8.61"
            c = to_string(true) # "true"

            return a + " " + b + " " + c
            "#,
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::String("54 8.61 true".to_string()));

        let mut vm = VM::new();
        vm.import_all(prelude()).unwrap();
        vm.parse_top_level(
            r#"
            a = to_int(5)    # 5
            b = to_int(8.61) # 8
            c = to_int(true) # 1
            d = to_int("-9") # -9

            return a + b + c + d
            "#,
        )
        .unwrap();
        assert_eq!(vm.run().unwrap(), Value::Int(5));
    }
}
