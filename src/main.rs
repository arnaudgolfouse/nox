use nox2::vm::{Value, VM};

fn main() {
    let mut vm = VM::new();
    vm.parse_top_level(
        "
    fn f()
        x = 5
        fn g(a)
            x += a
            return x
        end
        return g
    end

    f = f()
    f(1)

    x = f(-60.5)

    return x
    ",
    )
    .unwrap();

    match vm.run() {
        Ok(value) => assert_eq!(value, Value::Float(-54.5)),
        Err(err) => panic!("{}", err),
    }
    println!("[OK]")
}
