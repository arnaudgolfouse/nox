use nox2::{libraries, runtime::VM};

fn main() {
    let mut vm = VM::new();
    vm.import_all(libraries::prelude()).unwrap();

    vm.parse_top_level(
        "
fn range(a, b)
    x = a - 1
    fn f()
        x += 1
        if x < b then
            return x
        end
    end
    return f
end

x = 0
for i in range(0, 20000)
    x += 1
end

return x
    ",
    )
    .unwrap();

    match vm.run() {
        Ok(value) => println!("[OK] : {}", value),
        Err(err) => panic!("{}", err),
    }
}
