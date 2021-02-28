use nox::{
    libraries,
    runtime::{VmError, VirtualMachine},
};

const _PROGRAM1: &str = "
x = 4
";

const _PROGRAM2: &str = "
t = { x = 8 }
";

const _PROGRAM3: &str = "
for i in range(0, 4)
    x = 8
end
";

const _PROGRAM4: &str = "
fn(y)
    t = { f = fn(t, a) return t.x + a - y end, x = 8 }
    t1 = t
    for i in range(0, 2000)
        t1 = { f = t1.f, x = 7, y = t.x * 12 }
    end
    t = nil
    return t1.f(t1, 2)
end
(8)
";

fn main() -> Result<(), VmError> {
    let mut vm = VirtualMachine::new();
    vm.import_all(libraries::std())?;
    vm.parse_top_level(_PROGRAM4)?;
    vm.run()?;
    Ok(())
}
