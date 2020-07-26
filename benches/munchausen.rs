use criterion::{criterion_group, criterion_main, Criterion};

use nox::{
    libraries,
    runtime::{Value, VM},
};

fn munchausen(c: &mut Criterion) {
    let mut vm = VM::new();
    vm.import_all(libraries::prelude()).unwrap();
    match vm.parse_top_level(
        r#"
fn isMunchausen(n)
    nStr = to_string(n)
    sum = 0
    for l in letters(nStr)
        i = to_int(l)
        sum += i ^ i
    end
    return sum == n
end

total = 0
for i in range(1, 50000)
    if isMunchausen(i) then
        total += i
    end
end
return total
"#,
    ) {
        Err(err) => panic!("{}", err),
        Ok(()) => {}
    }
    c.bench_function("munchausen", |b| {
        b.iter(|| {
            vm.partial_reset();
            match vm.run() {
                Err(err) => panic!("{}", err),
                Ok(ok) => assert_eq!(ok, Value::Int(3436)),
            }
        })
    });
}

criterion_group!(benches, munchausen);
criterion_main!(benches);
