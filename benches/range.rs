use criterion::{criterion_group, criterion_main, Criterion};

use nox2::{
    libraries,
    vm::{Value, VM},
};

fn range(criterion: &mut Criterion) {
    criterion.bench_function("range", |bencher| {
        bencher.iter(|| {
            let mut vm = VM::new();
            vm.parse_top_level(
                r#"
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
"#,
            )
            .unwrap();
            assert_eq!(vm.run().unwrap(), Value::Int(20000));
        });
    });

    criterion.bench_function("range_compiled", |bencher| {
        let mut vm = VM::new();
        vm.parse_top_level(
            r#"
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
    "#,
        )
        .unwrap();
        bencher.iter(|| {
            vm.partial_reset();
            assert_eq!(vm.run().unwrap(), Value::Int(20000));
        });
    });

    criterion.bench_function("range_native", |bencher| {
        let mut vm = VM::new();
        vm.import_all(libraries::prelude()).unwrap();
        vm.parse_top_level(
            r#"
x = 0
for i in range(0, 20000)
    x += 1
end

return x
    "#,
        )
        .unwrap();
        bencher.iter(|| {
            vm.partial_reset();
            assert_eq!(vm.run().unwrap(), Value::Int(20000));
        });
    });

    criterion.bench_function("range_pure_native", |bencher| {
        #[inline(never)]
        fn add_one(x: &mut i32) {
            *x += 1;
        };
        bencher.iter(|| {
            let mut x = 0;
            for _ in 0..20000 {
                add_one(&mut x)
            }
            assert_eq!(x, 20000);
        });
    });
}

criterion_group!(benches, range);
criterion_main!(benches);
