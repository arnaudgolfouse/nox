use super::*;
use crate::libraries;

#[test]
fn operations() {
    let mut vm = VM::new();
    vm.parse_top_level(
        "
x = 5                  # x = 5
y = x + 1              # y = 6
z = y * x + 8 - 2 % 2  # z = 38
return (z + 5) * -0.5  # return -21.5
        ",
    )
    .unwrap();

    assert_eq!(vm.run().unwrap(), Value::Float(-21.5));
    vm.reset();

    vm.parse_top_level(
        "
x = 2                  # x = 2
x = x ^ x              # x = 4.0
x += 5 ^ 3 % 20        # x = 9.0
return (x - 5) * -0.5  # return -2.0
        ",
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Float(-2.0));
    vm.reset();

    vm.parse_top_level(
        "
return 4 + 7 + 8 - 5 - 9 # 5
        ",
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(5));
    vm.reset();
}

#[test]
fn tables() {
    // manipulate fields
    let mut vm = VM::new();
    vm.parse_top_level(
        "
t = { x = 5, y = 6 }
t.y -= 9 - t.x
return t.x * t.y
        ",
    )
    .unwrap();

    assert_eq!(vm.run().unwrap(), Value::Int(10));
    vm.reset();

    // allocate / deallocate a lot + cycles
    vm.import_all(libraries::prelude()).unwrap();
    vm.parse_top_level(
        r#"
t = { x = 5, y = 6 }
t0 = t

# allocate lots
for _ in range(0, 10000)
    t0.t = { x = 1 }
    t0 = t0.t
end

t0 = t
res = 0
# deallocate lots
for _ in range(0, 10000)
    println(t0.t, "  ", t0.x, "  ", res)
    t1 = t0
    t0 = t0.t
    t1.t = nil
    res += t1.x
end

return res
        "#,
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(10004));
    vm.reset();
}

#[test]
fn control_flow() {
    let mut vm = VM::new();
    vm.parse_top_level(
        "
x = 5
y = 6
if x > y then
    if true then
        return x + y
    end
else
    if not not not false then # true
        y -= 2
    else
        y += 2
    end
end
return y",
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(4));

    vm.reset();
    vm.parse_top_level(
        "
y = 1
x = 64
while x > y
    x -= 5
end
return x",
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(-1));
    vm.reset();

    // testing extended instructions
    vm.parse_top_level(
        "
total = 0
y = 1
x = 64
while x > y
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
end
total += x
x = 64
while x > y
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    if x == 0 then
        break
    end
end
total += x
x = 64
while x > y
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
    if x == 0 then
        continue
    end
end
total += x
return total
            ",
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(0));
    vm.reset();

    vm.parse_top_level(
        "
x1 = 0
x2 = 1
i = 5
while true
    i -= 1
    x = x1 + x2
    x1 = x2
    x2 = x
    if i <= 0 then
        break
    end
end
return x2",
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(8));
    vm.reset();
}

#[test]
fn for_loop() {
    let mut vm = VM::new();
    vm.parse_top_level(
        "
    fn range(a, b)
        it = a
        fn iter()
            if it == b then
                return nil
            else
                it += 1
                return it - 1
            end
        end
        return iter
    end
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
    vm.reset();

    // a somewhat complex example
    vm.import_all(libraries::prelude()).unwrap();
    vm.parse_top_level(
        r#"
fn some_func(a, b)
    it = a
    fn other_func()
        if it == b then
            return nil
        else
            tot = 0
            for i in range(0, 1)      # stupid loop, only here for fun
                for i in range(1, it)
                    tot += i
                    if tot == 10 then
                        for i in range(0, 1) # same here ;)
                            tot = 0
                        end 
                        continue
                    end
                end
                it += 1
            end
            return tot
        end
    end
    return other_func
end

x = 0
for i in some_func(1, 7)
    while i != 0
        i -= 1
        x += 1
    end
end
return x
            "#,
    )
    .unwrap();
    assert_eq!(vm.run().unwrap(), Value::Int(15));
    vm.reset();
}

#[test]
fn errors() {
    let mut vm = VM::new();
    // ======== parsing errors ========
    vm.parse_top_level("0 = x").unwrap_err();
    vm.parse_top_level("fn f() break end").unwrap_err();
    vm.parse_top_level("x = 5 continue").unwrap_err();
    // ======== runtime errors ========
    // operation errors
    vm.parse_top_level("return 5 + \"hello\"").unwrap();
    vm.run().unwrap_err();
    vm.parse_top_level("return nil ^ 5.2").unwrap();
    vm.run().unwrap_err();
    vm.parse_top_level("return { x = 5 } - fn() return 1 end")
        .unwrap();
    vm.run().unwrap_err();
    vm.reset();
    // not a table
    vm.parse_top_level("x.a = 7").unwrap();
    vm.run().unwrap_err();
    vm.parse_top_level("x[789] = 9").unwrap();
    vm.run().unwrap_err();
    vm.reset();
    // not a function
    vm.parse_top_level("return 5(0, 1)").unwrap();
    vm.run().unwrap_err();
    vm.parse_top_level("x = nil return x()").unwrap();
    vm.run().unwrap_err();
    vm.reset();
}
