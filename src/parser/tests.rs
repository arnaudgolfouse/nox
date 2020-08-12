use super::*;

use Instruction::*;

#[test]
fn errors() {
    // no expression after 'return'
    let parser = Parser::new(Source::TopLevel("return"));
    assert!(parser.parse_top_level().is_err());

    // no 'end' to close this 'if'
    let parser = Parser::new(Source::TopLevel("if true then return 0 else return 1"));
    assert!(parser.parse_top_level().is_err());

    // 'break' in an incorrect position
    let parser = Parser::new(Source::TopLevel("return break"));
    assert!(parser.parse_top_level().is_err());

    // Expected an identifier, found something else.
    let parser = Parser::new(Source::TopLevel("for 0 in range(1, 2) print(1) end"));
    assert!(parser.parse_top_level().is_err());

    // Parsed an expression that we realized later was in an incorrect
    // position.
    let parser = Parser::new(Source::TopLevel("x + 1"));
    assert!(parser.parse_top_level().is_err());
}

#[test]
fn simple_statements() {
    let parser = Parser::new(Source::TopLevel("return 1"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1)]);
    assert_eq!(chunk.code, [ReadConstant(0), Return, PushNil, Return]);

    let parser = Parser::new(Source::TopLevel("if 1 + 2 then return 3 end"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [Constant::Int(1), Constant::Int(2), Constant::Int(3)]
    );
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            ReadConstant(1),
            Add,
            JumpPopFalse(3),
            ReadConstant(2),
            Return,
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "
        if (\"hello\" + \"world\") == \"hello world\" then
            return f(2, true)
        else
            return 5 - (f - g)(6) * 8
        end",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [
            Constant::String("hello".into()),
            Constant::String("world".into()),
            Constant::String("hello world".into()),
            Constant::Int(2),
            Constant::Int(5),
            Constant::Int(6),
            Constant::Int(8),
        ]
    );
    assert_eq!(chunk.globals, [Box::from("f"), Box::from("g")]);
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            ReadConstant(1),
            Add,
            ReadConstant(2),
            Equal,
            JumpPopFalse(7),
            ReadGlobal(0),
            ReadConstant(3),
            PushTrue,
            Call(2),
            Return,
            Jump(11),
            ReadConstant(4),
            ReadGlobal(0),
            ReadGlobal(1),
            Subtract,
            ReadConstant(5),
            Call(1),
            ReadConstant(6),
            Multiply,
            Subtract,
            Return,
            PushNil,
            Return
        ]
    );
}

#[test]
fn binary_ops() {
    let parser = Parser::new(Source::TopLevel("return 1 + 2 * 3 + 4"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            ReadConstant(1),
            ReadConstant(2),
            Multiply,
            ReadConstant(3),
            Add,
            Add,
            Return,
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "return (1 + 2) << 3 - 4 * 5 % 6 == 7 / -8 ^ 9",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            ReadConstant(1),
            Add,
            ReadConstant(2),
            ReadConstant(3),
            ReadConstant(4),
            ReadConstant(5),
            Modulo,
            Multiply,
            Subtract,
            ShiftL,
            ReadConstant(6),
            ReadConstant(7),
            Negative,
            ReadConstant(8),
            Pow,
            Divide,
            Equal,
            Return,
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "return not true and false or false == true xor true or not true",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.code,
        [
            PushTrue, Not, PushFalse, And, PushFalse, PushTrue, Equal, PushTrue, PushTrue, Not, Or,
            Xor, Or, Return, PushNil, Return
        ]
    );
}

#[test]
fn while_loop() {
    let parser = Parser::new(Source::TopLevel("while x > y x -= 1 end"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1)]);
    assert_eq!(chunk.globals, [Box::from("x"), Box::from("y")]);
    assert_eq!(
        chunk.code,
        [
            PrepareLoop(3),
            ReadGlobal(0),
            ReadGlobal(1),
            More,
            JumpEndWhile(6),
            ReadGlobal(0),
            ReadConstant(0),
            Subtract,
            WriteGlobal(0),
            Continue(0),
            PushNil,
            Return
        ]
    );

    // while extended operands
    let parser = Parser::new(Source::TopLevel(
        "while x > y
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
                x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1 x -= 1
            end",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1)]);
    assert_eq!(chunk.globals, [Box::from("x"), Box::from("y")]);
    assert_eq!(
        chunk.code[0..6],
        [
            PrepareLoop(3),
            ReadGlobal(0),
            ReadGlobal(1),
            More,
            Extended(1),
            JumpEndWhile(2),
        ]
    );
    for i in 1..65 {
        assert_eq!(
            chunk.code[(i * 4 + 2)..(i + 1) * 4 + 2],
            [ReadGlobal(0), ReadConstant(0), Subtract, WriteGlobal(0),]
        );
    }
    assert_eq!(chunk.code[262..], [Continue(0), PushNil, Return]);
}

#[test]
fn for_loop() {
    let parser = Parser::new(Source::TopLevel(
        "
        for i in range(1, 2)
            x += 1
        end
        ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1), Constant::Int(2)]);
    assert_eq!(chunk.globals, [Box::from("range"), Box::from("x")]);
    assert_eq!(
        chunk.code,
        [
            ReadGlobal(0),
            ReadConstant(0),
            ReadConstant(1),
            Call(2),
            PrepareLoop(2),
            DuplicateTop(0),
            Call(0),
            JumpEndFor(7),
            WriteLocal(0),
            ReadGlobal(1),
            ReadConstant(0),
            Add,
            WriteGlobal(1),
            Continue(1),
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "
            fn range(a, b)
                # ...
            end
            x = 0
            for i in range(1, 3)
                x += 1
            end
            return x
        ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [Constant::Int(0), Constant::Int(1), Constant::Int(3)]
    );
    assert_eq!(chunk.globals, [Box::from("range"), Box::from("x")]);
    assert_eq!(
        chunk.code,
        [
            ReadFunction(0),
            WriteGlobal(0),
            ReadConstant(0),
            WriteGlobal(1),
            ReadGlobal(0),
            ReadConstant(1),
            ReadConstant(2),
            Call(2),
            PrepareLoop(2),
            DuplicateTop(0),
            Call(0),
            JumpEndFor(7),
            WriteLocal(0),
            ReadGlobal(1),
            ReadConstant(1),
            Add,
            WriteGlobal(1),
            Continue(1),
            ReadGlobal(1),
            Return,
            PushNil,
            Return
        ]
    );
}

#[test]
fn tables() {
    let parser = Parser::new(Source::TopLevel("t = {}"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, []);
    assert_eq!(chunk.globals, [Box::from("t")]);
    assert_eq!(chunk.code, [MakeTable(0), WriteGlobal(0), PushNil, Return]);

    let parser = Parser::new(Source::TopLevel("t = { x = 1 + 2, y = \"hello\" }"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [
            Constant::String("x".into()),
            Constant::Int(1),
            Constant::Int(2),
            Constant::String("y".into()),
            Constant::String("hello".into())
        ]
    );
    assert_eq!(chunk.globals, [Box::from("t")]);
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            ReadConstant(1),
            ReadConstant(2),
            Add,
            ReadConstant(3),
            ReadConstant(4),
            MakeTable(2),
            WriteGlobal(0),
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel("t1[t1.a + f()] -= t2.b[t3[2]]"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [
            Constant::String("a".into()),
            Constant::String("b".into()),
            Constant::Int(2)
        ]
    );
    assert_eq!(
        chunk.globals,
        [
            Box::from("t1"),
            Box::from("f"),
            Box::from("t2"),
            Box::from("t3")
        ]
    );
    assert_eq!(
        chunk.code,
        [
            ReadGlobal(0),
            ReadGlobal(0),
            ReadConstant(0),
            ReadTable,
            ReadGlobal(1),
            Call(0),
            Add,
            DuplicateTop(1),
            ReadTable,
            ReadGlobal(2),
            ReadConstant(1),
            ReadTable,
            ReadGlobal(3),
            ReadConstant(2),
            ReadTable,
            ReadTable,
            Subtract,
            WriteTable,
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "
        t = { x = 5 }
        t.x -= 3
        return t.x
        ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [
            Constant::String("x".into()),
            Constant::Int(5),
            Constant::Int(3)
        ]
    );
    assert_eq!(
        chunk // not very... nice...
            .globals
            .iter()
            .map(|name| name.as_ref())
            .collect::<Vec<&str>>()
            .as_slice(),
        ["t"]
    );
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            ReadConstant(1),
            MakeTable(1),
            WriteGlobal(0),
            ReadGlobal(0),
            ReadConstant(0),
            DuplicateTop(1),
            ReadTable,
            ReadConstant(2),
            Subtract,
            WriteTable,
            ReadGlobal(0),
            ReadConstant(0),
            ReadTable,
            Return,
            PushNil,
            Return
        ]
    );
}

#[test]
fn functions() {
    let parser = Parser::new(Source::TopLevel("fn f() return 0 end x = f()"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, []);
    assert_eq!(
        chunk // not very... nice...
            .globals
            .iter()
            .map(|name| name.as_ref())
            .collect::<Vec<&str>>()
            .as_slice(),
        ["f", "x"]
    );
    assert_eq!(
        chunk.code,
        [
            ReadFunction(0),
            WriteGlobal(0),
            ReadGlobal(0),
            Call(0),
            WriteGlobal(1),
            PushNil,
            Return
        ]
    );
    assert_eq!(
        chunk.functions[0].code,
        [ReadConstant(0), Return, PushNil, Return]
    );

    let parser = Parser::new(Source::TopLevel(
        "
        x = 0
        fn f()
            y = 1
            fn g()
                x = 2
                y = 2
            end
            return g + 1
        end
        ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(0)]);
    assert_eq!(
        chunk // not very... nice...
            .globals
            .iter()
            .map(|name| name.as_ref())
            .collect::<Vec<&str>>()
            .as_slice(),
        ["x", "f"]
    );
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            WriteGlobal(0),
            ReadFunction(0),
            WriteGlobal(1),
            PushNil,
            Return
        ]
    );
    assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
    assert!(chunk.functions[0].globals.is_empty());
    assert_eq!(
        chunk.functions[0].code,
        [
            ReadConstant(0),
            WriteLocal(0),
            ReadFunction(0),
            WriteLocal(1),
            ReadLocal(1),
            ReadConstant(0),
            Add,
            Return,
            PushNil,
            Return
        ]
    );

    assert_eq!(
        chunk.functions[0].functions[0].constants,
        [Constant::Int(2)]
    );
    assert!(chunk.functions[0].functions[0].globals.is_empty());
    assert_eq!(
        chunk.functions[0].functions[0].code,
        [
            ReadConstant(0),
            WriteLocal(0),
            ReadConstant(0),
            WriteCaptured(0),
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "
            x = fn()
                    y = 1
                    return (fn(a, b) return y + a + b end)(1, 2)
                end
            ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, []);
    assert_eq!(chunk.globals[0].as_ref(), "x");
    assert_eq!(
        chunk.code,
        [ReadFunction(0), WriteGlobal(0), PushNil, Return]
    );
    assert_eq!(
        chunk.functions[0].code,
        [
            ReadConstant(0),
            WriteLocal(0),
            ReadFunction(0),
            ReadConstant(0),
            ReadConstant(1),
            Call(2),
            Return,
            PushNil,
            Return
        ]
    );
    assert_eq!(
        chunk.functions[0].functions[0].code,
        [
            ReadCaptured(0),
            ReadLocal(0),
            ReadLocal(1),
            Add,
            Add,
            Return,
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "
        x = 0
        y = fn()
            y = 1
            fn f()
                fn g()
                    x = 2
                    y = 2
                end
                return g + 1
            end
        end
        ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(0)]);
    assert_eq!(chunk.captures, []);
    assert_eq!(
        chunk // not very... nice...
            .globals
            .iter()
            .map(|name| name.as_ref())
            .collect::<Vec<&str>>()
            .as_slice(),
        ["x", "y"]
    );
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            WriteGlobal(0),
            ReadFunction(0),
            WriteGlobal(1),
            PushNil,
            Return
        ]
    );
    assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
    assert_eq!(chunk.functions[0].captures, []);
    assert!(chunk.functions[0].globals.is_empty());
    assert_eq!(
        chunk.functions[0].code,
        [
            ReadConstant(0),
            WriteLocal(0),
            ReadFunction(0),
            WriteLocal(1),
            PushNil,
            Return
        ]
    );

    assert_eq!(
        chunk.functions[0].functions[0].constants,
        [Constant::Int(1)]
    );
    assert_eq!(
        chunk.functions[0].functions[0].captures,
        [LocalOrCaptured::Local(0)]
    );
    assert!(chunk.functions[0].functions[0].globals.is_empty());
    assert_eq!(
        chunk.functions[0].functions[0].code,
        [
            ReadFunction(0),
            WriteLocal(0),
            ReadLocal(0),
            ReadConstant(0),
            Add,
            Return,
            PushNil,
            Return
        ]
    );

    assert_eq!(
        chunk.functions[0].functions[0].functions[0].constants,
        [Constant::Int(2)]
    );
    assert_eq!(
        chunk.functions[0].functions[0].functions[0].captures,
        [LocalOrCaptured::Captured(0)]
    );
    assert!(chunk.functions[0].functions[0].functions[0]
        .globals
        .is_empty());
    assert_eq!(
        chunk.functions[0].functions[0].functions[0].code,
        [
            ReadConstant(0),
            WriteLocal(0),
            ReadConstant(0),
            WriteCaptured(0),
            PushNil,
            Return
        ]
    );

    let parser = Parser::new(Source::TopLevel(
        "
    x = 0
    fn g()
        x += 1
    end
    fn f()
        global x
        x += 1
    end
    g()
    f()
    return x
    ",
    ));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(0)]);
    assert_eq!(
        chunk // not very... nice...
            .globals
            .iter()
            .map(|name| name.as_ref())
            .collect::<Vec<&str>>()
            .as_slice(),
        ["x", "g", "f"]
    );
    assert_eq!(
        chunk.code,
        [
            ReadConstant(0),
            WriteGlobal(0),
            ReadFunction(0),
            WriteGlobal(1),
            ReadFunction(1),
            WriteGlobal(2),
            ReadGlobal(1),
            Call(0),
            Pop(1),
            ReadGlobal(2),
            Call(0),
            Pop(1),
            ReadGlobal(0),
            Return,
            PushNil,
            Return
        ]
    );
    assert_eq!(
        chunk.functions[0].code,
        [
            ReadGlobal(0),
            ReadConstant(0),
            Add,
            WriteLocal(0), // local
            PushNil,
            Return
        ]
    );
    assert_eq!(
        chunk.functions[1].code,
        [
            ReadGlobal(0),
            ReadConstant(0),
            Add,
            WriteGlobal(0), // global
            PushNil,
            Return
        ]
    )
}
