use super::*;
#[test]
fn errors() {
    // no expression after 'return'
    let parser = Parser::new(Source::TopLevel("return"));
    assert!(parser.parse_top_level().is_err());

    // no 'end' to close this 'if'
    let parser = Parser::new(Source::TopLevel("if true then return 0 else return 1"));
    assert!(parser.parse_top_level().is_err());
}

#[test]
fn simple_statements() {
    let parser = Parser::new(Source::TopLevel("return 1"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1)]);
    assert_eq!(
        chunk.code,
        [
            Instruction::ReadConstant(0),
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
        ]
    );

    let parser = Parser::new(Source::TopLevel("if 1 + 2 then return 3 end"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [Constant::Int(1), Constant::Int(2), Constant::Int(3)]
    );
    assert_eq!(
        chunk.code,
        [
            Instruction::ReadConstant(0),
            Instruction::ReadConstant(1),
            Instruction::Add,
            Instruction::JumpPopFalse(3),
            Instruction::ReadConstant(2),
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadConstant(0),
            Instruction::ReadConstant(1),
            Instruction::Add,
            Instruction::ReadConstant(2),
            Instruction::Equal,
            Instruction::JumpPopFalse(7),
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(3),
            Instruction::PushTrue,
            Instruction::Call(2),
            Instruction::Return,
            Instruction::Jump(11),
            Instruction::ReadConstant(4),
            Instruction::ReadGlobal(0),
            Instruction::ReadGlobal(1),
            Instruction::Subtract,
            Instruction::ReadConstant(5),
            Instruction::Call(1),
            Instruction::ReadConstant(6),
            Instruction::Multiply,
            Instruction::Subtract,
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::PrepareLoop(3),
            Instruction::ReadGlobal(0),
            Instruction::ReadGlobal(1),
            Instruction::More,
            Instruction::JumpEndWhile(6),
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::Subtract,
            Instruction::WriteGlobal(0),
            Instruction::Continue(0),
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::PrepareLoop(3),
            Instruction::ReadGlobal(0),
            Instruction::ReadGlobal(1),
            Instruction::More,
            Instruction::Extended(1),
            Instruction::JumpEndWhile(2),
        ]
    );
    for i in 1..65 {
        assert_eq!(
            chunk.code[(i * 4 + 2)..(i + 1) * 4 + 2],
            [
                Instruction::ReadGlobal(0),
                Instruction::ReadConstant(0),
                Instruction::Subtract,
                Instruction::WriteGlobal(0),
            ]
        );
    }
    assert_eq!(
        chunk.code[262..],
        [
            Instruction::Continue(0),
            Instruction::PushNil,
            Instruction::Return
        ]
    );
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
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::ReadConstant(1),
            Instruction::Call(2),
            Instruction::PrepareLoop(2),
            Instruction::DuplicateTop(0),
            Instruction::Call(0),
            Instruction::JumpEndFor(7),
            Instruction::WriteLocal(0),
            Instruction::ReadGlobal(1),
            Instruction::ReadConstant(0),
            Instruction::Add,
            Instruction::WriteGlobal(1),
            Instruction::Continue(1),
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadFunction(0),
            Instruction::WriteGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::WriteGlobal(1),
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(1),
            Instruction::ReadConstant(2),
            Instruction::Call(2),
            Instruction::PrepareLoop(2),
            Instruction::DuplicateTop(0),
            Instruction::Call(0),
            Instruction::JumpEndFor(7),
            Instruction::WriteLocal(0),
            Instruction::ReadGlobal(1),
            Instruction::ReadConstant(1),
            Instruction::Add,
            Instruction::WriteGlobal(1),
            Instruction::Continue(1),
            Instruction::ReadGlobal(1),
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
        ]
    );
}

#[test]
fn tables() {
    let parser = Parser::new(Source::TopLevel("t = {}"));
    let chunk = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, []);
    assert_eq!(chunk.globals, [Box::from("t")]);
    assert_eq!(
        chunk.code,
        [
            Instruction::MakeTable(0),
            Instruction::WriteGlobal(0),
            Instruction::PushNil,
            Instruction::Return
        ]
    );

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
            Instruction::ReadConstant(0),
            Instruction::ReadConstant(1),
            Instruction::ReadConstant(2),
            Instruction::Add,
            Instruction::ReadConstant(3),
            Instruction::ReadConstant(4),
            Instruction::MakeTable(2),
            Instruction::WriteGlobal(0),
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadGlobal(0),
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::ReadTable,
            Instruction::ReadGlobal(1),
            Instruction::Call(0),
            Instruction::Add,
            Instruction::DuplicateTop(1),
            Instruction::ReadTable,
            Instruction::ReadGlobal(2),
            Instruction::ReadConstant(1),
            Instruction::ReadTable,
            Instruction::ReadGlobal(3),
            Instruction::ReadConstant(2),
            Instruction::ReadTable,
            Instruction::ReadTable,
            Instruction::Subtract,
            Instruction::WriteTable,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadConstant(0),
            Instruction::ReadConstant(1),
            Instruction::MakeTable(1),
            Instruction::WriteGlobal(0),
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::DuplicateTop(1),
            Instruction::ReadTable,
            Instruction::ReadConstant(2),
            Instruction::Subtract,
            Instruction::WriteTable,
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::ReadTable,
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadFunction(0),
            Instruction::WriteGlobal(0),
            Instruction::ReadGlobal(0),
            Instruction::Call(0),
            Instruction::WriteGlobal(1),
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(
        chunk.functions[0].code,
        [
            Instruction::ReadConstant(0),
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
        ]
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
            Instruction::ReadConstant(0),
            Instruction::WriteGlobal(0),
            Instruction::ReadFunction(0),
            Instruction::WriteGlobal(1),
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
    assert!(chunk.functions[0].globals.is_empty());
    assert_eq!(
        chunk.functions[0].code,
        [
            Instruction::ReadConstant(0),
            Instruction::WriteLocal(0),
            Instruction::ReadFunction(0),
            Instruction::WriteLocal(1),
            Instruction::ReadLocal(1),
            Instruction::ReadConstant(0),
            Instruction::Add,
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadConstant(0),
            Instruction::WriteLocal(0),
            Instruction::ReadConstant(0),
            Instruction::WriteCaptured(0),
            Instruction::PushNil,
            Instruction::Return
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
        [
            Instruction::ReadFunction(0),
            Instruction::WriteGlobal(0),
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(
        chunk.functions[0].code,
        [
            Instruction::ReadConstant(0),
            Instruction::WriteLocal(0),
            Instruction::ReadFunction(0),
            Instruction::ReadConstant(0),
            Instruction::ReadConstant(1),
            Instruction::Call(2),
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(
        chunk.functions[0].functions[0].code,
        [
            Instruction::ReadCaptured(0),
            Instruction::ReadLocal(0),
            Instruction::ReadLocal(1),
            Instruction::Add,
            Instruction::Add,
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadConstant(0),
            Instruction::WriteGlobal(0),
            Instruction::ReadFunction(0),
            Instruction::WriteGlobal(1),
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
    assert_eq!(chunk.functions[0].captures, []);
    assert!(chunk.functions[0].globals.is_empty());
    assert_eq!(
        chunk.functions[0].code,
        [
            Instruction::ReadConstant(0),
            Instruction::WriteLocal(0),
            Instruction::ReadFunction(0),
            Instruction::WriteLocal(1),
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadFunction(0),
            Instruction::WriteLocal(0),
            Instruction::ReadLocal(0),
            Instruction::ReadConstant(0),
            Instruction::Add,
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadConstant(0),
            Instruction::WriteLocal(0),
            Instruction::ReadConstant(0),
            Instruction::WriteCaptured(0),
            Instruction::PushNil,
            Instruction::Return
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
            Instruction::ReadConstant(0),
            Instruction::WriteGlobal(0),
            Instruction::ReadFunction(0),
            Instruction::WriteGlobal(1),
            Instruction::ReadFunction(1),
            Instruction::WriteGlobal(2),
            Instruction::ReadGlobal(1),
            Instruction::Call(0),
            Instruction::Pop(1),
            Instruction::ReadGlobal(2),
            Instruction::Call(0),
            Instruction::Pop(1),
            Instruction::ReadGlobal(0),
            Instruction::Return,
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(
        chunk.functions[0].code,
        [
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::Add,
            Instruction::WriteLocal(0), // local
            Instruction::PushNil,
            Instruction::Return
        ]
    );
    assert_eq!(
        chunk.functions[1].code,
        [
            Instruction::ReadGlobal(0),
            Instruction::ReadConstant(0),
            Instruction::Add,
            Instruction::WriteGlobal(0), // global
            Instruction::PushNil,
            Instruction::Return
        ]
    )
}
