use super::*;

use Instruction::*;

mod errors {
    use super::*;

    macro_rules! make_tests {
        ([
            $($name:ident: $input:expr),* $(,)?
        ]) => {
            $(
                #[test]
                fn $name() {
                    insta::assert_display_snapshot!(Parser::new(Source::TopLevel($input)).parse_top_level().unwrap_err()[0]);
                }
            )*
        };
    }

    make_tests! {
        [
            expected_expression: "return",
            missing_end: "if true then return 0 else return 1",
            incorrect_break: "return break",
            break_outside_of_loop: "break",
            incorrect_stmt_start: "0 = 5",
            for_variable_expected_identifier: "for 0 in range(1, 2) print(1) end",
            incorrect_expression: "x + 1",
            assign_read_only: "x + 1 = 6",
            global_local_conflict: "(fn() x = 1 global x end)",
            table_declare_variable_twice: "t = { a = 1, a = 2 }",
        ]
    }
}

#[test]
fn return_statement() {
    let parser = Parser::new(Source::TopLevel("return 1"));
    let (chunk, _) = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1)]);
    insta::assert_debug_snapshot!(chunk.code)
}

#[test]
fn if_statement() {
    let parser = Parser::new(Source::TopLevel("if 1 + 2 then return 3 end"));
    let (chunk, _) = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [Constant::Int(1), Constant::Int(2), Constant::Int(3)]
    );
    insta::assert_debug_snapshot!(chunk.code);
}

#[test]
fn if_statement_with_expressions() {
    let parser = Parser::new(Source::TopLevel(
        "
    if (\"hello\" + \"world\") == \"hello world\" then
        return f(2, true)
    else
        return 5 - (f - g)(6) * 8
    end",
    ));
    let (chunk, _) = parser.parse_top_level().unwrap();
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
    insta::assert_debug_snapshot!(chunk.code);
}

mod binary_ops {
    use super::*;

    #[test]
    fn simple_arithmetics() {
        let parser = Parser::new(Source::TopLevel("return 1 + 2 * 3 + 4"));
        let (chunk, _) = parser.parse_top_level().unwrap();
        insta::assert_debug_snapshot!(chunk.code);
    }

    #[test]
    fn complex_arithmetics() {
        let parser = Parser::new(Source::TopLevel(
            "return (1 + 2) << 3 - 4 * 5 % 6 == 7 / -8 ^ 9",
        ));
        let (chunk, _) = parser.parse_top_level().unwrap();
        insta::assert_debug_snapshot!(chunk.code);
    }

    #[test]
    fn boolean() {
        let parser = Parser::new(Source::TopLevel(
            "return not true and false or false == true xor true or not true",
        ));
        let (chunk, _) = parser.parse_top_level().unwrap();
        insta::assert_debug_snapshot!(chunk.code);
    }

    #[test]
    fn left_associativity() {
        let parser = Parser::new(Source::TopLevel("return 5 + 9 + 2 - 3 - 1"));
        let (chunk, _) = parser.parse_top_level().unwrap();
        insta::assert_debug_snapshot!(chunk.code);
    }
}

#[test]
fn while_loop() {
    let parser = Parser::new(Source::TopLevel("while x > y x -= 1 end"));
    let (chunk, _) = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1)]);
    assert_eq!(chunk.globals, [Box::from("x"), Box::from("y")]);
    insta::assert_debug_snapshot!(chunk.code);
}

#[test]
fn while_extended_operands() {
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
    let (chunk, _) = parser.parse_top_level().unwrap();
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
    let (chunk, _) = parser.parse_top_level().unwrap();
    assert_eq!(chunk.constants, [Constant::Int(1), Constant::Int(2)]);
    assert_eq!(chunk.globals, [Box::from("range"), Box::from("x")]);
    insta::assert_debug_snapshot!(chunk.code);
}

#[test]
fn for_loop_complete() {
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
    let (chunk, _) = parser.parse_top_level().unwrap();
    assert_eq!(
        chunk.constants,
        [Constant::Int(0), Constant::Int(1), Constant::Int(3)]
    );
    assert_eq!(chunk.globals, [Box::from("range"), Box::from("x")]);
    insta::assert_debug_snapshot!(chunk.code);
}

mod tables {
    use super::*;

    #[test]
    fn create_empty() {
        let parser = Parser::new(Source::TopLevel("t = {}"));
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.globals, [Box::from("t")]);
        insta::assert_debug_snapshot!(chunk.code);
    }

    #[test]
    fn create() {
        let parser = Parser::new(Source::TopLevel("t = { x = 1 + 2, y = \"hello\" }"));
        let (chunk, _) = parser.parse_top_level().unwrap();
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
        insta::assert_debug_snapshot!(chunk.code);
    }

    #[test]
    fn index_syntax() {
        let parser = Parser::new(Source::TopLevel("t1[t1.a + f()] -= t2.b[t3[2]]"));
        let (chunk, _) = parser.parse_top_level().unwrap();
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
        insta::assert_debug_snapshot!(chunk.code);
    }

    #[test]
    fn field_syntax() {
        let parser = Parser::new(Source::TopLevel(
            "
        t = { x = 5 }
        t.x -= 3
        return t.x
        ",
        ));
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(
            chunk.constants,
            [
                Constant::String("x".into()),
                Constant::Int(5),
                Constant::Int(3)
            ]
        );
        assert_eq!(chunk.globals, [Box::from("t")]);
        insta::assert_debug_snapshot!(chunk.code);
    }
}

mod functions {
    use super::*;

    #[test]
    fn simple() {
        let parser = Parser::new(Source::TopLevel("fn f() return 0 end x = f()"));
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.globals, [Box::from("f"), Box::from("x")]);
        insta::assert_debug_snapshot!((chunk.code, &chunk.functions[0].code));
    }

    #[test]
    fn nested_with_captured() {
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
        end",
        ));
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(0)]);
        assert_eq!(chunk.globals, [Box::from("x"), Box::from("f")]);

        assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
        assert_eq!(chunk.functions[0].globals, []);

        assert_eq!(
            chunk.functions[0].functions[0].constants,
            [Constant::Int(2)]
        );
        assert_eq!(chunk.functions[0].functions[0].globals, []);

        insta::assert_debug_snapshot!((
            chunk.code,
            &chunk.functions[0].code,
            &chunk.functions[0].functions[0].code
        ));
    }

    #[test]
    fn anonymous() {
        let parser = Parser::new(Source::TopLevel(
            "
            x = fn()
                    y = 1
                    return (fn(a, b) return y + a + b end)(1, 2)
                end
            ",
        ));
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, []);
        assert_eq!(chunk.globals, [Box::from("x")]);

        insta::assert_debug_snapshot!((
            chunk.code,
            &chunk.functions[0].code,
            &chunk.functions[0].functions[0].code
        ));
    }

    #[test]
    fn nested_with_deep_captured() {
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
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(0)]);
        assert_eq!(chunk.captures, []);
        assert_eq!(chunk.globals, [Box::from("x"), Box::from("y")]);

        assert_eq!(chunk.functions[0].constants, [Constant::Int(1)]);
        assert_eq!(chunk.functions[0].captures, []);
        assert_eq!(chunk.functions[0].globals, []);

        assert_eq!(
            chunk.functions[0].functions[0].constants,
            [Constant::Int(1)]
        );
        assert_eq!(
            chunk.functions[0].functions[0].captures,
            [LocalOrCaptured::Local(0)]
        );
        assert_eq!(chunk.functions[0].functions[0].globals, []);

        assert_eq!(
            chunk.functions[0].functions[0].functions[0].constants,
            [Constant::Int(2)]
        );
        assert_eq!(
            chunk.functions[0].functions[0].functions[0].captures,
            [LocalOrCaptured::Captured(0)]
        );
        assert_eq!(chunk.functions[0].functions[0].functions[0].globals, []);

        insta::assert_debug_snapshot!((
            chunk.code,
            &chunk.functions[0].code,
            &chunk.functions[0].functions[0].code,
            &chunk.functions[0].functions[0].functions[0].code
        ));
    }

    #[test]
    fn global_statement() {
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
        let (chunk, _) = parser.parse_top_level().unwrap();
        assert_eq!(chunk.constants, [Constant::Int(0)]);
        assert_eq!(
            chunk.globals,
            [Box::from("x"), Box::from("g"), Box::from("f")]
        );

        insta::assert_debug_snapshot!((
            chunk.code,
            &chunk.functions[0].code,
            &chunk.functions[1].code,
        ));
    }
}

/// Just some stress testing of the parser
#[test]
#[ignore]
fn parse_a_lot() {
    const SIZE: usize = 100_000;

    let mut source = String::with_capacity(SIZE * "x = 0\n".len());
    for _ in 0..SIZE {
        source.push_str("x = 0\n");
    }
    let parser = Parser::new(Source::TopLevel(&source));
    parser.parse_top_level().unwrap();

    let mut source = String::with_capacity(SIZE * "for i in nil\nend\n".len());
    for _ in 0..SIZE {
        source.push_str("for i in nil\n");
    }
    source.push_str("x = i\n");
    for _ in 0..SIZE {
        source.push_str("end\n");
    }
    let parser = Parser::new(Source::TopLevel(&source));
    parser.parse_top_level().unwrap();
}
