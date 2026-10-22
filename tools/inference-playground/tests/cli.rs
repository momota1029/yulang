use std::{
    io::Write,
    process::{Command, Stdio},
};
use yu_playground::{
    INPUT_CAP, execute_module_events, execute_module_report, infer, infer_types, infer_with_intrusion, location,
    read_source,
};

fn cli(source: &str) -> std::process::Output {
    cli_with_args(source, &[])
}

fn cli_with_args(source: &str, args: &[&str]) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(args)
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn unchanged_yulang2_types_sample_runs_through_the_cli() {
    let source = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
    assert_eq!(source.len(), 142);
    let output = cli_with_args(source, &["--run", "pair", "--steps", "100000"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"(42, Yulang)\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn unchanged_yulang2_console_sample_runs_through_the_cli() {
    let source = "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";
    assert_eq!(source.len(), 92);
    let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"hello from Yulang\n3\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn unchanged_yulang2_effects_sample_runs_through_the_cli() {
    let source = include_str!("../../../web/playground/examples/yulang2-effects.yu");
    let output = cli_with_args(source, &["--run-module"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"42\n");
    assert!(output.stderr.is_empty());
    let report = execute_module_report(source, "effects.yu", 100_000, false).unwrap();
    assert_eq!(report.events, ["42\n"]);
}

#[test]
fn unit_formals_preserve_currying_local_scope_and_argument_effects() {
    for (source, expected) in [
        ("my f() = 7\nmy main = f()\n", "7\n"),
        ("my f () = 7\nmy main = f ()\n", "7\n"),
        ("my main = { my f() = 7; f() }\n", "7\n"),
        ("my f() x = x\nmy main = (f() 3, f() \"a\")\n", "(3, \"a\")\n"),
        ("my f x () = x\nmy main = (f 3 (), f \"a\" ())\n", "(3, \"a\")\n"),
        ("my f()() = 7\nmy main = f()()\n", "7\n"),
        ("act io:\n    our tick: int -> ()\nmy relay (thunk:[io] _) = catch thunk { io::tick(p), k -> { k (); k () } }\nmy f() = 7\nmy main = relay(f (io::tick 0))\n", "7\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main"]);
        assert!(output.status.success(), "{source}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "{source}");
        assert!(output.stderr.is_empty());
    }
    for source in [
        "my f() = 7\nmy main = f true\n",
        "my main = { my f() = 7; f 3 }\n",
        "my f x () = x\nmy main = f 7 false\n",
    ] {
        let output = cli_with_args(source, &["--run", "main"]);
        assert!(!output.status.success(), "{source}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("candidate type conflicts"));
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn unresolved_qualified_names_never_gain_execution_authority() {
    let source = "my invoke() = missing::module::next()\ninvoke()\n";
    let output = cli_with_args(source, &["--run-module"]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, b"unsupported source: current candidate lowering/inference cannot observe this program\n");
}

#[test]
fn library_operator_dependencies_do_not_require_an_operator_in_the_caller() {
    for (source, expected) in [
        ("println \"one\"\n", "one\n"),
        ("println \"first\"\nprintln \"second\"\n", "first\nsecond\n"),
        ("my emit message = println message\nemit \"wrapped\"\n", "wrapped\n"),
        ("my message = \"a\" + \"b\"\nprintln message\n", "ab\n"),
        ("my forward message = emit message\nmy emit message = println message\nforward \"twice wrapped\"\n", "twice wrapped\n"),
    ] {
        let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn local_functions_retain_their_member_constraints() {
    for (source, expected) in [
        ("my main = { my add x = x + x; add 3 }\n", "6\n"),
        ("my main = { my add x = x + x; add \"a\" }\n", "\"aa\"\n"),
        ("my main = { my add x = x + x; my cat x = x + x; (add 3, cat \"a\") }\n", "(6, \"aa\")\n"),
        ("my main = { my x = 1 + 2; x }\n", "3\n"),
        ("my main = { my outer x = { my add y = y + y; add x }; outer 3 }\n", "6\n"),
        ("my outer ignored = { my add x = x + x; add }\nmy main = outer () 3\n", "6\n"),
        ("my main = { my show x = x.show; show 3 }\n", "\"3\"\n"),
        ("my main = { my add x = x + x; (add 3, add 4) }\n", "(6, 8)\n"),
        ("my outer x = { my unused = x.show; 1 }\nmy main = outer 3\n", "1\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn expression_statements_and_bindings_follow_source_order() {
    for (source, expected) in [
        ("my main = { 1; my x = 2; 3; x }\n", "2\n"),
        ("my main = { 1; 2; 7 }\n", "7\n"),
        ("my main = { true; my x = \"discarded\"; x; 7 }\n", "7\n"),
        ("my main =\n    1\n    my x = 2\n    3\n    x\n", "2\n"),
        ("my apply f = ({ 0; f }) 7\nmy main = apply (\\x -> x)\n", "7\n"),
        ("my main = { 0; my loop b = if b: loop false else: 9; 1; loop true }\n", "9\n"),
        ("my main = if true { my x = 1; 2; x } else { 3; 4 }\n", "1\n"),
        ("my main = { my x = 1; x; my x = \"s\"; x }\n", "\"s\"\n"),
        ("my main = { my add x = x + x; 0; my alias = add; 1; (alias 3, alias \"a\") }\n", "(6, \"aa\")\n"),
        ("my main = { my x = 3; { my x = 9; 0; x }; x }\n", "3\n"),
        ("my main = { println \"a\"; my x = { println \"init\"; 7 }; println \"b\"; x }\n", "a\ninit\nb\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
    for source in [
        "my main = { 1 + false; my x = 1; x }\n",
        "my main = { if true: 7 else: 1 + false; 1 }\n",
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("candidate type conflicts"));
    }
}

#[test]
fn statement_prefix_effects_survive_discard_and_local_publication() {
    let declarations = "act io:\n    our tick: int -> int\nact state:\n    our tick: int -> int\n";
    for body in [
        "{ io::tick 0; my x = 7; x }",
        "{ 0; my x = state::tick 7; 9 }",
        "{ if false: io::tick 0 else: 3; my x = 7; x }",
        "{ io::tick 0; my x = state::tick 7; x }",
    ] {
        let accepted = format!("{declarations}my main: [io, state] int = {body}\n");
        assert!(infer_types(&accepted, "statement-effects.yu").is_ok(), "{body}");
        let rejected = format!("{declarations}my main: [] int = {body}\n");
        let error = infer_types(&rejected, "statement-effects.yu").unwrap_err();
        assert!(error.contains("conflict"), "{body}: {error}");
        let latent = format!("{declarations}my run ignored = {body}\n");
        let rendered = infer_types(&latent, "statement-effects.yu").unwrap();
        let expected = if body.contains("io::tick") && body.contains("state::tick") { 2 } else { 1 };
        assert_eq!(rendered.matches("retained Effect bound support-view").count(), expected,
            "every performed family remains connected to the function result effect: {rendered}");
    }
    let pure = format!("{declarations}my main: [] int = {{ true; my x = 7; x }}\n");
    assert!(infer_types(&pure, "statement-effects.yu").is_ok());
}

#[test]
fn statement_suffixes_resume_without_repeating_the_completed_prefix() {
    for (source, expected) in [
        ("act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 11 }\nmy main = relay { 99; io::tick 0; my x = 9; x }\n", "9\n"),
        ("act io:\n    our tick: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> { k 11; k 23 } }\nmy main = relay { 99; io::tick 0; my x = 7; x }\n", "7\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes());
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn polymorphic_member_results_flow_through_later_uses() {
    for (source, expected) in [
        ("my f x = { say x; my y = x + x; say y; y }\nmy main = (f 3, f \"a\")\n", "3\n6\na\naa\n"),
        ("my f x = { my first = say x; my y = x + x; my second = say y; y }\nmy main = (f 3, f \"a\")\n", "3\n6\na\naa\n"),
        ("my f x = { my y = x + x; say y }\nmy main = (f 3, f \"a\")\n", "6\naa\n"),
        ("my f x = { my first = x.show; my y = x + x; my second = y.show; (first, second, y) }\nmy main = (f 3, f \"a\")\n", "((\"3\", \"6\", 6), (\"a\", \"aa\", \"aa\"))\n"),
        ("my main = { my f x = { say x; my y = x + x; say y; y }; (f 3, f \"a\") }\n", "3\n6\na\naa\n"),
        ("my make ignored = { my f x = { say x; my y = x + x; say y; y }; f }\nmy main = (make () 3, make () \"a\")\n", "3\n6\na\naa\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
    for source in [
        "my f x = { say x; my y = x + x; y }\nmy main = f true\n",
        "my f x = { say x; my y = x + true; y }\nmy main = f 3\n",
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(!output.status.success(), "source={source:?}");
        assert!(output.stdout.is_empty(), "a failed candidate cannot publish the earlier say output");
    }
}

#[test]
fn annotation_holes_infer_independently_and_preserve_checked_results() {
    for (source, expected) in [
        ("my pick (x:_) (y:_) = x\nmy main = (pick 3 true, pick \"a\" 9)\n", "(3, \"a\")\n"),
        ("my main = { my f: _ -> _ = \\x -> x; (f 3, f \"a\") }\n", "(3, \"a\")\n"),
        ("my id (x:_) = x\nmy main = id 7 + 1\n", "8\n"),
        ("act io:\n    our tick: int -> int\nmy relay (action:[io] _) = catch action { io::tick(p), k -> k 42 }\nmy main = relay { my x = io::tick 0; (x, true) }\n", "(42, true)\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main"]);
        assert!(output.status.success(), "{source}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "{source}");
        assert!(output.stderr.is_empty());
    }
    let output = cli_with_args("my id (x:_) = x\nmy main: int = id true\n", &["--run", "main"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("candidate type conflicts"));
    assert!(output.stdout.is_empty());
}

#[test]
fn generic_computation_results_preserve_values_and_continuations() {
    let operation = "act io:\n    our tick: int -> int\n";
    for (body, expected) in [
        ("my compute x = { my before = io::tick 7; x + x }\nmy relay (thunk:[io] 'a) = catch thunk { io::tick(value), k -> k 11 }\nmy main = (relay(compute 3), relay(compute \"a\"))\n", "(6, \"aa\")\n"),
        ("my relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my ignored = io::tick 0; (7, true) }\n", "(7, true)\n"),
        ("my relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my ignored = io::tick 0; \\x -> x } 7\n", "7\n"),
        ("my relay (thunk:[io] (int -> int)) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my ignored = io::tick 0; \\x -> x } 7\n", "7\n"),
        ("my helper (input:[] 'a) = input\nmy relay (thunk:[io] 'b) = catch helper thunk { io::tick(p), k -> k 11 }\nmy main = relay { my ignored = io::tick 0; (7, true) }\n", "(7, true)\n"),
        ("my relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> { my first = k 11; k 23 } }\nmy main = relay { my x = io::tick 0; (x, true) }\n", "(23, true)\n"),
        ("my outer (thunk:[io] 'a) = { my helper (pending:[io] 'b) = catch pending { io::tick(p), k -> k 11 }; helper thunk }\nmy main = outer { my x = io::tick 0; (x, true) }\n", "(11, true)\n"),
        ("my ignore (thunk:[io] 'a) = 7\nmy main = ignore(io::tick 0)\n", "7\n"),
        ("my relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy add x = x + x\nmy main = (relay { my ignored = io::tick 0; add } 3, relay { my ignored = io::tick 0; add } \"a\")\n", "(6, \"aa\")\n"),
        ("my relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy make x = relay { my ignored = io::tick 0; (\\u -> x + x, 7) }\nmy main = case make \"a\": (f, n) -> f n\n", "\"aa\"\n"),
        ("my outer (input:[io] 'a) = catch ({ my make (thunk:[] 'b) = thunk; my callback = make(\\u -> input); callback () }) { io::tick(p), k -> k 11 }\nmy main = outer(io::tick 7)\n", "11\n"),
    ] {
        let source = format!("{operation}{body}");
        let output = cli_with_args(&source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "{source}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "{source}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn annotation_holes_preserve_inferred_values_and_independent_positions() {
    for (source, expected) in [
        ("my identity (x:_) = x\nmy main = (identity 7, identity \"a\")\n", "(7, \"a\")\n"),
        ("my identity: _ -> _ = \\x -> x\nmy main = (identity 7, identity \"a\")\n", "(7, \"a\")\n"),
        ("my main = { my identity: _ -> _ = \\x -> x; (identity 7, identity \"a\") }\n", "(7, \"a\")\n"),
        ("my choose (x:_) (y:_) = (x, y)\nmy main = choose 7 true\n", "(7, true)\n"),
        ("my choose (x:_) (y:_) = if x: y else: y\nmy main = choose true 7\n", "7\n"),
        ("my constant: _ -> _ = \\x -> true\nmy main = constant 7\n", "true\n"),
        ("my identity: int -> _ = \\x -> x\nmy main = identity 7\n", "7\n"),
        ("my x:_ = 7\nmy main = x\n", "7\n"),
        ("my identity x = x\nmy alias:_ = identity\nmy main = (alias 7, alias \"a\")\n", "(7, \"a\")\n"),
        ("act io:\n    our tick: int -> int\nmy relay (thunk:[io] _) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { my x = io::tick 7; (x, true) }\n", "(11, true)\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "{source}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "{source}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn annotation_holes_retain_body_constraints_and_permission_requirements() {
    for (source, expected_error) in [
        ("my identity: int -> _ = \\x -> x\nmy main = identity true\n", "candidate type conflicts"),
        ("my choose (x:_) = if x: 1 else: 0\nmy main = choose 7\n", "candidate type conflicts"),
        ("my identity: _ -> _ = \\x -> x\nmy main:int = identity true\n", "candidate type conflicts"),
        ("act io:\n    our tick: int -> int\nmy relay (thunk:[] _) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay(io::tick 7)\n", "HandlerEvidence"),
        ("act io:\n    our tick: _ -> int\nmy main = io::tick 7\n", "unsupported source"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(!output.status.success(), "{source}");
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains(expected_error),
            "{source}: {}", String::from_utf8_lossy(&output.stderr));
    }
}

#[test]
fn generic_computation_grants_keep_the_original_receiver_and_permission() {
    let operation = "act io:\n    our tick: int -> int\n";
    for (body, expected_error) in [
        ("my relay (thunk:[] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay(io::tick 7)\n", "HandlerEvidence"),
        ("my relay (thunk:['e] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay(io::tick 7)\n", "HandlerEvidence"),
        ("my outer (thunk:[io] 'a) = { my helper ignored = catch thunk { io::tick(p), k -> k 11 }; helper () }\nmy main = outer(io::tick 7)\n", "HandlerEvidence"),
        ("my outer (thunk:[io] 'a) = \\u -> thunk\nmy saved = outer(io::tick 7)\nmy main = catch saved () { io::tick(p), k -> k 11 }\n", "HandlerEvidence"),
        ("my receive (thunk:[io] 'a) = thunk\nmy saved = receive(\\u -> io::tick 7)\nmy main = catch saved () { io::tick(p), k -> k 11 }\n", "HandlerEvidence"),
        ("act other:\n    our ping: int -> int\nmy relay (thunk:[io] 'a) = catch thunk { io::tick(p), k -> k 11 }\nmy main = relay { io::tick 0; other::ping 9 }\n", "unhandled runtime request"),
    ] {
        let source = format!("{operation}{body}");
        let output = cli_with_args(&source, &["--run", "main", "--steps", "100000"]);
        assert!(!output.status.success(), "{source}");
        assert!(String::from_utf8_lossy(&output.stderr).contains(expected_error),
            "{source}: {}", String::from_utf8_lossy(&output.stderr));
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn polymorphic_members_follow_aliases_and_captured_closures() {
    for source in [
        "my main = { my add x = x + x; (add 3, add \"a\") }\n",
        "my main = { my add x = x + x; my alias = add; (alias 3, alias \"a\") }\n",
        "my wrap x = { my add y = y + y; add x }\nmy main = (wrap 3, wrap \"a\")\n",
        "my make ignored = { my add x = x + x; add }\nmy main = (make () 3, make () \"a\")\n",
        "my add x = x + x\nmy main = (add 3, add \"a\")\n",
        "my make f = \\x -> f x\nmy add x = x + x\nmy wrapper = make add\nmy main = (wrapper 3, wrapper \"a\")\n",
        "my make f = \\x -> f x\nmy add x = x + x\nmy first = make add\nmy wrapper = make first\nmy main = (wrapper 3, wrapper \"a\")\n",
        "my box f = (f, 0)\nmy add x = x + x\nmy unwrap pair = case pair:\n    (f, _) -> f\nmy wrapped = unwrap (box add)\nmy main = (wrapped 3, wrapped \"a\")\n",
        "my unused x = x.show\nmy add x = x + x\nmy main = (add 3, add \"a\")\n",
        "my add x = x + x\nmy loop b x = if b: loop false x else: add x\nmy main = (loop true 3, loop true \"a\")\n",
        "my main = { my add x = x + x; my loop b x = if b: loop false x else: add x; (loop true 3, loop true \"a\") }\n",
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, b"(6, \"aa\")\n", "source={source:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn polymorphic_member_dictionaries_coexist_with_handler_resumption() {
    let source = "act io:\n    our tick: int -> int\nmy add x = x + x\nmy relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 11 }\nmy main = (add 3, add \"a\", relay(io::tick 7))\n";
    let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"(6, \"aa\", 11)\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn polymorphic_role_calls_keep_exact_static_member_dictionaries() {
    let source = "my outer x = { my unused = say x; 1 }\nouter 3\nouter \"text\"\nouter (3, \"text\")\n";
    let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"3\ntext\n(3, text)\n");
    assert!(output.stderr.is_empty());
    let source = "my show x = x.show\nmy main = (show 3, show \"a\")\n";
    let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"(\"3\", \"a\")\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn uncalled_generic_bodies_retain_their_abstract_member_constraints() {
    for (source, expected) in [
        ("my outer x = { my unused y = y + y; x }\nmy main = outer 3\n", "3\n"),
        ("my unused x = x + x\nmy main = 7\n", "7\n"),
        ("my main = { my unused x = x.show; 7 }\n", "7\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
    let output = cli_with_args("my main = { my unused x = 1 + false; 7 }\n",
        &["--run", "main", "--steps", "100000"]);
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("candidate type conflicts"));
}

#[test]
fn local_role_wrappers_execute_through_module_entry() {
    for source in [
        "my main ignored = { my emit x = say x; emit (3, \"text\") }\nmain ()\n",
        "{ my emit x = say x; emit (3, \"text\") }\n",
    ] {
        let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, b"(3, text)\n");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn scheduled_initializers_resume_output_in_source_order() {
    for (source, expected) in [
        ("my main = { my emit x = say x; emit (3, \"text\") }\n", "(3, text)\n"),
        ("my first = { my output = println \"first\"; 1 }\nmy second = { my output = println \"second\"; 2 }\nprintln \"after\"\nmy main = (first, second)\n", "first\nsecond\nafter\n"),
        ("my main = { my unused = say 3; my next = println \"next\"; 7 }\n", "3\nnext\n"),
    ] {
        let output = cli_with_args(source, &["--run", "main", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn local_initializer_effects_and_unused_constraints_are_preserved() {
    let source = "my run ignored = { my unused = println \"init\"; say 1 }\nrun ()\n";
    let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"init\n1\n");
    for source in [
        "my main = { my unused = 1 + false; 1 }\n",
        "my main = { my local x = if true: 1 else: 1 + false; local () }\n",
    ] {
        let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
        assert!(!output.status.success(), "source={source:?}");
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("candidate type conflicts"));
    }
}

#[test]
fn eager_local_role_initializers_keep_internal_constraints_and_execute_once() {
    for (source, expected) in [
        ("my outer x = { my unused = say x; 1 }\nouter 3\n", "3\n"),
        ("my outer x = { my unused = say x; 1 }\nouter \"text\"\n", "text\n"),
        ("my outer x = { my unused = say x; 1 }\nouter (3, \"text\")\n", "(3, text)\n"),
        ("my outer x = { my unused = { my inner = say x; 2 }; 1 }\nouter 3\n", "3\n"),
        ("my outer x = { my unused = say x; 1 }\nouter 3\nouter 4\n", "3\n4\n"),
    ] {
        let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn role_prerequisites_survive_enclosing_function_capture() {
    for (source, expected) in [
        ("my emit value = say value\nemit 3\n", "3\n"),
        ("my emit value = say value\nemit \"wrapped\"\n", "wrapped\n"),
        ("my forward value = emit value\nmy emit value = say value\nforward (3, \"text\")\n", "(3, text)\n"),
        ("my emit value = (say value, say value)\nemit 3\n", "3\n3\n"),
        ("my left(value: 'a) =\n    where 'a: Display\n    println value.show\nmy right(value: 'b) =\n    where 'b: Display\n    println value.show\nmy both x y = (left x, right y)\nboth 3 \"text\"\n", "3\ntext\n"),
    ] {
        let output = cli_with_args(source, &["--run-module", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected.as_bytes(), "source={source:?}");
        assert!(output.stderr.is_empty());
    }
}

#[test]
fn captured_initializers_resolve_members_without_a_later_name_use() {
    for (source, expected_value, expected_type) in [
        ("pub answer = 1 + 2\n", "3\n", "int"),
        ("pub answer = \"a\" + \"b\"\n", "\"ab\"\n", "str"),
        ("pub answer = if true: 1 + 2 else: 3 + 4\n", "3\n", "int"),
        ("my constant ignored = 1 + 2\npub answer = constant false\n", "3\n", "int"),
    ] {
        let output = cli_with_args(source, &["--run", "answer", "--steps", "100000"]);
        assert!(output.status.success(), "source={source:?}: {}", String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.stdout, expected_value.as_bytes(), "source={source:?}");
        let report = execute_module_report(source, "captured-initializer.yu", 100_000, false).unwrap();
        assert!(report.events.is_empty());
        let declaration = report.types.lines().find_map(|line| line.strip_prefix("answer: ")).unwrap();
        // Retained effect-bound variables can remain quantified even when
        // the result value has this concrete head.
        assert!(declaration == expected_type
            || (declaration.starts_with('∀') && declaration.ends_with(&format!(". {expected_type}"))),
            "source={source:?}: {}", report.types);
    }
    let bad_branch = "pub answer = if true: 1 + 2 else: 1 + false\n";
    let error = infer_types(bad_branch, "captured-bad-branch.yu").unwrap_err();
    assert!(error.to_string().contains("candidate type conflicts"), "{error}");
}

#[test]
fn unchanged_yulang2_samples_preserve_ordered_module_write_events() {
    let types = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
    let console = "// println is a library effect handled by the host.\n\nprintln \"hello from Yulang\"\nsay: 1 + 2\n";
    assert_eq!(
        execute_module_events(types, "types.yu", 100_000, false).unwrap(),
        ["(42, Yulang)\n"]
    );
    assert_eq!(
        execute_module_events(console, "console.yu", 100_000, false).unwrap(),
        ["hello from Yulang\n", "3\n"]
    );
    let types_report = execute_module_report(types, "types.yu", 100_000, false).unwrap();
    assert_eq!(types_report.events, ["(42, Yulang)\n"]);
    for expected in ["id: ∀", "answer: int", "name: str", "pair: (int, str)"] {
        assert!(types_report.types.contains(expected), "{}", types_report.types);
    }
    let console_report = execute_module_report(console, "console.yu", 100_000, false).unwrap();
    assert_eq!(console_report.events, ["hello from Yulang\n", "3\n"]);
    assert!(console_report.types.contains("No binding types in this source."));
}

#[test]
fn unchanged_yulang2_types_sample_exposes_candidate_public_types() {
    let source = "// our and pub bindings appear in the Types pane.\n\nour id x = x\npub answer = id 42\npub name = id \"Yulang\"\npub pair = (answer, name)\n\npair.say\n";
    let output = infer_types(source, "types.yu").unwrap();
    let id = output.lines().find(|line| line.starts_with("id: ")).expect("id type entry");
    assert!(id.starts_with("id: ∀"), "{output}");
    let id_body = id.split_once(". ").expect("id type quantifier body").1;
    let argument = id_body.split_once("argument=").expect("id argument").1.split(',').next().unwrap();
    let result = id_body.rsplit_once("result=").expect("id result").1.trim_end_matches(')');
    assert_eq!(argument, result, "identity must preserve its shared value row: {id}");
    assert!(output.contains("answer: int"), "{output}");
    assert!(!output.contains("answer: ∀"), "ground exports do not quantify internal candidate rows: {output}");
    assert!(output.contains("name: str"), "{output}");
    assert!(!output.contains("name: ∀"), "ground exports do not quantify internal candidate rows: {output}");
    assert!(output.contains("pair: (int, str)"), "{output}");
    assert!(!output.contains("pair: ∀"), "ground tuple exports do not quantify internal candidate rows: {output}");
    assert!(output.contains("argument-effect="), "effect ports must remain visible: {output}");
    assert!(output.contains("retained Effect bound"), "effect-row relationships must remain visible: {output}");
    assert!(output.contains("retained Value bound"), "value-row relationships must remain visible: {output}");
    assert!(!output.contains("effect-operand"), "unsupported internal nodes must never be printed as types: {output}");
}

#[test]
fn candidate_playground_accepts_state_callback_under_open_io_permission() {
    let source = "act io:\n    our tick: int -> ()\nact state:\n    our tick: int -> ()\nmy bridge (callback: int -> [io] ()) = callback\nmy state_callback value = state::tick value\nmy answer = bridge state_callback\n";
    let output = infer_types(source, "open-io-state-callback.yu").unwrap();
    assert!(output.contains("open formal effect permission result"), "{output}");
    assert!(output.contains(" (open)"), "the permission keeps an open effect tail: {output}");
    assert!(output.contains("state_callback:"), "{output}");
    let answer = output.split_once("answer: ").expect("answer type entry").1;
    assert!(answer.contains("retained Effect bound support-view"), "the performed state effect remains in the answer's residual effect view: {answer}");
    assert!(answer.contains("⊆ ε"), "the state effect view remains connected to an open residual row: {answer}");
    assert!(output.contains("retained Effect bound"), "the callback effect must remain in the open residual view: {output}");
    assert!(!output.contains("candidate type conflicts"), "[io] is an open permission, so [state] must remain admissible: {output}");
}

#[test]
fn combined_module_report_withholds_types_and_events_on_failure() {
    let conflict = include_str!("../examples/type-error.yu");
    let error = execute_module_report(conflict, "conflict.yu", 100_000, false).unwrap_err();
    assert!(error.contains("candidate type conflicts"), "{error}");
    let exhausted = execute_module_report("my identity x = x\nmy main = identity 7", "budget.yu", 0, false).unwrap_err();
    assert!(exhausted.contains("runtime step budget exhausted"), "{exhausted}");
    let unhandled = "act io:\n    our tick: int -> ()\nprintln \"prefix\"\nsay: 1 + 2\nio::tick 1\n";
    let error = execute_module_report(unhandled, "unhandled.yu", 100_000, false).unwrap_err();
    assert!(error.contains("unhandled runtime request"), "{error}");
}

#[test]
fn reads_utf8_and_distinguishes_tool_caps() {
    assert_eq!(read_source("é".as_bytes()).unwrap(), "é");
    assert!(read_source(&[0xff][..]).unwrap_err().contains("UTF-8"));
    assert!(
        read_source(vec![b'x'; INPUT_CAP + 1].as_slice())
            .unwrap_err()
            .contains("tool input cap")
    );
}

#[test]
fn identity_runs_the_solver_and_prints_constraints() {
    let result = cli(include_str!("../examples/identity.yu"));
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let output = String::from_utf8(result.stdout).unwrap();
    assert!(output.contains("definition identity:"));
    assert!(output.contains("Function(argument="));
    assert!(output.contains(" <: "));
    assert!(output.contains("no principal-type"));
}

#[test]
fn recursive_graph_is_finite_and_deterministic() {
    let source = include_str!("../examples/nested-recursion.yu");
    let first = infer(source, "recursion.yu").unwrap();
    let second = infer(source, "recursion.yu").unwrap();
    assert_eq!(first, second);
    assert!(first.contains("definition loop:"));
    assert!(first.contains("finite references"));
    assert!(first.len() < 1_000_000);
}

#[test]
fn conflicts_exit_unsuccessfully_and_withhold_exports() {
    let result = cli(include_str!("../examples/type-error.yu"));
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("candidate type conflicts"));
    assert!(error.contains("bytes "));
    assert!(!error.contains("source span unavailable"));
}

#[test]
fn constant_conditions_observe_both_branch_leaves() {
    let source = include_str!("../examples/conditional-union.yu");
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(output.contains("definition mixed:"));
        assert!(output.contains("IntPositive"));
        assert!(output.contains("StrPositive"));
        assert!(output.contains(" <: "));
        assert!(output.contains("no principal-type"));
    }
}

#[test]
fn catch_value_binder_observes_both_conditional_results() {
    let source = include_str!("../examples/catch-value.yu");
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(output.contains("definition mixed:"));
        assert!(output.contains("IntPositive"));
        assert!(output.contains("StrPositive"));
        assert!(output.contains("no principal-type"));
    }
}

#[test]
fn catch_value_conflicts_withhold_cli_observations() {
    let source = "my mixed: int = catch (if true: 1 else: \"str\") { value -> value }";
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"));
        assert!(!error.contains("unsupported source"));
    }
}

#[test]
fn operation_catch_binds_payload_and_raw_continuation() {
    let result = cli(include_str!("../examples/catch-operation.yu"));
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output = String::from_utf8(result.stdout).unwrap();
    assert!(output.contains("definition handled:"));
    assert!(output.contains("StrPositive"));
    assert!(output.contains("no principal-type"));
}

#[test]
fn operation_catch_checks_payload_and_response_types() {
    let source = include_str!("../examples/catch-operation.yu");
    for source in [
        source.replace("checked: int", "checked: str"),
        source.replace("resume \"resumed\"", "resume true"),
    ] {
        let result = cli(&source);
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"), "{error}");
        assert!(!error.contains("unsupported source"));
    }
}

#[test]
fn conditional_conflicts_withhold_all_cli_observations() {
    let source = include_str!("../examples/conditional-conflict.yu");
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"));
        assert!(!error.contains("unsupported source"));
        assert!(!error.contains("definition mixed:"));
    }
    let result = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .arg("--intrusion")
        .arg(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/conditional-conflict.yu"
        ))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("candidate type conflicts"), "unexpected --intrusion stderr: {error}");
    assert!(!error.contains("Retained intrusion state"));
}

#[test]
fn discarded_expression_conflicts_withhold_all_cli_modes() {
    for (source, location, conditional) in [
        (
            "if 1: 1 else: 2;\nmy main = 7",
            " at 1:",
            "if 1: 1 else: 2;",
        ),
        (
            "my main = 7;\nif 1: 1 else: 2",
            " at 2:",
            "if 1: 1 else: 2",
        ),
    ] {
        for args in [&[][..], &["--intrusion"][..], &["--run", "main"][..]] {
            let result = cli_with_args(source, args);
            assert!(
                !result.status.success(),
                "CLI mode {args:?} accepted: {source}"
            );
            assert!(
                result.stdout.is_empty(),
                "CLI mode {args:?} exposed stdout: {source}"
            );
            let error = String::from_utf8(result.stderr).unwrap();
            assert!(
                error.contains("candidate type conflicts"),
                "CLI mode {args:?}: {error}"
            );
            assert!(error.contains(location), "CLI mode {args:?}: {error}");
            assert!(
                error.contains(&format!("\n  {conditional}")),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("source span unavailable"),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("unsupported source"),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("Retained intrusion state"),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("definition main:"),
                "CLI mode {args:?}: {error}"
            );
        }
    }
}

#[test]
fn expression_only_modules_are_checked_before_no_binding_output() {
    let valid = r"(\x -> x) 1;
if true: true else: false";
    let invalid = r"(\x -> x) 1;
if 1: true else: false";

    for args in [&[][..], &["--intrusion"][..]] {
        let result = cli_with_args(valid, args);
        assert!(
            result.status.success(),
            "CLI mode {args:?}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(
            output.contains("No binding exports in this source."),
            "CLI mode {args:?}: {output}"
        );
        assert!(
            !output.contains("definition "),
            "CLI mode {args:?}: {output}"
        );

        let result = cli_with_args(invalid, args);
        assert!(!result.status.success(), "CLI mode {args:?} accepted conflict");
        assert!(result.stdout.is_empty(), "CLI mode {args:?} exposed stdout");
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"), "{error}");
        assert!(error.contains(" at 2:"), "{error}");
        assert!(
            error.contains("\n  if 1: true else: false"),
            "{error}"
        );
        assert!(!error.contains("unsupported source"), "{error}");
        assert!(!error.contains("No binding exports"), "{error}");
    }
}

#[test]
fn boolean_and_string_consumers_accept_matching_literals() {
    let result = cli("my bool_id (x:bool) = x; my str_id (x:str) = x; \
         my boolean = bool_id false; my string = str_id \"str\"");
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let output = String::from_utf8(result.stdout).unwrap();
    let boolean = output
        .split("definition boolean:\n")
        .nth(1)
        .unwrap()
        .split("\ndefinition ")
        .next()
        .unwrap();
    assert!(boolean.contains("BoolPositive"));
    let string = output.split("definition string:\n").nth(1).unwrap();
    assert!(string.contains("StrPositive"));
}

#[test]
fn unsupported_source_is_distinct_from_conflicts() {
    let error = infer("my outer = { my value = value; value }", "unsupported.yu").unwrap_err();
    assert!(error.contains("unsupported source"));
    assert!(!error.contains("candidate type conflicts"));
}

#[test]
fn syntax_diagnostics_are_reported() {
    let error = infer("my broken =", "broken.yu").unwrap_err();
    assert!(error.contains("syntax diagnostics"));
    assert!(error.contains("bytes "));
}

#[test]
fn unicode_byte_spans_use_character_columns_and_safe_excerpts() {
    let source = "αβ\nγ = δ";
    assert_eq!(location(source, &(10..12)), "2:5 (bytes 10..12)\n  γ = δ");
    assert!(location(source, &(1..2)).starts_with("1:1"));
    assert!(location(source, &(100..200)).contains("γ = δ"));
}

#[test]
fn effects_remain_observed_without_inventing_an_empty_operand() {
    let output = infer(include_str!("../examples/effects.yu"), "effects.yu").unwrap();
    assert!(output.contains("definition lookup:"));
    assert!(output.contains("opaque effect operand (contents unavailable)"));
}

#[test]
fn file_and_help_entrypoints_are_runnable() {
    let binary = env!("CARGO_BIN_EXE_yu-playground");
    assert!(
        Command::new(binary)
            .arg("--help")
            .output()
            .unwrap()
            .status
            .success()
    );
    let result = Command::new(binary)
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/identity.yu"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn intrusion_flag_observes_actual_source_associations() {
    let source = include_str!("../examples/nested-recursion.yu");
    assert!(
        !infer(source, "loop.yu")
            .unwrap()
            .contains("Retained intrusion state")
    );
    let output = infer_with_intrusion(source, "loop.yu", true).unwrap();
    assert!(output.contains("Retained intrusion state (not a chronological trace)"));
    assert!(output.contains("pending consumed="));
    assert!(output.contains("same_scc=true"));
    assert!(output.contains("at retained call-tail occurrence "));
    assert!(output.contains("module loop"));
    assert!(output.contains("local helper"));
    assert!(
        output.contains("  pair "),
        "nested source calls retain actual extrusion parent/copy pairs"
    );
    assert!(output.contains("target_level="));
    assert!(output.contains("  group "));
    assert!(!output.contains("source span unavailable"));
    let result = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .arg("--intrusion")
        .arg(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/nested-recursion.yu"
        ))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("Retained intrusion state")
    );
}

#[test]
fn intrusion_expression_calls_keep_original_spans_and_local_names() {
    let cases = [
        (
            "id 1; my id x = x; my main = 7",
            "id 1",
            "module id",
        ),
        (
            "{ my helper x = x; helper 1 }; my main = 7",
            "helper 1",
            "local helper",
        ),
    ];

    for (source, call, expected_label) in cases {
        let output = infer_with_intrusion(source, "expression-intrusion.yu", true).unwrap();
        assert!(output.contains("Retained intrusion state (not a chronological trace)"));
        assert!(output.contains("  event "), "retained event missing: {output}");
        assert!(output.contains("origin=v"), "expression origin missing: {output}");
        assert!(
            output.contains("(expression value, SCC "),
            "expression-origin label missing: {output}"
        );
        assert!(
            output.contains(expected_label),
            "receiver source label missing: {output}"
        );
        assert!(!output.contains("source span unavailable"));

        let start = source.find(call).unwrap();
        let expected_location = format!(
            "at retained call-tail occurrence {}\n",
            location(source, &(start + call.len() - 1..start + call.len()))
        );
        assert!(
            output.contains(&expected_location),
            "original call-tail location missing: {expected_location:?}\n{output}"
        );
    }
}

#[test]
fn conflicts_also_withhold_intrusion_observations() {
    let error = infer_with_intrusion(
        include_str!("../examples/type-error.yu"),
        "conflict.yu",
        true,
    )
    .unwrap_err();
    assert!(error.contains("candidate type conflicts"));
    assert!(!error.contains("Retained intrusion state"));
}

#[test]
fn aggregate_output_limit_withholds_all_cli_output() {
    // Twenty small calls keep solver work small. A long source line makes
    // their authentic excerpts exercise the shared output byte budget.
    let mut source = String::from("my id x = x;");
    for index in 0..20 {
        source.push_str(&format!(" my client{index} x = id x;"));
    }
    source.push_str(&" ".repeat(60_000));
    source.push('\n');
    assert!(source.len() < INPUT_CAP);
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--intrusion", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    assert!(
        String::from_utf8(result.stderr)
            .unwrap()
            .contains("tool output cap exceeded")
    );
}

#[test]
fn directional_introductions_show_exact_uses_and_provider_exclusion() {
    let source = "my apply f = f 1; my id x = x; my good = apply id";
    let output = infer_with_intrusion(source, "directional.yu", true).unwrap();
    assert!(
        output.contains("symbolic candidate evidence; not event consumption or runtime hygiene")
    );
    assert_eq!(output.matches("  introduction ").count(), 1);
    assert_eq!(output.matches("ResultEffect=").count(), 1);
    assert!(output.contains("no authenticated omitted-formal introduction"));
    assert!(
        !infer(source, "directional.yu")
            .unwrap()
            .contains("Directional introductions")
    );
    let repeated = infer_with_intrusion("my apply f = f (f 1)", "repeated.yu", true).unwrap();
    assert_eq!(repeated.matches("  introduction ").count(), 2);
}
