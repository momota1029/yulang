use std::{
    io::Write,
    process::{Command, Stdio},
};
use yu_playground::execute;

fn run(source: &str) -> Result<String, String> {
    execute(source, "runtime.yu", "main", 10_000, false)
}

fn cli(source: &str, steps: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", steps, "-"])
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
fn ordinary_function_application_returns_its_argument() {
    assert_eq!(run("my id x = x\nmy main = id 7").unwrap(), "7\n");
}

#[test]
fn public_execution_uses_the_original_mixed_source_schedule() {
    assert_eq!(
        run("later; 99; my later = { my value = 11; value }; later; my main = 7").unwrap(),
        "7\n"
    );
}

#[test]
fn returned_closure_retains_its_lexical_capture() {
    let source = "my main = { my capture x = \\y -> x; my f = capture 7; f 9 }";
    assert_eq!(run(source).unwrap(), "7\n");
}

#[test]
fn local_recursion_can_finish_through_a_conditional() {
    let source = "my main = { my loop b = if b: loop false else: 7; loop true }";
    assert_eq!(run(source).unwrap(), "7\n");
}

#[test]
fn omitted_else_discards_the_taken_branch_value() {
    for source in ["my main = if true: 7", "my main = if false: 7"] {
        assert_eq!(run(source).unwrap(), "()\n", "{source}");
    }
}

#[test]
fn explicit_else_returns_the_selected_branch_value() {
    assert_eq!(run("my main = if false: 7 else: 9").unwrap(), "9\n");
}

#[test]
fn positive_integer_display_preserves_arbitrary_precision() {
    let digits = "1234567890123456789012345678901234567890123456789012345678901234567890";
    assert_eq!(
        run(&format!("my main = {digits}")).unwrap(),
        format!("{digits}\n")
    );
}

#[test]
fn normal_and_heredoc_strings_decode_escapes_before_display() {
    for source in [r#"my main = "a\nb""#, r#"my main = """a\nb""""#] {
        assert_eq!(run(source).unwrap(), "\"a\\nb\"\n", "{source}");
    }
}

#[test]
fn value_parameter_consumes_fuel_for_an_ignored_recursive_argument() {
    let source = "my main = { my loop x = loop x; my ignore x = 7; ignore (loop ()) }";
    let error = execute(source, "runtime.yu", "main", 1_000, false).unwrap_err();
    assert!(error.contains("runtime step budget exhausted"), "{error}");
}

#[test]
fn computation_parameter_can_ignore_its_recursive_argument() {
    let source = "my main = { my loop x = loop x; my ignore (x:[] int) = 7; ignore (loop ()) }";
    assert_eq!(run(source).unwrap(), "7\n");
}

#[test]
fn computation_parameter_body_can_consume_its_argument() {
    let source = "my consume (x:[] int) = x\nmy main = consume 7";
    assert_eq!(run(source).unwrap(), "7\n");
}

#[test]
fn module_expression_result_is_discarded_before_selected_definition() {
    assert_eq!(run("my main = 1; 7").unwrap(), "1\n");
}

#[test]
fn admitted_annotations_preserve_the_ordinary_value() {
    for source in [
        "my main = 7 as int",
        "my main:int = 7",
        "my main = { my local:int = 7; local }",
    ] {
        assert_eq!(run(source).unwrap(), "7\n", "{source}");
    }
}

#[test]
fn cli_run_prints_the_completed_value() {
    let result = cli("my id x = x\nmy main = id 7", "1000");
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(String::from_utf8(result.stdout).unwrap(), "7\n");
}

#[test]
fn cli_type_conflicts_withhold_runtime_output() {
    let result = cli(include_str!("../examples/type-error.yu"), "1000");
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("candidate type conflicts"), "{error}");
}

#[test]
fn discarded_expression_type_conflicts_keep_source_locations() {
    for (source, line, conditional) in [
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
        let error = run(source).expect_err("a type-conflicting expression must block runtime");
        assert!(
            error.starts_with("candidate type conflicts"),
            "unexpected error category: {error}"
        );
        assert!(error.contains(line), "missing original source location: {error}");
        assert!(
            error.contains(&format!("\n  {conditional}")),
            "missing original conditional line: {error}"
        );
        assert!(!error.contains("source span unavailable"), "{error}");
        assert!(!error.contains("unsupported source"), "{error}");
    }
}

#[test]
fn cli_resource_exhaustion_withholds_runtime_output() {
    let source = "my main = { my loop x = loop x; my ignore x = 7; ignore (loop ()) }";
    let result = cli(source, "1000");
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("runtime step budget exhausted"), "{error}");
}
