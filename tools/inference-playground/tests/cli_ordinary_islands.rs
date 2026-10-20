use std::io::Write;
use std::process::{Command, Stdio};

fn run(source: &str, definition: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", definition, "--steps", "10000", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(source.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn unchanged_yulang2_ordinary_islands_fixture_runs_to_eight() {
    let source = include_str!("../../../web/playground/examples/yulang2-ordinary-islands.yu");
    let output = run(source, "countdown_result");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"8\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn braced_conditional_returns_the_last_ordered_item() {
    let source = "my main = if true {\n  3\n  8\n} else {\n  0\n}\n";
    let output = run(source, "main");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"8\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn braced_conditional_elsif_returns_the_selected_sequences_final_item() {
    let source = "my main = if false {\n  1\n} elsif true {\n  3\n  8\n} else {\n  0\n}\n";
    let output = run(source, "main");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"8\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn braced_conditional_without_else_still_returns_unit() {
    let output = run("my main = if true {\n  3\n  8\n}\n", "main");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"()\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn braced_sequence_resumes_after_a_handled_operation() {
    let source = "act signal:\n    our ping: int -> int\nmy main = catch { if true {\n  3\n  signal::ping 7\n  8\n} else {\n  0\n} } { signal::ping(payload), resume -> resume 9 }\n";
    let output = run(source, "main");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"8\n");
    assert!(output.stderr.is_empty());
}
