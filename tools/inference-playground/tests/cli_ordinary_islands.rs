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
fn unchanged_yulang2_ordinary_islands_fixture_runs_each_sample_definition() {
    let source = include_str!("../../../web/playground/examples/yulang2-ordinary-islands.yu");
    for (definition, expected) in [
        ("int_identity", b"7\n".as_slice()),
        ("bool_identity", b"true\n".as_slice()),
        ("string_identity", b"\"ok\"\n".as_slice()),
        ("countdown_result", b"8\n".as_slice()),
    ] {
        let output = run(source, definition);
        assert!(
            output.status.success(),
            "{definition}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, expected, "{definition}");
        assert!(output.stderr.is_empty(), "{definition}");
    }
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
fn braced_sequence_preserves_a_middle_operation_effect() {
    let source = "act signal:\n    our ping: int -> int\nmy main = catch { if true {\n  signal::ping 7\n  8\n} else {\n  0\n} } { signal::ping(payload), _ -> 17 }\n";
    let output = run(source, "main");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"17\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn braced_sequence_resumes_once_and_reaches_the_suffix() {
    let source = "act signal:\n    our ping: int -> int\n    our pong: int -> int\nmy main = catch { if true {\n  signal::ping 7\n  signal::pong 8\n  3\n} else {\n  0\n} } { signal::ping(payload), resume -> resume 9, signal::pong(payload), _ -> 17 }\n";
    let output = run(source, "main");
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"17\n");
    assert!(output.stderr.is_empty());
}
