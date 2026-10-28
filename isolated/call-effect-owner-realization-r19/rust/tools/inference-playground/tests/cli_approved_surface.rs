use std::io::Write;
use std::process::{Command, Output, Stdio};

const ORDINARY: &str = "my id x = x\nmy main = id 7";
const EFFECTFUL: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\nmy main = catch io::tick 7 { io::tick(p), _ -> p }";

fn run_stdin_cli(source: &str, steps: &str) -> Output {
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
fn ordinary_callable_runs_from_public_stdin_cli() {
    let output = run_stdin_cli(ORDINARY, "1000");

    assert!(
        output.status.success(),
        "CLI failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"7\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn unambiguous_effectful_source_runs_from_public_stdin_cli() {
    let output = run_stdin_cli(EFFECTFUL, "10000");

    assert!(
        output.status.success(),
        "CLI failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"7\n");
    assert!(output.stderr.is_empty());
}
