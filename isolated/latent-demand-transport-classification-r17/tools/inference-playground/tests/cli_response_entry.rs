use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn response_expression_runs_before_saved_continuation_entry() {
    let source = "act io:\n    our tick: int -> int\n    our other: int -> int\nmy answer (pending:[io] int) = catch pending { io::other(p), j -> j p }\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> answer (k (io::other 11)) }\nmy main = relay (io::tick 7)";
    assert_eq!(source.len(), 247);
    assert!(!source.ends_with('\n'));

    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "10000", "-"])
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
    let output = child.wait_with_output().unwrap();

    assert!(
        output.status.success(),
        "expected successful response-entry execution, got: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"11\n");
    assert!(output.stderr.is_empty());
}
