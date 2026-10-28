use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn nested_handler_arm_request_runs_in_outer_context() {
    let source = "act io:\n    our tick: int -> int\n    our other: int -> int\nmy inner (thunk:[io] int) = catch thunk { io::other(p), _ -> io::tick 11 }\nmy outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }\nmy main = outer (inner (io::other 7))";
    assert_eq!(source.len(), 235);

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
        "expected successful execution, got: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"11\n");
    assert!(output.stderr.is_empty());
}
