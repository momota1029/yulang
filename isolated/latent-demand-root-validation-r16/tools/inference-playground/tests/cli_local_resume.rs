use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn local_resume_publishes_the_pending_local_result_through_cli() {
    let source = "act io:\n    our tick: int -> int\n    our other: int -> int\nmy relay (thunk:[io] int) = catch thunk { io::tick(p), k -> k 9 }\nmy main = relay { my result = io::tick 7; result }";
    assert_eq!(source.len(), 175);
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
        "expected successful execution, got: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"9\n");
    assert!(output.stderr.is_empty());
}
