use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn returned_closure_preserves_original_capture_through_cli() {
    let source = "my main = { my capture x = \\y -> x; my f = capture 7; f 9 }";
    assert_eq!(source.len(), 59);
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
        "expected successful ordinary-source execution, got: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"7\n");
    assert!(output.stderr.is_empty());
}
