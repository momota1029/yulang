use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn locally_generalized_identity_escapes_and_serves_three_clients() {
    let source = include_str!("../../../web/playground/examples/polymorphic-escaping-closure.yu");

    for (definition, expected) in [
        ("int_result", "7\n"),
        ("bool_result", "true\n"),
        ("string_result", "\"ok\"\n"),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
            .args(["--run", definition, "--steps", "100000", "-"])
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
            "{definition}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            expected,
            "{definition}"
        );
        assert!(
            output.stderr.is_empty(),
            "{definition}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
