use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn wrong_family_permission_withholds_runtime_and_cli_result() {
    let source = "act signal:\n    our ping: bool -> bool\nact other:\n    our unrelated: int -> int\nmy receive (input:[other] bool) = catch input { signal::ping(p), _ -> false }\nmy main = receive (signal::ping true)";
    assert_eq!(source.len(), 195);

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
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("runtime unavailable: HandlerEvidence("), "{stderr}");
    assert!(stderr.ends_with('\n'), "{stderr}");
}
