use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn entry_demand_controls_cli_completion() {
    const DECL: &str = "act signal:\n    our ping: () -> int\n";
    let value_source = format!(
        "{DECL}my loop x = loop x\nmy ignore x = 9\nmy main = ignore (loop ())"
    );
    let computation_source = format!(
        "{DECL}my loop x = loop x\nmy ignore (x:[] int) = 9\nmy main = ignore (loop ())"
    );
    assert_eq!(value_source.len(), 97);
    assert_eq!(computation_source.len(), 106);
    assert!(!value_source.ends_with('\n'));
    assert!(!computation_source.ends_with('\n'));

    let run = |source: &str| {
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
        child.wait_with_output().unwrap()
    };

    let value = run(&value_source);
    assert!(!value.status.success());
    assert!(value.stdout.is_empty());
    let value_stderr = String::from_utf8(value.stderr).unwrap();
    assert!(
        value_stderr.contains(
            "runtime step budget exhausted after 10000 steps; no completed result"
        ),
        "expected step-budget-exhausted diagnostic, got: {value_stderr}"
    );

    let computation = run(&computation_source);
    assert!(
        computation.status.success(),
        "expected successful computation entry, got: {}",
        String::from_utf8_lossy(&computation.stderr)
    );
    assert_eq!(computation.stdout, b"9\n");
    assert!(computation.stderr.is_empty());
}
