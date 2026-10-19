use std::{path::Path, process::Command};

fn run_example(path: &str) -> std::process::Output {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join(path);
    Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "1000"])
        .arg(path)
        .output()
        .unwrap()
}

#[test]
fn entry_role_controls_cli_publication() {
    let unmatched = run_example("entry-unmatched-request.yu");
    assert!(!unmatched.status.success());
    assert!(unmatched.stdout.is_empty());
    let unmatched_stderr = String::from_utf8(unmatched.stderr).unwrap();
    assert!(
        unmatched_stderr.contains("unhandled runtime request"),
        "expected unhandled request diagnostic, got: {unmatched_stderr}"
    );

    let computation = run_example("entry-computation-argument.yu");
    assert!(
        computation.status.success(),
        "expected successful computation entry, got: {}",
        String::from_utf8_lossy(&computation.stderr)
    );
    assert_eq!(computation.stdout, b"9\n");
    assert!(computation.stderr.is_empty());
}
