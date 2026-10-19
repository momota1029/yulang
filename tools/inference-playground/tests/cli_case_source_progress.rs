use std::io::Write;
use std::process::{Command, Stdio};

fn run(source: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "30000", "-"])
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
fn case_unused_and_nested_binder_endpoints_are_inferred_and_executed() {
    let unused = run("my main = case 7: unused -> 11");
    assert!(
        unused.status.success(),
        "{}",
        String::from_utf8_lossy(&unused.stderr)
    );
    assert_eq!(unused.stdout, b"11\n");
    assert!(unused.stderr.is_empty());

    let nested = run("my main = case 7: outer -> case outer: inner -> inner");
    assert!(
        nested.status.success(),
        "{}",
        String::from_utf8_lossy(&nested.stderr)
    );
    assert_eq!(nested.stdout, b"7\n");
    assert!(nested.stderr.is_empty());

    let stale_endpoint = yu_playground::infer(
        "my takes_int (value:int) = value\nmy main = case \"s\": outer -> case outer: inner -> takes_int inner",
        "case-source-progress-negative.yu",
    )
    .expect_err("the inner binder must retain the outer string endpoint");
    assert!(
        stale_endpoint.contains("candidate type conflicts"),
        "{stale_endpoint}"
    );
    assert!(!stale_endpoint.contains("unsupported source"), "{stale_endpoint}");
}
