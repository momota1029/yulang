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

fn run_file(source: &str) -> std::process::Output {
    let path = format!("tuple-case-{}.yu", std::process::id());
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "30000", path.as_str()])
        .output()
        .unwrap();
    std::fs::remove_file(path).unwrap();
    output
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

#[test]
fn flat_tuple_case_patterns_project_ordered_binders_and_wildcards_at_runtime() {
    let swapped = run_file(
        "my main = case (11, 22): (left, right) -> (right, left)",
    );
    assert!(swapped.status.success(), "{}", String::from_utf8_lossy(&swapped.stderr));
    assert_eq!(swapped.stdout, b"(22, 11)\n");
    assert!(swapped.stderr.is_empty());

    let wildcard = run_file(
        "my main = case (11, 22): (_, right) -> right",
    );
    assert!(wildcard.status.success(), "{}", String::from_utf8_lossy(&wildcard.stderr));
    assert_eq!(wildcard.stdout, b"22\n");
    assert!(wildcard.stderr.is_empty());

    let wrong_arity = run_file(
        "my main = case (1, 2, 3): (left, right) -> left",
    );
    assert!(!wrong_arity.status.success());
    assert!(String::from_utf8_lossy(&wrong_arity.stderr).contains("candidate type conflicts"), "{}", String::from_utf8_lossy(&wrong_arity.stderr));

    let non_tuple = run_file(
        "my main = case \"text\": (left, right) -> left",
    );
    assert!(!non_tuple.status.success());
    assert!(String::from_utf8_lossy(&non_tuple.stderr).contains("candidate type conflicts"), "{}", String::from_utf8_lossy(&non_tuple.stderr));
}
