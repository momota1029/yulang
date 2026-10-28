use std::io::Write;
use std::process::{Command, Stdio};

const POSITIVE: &str = r#"act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), k -> k 9 }
    helper(thunk)
}
my main = relay { my result = io::tick 7; result }"#;

const NEGATIVE: &str = r#"act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch thunk { io::tick(p), k -> k 9 }
    helper(thunk)
}
my main = relay { my result = io::tick 7; result }"#;

fn run(source: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "30000", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(source.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn resumed_continuation_uses_the_receivers_own_permission_through_cli() {
    let positive = run(POSITIVE);
    assert!(
        positive.status.success(),
        "positive CLI failed: {}",
        String::from_utf8_lossy(&positive.stderr)
    );
    assert_eq!(positive.stdout, b"9\n");
    assert!(positive.stderr.is_empty());

    let negative = run(NEGATIVE);
    assert!(!negative.status.success());
    assert!(negative.stdout.is_empty());
    assert!(String::from_utf8_lossy(&negative.stderr).contains("runtime unavailable: HandlerEvidence"));
}
