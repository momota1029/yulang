use std::io::Write;
use std::process::{Command, Stdio};

const POSITIVE: &str = r#"act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)"#;

const NEGATIVE: &str = r#"act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch thunk { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)"#;

fn run(source: &str) -> std::process::Output {
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
}

#[test]
fn receiver_permission_controls_cli_publication() {
    assert_eq!(POSITIVE.len(), 210);
    assert_eq!(NEGATIVE.len(), 208);

    let positive = run(POSITIVE);
    assert!(positive.status.success());
    assert_eq!(positive.stdout, b"7\n");
    assert!(positive.stderr.is_empty());

    let negative = run(NEGATIVE);
    assert!(!negative.status.success());
    assert!(negative.stdout.is_empty());
    assert!(String::from_utf8(negative.stderr)
        .unwrap()
        .contains("runtime unavailable: HandlerEvidence"));
}
