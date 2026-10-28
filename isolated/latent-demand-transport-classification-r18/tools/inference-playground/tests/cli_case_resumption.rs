use std::io::Write;
use std::process::{Command, Stdio};

const POSITIVE: &str = r#"act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }
my main = relay { case io::tick 0: 9 -> 91, _ -> 17 }"#;

const SHALLOW_NEGATIVE: &str = r#"act io:
    our tick: int -> int
my relay (thunk:[io] int) = catch thunk { io::tick(value), k -> k 9 }
my main = relay { case io::tick 0: 9 -> io::tick 8, _ -> 17 }"#;

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
fn case_scrutinee_resumes_into_selected_arm_and_shallow_handler_stays_absent() {
    let positive = run(POSITIVE);
    assert!(
        positive.status.success(),
        "positive CLI failed: {}",
        String::from_utf8_lossy(&positive.stderr)
    );
    assert_eq!(positive.stdout, b"91\n");
    assert!(positive.stderr.is_empty());

    let shallow_negative = run(SHALLOW_NEGATIVE);
    assert!(!shallow_negative.status.success());
    assert!(shallow_negative.stdout.is_empty());
    let second_tick = SHALLOW_NEGATIVE.rfind("io::tick 8").unwrap();
    let payload_start = second_tick + "io::tick ".len();
    let payload_range = format!("{payload_start}..{}", payload_start + 1);
    assert!(
        String::from_utf8_lossy(&shallow_negative.stderr)
            .contains(&format!("unhandled runtime request at {payload_range}")),
        "{}",
        String::from_utf8_lossy(&shallow_negative.stderr)
    );
}
