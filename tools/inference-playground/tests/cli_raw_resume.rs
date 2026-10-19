use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn raw_continuation_resumes_publish_the_saved_suffix_result() {
    let sources = [
        "act signal:\n    our ping: bool -> bool\nmy receive (input:[signal] bool) = catch input { signal::ping(p), k -> { my first = k true; k false } }\nmy forward (pending:[signal] bool) = receive pending\nmy main = receive { my result = signal::ping true; result }",
        "act signal:\n    our ping: int -> int\nmy receive (input:[signal] bool) = catch input { signal::ping(p), k -> k 23 }\nmy forward (pending:[signal] bool) = receive pending\nmy main = forward { my ignored = signal::ping 7; false }",
    ];

    for source in sources {
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

        assert!(output.status.success());
        assert_eq!(output.stdout, b"false\n");
        assert!(output.stderr.is_empty());
    }
}
