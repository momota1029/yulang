use std::{
    io::Write,
    process::{Command, Stdio},
};

const PRELUDE: &str = "act io:\n    our ping: int -> int\nact state:\n    our put: int -> int\n";

fn infer_source(source: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(source.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

fn assert_type_conflict(source: &str, label: &str) {
    let output = infer_source(source);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{label} unexpectedly inferred successfully: {stderr}");
    assert!(output.stdout.is_empty(), "{label} published a graph after conflict");
    assert!(stderr.starts_with("candidate type conflicts (experimental; graph export withheld):\n"),
        "{label} failed at an unexpected stage: {stderr}");
    assert!(stderr.contains("IncompatibleEffect"), "{label} must identify the effect mismatch: {stderr}");
}

fn assert_infers(source: &str, label: &str) {
    let output = infer_source(source);
    assert!(
        output.status.success(),
        "{label} should infer successfully: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{label} emitted diagnostics: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn contravariant_formal_effect_keeps_its_open_tail() {
    let direct = format!(
        "{PRELUDE}my bad: int -> [state] int = \\x -> state::put x\nmy good: int -> [io] int = bad\n"
    );
    assert_type_conflict(&direct, "direct annotation control");

    let higher_order_unused = format!(
        "{PRELUDE}my bad: int -> [state] int = \\x -> state::put x\nmy accept (f: int -> [io] int) = 0\nmy main = accept bad\n"
    );
    assert_infers(
        &higher_order_unused,
        "unused higher-order formal accepts an open row",
    );

    let higher_order_called = format!(
        "{PRELUDE}my bad: int -> [state] int = \\x -> state::put x\nmy accept (f: int -> [io] int) = f 0\nmy main = accept bad\n"
    );
    assert_infers(
        &higher_order_called,
        "called higher-order formal accepts an open row",
    );

    let higher_order_inline = format!(
        "{PRELUDE}my accept (f: int -> [io] int) = 0\nmy main = accept (\\x -> state::put x)\n"
    );
    assert_infers(
        &higher_order_inline,
        "inline higher-order actual accepts an open row",
    );

    let compatible = format!(
        "{PRELUDE}my good: int -> [io] int = \\x -> io::ping x\nmy accept (f: int -> [io] int) = f 0\nmy main = accept good\n"
    );
    assert_infers(&compatible, "matching higher-order effects");
}
