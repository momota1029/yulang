use std::{
    io::Write,
    process::{Command, Stdio},
};

#[test]
fn yulang2_diagnostic_examples_reject_at_candidate_type_conflicts() {
    for (name, source) in [
        (
            "type mismatch",
            include_str!("../../../web/playground/examples/yulang2-type-mismatch.yu"),
        ),
        (
            "parameter provenance",
            include_str!("../../../web/playground/examples/yulang2-parameter-provenance.yu"),
        ),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
            .arg("-")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(source.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(!output.status.success(), "{name} unexpectedly succeeded");
        assert!(output.stdout.is_empty(), "{name} published stdout");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.starts_with("candidate type conflicts (experimental; graph export withheld):\n"),
            "{name} failed at an unexpected stage: {stderr}"
        );
        assert!(!stderr.contains("syntax errors"), "{name}: {stderr}");
        assert!(!stderr.contains("lowering failed"), "{name}: {stderr}");
        assert!(!stderr.contains("runtime"), "{name}: {stderr}");
    }
}
