use std::{
    io::Write,
    process::{Command, Stdio},
};
use yu_playground::{INPUT_CAP, infer, infer_with_intrusion, location, read_source};

fn cli(source: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .arg("-")
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
fn reads_utf8_and_distinguishes_tool_caps() {
    assert_eq!(read_source("é".as_bytes()).unwrap(), "é");
    assert!(read_source(&[0xff][..]).unwrap_err().contains("UTF-8"));
    assert!(
        read_source(vec![b'x'; INPUT_CAP + 1].as_slice())
            .unwrap_err()
            .contains("tool input cap")
    );
}

#[test]
fn identity_runs_the_solver_and_prints_constraints() {
    let result = cli(include_str!("../examples/identity.yu"));
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let output = String::from_utf8(result.stdout).unwrap();
    assert!(output.contains("definition identity:"));
    assert!(output.contains("Function(argument="));
    assert!(output.contains(" <: "));
    assert!(output.contains("no principal-type"));
}

#[test]
fn recursive_graph_is_finite_and_deterministic() {
    let source = include_str!("../examples/nested-recursion.yu");
    let first = infer(source, "recursion.yu").unwrap();
    let second = infer(source, "recursion.yu").unwrap();
    assert_eq!(first, second);
    assert!(first.contains("definition loop:"));
    assert!(first.contains("finite references"));
    assert!(first.len() < 1_000_000);
}

#[test]
fn conflicts_exit_unsuccessfully_and_withhold_exports() {
    let result = cli(include_str!("../examples/type-error.yu"));
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("candidate type conflicts"));
    assert!(error.contains("bytes "));
    assert!(!error.contains("source span unavailable"));
}

#[test]
fn unsupported_source_is_distinct_from_conflicts() {
    let error = infer("my outer = { my value = value; value }", "unsupported.yu").unwrap_err();
    assert!(error.contains("unsupported source"));
    assert!(!error.contains("candidate type conflicts"));
}

#[test]
fn syntax_diagnostics_are_reported() {
    let error = infer("my broken =", "broken.yu").unwrap_err();
    assert!(error.contains("syntax diagnostics"));
    assert!(error.contains("bytes "));
}

#[test]
fn unicode_byte_spans_use_character_columns_and_safe_excerpts() {
    let source = "αβ\nγ = δ";
    assert_eq!(location(source, &(10..12)), "2:5 (bytes 10..12)\n  γ = δ");
    assert!(location(source, &(1..2)).starts_with("1:1"));
    assert!(location(source, &(100..200)).contains("γ = δ"));
}

#[test]
fn effects_remain_observed_without_inventing_an_empty_operand() {
    let output = infer(include_str!("../examples/effects.yu"), "effects.yu").unwrap();
    assert!(output.contains("definition lookup:"));
    assert!(output.contains("opaque effect operand (contents unavailable)"));
}

#[test]
fn file_and_help_entrypoints_are_runnable() {
    let binary = env!("CARGO_BIN_EXE_yu-playground");
    assert!(
        Command::new(binary)
            .arg("--help")
            .output()
            .unwrap()
            .status
            .success()
    );
    let result = Command::new(binary)
        .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/examples/identity.yu"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn intrusion_flag_observes_actual_source_associations() {
    let source = include_str!("../examples/nested-recursion.yu");
    assert!(
        !infer(source, "loop.yu")
            .unwrap()
            .contains("Retained intrusion state")
    );
    let output = infer_with_intrusion(source, "loop.yu", true).unwrap();
    assert!(output.contains("Retained intrusion state (not a chronological trace)"));
    assert!(output.contains("pending consumed="));
    assert!(output.contains("same_scc=true"));
    assert!(output.contains("at retained call-tail occurrence "));
    assert!(output.contains("module loop"));
    assert!(output.contains("local helper"));
    assert!(
        output.contains("  pair "),
        "nested source calls retain actual extrusion parent/copy pairs"
    );
    assert!(output.contains("target_level="));
    assert!(output.contains("  group "));
    assert!(!output.contains("source span unavailable"));
    let result = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .arg("--intrusion")
        .arg(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/nested-recursion.yu"
        ))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(
        String::from_utf8(result.stdout)
            .unwrap()
            .contains("Retained intrusion state")
    );
}

#[test]
fn conflicts_also_withhold_intrusion_observations() {
    let error = infer_with_intrusion(
        include_str!("../examples/type-error.yu"),
        "conflict.yu",
        true,
    )
    .unwrap_err();
    assert!(error.contains("candidate type conflicts"));
    assert!(!error.contains("Retained intrusion state"));
}

#[test]
fn aggregate_output_limit_withholds_all_cli_output() {
    // Twenty small calls keep solver work small. A long source line makes
    // their authentic excerpts exercise the shared output byte budget.
    let mut source = String::from("my id x = x;");
    for index in 0..20 {
        source.push_str(&format!(" my client{index} x = id x;"));
    }
    source.push_str(&" ".repeat(60_000));
    source.push('\n');
    assert!(source.len() < INPUT_CAP);
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--intrusion", "-"])
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
    let result = child.wait_with_output().unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    assert!(
        String::from_utf8(result.stderr)
            .unwrap()
            .contains("tool output cap exceeded")
    );
}
