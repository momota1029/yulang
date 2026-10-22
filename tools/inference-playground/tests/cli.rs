use std::{
    io::Write,
    process::{Command, Stdio},
};
use yu_playground::{INPUT_CAP, infer, infer_with_intrusion, location, read_source};

fn cli(source: &str) -> std::process::Output {
    cli_with_args(source, &[])
}

fn cli_with_args(source: &str, args: &[&str]) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(args)
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
fn constant_conditions_observe_both_branch_leaves() {
    let source = include_str!("../examples/conditional-union.yu");
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(output.contains("definition mixed:"));
        assert!(output.contains("IntPositive"));
        assert!(output.contains("StrPositive"));
        assert!(output.contains(" <: "));
        assert!(output.contains("no principal-type"));
    }
}

#[test]
fn catch_value_binder_observes_both_conditional_results() {
    let source = include_str!("../examples/catch-value.yu");
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(output.contains("definition mixed:"));
        assert!(output.contains("IntPositive"));
        assert!(output.contains("StrPositive"));
        assert!(output.contains("no principal-type"));
    }
}

#[test]
fn catch_value_conflicts_withhold_cli_observations() {
    let source = "my mixed: int = catch (if true: 1 else: \"str\") { value -> value }";
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"));
        assert!(!error.contains("unsupported source"));
    }
}

#[test]
fn operation_catch_binds_payload_and_raw_continuation() {
    let result = cli(include_str!("../examples/catch-operation.yu"));
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output = String::from_utf8(result.stdout).unwrap();
    assert!(output.contains("definition handled:"));
    assert!(output.contains("StrPositive"));
    assert!(output.contains("no principal-type"));
}

#[test]
fn operation_catch_checks_payload_and_response_types() {
    let source = include_str!("../examples/catch-operation.yu");
    for source in [
        source.replace("checked: int", "checked: str"),
        source.replace("resume \"resumed\"", "resume true"),
    ] {
        let result = cli(&source);
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"), "{error}");
        assert!(!error.contains("unsupported source"));
    }
}

#[test]
fn conditional_conflicts_withhold_all_cli_observations() {
    let source = include_str!("../examples/conditional-conflict.yu");
    for source in [source.to_owned(), source.replace("if true:", "if false:")] {
        let result = cli(&source);
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"));
        assert!(!error.contains("unsupported source"));
        assert!(!error.contains("definition mixed:"));
    }
    let result = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .arg("--intrusion")
        .arg(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/conditional-conflict.yu"
        ))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("candidate type conflicts"), "unexpected --intrusion stderr: {error}");
    assert!(!error.contains("Retained intrusion state"));
}

#[test]
fn discarded_expression_conflicts_withhold_all_cli_modes() {
    for (source, location, conditional) in [
        (
            "if 1: 1 else: 2;\nmy main = 7",
            " at 1:",
            "if 1: 1 else: 2;",
        ),
        (
            "my main = 7;\nif 1: 1 else: 2",
            " at 2:",
            "if 1: 1 else: 2",
        ),
    ] {
        for args in [&[][..], &["--intrusion"][..], &["--run", "main"][..]] {
            let result = cli_with_args(source, args);
            assert!(
                !result.status.success(),
                "CLI mode {args:?} accepted: {source}"
            );
            assert!(
                result.stdout.is_empty(),
                "CLI mode {args:?} exposed stdout: {source}"
            );
            let error = String::from_utf8(result.stderr).unwrap();
            assert!(
                error.contains("candidate type conflicts"),
                "CLI mode {args:?}: {error}"
            );
            assert!(error.contains(location), "CLI mode {args:?}: {error}");
            assert!(
                error.contains(&format!("\n  {conditional}")),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("source span unavailable"),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("unsupported source"),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("Retained intrusion state"),
                "CLI mode {args:?}: {error}"
            );
            assert!(
                !error.contains("definition main:"),
                "CLI mode {args:?}: {error}"
            );
        }
    }
}

#[test]
fn expression_only_modules_are_checked_before_no_binding_output() {
    let valid = r"(\x -> x) 1;
if true: true else: false";
    let invalid = r"(\x -> x) 1;
if 1: true else: false";

    for args in [&[][..], &["--intrusion"][..]] {
        let result = cli_with_args(valid, args);
        assert!(
            result.status.success(),
            "CLI mode {args:?}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        let output = String::from_utf8(result.stdout).unwrap();
        assert!(
            output.contains("No binding exports in this source."),
            "CLI mode {args:?}: {output}"
        );
        assert!(
            !output.contains("definition "),
            "CLI mode {args:?}: {output}"
        );

        let result = cli_with_args(invalid, args);
        assert!(!result.status.success(), "CLI mode {args:?} accepted conflict");
        assert!(result.stdout.is_empty(), "CLI mode {args:?} exposed stdout");
        let error = String::from_utf8(result.stderr).unwrap();
        assert!(error.contains("candidate type conflicts"), "{error}");
        assert!(error.contains(" at 2:"), "{error}");
        assert!(
            error.contains("\n  if 1: true else: false"),
            "{error}"
        );
        assert!(!error.contains("unsupported source"), "{error}");
        assert!(!error.contains("No binding exports"), "{error}");
    }
}

#[test]
fn boolean_and_string_consumers_accept_matching_literals() {
    let result = cli("my bool_id (x:bool) = x; my str_id (x:str) = x; \
         my boolean = bool_id false; my string = str_id \"str\"");
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let output = String::from_utf8(result.stdout).unwrap();
    let boolean = output
        .split("definition boolean:\n")
        .nth(1)
        .unwrap()
        .split("\ndefinition ")
        .next()
        .unwrap();
    assert!(boolean.contains("BoolPositive"));
    let string = output.split("definition string:\n").nth(1).unwrap();
    assert!(string.contains("StrPositive"));
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
fn intrusion_expression_calls_keep_original_spans_and_local_names() {
    let cases = [
        (
            "id 1; my id x = x; my main = 7",
            "id 1",
            "module id",
        ),
        (
            "{ my helper x = x; helper 1 }; my main = 7",
            "helper 1",
            "local helper",
        ),
    ];

    for (source, call, expected_label) in cases {
        let output = infer_with_intrusion(source, "expression-intrusion.yu", true).unwrap();
        assert!(output.contains("Retained intrusion state (not a chronological trace)"));
        assert!(output.contains("  event "), "retained event missing: {output}");
        assert!(output.contains("origin=v"), "expression origin missing: {output}");
        assert!(
            output.contains("(expression value, SCC "),
            "expression-origin label missing: {output}"
        );
        assert!(
            output.contains(expected_label),
            "receiver source label missing: {output}"
        );
        assert!(!output.contains("source span unavailable"));

        let start = source.find(call).unwrap();
        let expected_location = format!(
            "at retained call-tail occurrence {}\n",
            location(source, &(start + call.len() - 1..start + call.len()))
        );
        assert!(
            output.contains(&expected_location),
            "original call-tail location missing: {expected_location:?}\n{output}"
        );
    }
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

#[test]
fn directional_introductions_show_exact_uses_and_provider_exclusion() {
    let source = "my apply f = f 1; my id x = x; my good = apply id";
    let output = infer_with_intrusion(source, "directional.yu", true).unwrap();
    assert!(
        output.contains("symbolic candidate evidence; not event consumption or runtime hygiene")
    );
    assert_eq!(output.matches("  introduction ").count(), 1);
    assert_eq!(output.matches("ResultEffect=").count(), 1);
    assert!(output.contains("no authenticated omitted-formal introduction"));
    assert!(
        !infer(source, "directional.yu")
            .unwrap()
            .contains("Directional introductions")
    );
    let repeated = infer_with_intrusion("my apply f = f (f 1)", "repeated.yu", true).unwrap();
    assert_eq!(repeated.matches("  introduction ").count(), 2);
}
