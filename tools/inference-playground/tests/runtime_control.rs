use std::{
    io::Write,
    process::{Command, Stdio},
    sync::Arc,
};
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const DECL: &str = "act signal:\n    our ping: () -> int\n";

fn machine(source: &str) -> (Machine, Option<SourceOperationId>) {
    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("runtime-control", "test.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let ping = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|declaration| &declaration.operations)
        .find(|operation| operation.spelling.as_ref() == "ping")
        .map(|operation| operation.id.clone());
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
    let selected = program.definition_named("main").unwrap();
    let roots = program.execution_roots().unwrap();
    (program.start(selected, &roots).unwrap(), ping)
}

fn assert_integer(source: &str, expected: &str) {
    let (mut machine, _) = machine(source);
    let RuntimeOutcome::Completed(value) = machine.run(10_000) else {
        panic!("expected a completed normal return");
    };
    let RuntimeValueKind::Integer(actual) = &machine.value(value).unwrap().kind else {
        panic!("expected an integer result");
    };
    assert_eq!(actual.as_ref(), expected);
}

fn assert_unhandled(source: &str, computation_payload: bool) {
    let (mut machine, ping) = machine(source);
    let outcome = machine.run(10_000);
    let RuntimeOutcome::UnhandledRequest {
        source: site,
        operation,
        payload,
        continuation,
        ..
    } = outcome
    else {
        panic!("expected an unhandled request, got {outcome:?}");
    };
    assert_eq!(Some(operation), ping);
    assert!(site.range.start < site.range.end);
    assert!(site.range.end <= source.len());
    let payload = &machine.value(payload).unwrap().kind;
    if computation_payload {
        assert!(matches!(payload, RuntimeValueKind::Computation));
    } else {
        assert!(matches!(payload, RuntimeValueKind::Unit));
    }
    assert!(machine.continuation_depth(continuation).is_some());
}

#[test]
fn operation_request_retains_resolved_identity_payload_and_continuation() {
    assert_unhandled(&format!("{DECL}my main = signal::ping()"), false);
}

#[test]
fn value_only_catch_forwards_an_operation_request() {
    assert_unhandled(
        &format!("{DECL}my main = catch signal::ping() {{ value -> value }}"),
        false,
    );
}

#[test]
fn matching_operation_catch_requires_handler_evidence() {
    let source = format!("{DECL}my main = catch signal::ping() {{ signal::ping(), k -> 9 }}");
    let (mut machine, _) = machine(&source);
    assert!(matches!(
        machine.run(10_000),
        RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
    ));
}

#[test]
fn normal_return_catch_binds_its_value() {
    assert_integer("my main = catch 7 { value -> value }", "7");
}

#[test]
fn wildcard_normal_return_arm_runs_its_body() {
    assert_integer("my main = catch 7 { _ -> 9 }", "9");
}

#[test]
fn operation_only_catch_preserves_normal_return() {
    assert_integer(
        &format!("{DECL}my main = catch 7 {{ signal::ping(), k -> 9 }}"),
        "7",
    );
}

#[test]
fn normal_return_arm_executes_outside_the_catch() {
    assert_unhandled(
        &format!("{DECL}my main = catch 7 {{ signal::ping(), k -> 9, value -> signal::ping() }}"),
        false,
    );
}

#[test]
fn different_operation_in_the_same_family_does_not_match() {
    let source = "act signal:\n    our ping: () -> int\n    our pong: () -> int\n\
                  my main = catch signal::ping() { signal::pong(), k -> 9 }";
    assert_unhandled(source, false);
}

#[test]
fn value_payload_consumes_fuel_before_publishing_a_request() {
    let source = "act signal:\n    our ping: int -> int\n\
                  my main = { my loop x = loop x; signal::ping(loop ()) }";
    let (mut machine, _) = machine(source);
    assert!(matches!(
        machine.run(1_000),
        RuntimeOutcome::ResourceExhausted { .. }
    ));
}

#[test]
fn computation_payload_is_published_without_running_it() {
    let source = "act signal:\n    our ping: [] int -> int\n\
                  my main = { my loop x = loop x; signal::ping(loop ()) }";
    assert_unhandled(source, true);
}

#[test]
fn cli_unhandled_request_withholds_output() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "1000", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(format!("{DECL}my main = signal::ping()").as_bytes())
        .unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(!result.status.success());
    assert!(result.stdout.is_empty());
    let error = String::from_utf8(result.stderr).unwrap();
    assert!(error.contains("unhandled runtime request"), "{error}");
}

#[test]
fn catch_string_spelling_preserves_content_inside_its_delimiters() {
    for source in [
        r#"my main = catch " a\nb " { value -> value }"#,
        r#"my main = catch """ a\nb """ { value -> value }"#,
    ] {
        assert_eq!(
            yu_playground::execute(source, "string.yu", "main", 1_000, false).unwrap(),
            "\" a\\nb \"\n",
            "{source}",
        );
    }
}
