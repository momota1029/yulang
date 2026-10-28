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

fn machine(source: &str) -> yu_playground::runtime::Machine {
    let text: std::sync::Arc<yu_syntax::SourceText> = std::sync::Arc::from(source);
    let parsed = yu_syntax::parse_file(
        text.clone(),
        std::sync::Arc::new(yu_syntax::scan_header(text)),
        std::sync::Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
    let hir = std::sync::Arc::new(
        yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "cli-receiver-permission-machine",
                "test.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = yu_solver::shadow_apply::CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");
    let program = yu_playground::runtime::RuntimeProgram::from_hir(
        hir,
        yu_playground::runtime::RuntimeEvidence::default(),
    )
    .unwrap();
    let selected = program.definition_named("main").unwrap();
    let roots = program.execution_roots().unwrap();
    program.start(selected, &roots).unwrap()
}

#[test]
fn nested_receiver_permission_has_distinct_machine_outcomes() {
    let mut positive = machine(POSITIVE);
    let positive_outcome = positive.run(30_000);
    let yu_playground::runtime::RuntimeOutcome::Completed(value) = positive_outcome else {
        panic!("positive nested receiver must complete: {positive_outcome:?}");
    };
    let yu_playground::runtime::RuntimeValueKind::Integer(value) =
        &positive.value(value).unwrap().kind
    else {
        panic!("positive result must be an integer");
    };
    assert_eq!(value.as_ref(), "7");

    let mut negative = machine(NEGATIVE);
    assert!(matches!(
        negative.run(30_000),
        yu_playground::runtime::RuntimeOutcome::Unavailable(
            yu_playground::runtime::RuntimeUnavailable::HandlerEvidence(_)
        )
    ));
}
