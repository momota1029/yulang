use std::{
    io::Write,
    process::{Command, Stdio},
    sync::Arc,
};
use yu_hir::shadow::{
    LocalSourceForm, SourceOperationId, SourceOperationResolution, lower_module_with_local_source,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports, SourceRootId};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

const CONTROL: &str =
    "act signal:\n    our ping: () -> int\nmy main = catch 7 { signal::ping(), k -> 9 }";
const OUTSIDE: &str =
    "act signal:\n    our ping: () -> int\nmy main = catch 7 { signal::ping(), k -> 9, value -> signal::ping() }";

struct Case {
    hir: Arc<HirModule>,
    machine: Machine,
    ping: SourceOperationId,
}

fn case(source: &str) -> Case {
    let text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        text.clone(),
        Arc::new(scan_header(text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "cli-value-arm-outside",
                "test.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");
    let ping = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|family| &family.operations)
        .find(|operation| operation.spelling.as_ref() == "ping")
        .expect("source declaration owns ping")
        .id
        .clone();
    let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
    let selected = program.definition_named("main").unwrap();
    let roots = program.execution_roots().unwrap();
    let machine = program.start(selected, &roots).unwrap();
    Case { hir, machine, ping }
}

fn run_stdin(source: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", "10000", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(source.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn normal_value_arm_runs_after_shallow_handler_exit() {
    assert_eq!(CONTROL.len(), 80);
    assert!(!CONTROL.ends_with('\n'));
    assert_eq!(OUTSIDE.len(), 105);
    assert!(!OUTSIDE.ends_with('\n'));

    let mut control = case(CONTROL);
    let control_outcome = control.machine.run(10_000);
    let RuntimeOutcome::Completed(value) = control_outcome else {
        panic!("control normal return must complete: {control_outcome:?}");
    };
    let RuntimeValueKind::Integer(value) = &control.machine.value(value).unwrap().kind else {
        panic!("control result must be an integer");
    };
    assert_eq!(value.as_ref(), "7");

    let mut outside = case(OUTSIDE);
    let RuntimeOutcome::UnhandledRequest {
        source: site,
        operation,
        payload,
        continuation,
        ..
    } = outside.machine.run(10_000)
    else {
        panic!("outside Value arm must publish its request");
    };
    assert_eq!(operation, outside.ping);
    assert_eq!(site.range, 101..103);
    assert_eq!(&OUTSIDE[site.range.clone()], "()");
    let main = outside
        .hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "main" => {
                Some(binding.definition_root().clone())
            }
            _ => None,
        })
        .expect("main definition remains in the same HIR");
    assert_eq!(site.source_root, SourceRootId::Definition(main.clone()));
    let local = outside
        .hir
        .local_source_for(&SourceRootId::Definition(main))
        .unwrap()
        .unwrap();
    let apply = local
        .expressions()
        .iter()
        .find(|expression| {
            expression.occurrence == site.occurrence && expression.range == site.range
        })
        .expect("request site is the authentic LocalSource Apply");
    let LocalSourceForm::Apply {
        callee,
        argument,
        source_form: SyntaxKind::CallTail,
    } = &apply.form
    else {
        panic!("empty call source must remain its original CallTail Apply");
    };
    let LocalSourceForm::Operation {
        resolution: SourceOperationResolution::Resolved(declaration),
    } = &local.expression(callee).expect("Apply retains its source callee").form
    else {
        panic!("CallTail callee must retain the resolved operation");
    };
    assert_eq!(declaration.id, outside.ping);
    assert!(matches!(
        &local.expression(argument).unwrap().form,
        LocalSourceForm::Unit
    ));
    let RuntimeValueKind::Unit = &outside.machine.value(payload).unwrap().kind else {
        panic!("zero-argument operation payload must be Unit");
    };
    let depth = outside
        .machine
        .continuation_depth(continuation)
        .expect("unhandled request retains its continuation");
    assert!(depth > 0, "the saved continuation remains live");

    let control_cli = run_stdin(CONTROL);
    assert!(
        control_cli.status.success(),
        "control CLI failed: {}",
        String::from_utf8_lossy(&control_cli.stderr)
    );
    assert_eq!(control_cli.stdout, b"7\n");
    assert!(control_cli.stderr.is_empty());

    let outside_cli = run_stdin(OUTSIDE);
    assert!(!outside_cli.status.success());
    assert!(outside_cli.stdout.is_empty());
    assert_eq!(
        outside_cli.stderr,
        b"unhandled runtime request at 101..103\n"
    );
}
