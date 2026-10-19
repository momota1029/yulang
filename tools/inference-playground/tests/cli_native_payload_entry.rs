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

const VALUE_SOURCE: &str =
    "act signal:\n    our ping: int -> int\nmy main = { my loop x = loop x; signal::ping(loop ()) }";
const COMPUTATION_SOURCE: &str =
    "act signal:\n    our ping: [] int -> int\nmy main = { my loop x = loop x; signal::ping(loop ()) }";

struct ApplyEvidence {
    source_root: SourceRootId,
    occurrence: yu_hir::HirOccurrenceId,
    range: std::ops::Range<usize>,
    operation: SourceOperationId,
}
struct Case {
    hir: Arc<HirModule>,
    machine: Machine,
    ping: SourceOperationId,
    apply: ApplyEvidence,
}

fn case(source: &str, expected_range: std::ops::Range<usize>) -> Case {
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
                "cli-native-payload-entry",
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
        .expect("source owns the ping declaration")
        .id
        .clone();
    let main = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "main" => {
                Some(binding.definition_root().clone())
            }
            _ => None,
        })
        .expect("source owns main");
    let source_root = SourceRootId::Definition(main.clone());
    let local = hir.local_source_for(&source_root).unwrap().unwrap();
    let apply = local
        .expressions()
        .iter()
        .find(|expression| {
            expression.range == expected_range
                && matches!(
                    &expression.form,
                    LocalSourceForm::Apply {
                        source_form: SyntaxKind::CallTail,
                        ..
                    }
                )
        })
        .expect("the expected call tail is an authentic LocalSource Apply");
    let LocalSourceForm::Apply {
        callee,
        source_form: SyntaxKind::CallTail,
        ..
    } = &apply.form
    else {
        unreachable!()
    };
    let LocalSourceForm::Operation {
        resolution: SourceOperationResolution::Resolved(declaration),
    } = &local.expression(callee).unwrap().form
    else {
        panic!("the CallTail callee must be the resolved source operation");
    };
    assert_eq!(declaration.id, ping);
    let apply_evidence = ApplyEvidence {
        source_root,
        occurrence: apply.occurrence.clone(),
        range: apply.range.clone(),
        operation: declaration.id.clone(),
    };
    let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
    let selected = program.definition_named("main").unwrap();
    let roots = program.execution_roots().unwrap();
    let machine = program.start(selected, &roots).unwrap();
    Case {
        hir,
        machine,
        ping,
        apply: apply_evidence,
    }
}

fn run_stdin(source: &str, steps: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_yu-playground"))
        .args(["--run", "main", "--steps", steps, "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(source.as_bytes()).unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn native_operation_payload_role_controls_publication() {
    assert_eq!(VALUE_SOURCE.len(), 92);
    assert!(!VALUE_SOURCE.ends_with('\n'));
    assert_eq!(COMPUTATION_SOURCE.len(), 95);
    assert!(!COMPUTATION_SOURCE.ends_with('\n'));

    let mut value_case = case(VALUE_SOURCE, 81..90);
    assert_eq!(value_case.apply.range, 81..90);
    assert_eq!(value_case.apply.source_root, value_case.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "main" => Some(SourceRootId::Definition(binding.definition_root().clone())),
        _ => None,
    }).unwrap());
    assert_eq!(value_case.apply.operation, value_case.ping);
    assert!(matches!(
        value_case.machine.run(1_000),
        RuntimeOutcome::ResourceExhausted { steps: 1_000 }
    ));

    let mut computation_case = case(COMPUTATION_SOURCE, 84..93);
    assert_eq!(computation_case.apply.range, 84..93);
    assert_eq!(computation_case.apply.operation, computation_case.ping);
    let RuntimeOutcome::UnhandledRequest {
        source,
        operation,
        payload,
        continuation,
        ..
    } = computation_case.machine.run(10_000)
    else {
        panic!("Computation argument must publish the outer ping request");
    };
    assert_eq!(operation, computation_case.ping);
    assert_eq!(source.source_root, computation_case.apply.source_root);
    assert_eq!(source.occurrence, computation_case.apply.occurrence);
    assert_eq!(source.range, computation_case.apply.range);
    let RuntimeValueKind::Computation = &computation_case.machine.value(payload).unwrap().kind else {
        panic!("native computation payload must remain unforced");
    };
    let depth = computation_case
        .machine
        .continuation_depth(continuation)
        .expect("unhandled request retains a continuation");
    assert!(depth > 0);

    let value_cli = run_stdin(VALUE_SOURCE, "1000");
    assert!(!value_cli.status.success());
    assert!(value_cli.stdout.is_empty());
    assert_eq!(
        value_cli.stderr,
        b"runtime step budget exhausted after 1000 steps; no completed result\n"
    );

    let computation_cli = run_stdin(COMPUTATION_SOURCE, "10000");
    assert!(!computation_cli.status.success());
    assert!(computation_cli.stdout.is_empty());
    assert_eq!(
        computation_cli.stderr,
        b"unhandled runtime request at 84..93\n"
    );
}
