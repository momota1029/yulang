use std::{
    io::Write,
    process::{Command, Stdio},
    sync::Arc,
};
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{
    FileId, FileKey, HirItem, HirModule, LocalSourceForm, ModuleIdentity, SemanticImports,
    SourceOperationResolution, SourceRootId,
};
use yu_playground::runtime::{
    ExecutionRoot, Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeValueKind,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const NEGATIVE: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\ncatch io::tick 7 { io::other(p), _ -> 99 }; catch io::other 23 { io::other(q), _ -> q }; my main = 7";
const POSITIVE: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\ncatch io::tick 7 { io::tick(p), _ -> 99 }; catch io::other 23 { io::other(q), _ -> q }; my main = 7";

struct Case {
    hir: Arc<HirModule>,
    machine: Machine,
    operation_ids: Vec<(Box<str>, SourceOperationId)>,
    roots: Vec<yu_playground::runtime::ExpressionExecutionRoot>,
}

fn case(source: &str) -> Case {
    let source_text: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        source_text.clone(),
        Arc::new(scan_header(source_text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "cli-outward-root-suffix",
                "test.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let operation_ids = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|family| &family.operations)
        .map(|operation| (operation.spelling.clone(), operation.id.clone()))
        .collect();
    let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
    let roots = program.execution_roots().unwrap();
    let expression_roots: Vec<_> = roots
        .iter()
        .filter_map(|root| match root {
            ExecutionRoot::Expression(root) => Some(root.clone()),
            ExecutionRoot::Definition(_) => None,
        })
        .collect();
    let source_expression_roots: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Expression(expression) => Some(
                hir.expression_root(expression.occurrence())
                    .unwrap()
                    .unwrap()
                    .clone(),
            ),
            _ => None,
        })
        .collect();
    assert_eq!(
        expression_roots
            .iter()
            .map(|root| root.source_root().clone())
            .collect::<Vec<_>>(),
        source_expression_roots
    );
    assert_eq!(expression_roots.len(), 2);
    let machine = program
        .start(program.definition_named("main").unwrap(), &roots)
        .unwrap();
    Case {
        hir,
        machine,
        operation_ids,
        roots: expression_roots,
    }
}

fn run_stdin(source: &str) -> std::process::Output {
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
fn outward_request_preserves_the_live_second_root_and_cli_observation() {
    let mut positive = case(POSITIVE);
    let positive_outcome = positive.machine.run(30_000);
    let RuntimeOutcome::Completed(value) = positive_outcome else {
        panic!("positive roots must complete before selected main: {positive_outcome:?}");
    };
    let RuntimeValueKind::Integer(value) = &positive.machine.value(value).unwrap().kind else {
        panic!("positive selected result must be an integer");
    };
    assert_eq!(value.as_ref(), "7");
    let positive_cli = run_stdin(POSITIVE);
    assert!(
        positive_cli.status.success(),
        "positive CLI failed: {}",
        String::from_utf8_lossy(&positive_cli.stderr)
    );
    assert_eq!(positive_cli.stdout, b"7\n");
    assert!(positive_cli.stderr.is_empty());

    let mut negative = case(NEGATIVE);
    let RuntimeOutcome::UnhandledRequest {
        source,
        operation,
        payload,
        continuation,
        ..
    } = negative.machine.run(30_000)
    else {
        panic!("the unmatched first root must forward its request");
    };
    assert_eq!(
        operation,
        negative
            .operation_ids
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    let RuntimeValueKind::Integer(payload_value) = &negative.machine.value(payload).unwrap().kind
    else {
        panic!("forwarded payload must remain an integer");
    };
    assert_eq!(payload_value.as_ref(), "7");
    assert_eq!(
        source.source_root,
        SourceRootId::Expression(negative.roots[0].source_root().clone())
    );
    let owning_source = negative
        .hir
        .local_source_for(&source.source_root)
        .unwrap()
        .unwrap();
    let original_operation = owning_source
        .expressions()
        .iter()
        .find(|expression| expression.occurrence == source.occurrence)
        .expect("request source occurrence must belong to the authentic HIR source");
    assert_eq!(original_operation.range, source.range);
    let LocalSourceForm::Apply { callee, .. } = &original_operation.form else {
        panic!("request source occurrence must be the original Apply");
    };
    let callee = owning_source.expression(callee).unwrap();
    let LocalSourceForm::Operation {
        resolution: SourceOperationResolution::Resolved(declaration),
    } = &callee.form
    else {
        panic!("original Apply callee must resolve to its declared operation");
    };
    assert_eq!(
        declaration.id,
        negative
            .operation_ids
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    assert!(negative.machine.continuation_depth(continuation).unwrap() > 0);

    let diagnostic = format!("unhandled runtime request at {:?}", source.range);
    let negative_cli = run_stdin(NEGATIVE);
    assert!(!negative_cli.status.success());
    assert!(negative_cli.stdout.is_empty());
    assert_eq!(
        String::from_utf8(negative_cli.stderr).unwrap(),
        format!("{diagnostic}\n")
    );
}
