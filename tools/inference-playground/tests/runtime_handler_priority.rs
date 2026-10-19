use std::sync::Arc;
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const IO: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\n";
const NESTED: &str = "my inner (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::tick 11, io::tick(p), _ -> io::tick 23 }\nmy outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }\nmy main = outer (inner (io::tick 7))";

fn machine(source: &str) -> (Machine, Vec<(Box<str>, SourceOperationId)>) {
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
                "runtime-handler-priority",
                "test.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");
    let operations = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|declaration| &declaration.operations)
        .map(|operation| (operation.spelling.clone(), operation.id.clone()))
        .collect();
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
    let selected = program.definition_named("main").unwrap();
    let roots = program.execution_roots().unwrap();
    (program.start(selected, &roots).unwrap(), operations)
}

fn assert_completed_integer(source: &str, expected: &str) {
    let (mut machine, _) = machine(source);
    let outcome = machine.run(10_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("expected completion, got {outcome:?}");
    };
    let RuntimeValueKind::Integer(actual) = &machine.value(value).unwrap().kind else {
        panic!("expected integer");
    };
    assert_eq!(actual.as_ref(), expected);
}

#[test]
fn nested_handler_priority_and_shallow_arm_requests() {
    let exact = format!("{IO}{NESTED}");
    assert_completed_integer(&exact, "11");

    let swapped_arms = exact.replacen(
        "io::tick(p), _ -> io::tick 11, io::tick(p), _ -> io::tick 23",
        "io::tick(p), _ -> io::tick 23, io::tick(p), _ -> io::tick 11",
        1,
    );
    assert_ne!(swapped_arms, exact);
    assert_completed_integer(&swapped_arms, "23");

    let mismatched_outer = exact.replacen(
        "my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }",
        "my outer (thunk:[io] int) = catch thunk { io::other(p), _ -> p }",
        1,
    );
    assert_ne!(mismatched_outer, exact);
    let (mut machine, operations) = machine(&mismatched_outer);
    let outcome = machine.run(10_000);
    let RuntimeOutcome::UnhandledRequest {
        source,
        operation,
        payload,
        ..
    } = outcome
    else {
        panic!("expected outward tick request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("expected integer payload");
    };
    assert_eq!(payload.as_ref(), "11");

    let initial_request = mismatched_outer.find("io::tick 7").unwrap();
    let inner_request = mismatched_outer.rfind("io::tick 11").unwrap();
    let expected_site = inner_request + "io".len()..inner_request + "io::tick 11".len();
    assert_ne!(source.range, initial_request..initial_request + "io::tick 7".len());
    assert_eq!(source.range, expected_site);
    assert_eq!(&mismatched_outer[source.range], "::tick 11");
}
