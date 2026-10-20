use std::sync::Arc;
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const POSITIVE: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\nmy inner (thunk:[io] int) = catch thunk { io::other(p), _ -> p }\nmy outer (thunk:[io] int) = catch thunk { io::tick(p), k -> k 23 }\nmy main = outer (inner { my answer = io::tick 7; io::other answer })";

fn machine(source: &str) -> (Machine, SourceOperationId) {
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
                "runtime-unmatched",
                "test.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );

    // Prepare candidate inference independently before constructing the runtime.
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty(), "{source}");

    let tick = hir
        .source_effect_declarations()
        .iter()
        .flat_map(|declaration| &declaration.operations)
        .find(|operation| operation.spelling.as_ref() == "tick")
        .expect("the source declaration owns tick")
        .id
        .clone();
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
    let selected = program.definition_named("main").unwrap();
    let roots = program.execution_roots().unwrap();
    (program.start(selected, &roots).unwrap(), tick)
}

#[test]
fn resumed_suffix_reaches_inner_handler_without_reviving_expired_grant() {
    // The outer handler resumes tick with 23. The preserved suffix then
    // requests other 23, but its fresh owner has no original receiver Grant.
    let (mut resumed, _) = machine(POSITIVE);
    let outcome = resumed.run(10_000);
    let site = match outcome {
        RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(site)) => site,
        outcome => panic!(
            "expected the resumed request to stop at the inner handler, got {outcome:?}"
        ),
    };
    assert_eq!(site.range, 87..123);

    // Change only the outer operation pattern. The inner handler still misses
    // tick, leaving the declaration-owned request and its suffix observable.
    let negative_source = POSITIVE.replacen(
        "io::tick(p), k -> k 23",
        "io::other(p), k -> k 23",
        1,
    );
    assert_ne!(negative_source, POSITIVE);
    let (mut negative, declared_tick) = machine(&negative_source);
    let outcome = negative.run(10_000);
    let RuntimeOutcome::UnhandledRequest {
        operation,
        payload,
        continuation,
        ..
    } = outcome
    else {
        panic!("expected the unmatched tick request, got {outcome:?}");
    };
    assert_eq!(operation, declared_tick);
    let RuntimeValueKind::Integer(actual_payload) = &negative.value(payload).unwrap().kind else {
        panic!("expected an integer request payload");
    };
    assert_eq!(actual_payload.as_ref(), "7");
    assert!(negative.continuation_depth(continuation).unwrap() > 0);
}
