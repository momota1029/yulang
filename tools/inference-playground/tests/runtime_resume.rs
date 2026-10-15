use std::sync::Arc;
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const IO: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\n";
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
            ModuleIdentity::source_root(FileId::new(FileKey::new("runtime-resume", "test.yu"))),
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
        .flat_map(|family| &family.operations)
        .map(|operation| (operation.spelling.clone(), operation.id.clone()))
        .collect();
    let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
    let roots = program.execution_roots().unwrap();
    (
        program
            .start(program.definition_named("main").unwrap(), &roots)
            .unwrap(),
        operations,
    )
}
fn assert_integer(source: &str, expected: &str) {
    let (mut machine, _) = machine(source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("expected completion, got {outcome:?}");
    };
    let RuntimeValueKind::Integer(actual) = &machine.value(value).unwrap().kind else {
        panic!("expected integer");
    };
    assert_eq!(actual.as_ref(), expected);
}

#[test]
fn raw_response_enters_the_hole_under_the_still_active_containing_owner() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 9 }}\nmy main = relay {{ my result = io::tick 7; result }}"
        ),
        "9",
    );
}

#[test]
fn reusable_raw_context_writes_its_original_pending_local_cell() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> {{ my first = k 11; k 23 }} }}\nmy main = relay {{ my result = io::tick 7; result }}"
        ),
        "23",
    );
}

#[test]
fn inner_owner_completion_runs_the_outer_effectful_suffix_without_reinstalling_selection() {
    let source = format!(
        "{IO}my inner ignored = io::tick 7\nmy outer ignored = {{ my first = inner(); io::other first }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 11 }}\nmy main = relay (outer())"
    );
    let (mut machine, operations) = machine(&source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::UnhandledRequest {
        operation, payload, ..
    } = outcome
    else {
        panic!("expected shallow suffix request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "other")
            .unwrap()
            .1
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("expected integer payload");
    };
    assert_eq!(payload.as_ref(), "11");
}

#[test]
fn forwarded_handler_reentry_runs_its_normal_value_arm_before_parent_completion() {
    assert_integer(
        &format!(
            "{IO}my helper (input:[io] int) = catch input {{ io::other(p), _ -> 99, value -> 23 }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 11 }}\nmy main = relay (helper (io::tick 7))"
        ),
        "23",
    );
}

#[test]
fn response_expression_is_forced_once_before_entering_the_saved_context() {
    assert_integer(
        &format!(
            "{IO}my answer (pending:[io] int) = catch pending {{ io::other(p), j -> j p }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> answer (k (io::other 11)) }}\nmy main = relay (io::tick 7)"
        ),
        "11",
    );
}

#[test]
fn recapture_after_inner_completion_retains_the_entire_remaining_resume_context() {
    assert_integer(
        &format!(
            "{IO}my inner ignored = io::tick 7\nmy outer ignored = {{ my first = inner(); io::other first }}\nmy answer (pending:[io] int) = catch pending {{ io::other(p), j -> j 23 }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> answer (k 11) }}\nmy main = relay (outer())"
        ),
        "23",
    );
}

#[test]
fn fresh_owner_reentry_does_not_resurrect_an_expired_receivers_grant() {
    let source = format!(
        "{IO}my helper (input:[io] int) = catch input {{ io::other(p), _ -> 99 }}\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 11 }}\nmy main = relay (helper {{ my first = io::tick 7; io::other first }})"
    );
    let (mut machine, _) = machine(&source);
    let outcome = machine.run(30_000);
    assert!(
        matches!(
            outcome,
            RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
        ),
        "{outcome:?}"
    );
}

#[test]
fn captured_definition_materialization_keeps_its_separate_decision_gate_open() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k p }}\nmy main = relay later\nmy later = io::tick 7"
    );
    let (mut machine, _) = machine(&source);
    let outcome = machine.run(30_000);
    assert!(
        matches!(
            outcome,
            RuntimeOutcome::Unavailable(RuntimeUnavailable::ContinuationMaterialization(_))
        ),
        "{outcome:?}"
    );
}

#[test]
fn raw_response_uses_the_declared_boolean_response_type() {
    let source = "act signal:\n    our choose: () -> bool\nmy relay (thunk:[signal] int) = catch thunk { signal::choose(), k -> k true }\nmy main = relay { my choice = signal::choose(); if choice: 7 else: 9 }";
    assert_integer(source, "7");
}
