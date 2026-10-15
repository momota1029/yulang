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
    let (machine, operations, _) = machine_with_hir(source);
    (machine, operations)
}
fn machine_with_hir(
    source: &str,
) -> (
    Machine,
    Vec<(Box<str>, SourceOperationId)>,
    Arc<yu_hir::HirModule>,
) {
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
    let program = RuntimeProgram::from_hir(hir.clone(), RuntimeEvidence::default()).unwrap();
    let roots = program.execution_roots().unwrap();
    (
        program
            .start(program.definition_named("main").unwrap(), &roots)
            .unwrap(),
        operations,
        hir,
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
fn forward_initializer_request_does_not_enter_the_name_callers_handler() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k p }}\nmy main = relay later\nmy later = io::tick 7"
    );
    // This reproduces the low-level initializer boundary. It is not a valid
    // source cache/Resume witness, an initialization-order result, or A/B closure.
    let (mut machine, operations, hir) = machine_with_hir(&source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::UnhandledRequest {
        operation,
        payload,
        source: site,
        ..
    } = outcome
    else {
        panic!("expected initializer request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    let definition = hir
        .items()
        .iter()
        .find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "later" => {
                Some(binding)
            }
            _ => None,
        })
        .unwrap();
    let carrier = hir
        .local_source(definition.definition_root())
        .unwrap()
        .unwrap();
    let application = carrier.expression(carrier.body()).unwrap();
    assert_eq!(
        site.source_root.definition_root(),
        Some(definition.definition_root())
    );
    assert_eq!(site.occurrence, application.occurrence);
    assert_eq!(site.range, application.range);
    assert_eq!(
        hir.occurrence_source_key(&site.occurrence).unwrap(),
        Some(&application.source)
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("integer payload");
    };
    assert_eq!(payload.as_ref(), "7");
}

#[test]
fn raw_response_uses_the_declared_boolean_response_type() {
    let source = "act signal:\n    our choose: () -> bool\nmy relay (thunk:[signal] int) = catch thunk { signal::choose(), k -> k true }\nmy main = relay { my choice = signal::choose(); if choice: 7 else: 9 }";
    assert_integer(source, "7");
}

#[test]
fn initializer_internal_handler_can_resume_before_publishing_its_value() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 19 }}\nmy main = {{ my value = later; value }}\nmy later = relay (io::tick 7)"
        ),
        "19",
    );
}

#[test]
fn nested_initializer_request_does_not_enter_the_outer_initializers_name_handler() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 99 }}\nmy main = relay outer\nmy outer = relay inner\nmy inner = io::tick 7"
    );
    let (mut machine, operations, hir) = machine_with_hir(&source);
    let outcome = machine.run(30_000);
    let RuntimeOutcome::UnhandledRequest {
        operation,
        payload,
        source: site,
        ..
    } = outcome
    else {
        panic!("expected inner initializer request, got {outcome:?}");
    };
    assert_eq!(
        operation,
        operations
            .iter()
            .find(|(name, _)| name.as_ref() == "tick")
            .unwrap()
            .1
    );
    let definition = hir
        .items()
        .iter()
        .find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "inner" => {
                Some(binding)
            }
            _ => None,
        })
        .unwrap();
    let carrier = hir
        .local_source(definition.definition_root())
        .unwrap()
        .unwrap();
    let application = carrier.expression(carrier.body()).unwrap();
    assert_eq!(
        site.source_root.definition_root(),
        Some(definition.definition_root())
    );
    assert_eq!(site.occurrence, application.occurrence);
    assert_eq!(site.range, application.range);
    assert_eq!(
        hir.occurrence_source_key(&site.occurrence).unwrap(),
        Some(&application.source)
    );
    let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
        panic!("integer payload");
    };
    assert_eq!(payload.as_ref(), "7");
}

#[test]
fn forward_function_initialization_finishes_before_its_latent_request_uses_the_caller_handler() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> k 29 }}\nmy main = relay (later())\nmy later ignored = io::tick 7"
        ),
        "29",
    );
}

#[test]
fn initializer_internal_handler_can_discard_the_request_before_publication() {
    assert_integer(
        &format!(
            "{IO}my main = {{ my value = later; value }}\nmy later = catch io::tick 7 {{ io::tick(p), _ -> 17 }}"
        ),
        "17",
    );
}
