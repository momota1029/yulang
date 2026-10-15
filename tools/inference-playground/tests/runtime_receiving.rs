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
            ModuleIdentity::source_root(FileId::new(FileKey::new("runtime-receiving", "test.yu"))),
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
fn assert_integer(source: &str, expected: &str) {
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
fn assert_missing_evidence(source: &str) {
    let (mut machine, _) = machine(source);
    let outcome = machine.run(10_000);
    assert!(
        matches!(
            outcome,
            RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
        ),
        "{outcome:?}"
    );
}

#[test]
fn received_ground_computation_supplies_its_local_operation_grant() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), _ -> p }}\nmy main = relay (io::tick 7)"
        ),
        "7",
    );
}

#[test]
fn receiving_grant_uses_resolved_identities_under_renaming() {
    let source = "act channel:\n    our emit: int -> int\nmy accept (pending:[channel] int) = catch pending { channel::emit(item), _ -> item }\nmy main = accept (channel::emit 23)";
    assert_integer(source, "23");
}

#[test]
fn direct_formal_forwarding_preserves_the_received_root() {
    assert_integer(
        &format!(
            "{IO}my receive (input:[io] int) = catch input {{ io::tick(p), _ -> p }}\nmy forward (pending:[io] int) = receive pending\nmy main = forward (io::tick 11)"
        ),
        "11",
    );
}

#[test]
fn a_different_operation_arm_does_not_preempt_the_exact_operation() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::other(p), _ -> 99, io::tick(p), _ -> p }}\nmy main = relay (io::tick 7)"
        ),
        "7",
    );
}

#[test]
fn selected_operation_arm_runs_outside_its_shallow_handler() {
    let source = format!(
        "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), _ -> io::other p, io::other(p), _ -> 99 }}\nmy main = relay (io::tick 7)"
    );
    let (mut machine, operations) = machine(&source);
    let outcome = machine.run(10_000);
    let RuntimeOutcome::UnhandledRequest {
        operation, payload, ..
    } = outcome
    else {
        panic!("expected arm request, got {outcome:?}");
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
    assert_eq!(payload.as_ref(), "7");
}

#[test]
fn empty_written_permission_does_not_fabricate_a_local_grant() {
    assert_missing_evidence(&format!(
        "{IO}my relay (thunk:[] int) = catch thunk {{ io::tick(p), _ -> p }}\nmy main = relay (io::tick 7)"
    ));
}

#[test]
fn a_nested_helper_cannot_borrow_its_captured_formals_receiver_permission() {
    assert_missing_evidence(&format!(
        "{IO}my relay (thunk:[io] int) = {{ my helper ignored = catch thunk {{ io::tick(p), _ -> p }}; helper() }}\nmy main = relay (io::tick 7)"
    ));
}

#[test]
fn matching_continuation_binder_can_be_discarded_by_its_arm() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), k -> p }}\nmy main = relay (io::tick 7)"
        ),
        "7",
    );
}

#[test]
fn unit_payload_empty_call_pattern_selects_its_arm() {
    assert_integer(
        "act signal:\n    our ping: () -> int\nmy relay (thunk:[signal] int) = catch thunk { signal::ping(), _ -> 1 }\nmy main = relay (signal::ping())",
        "1",
    );
}

#[test]
fn empty_call_payload_pattern_is_a_wildcard_for_nonunit_values() {
    assert_integer(
        "act signal:\n    our ping: int -> int\nmy relay (thunk:[signal] int) = catch thunk { signal::ping(), _ -> 1, signal::ping(p), _ -> p }\nmy main = relay (signal::ping 7)",
        "1",
    );
}

#[test]
fn declared_boolean_and_string_payloads_select_total_arms() {
    for (ty, value) in [("bool", "true"), ("str", "\"text\"")] {
        assert_integer(
            &format!(
                "act signal:\n    our ping: {ty} -> int\nmy relay (thunk:[signal] int) = catch thunk {{ signal::ping(p), _ -> 1 }}\nmy main = relay (signal::ping {value})"
            ),
            "1",
        );
    }
}

#[test]
fn discarding_the_raw_suffix_does_not_require_an_integer_operation_response() {
    assert_integer(
        "act signal:\n    our ping: () -> bool\nmy relay (thunk:[signal] int) = catch thunk { signal::ping(), _ -> 1 }\nmy main = relay { my ignored = signal::ping(); 7 }",
        "1",
    );
}

#[test]
fn direct_runtime_construction_rejects_incompatible_primitive_payloads() {
    for (ty, value) in [
        ("int", "()"),
        ("bool", "7"),
        ("str", "true"),
        ("()", "\"text\""),
    ] {
        let source = format!(
            "act signal:\n    our ping: {ty} -> int\nmy relay (thunk:[signal] int) = catch thunk {{ signal::ping(p), _ -> p, signal::ping(), _ -> 99 }}\nmy main = relay (signal::ping {value})"
        );
        let text: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            text.clone(),
            Arc::new(scan_header(text)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(
            lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "runtime-receiving",
                    "unchecked.yu",
                ))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        // Deliberately bypass CandidateInference: runtime selection still owns
        // authentication and declaration compatibility of its actual payload.
        let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
        let roots = program.execution_roots().unwrap();
        let mut machine = program
            .start(program.definition_named("main").unwrap(), &roots)
            .unwrap();
        let outcome = machine.run(10_000);
        assert!(
            matches!(
                outcome,
                RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
            ),
            "{ty}: {outcome:?}"
        );
    }
}

#[test]
fn discarded_global_materialization_can_be_demanded_again() {
    let source = format!(
        "{IO}my twice (thunk:[io] int) = {{ my ignored = catch thunk {{ io::tick(p), _ -> p }}; catch thunk {{ io::tick(p), _ -> p }} }}\nmy main = twice later\nmy later = io::tick 7"
    );
    let (mut machine, operations) = machine(&source);
    let outcome = machine.run(10_000);
    let RuntimeOutcome::UnhandledRequest {
        operation, payload, ..
    } = outcome
    else {
        panic!("expected later root request, got {outcome:?}");
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
    assert_eq!(payload.as_ref(), "7");
}

#[test]
fn live_receiver_joins_its_retained_receipt_with_a_helpers_same_view_observation() {
    let source = "act io:\n    our tick: int -> int\nmy helper (item:[] int) = item\nmy relay (thunk:[io] int) = catch helper thunk { io::tick(p), _ -> p }\nmy main = relay (io::tick 7)";
    assert_integer(source, "7");
}
