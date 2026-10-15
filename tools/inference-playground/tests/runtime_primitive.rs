use std::sync::Arc;
use yu_hir::shadow::{SourceOperationId, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_playground::runtime::{
    Machine, RuntimeEvidence, RuntimeOutcome, RuntimeProgram, RuntimeUnavailable, RuntimeValueKind,
};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const IO: &str = "act io:\n    our tick: int -> int\n    our other: int -> int\n";

fn machine(source: &str, check_types: bool) -> (Machine, Vec<(Box<str>, SourceOperationId)>) {
    let source: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new("runtime-primitive", "test.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    if check_types {
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
    }
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
    let (mut machine, _) = machine(source, true);
    let outcome = machine.run(10_000);
    let RuntimeOutcome::Completed(value) = outcome else {
        panic!("{outcome:?}");
    };
    let RuntimeValueKind::Integer(value) = &machine.value(value).unwrap().kind else {
        panic!("integer result");
    };
    assert_eq!(value.as_ref(), expected);
}

#[test]
fn module_run_direct_primitive_request_selects_its_total_payload_arm() {
    assert_integer(
        &format!("{IO}my main = catch io::tick 7 {{ io::tick(p), _ -> p }}"),
        "7",
    );
}
#[test]
fn primitive_selection_keeps_original_order_and_normal_value_arms() {
    assert_integer(
        &format!(
            "{IO}my main = catch io::tick 7 {{ io::other(p), _ -> 99, io::tick(p), _ -> p, io::tick(p), _ -> 23 }}"
        ),
        "7",
    );
    assert_integer(
        &format!(
            "{IO}my main = catch (catch io::tick 7 {{ io::tick(p), _ -> p }}) {{ value -> 23 }}"
        ),
        "23",
    );
}
#[test]
fn primitive_forwarding_and_shallow_arm_requests_keep_actual_operations() {
    for (body, expected_operation) in [
        ("catch io::tick 7 { io::other(p), _ -> 99 }", "tick"),
        (
            "catch io::tick 7 { io::tick(p), _ -> io::other p, io::other(p), _ -> 99 }",
            "other",
        ),
    ] {
        let (mut machine, operations) = machine(&format!("{IO}my main = {body}"), true);
        let outcome = machine.run(10_000);
        let RuntimeOutcome::UnhandledRequest {
            operation, payload, ..
        } = outcome
        else {
            panic!("{outcome:?}");
        };
        assert_eq!(
            operation,
            operations
                .iter()
                .find(|(name, _)| name.as_ref() == expected_operation)
                .unwrap()
                .1
        );
        let RuntimeValueKind::Integer(payload) = &machine.value(payload).unwrap().kind else {
            panic!("integer payload");
        };
        assert_eq!(payload.as_ref(), "7");
    }
}
#[test]
fn whole_program_callable_alias_and_raw_binder_controls_withhold_negative_evidence() {
    for body in [
        "my unused x = x; my main = catch io::tick 7 { io::tick(p), _ -> p }",
        "my alias = io::tick; my main = catch io::tick 7 { io::tick(p), _ -> p }",
        "my main = catch io::tick 7 { io::tick(p), k -> p }",
    ] {
        let (mut machine, _) = machine(&format!("{IO}{body}"), true);
        let outcome = machine.run(10_000);
        assert!(
            matches!(
                outcome,
                RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))
            ),
            "{outcome:?}"
        );
    }
}
#[test]
fn primitive_certificate_preserves_runtime_payload_compatibility_checks() {
    // Bypass inference deliberately, as in the existing runtime payload tests.
    // The handler owner must still reject Bool at the declared Int payload port.
    let (mut machine, _) = machine(
        &format!("{IO}my main = catch io::tick true {{ io::tick(p), _ -> p }}"),
        false,
    );
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
fn positive_receiving_grants_remain_available_outside_the_closed_certificate() {
    assert_integer(
        &format!(
            "{IO}my relay (thunk:[io] int) = catch thunk {{ io::tick(p), _ -> p }}\nmy main = relay (io::tick 7)"
        ),
        "7",
    );
}
