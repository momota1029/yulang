#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateError, CandidateInference};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn solve(text: &str) -> CandidateInference {
    try_solve(text).unwrap_or_else(|error| panic!("{text}: {error:?}"))
}
fn try_solve(text: &str) -> Result<CandidateInference, CandidateError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty(), "healthy operation Catch fixture: {text}");
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("operation-catch", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap();
    CandidateInference::solve(Arc::new(hir))
}

// These exercise the provisional monomorphic packet and conservative full-S
// construction. Exact suffix precision, capture eligibility and residual
// removal remain open; these cases do not assert principality.
#[test]
fn provisional_ground_payload_and_raw_response_ports() {
    for body in [
        "catch signal::ping 1 { signal::ping(x), k -> k x, v -> v }",
        "catch signal::ping 1 { signal::ping(x), k -> { my checked:int = x; k checked }, v -> v }",
        // Oracle's empty pattern denotes wildcard payload, including Int.
        "catch signal::ping 1 { signal::ping(), k -> k 1, v -> v }",
    ] {
        let text = format!("act signal:\n    our ping: int -> int\n\nmy result = {body}");
        assert!(solve(&text).candidate_conflicts().is_empty(), "{text}");
    }
    for body in [
        "catch signal::ping 1 { signal::ping(x), k -> k \"wrong\", v -> v }",
        "catch signal::ping 1 { signal::ping(x), k -> { my checked:str = x; k 1 }, v -> v }",
    ] {
        let text = format!("act signal:\n    our ping: int -> int\n\nmy result = {body}");
        assert!(!solve(&text).candidate_conflicts().is_empty(), "{text}");
    }
}

#[test]
fn provisional_raw_continuation_returns_original_value_not_catch_arm_result() {
    let prefix = "act signal:\n    our ping: () -> int\n\n";
    let good = format!("{prefix}my result = catch signal::ping() {{ signal::ping(), k -> {{ my resumed:int = k 1; \"arm\" }}, v -> \"normal\" }}");
    assert!(solve(&good).candidate_conflicts().is_empty());
    let bad = format!("{prefix}my result = catch signal::ping() {{ signal::ping(), k -> {{ my resumed:str = k 1; \"arm\" }}, v -> \"normal\" }}");
    assert!(!solve(&bad).candidate_conflicts().is_empty());
}

#[test]
fn provisional_operation_only_catch_forwards_original_normal_return() {
    let prefix = "act signal:\n    our ping: () -> int\n\n";
    let good = format!("{prefix}my result:int = catch signal::ping() {{ signal::ping(), _ -> 1 }}");
    assert!(solve(&good).candidate_conflicts().is_empty());
    let bad = format!("{prefix}my result:str = catch signal::ping() {{ signal::ping(), _ -> \"arm\" }}");
    assert!(!solve(&bad).candidate_conflicts().is_empty());
}

#[test]
fn outside_operation_arm_effect_is_preserved_without_residual_removal() {
    let prefix = "act signal:\n    our ping: () -> int\nact outer:\n    our ping: () -> int\n\n";
    for (row, valid) in [("[signal, outer]", true), ("[signal]", false)] {
        let text = format!("{prefix}my result:{row} int = catch signal::ping() {{ signal::ping(), _ -> outer::ping(), v -> v }}");
        assert_eq!(solve(&text).candidate_conflicts().is_empty(), valid, "{text}");
    }
}

#[test]
fn generic_operation_arm_remains_explicitly_unavailable() {
    let text: Arc<SourceText> = Arc::from("act echo:\n    our send: 'a -> 'a\n\nmy result = catch echo::send 1 { echo::send(x), k -> k x, v -> v }");
    let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty());
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("generic-operation-catch", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap();
    assert!(matches!(CandidateInference::solve(Arc::new(hir)), Err(CandidateError::Unsupported)), "rigid existential opening is not implemented");
}

#[test]
fn response_entry_effects_survive_direct_and_aliased_raw_resumption() {
    let prefix = "act signal:\n    our ping: () -> int\nact outer:\n    our next: () -> int\n\n";
    for body in [
        "k (outer::next())",
        "{ my resume = k; resume (outer::next()) }",
        "{ my resume = k; my first = resume 1; resume (outer::next()) }",
    ] {
        for (row, valid) in [("[signal, outer]", true), ("[signal]", false)] {
            let text = format!("{prefix}my result:{row} int = catch signal::ping() {{ signal::ping(), k -> {body}, v -> v }}");
            assert_eq!(solve(&text).candidate_conflicts().is_empty(), valid, "{text}");
        }
    }
}

#[test]
fn nested_payload_aliases_keep_the_arm_introduction_type() {
    let prefix = "act signal:\n    our ping: int -> int\n\n";
    for (checked, valid) in [("int", true), ("str", false)] {
        let text = format!("{prefix}my result = catch signal::ping 1 {{ signal::ping(x), k -> {{ my payload = x; my first:int = payload; my second:{checked} = payload; my resume = k; my a:int = resume 1; resume payload }}, v -> v }}");
        assert_eq!(solve(&text).candidate_conflicts().is_empty(), valid, "{text}");
    }
}

#[test]
fn monomorphic_callback_response_preserves_original_returned_callback() {
    let text = "act signal:\n    our ping: () -> (int -> int)\n\nmy id x = x; my result:int = catch (signal::ping())(1) { signal::ping(), k -> k id, v -> v }";
    assert!(solve(text).candidate_conflicts().is_empty());
}

#[test]
fn paired_negative_concrete_callback_interface_is_explicitly_unsupported() {
    let text: Arc<SourceText> = Arc::from("act outer:\n    our next: () -> int\nact signal:\n    our ping: () -> (int -> [outer] int)\n\nmy result = catch signal::ping() { signal::ping(), k -> k, v -> v }");
    let parsed = parse_file(text.clone(), Arc::new(scan_header(text)), Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty());
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("negative-concrete-operation-catch", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap();
    assert!(matches!(CandidateInference::solve(Arc::new(hir)), Err(CandidateError::Unsupported)));
}

#[test]
fn unused_packet_fields_do_not_require_negative_callback_ports() {
    let prefix = "act outer:\n    our next: () -> int\nact signal:\n    our ping: () -> (int -> [outer] int)\n\n";
    for body in [
        "catch 1 { signal::ping(), _ -> 1, v -> v }",
        "catch 1 { signal::ping(), k -> 1, v -> v }",
    ] {
        let text = format!("{prefix}my result = {body}");
        assert!(solve(&text).candidate_conflicts().is_empty(), "{text}");
    }
    let text = format!("{prefix}my result = catch 1 {{ signal::ping(), k -> k, v -> v }}");
    assert!(matches!(try_solve(&text), Err(CandidateError::Unsupported)));
}

#[test]
fn unused_payload_callback_does_not_construct_its_negative_port() {
    let prefix = "act outer:\n    our next: () -> int\nact signal:\n    our ping: (int -> [outer] int) -> int\n\n";
    for body in [
        "catch 1 { signal::ping(), _ -> 1, v -> v }",
        "catch 1 { signal::ping(x), _ -> 1, v -> v }",
    ] {
        let text = format!("{prefix}my result = {body}");
        assert!(solve(&text).candidate_conflicts().is_empty(), "{text}");
    }
    let text = format!("{prefix}my result = catch 1 {{ signal::ping(x), _ -> x, v -> v }}");
    assert!(matches!(try_solve(&text), Err(CandidateError::Unsupported)));
}

#[test]
fn primitive_response_does_not_inherit_operation_invocation_effect_row() {
    let text = "act outer:\n    our next: () -> int\nact signal:\n    our ping: () -> [outer] int\n\nmy result:[signal, outer] int = catch signal::ping() { signal::ping(), k -> k 1, v -> v }";
    assert!(solve(text).candidate_conflicts().is_empty());
}
