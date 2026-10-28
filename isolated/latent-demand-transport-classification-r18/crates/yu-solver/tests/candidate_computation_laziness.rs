#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

// These source controls observe inferred effects and constructor admission.
// They do not execute a delayed computation or establish handler eligibility.
use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn solve(text: &str) -> CandidateInference {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "{text}\n{:?}",
        parsed.structural_recoveries()
    );
    let hir = Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "computation-laziness",
                "source.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    CandidateInference::solve(hir).unwrap()
}

const IO: &str = "act io:\n    our tick: int -> int\n\n";
const ARGUMENT: &str = "{ my ignored = io::tick 0; io::tick 1 }";

fn assert_effect_conflicts(candidate: &CandidateInference) {
    assert!(
        !candidate.candidate_conflicts().is_empty(),
        "forcing the argument must violate the empty result allowance"
    );
    for error in candidate.candidate_conflicts() {
        assert!(
            candidate.effect_conflict(error.kind()).is_ok(),
            "the rejection must be an effect conflict, not an incidental value mismatch"
        );
    }
}

#[test]
fn unused_computation_formal_does_not_infer_whole_argument_block_effects() {
    let source =
        format!("{IO}my ignore (thunk:[io] int) = 1; my answer:[] int = ignore {ARGUMENT}");
    assert!(solve(&source).candidate_conflicts().is_empty());
}

#[test]
fn forwarding_computation_name_to_unused_computation_formal_keeps_empty_result() {
    let source = format!(
        "{IO}my ignore (thunk:[io] int) = 1; my relay (thunk:[io] int) = ignore thunk; my answer:[] int = relay {ARGUMENT}"
    );
    assert!(solve(&source).candidate_conflicts().is_empty());
}

#[test]
fn value_formal_forces_before_forwarding_to_unused_computation_formal() {
    let source = format!(
        "{IO}my ignore (thunk:[io] int) = 1; my relay value = ignore value; my answer:[] int = relay {ARGUMENT}"
    );
    assert_effect_conflicts(&solve(&source));
}

#[test]
fn passing_computation_name_to_value_consumer_infers_argument_effects() {
    let source = format!(
        "{IO}my consume value = 1; my relay (thunk:[io] int) = consume thunk; my answer:[] int = relay {ARGUMENT}"
    );
    assert_effect_conflicts(&solve(&source));
}

#[test]
fn nested_raw_resumption_source_is_admitted_with_both_effects_allowed() {
    let source = format!(
        "{IO}act pause:\n    our stop: int -> int\n\nmy relay (thunk:[io] int) = catch thunk {{ io::tick(p), _ -> 1, v -> v }}\nmy keep (thunk:[pause] int) = catch relay thunk {{ pause::stop(p), k -> k 0, v -> v }}\nmy answer:[io, pause] int = keep {{ my ignored = pause::stop 0; io::tick 1 }}"
    );
    let candidate = solve(&source);
    assert!(
        candidate.candidate_conflicts().is_empty(),
        "permissive admission does not claim subtraction or resumed handler eligibility"
    );
}

#[test]
fn body_pause_before_computation_name_is_admitted_with_both_effects_allowed() {
    let source = format!(
        "{IO}act pause:\n    our stop: int -> int\n\nmy relay (thunk:[io] int) = {{ my ignored = pause::stop 0; catch thunk {{ io::tick(p), _ -> 1, v -> v }} }}\nmy keep (thunk:[pause] int) = catch relay thunk {{ pause::stop(p), k -> k 0, v -> v }}\nmy answer:[io, pause] int = keep (io::tick 1)"
    );
    let candidate = solve(&source);
    assert!(
        candidate.candidate_conflicts().is_empty(),
        "permissive admission does not establish handler eligibility after the body pause"
    );
}
