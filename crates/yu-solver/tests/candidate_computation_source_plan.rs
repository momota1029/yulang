#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]

// These source controls observe inferred effects and constructor admission.
// They do not execute a delayed computation or establish handler eligibility.
use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::CandidateInference;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn solve(text: &str) -> (Arc<yu_hir::HirModule>, CandidateInference) {
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
                "computation-source-plan",
                "source.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    (hir, candidate)
}

const EFFECTS: &str = "act io:\n    our tick: int -> int\nact other:\n    our tick: int -> int\n\n";

#[test]
fn explicit_outer_rows_observe_resolved_members_and_symbolic_tail() {
    for (row, concrete, symbolic) in [
        ("[io]", vec!["io"], None),
        ("[other]", vec!["other"], None),
        ("[]", vec![], None),
        ("['e]", vec![], Some("'e")),
        ("[io, other, 'e]", vec!["io", "other"], Some("'e")),
    ] {
        let (hir, candidate) = solve(&format!("{EFFECTS}my relay (thunk:{row} int) = thunk"));
        assert!(candidate.candidate_conflicts().is_empty());
        assert_eq!(candidate.computation_source_plan_count(), 1);
        let plan = candidate.computation_source_plan(0).unwrap().unwrap();
        let expected: Vec<_> = concrete
            .iter()
            .map(|name| {
                &hir.source_effect_declarations()
                    .iter()
                    .find(|effect| effect.spelling.as_ref() == *name)
                    .unwrap()
                    .id
            })
            .collect();
        assert_eq!(plan.concrete_members().iter().collect::<Vec<_>>(), expected);
        assert_eq!(plan.symbolic_row_variable(), symbolic);
        assert_eq!(
            plan.original_owner(),
            plan.original_formal().definition_root()
        );
        assert_ne!(plan.annotation().position, plan.outer_row().position);
        assert!(candidate.computation_source_plan(1).is_err());
    }
}

#[test]
fn nested_callback_row_is_absent_at_the_value_formal_root() {
    let (_, candidate) = solve(&format!(
        "{EFFECTS}my relay (cb:(int -> [io] ()) -> ()) = cb"
    ));
    assert_eq!(candidate.computation_source_plan_count(), 1);
    assert!(candidate.computation_source_plan(0).unwrap().is_none());
}

#[test]
fn computation_root_members_exclude_nested_callback_rows() {
    let (hir, candidate) = solve(&format!(
        "{EFFECTS}my relay (thunk:[io] ((int -> [other] ()) -> ())) = thunk"
    ));
    let plan = candidate.computation_source_plan(0).unwrap().unwrap();
    let io = &hir
        .source_effect_declarations()
        .iter()
        .find(|effect| effect.spelling.as_ref() == "io")
        .unwrap()
        .id;
    assert_eq!(plan.concrete_members(), std::slice::from_ref(io));
}

#[test]
fn unannotated_and_scalar_value_formals_have_no_computation_root_plan() {
    for formal in ["value", "(value:int)"] {
        let (_, candidate) = solve(&format!("my relay {formal} = value"));
        assert_eq!(candidate.computation_source_plan_count(), 1);
        assert!(candidate.computation_source_plan(0).unwrap().is_none());
    }
}

#[test]
fn same_shaped_formals_keep_distinct_original_source_identities() {
    let (_, candidate) = solve(&format!(
        "{EFFECTS}my first (thunk:[io] int) = thunk; my second (thunk:[io] int) = thunk"
    ));
    assert_eq!(candidate.computation_source_plan_count(), 2);
    let first = candidate.computation_source_plan(0).unwrap().unwrap();
    let second = candidate.computation_source_plan(1).unwrap().unwrap();
    assert_eq!(first.concrete_members(), second.concrete_members());
    assert_ne!(first.original_formal(), second.original_formal());
    assert_ne!(first.original_lambda(), second.original_lambda());
    assert_ne!(first.annotation().position, second.annotation().position);
    assert_ne!(
        first.native_parameter_root(),
        second.native_parameter_root()
    );
    assert_ne!(first.entry_effect_row(), second.entry_effect_row());
}
