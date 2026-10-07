#![cfg(feature = "shadow-f5")]
use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports, lower_module,
    shadow::lower_module_with_shadow_applications,
};
#[cfg(feature = "shadow-apply-candidate")]
use yu_solver::SolvedValue;
#[cfg(feature = "shadow-apply-candidate")]
use yu_solver::shadow_apply::{CandidateError, CandidateValueObservation, UNRESOLVED};
use yu_solver::{ConstraintBatch, SolvedModule};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};
fn module(text: &str, shadow: bool) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let identity =
        ModuleIdentity::source_root(FileId::new(FileKey::new("candidate", "candidate.yu")));
    Arc::new(if shadow {
        lower_module_with_shadow_applications(identity, &parsed, SemanticImports::empty()).unwrap()
    } else {
        lower_module(identity, &parsed, SemanticImports::empty()).unwrap()
    })
}
fn root(hir: &HirModule, index: usize) -> &yu_hir::DefinitionRootId {
    let HirItem::Binding(b) = &hir.items()[index] else {
        panic!("binding")
    };
    b.definition_root()
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn int_observation_retains_every_unresolved_duty() {
    let hir = module("my id x = x; my n = id 1; pub exported = n", true);
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let export = candidate.export(root(&hir, 2)).unwrap();
    assert_eq!(export.value, SolvedValue::Int);
    assert_eq!(export.unresolved, UNRESOLVED);
    assert_eq!(candidate.calls().len(), 1);
    assert_eq!(candidate.calls()[0].unresolved, UNRESOLVED);
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn returned_function_whole_scheme_and_ordinary_fresh_routes() {
    let hir = module(
        "my id x = x; my returned = id id; pub exported = returned",
        true,
    );
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let id = candidate.export(root(&hir, 0)).unwrap();
    let returned = candidate.export(root(&hir, 1)).unwrap();
    let exported = candidate.export(root(&hir, 2)).unwrap();
    assert!(returned.endpoints().quantifier_count() > 0);
    assert!(id.endpoints().alpha_eq(returned.endpoints()));
    assert!(returned.endpoints().alpha_eq(exported.endpoints()));
    let call = &candidate.calls()[0];
    let callee = candidate.fresh_rows(&call.callee).unwrap();
    let argument = candidate.fresh_rows(&call.argument).unwrap();
    assert_eq!(callee.len(), 1);
    assert_eq!(argument.len(), 1);
    assert!(!callee[0].same_identity(&argument[0]));
    let HirItem::Binding(alias) = &hir.items()[2] else {
        panic!("alias")
    };
    let alias_rows = candidate.fresh_rows(alias.value().occurrence()).unwrap();
    assert_eq!(
        alias_rows.len(),
        1,
        "one ordinary substitution, no extra candidate instantiation"
    );
    assert!(!alias_rows[0].same_identity(&argument[0]));
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn nested_results_have_separate_occurrences_and_constraints() {
    let hir = module("my id x = x; my n = id id 1; pub exported = n", true);
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(candidate.calls().len(), 2);
    assert_ne!(
        candidate.calls()[0].occurrence,
        candidate.calls()[1].occurrence
    );
    assert_eq!(
        candidate.export(root(&hir, 2)).unwrap().value,
        SolvedValue::Int
    );
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn incompatible_candidate_is_attributed_to_exact_apply() {
    let hir = module("my bad = 1 1", true);
    let candidate = CandidateValueObservation::solve(hir).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
    assert!(
        candidate
            .candidate_conflicts()
            .iter()
            .all(|e| e.occurrence().occurrence() == &candidate.calls()[0].occurrence)
    );
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn unsupported_shape_returns_no_partial_candidate() {
    for text in [
        "my id x = x; my n = (id id) 1",
        "my id x = x; my n = id 1; my unsupported = true",
        "my f x = x 1",
        "my a = a",
        "my a = b; my b = a",
        "my f x = f",
        "my x = 1; my f y = x",
        "my missing = nope",
        "missing 1",
        "id 1",
    ] {
        assert!(
            matches!(
                CandidateValueObservation::solve(module(text, true)),
                Err(CandidateError::Unsupported)
            ),
            "{text}"
        );
    }
}
#[test]
fn regular_collection_remains_the_production_refusal_oracle() {
    let text = "my id x = x; my n = id 1; pub exported = n";
    let ordinary_hir = module(text, false);
    let shadow_hir = module(text, true);
    assert_eq!(ordinary_hir.diagnostics(), shadow_hir.diagnostics());
    let ordinary =
        SolvedModule::solve(ConstraintBatch::collect(ordinary_hir.clone()).unwrap()).unwrap();
    let first = SolvedModule::solve(ConstraintBatch::collect(shadow_hir.clone()).unwrap()).unwrap();
    #[cfg(feature = "shadow-apply-candidate")]
    let _candidate = CandidateValueObservation::solve(shadow_hir.clone()).unwrap();
    let second =
        SolvedModule::solve(ConstraintBatch::collect(shadow_hir.clone()).unwrap()).unwrap();
    assert!(!ordinary_hir.errors().is_empty());
    assert_eq!(first.hir().diagnostics(), second.hir().diagnostics());
    assert_eq!(first.errors(), second.errors());
    assert_eq!(
        first.counters().hir_traversals(),
        second.counters().hir_traversals()
    );
    assert_eq!(
        first.counters().body_pass_visits(),
        second.counters().body_pass_visits()
    );
    assert_eq!(
        first.counters().collected_definitions(),
        second.counters().collected_definitions()
    );
    assert_eq!(
        first.counters().emitted_facts(),
        second.counters().emitted_facts()
    );
    assert_eq!(
        first.counters().admitted_facts(),
        second.counters().admitted_facts()
    );
    assert_eq!(first.store().facts().len(), second.store().facts().len());
    assert_eq!(first.store().provenance(), second.store().provenance());
    for (left, right) in first.store().facts().iter().zip(second.store().facts()) {
        compare_terms(first.store(), left.lower(), second.store(), right.lower());
        compare_terms(first.store(), left.upper(), second.store(), right.upper());
    }
    for index in 0..3 {
        assert_eq!(
            first.root_value_for(root(&shadow_hir, index)).unwrap(),
            second.root_value_for(root(&shadow_hir, index)).unwrap()
        );
        assert!(
            first
                .shadow_closed_schemes()
                .for_root(root(&shadow_hir, index))
                .unwrap()
                .endpoints()
                .alpha_eq(
                    second
                        .shadow_closed_schemes()
                        .for_root(root(&shadow_hir, index))
                        .unwrap()
                        .endpoints()
                )
        );
    }
    for index in 0..3 {
        assert_eq!(
            ordinary.root_value_for(root(&ordinary_hir, index)).unwrap(),
            first.root_value_for(root(&shadow_hir, index)).unwrap()
        );
        assert!(
            ordinary
                .shadow_closed_schemes()
                .for_root(root(&ordinary_hir, index))
                .unwrap()
                .endpoints()
                .alpha_eq(
                    first
                        .shadow_closed_schemes()
                        .for_root(root(&shadow_hir, index))
                        .unwrap()
                        .endpoints()
                )
        );
    }
}

fn compare_terms(
    left: &yu_solver::ConstraintStore,
    l: yu_solver::Term,
    right: &yu_solver::ConstraintStore,
    r: yu_solver::Term,
) {
    use yu_solver::TermView;
    match (left.term_view(l).unwrap(), right.term_view(r).unwrap()) {
        (
            TermView::PositiveFunction {
                argument: la,
                argument_effect: le,
                result_effect: lf,
                result: lr,
            },
            TermView::PositiveFunction {
                argument: ra,
                argument_effect: re,
                result_effect: rf,
                result: rr,
            },
        )
        | (
            TermView::NegativeFunction {
                argument: la,
                argument_effect: le,
                result_effect: lf,
                result: lr,
            },
            TermView::NegativeFunction {
                argument: ra,
                argument_effect: re,
                result_effect: rf,
                result: rr,
            },
        ) => {
            for (a, b) in [(la, ra), (le, re), (lf, rf), (lr, rr)] {
                compare_terms(left, a, right, b);
            }
        }
        (l, r) => assert_eq!(l, r),
    }
}
