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
        // The experimental envelope covers retained HIR only. Grouped callee
        // `(id id) 1` currently lowers to Error and remains atomic Unsupported.
        "my id x = x; my n = (id id) 1",
        "my f x = host (\\y -> y)",
        "my f x = (my local = x; local)",
        "my id x = x; my n = id 1; my unsupported = true",
        "my a = a",
        "my a = b; my b = a",
        "my f x = f",
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
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn parameter_apply_retains_premises_and_ordinary_routes() {
    let hir = module("my apply f = f 1; my id x = x; pub out = apply id", true);
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    let out = candidate.export(root(&hir, 2)).unwrap();
    assert_eq!(out.value, SolvedValue::Int);
    assert_eq!(out.unresolved, UNRESOLVED);
    assert_eq!(candidate.calls().len(), 2);
    for call in candidate.calls() {
        assert_eq!(call.unresolved, UNRESOLVED);
    }
    let call = &candidate.calls()[1];
    assert!(!candidate.fresh_rows(&call.callee).unwrap().is_empty());
    assert_eq!(candidate.fresh_rows(&call.argument).unwrap().len(), 1);
    assert!(candidate.fresh_rows(&candidate.calls()[0].callee).is_none());
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn two_parameter_apply_uses_have_disjoint_substitutions() {
    let hir = module(
        "my apply f = f 1; my id x = x; my a = apply id; pub b = apply id",
        true,
    );
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    for index in [2, 3] {
        assert_eq!(
            candidate.export(root(&hir, index)).unwrap().value,
            SolvedValue::Int
        );
    }
    let a = candidate.fresh_rows(&candidate.calls()[1].callee).unwrap();
    let b = candidate.fresh_rows(&candidate.calls()[2].callee).unwrap();
    assert!(!a.is_empty());
    assert!(!b.is_empty());
    for left in &a {
        for right in &b {
            assert!(!left.same_identity(right));
        }
    }
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn module_name_in_lambda_body_uses_normal_incoming_route() {
    let hir = module(
        "my id x = x; my wrap ignored = id; pub out = wrap 1 2",
        true,
    );
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(candidate.candidate_conflicts().is_empty());
    assert_eq!(
        candidate.export(root(&hir, 2)).unwrap().value,
        SolvedValue::Int
    );
    let HirItem::Binding(binding) = &hir.items()[1] else {
        panic!("binding")
    };
    let yu_hir::ResolvedExpr::Lambda { body, .. } = binding.value() else {
        panic!("lambda")
    };
    assert_eq!(candidate.fresh_rows(body.occurrence()).unwrap().len(), 1);
    let supported = CandidateValueObservation::solve(module("my x = 1; my f y = x", true)).unwrap();
    assert!(supported.candidate_conflicts().is_empty());
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn grouped_application_and_nested_module_name_body_are_supported() {
    for text in [
        "my id x = x; my wrap y = id y; pub out = wrap 1",
        "my id x = x; my wrap y = id (id y); pub out = wrap 1",
    ] {
        let hir = module(text, true);
        let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert_eq!(
            candidate.export(root(&hir, 2)).unwrap().value,
            SolvedValue::Int
        );
        assert_eq!(
            candidate
                .fresh_rows(&candidate.calls()[0].callee)
                .unwrap()
                .len(),
            1
        );
    }
}

#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn parameter_apply_to_integer_has_candidate_conflict() {
    let candidate =
        CandidateValueObservation::solve(module("my apply f = f 1; pub bad = apply 1", true))
            .unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
    assert!(
        candidate
            .calls()
            .iter()
            .all(|call| call.unresolved == UNRESOLVED)
    );
}
#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn self_application_retains_unresolved_boundary_or_atomic_availability_failure() {
    let hir = module("my self x = x x", true);
    match CandidateValueObservation::solve(hir.clone()) {
        Ok(candidate) => {
            assert_eq!(candidate.calls().len(), 1);
            assert_eq!(candidate.calls()[0].unresolved, UNRESOLVED);
            assert_eq!(
                candidate.export(root(&hir, 0)).unwrap().unresolved,
                UNRESOLVED
            );
        }
        Err(CandidateError::Solve(_)) => {}
        Err(other) => panic!("retained supported HIR failed before solver boundary: {other:?}"),
    }
}
#[test]
fn regular_collection_remains_the_production_refusal_oracle() {
    for text in [
        "my id x = x; my n = id 1; pub exported = n",
        "my apply f = f 1; my id x = x; pub exported = apply id",
    ] {
        assert_production_collection_noninterference(text);
    }
}
fn assert_production_collection_noninterference(text: &str) {
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

#[cfg(feature = "shadow-apply-candidate")]
#[path = "../src/shadow_candidate_source_crosswalk.rs"]
mod source_crosswalk;

#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn module_names_join_target_fresh_rows_and_receiving_schemes_without_calls() {
    use source_crosswalk::CandidateSourceModuleUses;
    use yu_solver::shadow_f5::{FreshCaptureState, GeneralizationOriginState};
    let text = "my id x = x; my alias = id; pub first = alias; pub second = alias";
    let source_text: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source_text.clone(),
        Arc::new(scan_header(source_text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let source = yu_hir::shadow::ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new("candidate", "module-uses.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(
        candidate.calls().is_empty(),
        "module Names introduce no source call premise"
    );
    let crosswalk = CandidateSourceModuleUses::new(&source, &hir, &candidate).unwrap();
    assert_eq!(crosswalk.uses().len(), 3);
    for use_ in crosswalk.uses() {
        let observation = use_.observation();
        assert!(use_.declaration_skeleton().is_none());
        assert_eq!(
            use_.position(),
            &source
                .occurrence_source_position(&hir, observation.occurrence())
                .unwrap()
        );
        assert_eq!(
            use_.target_position(),
            &source
                .definition_source_position(&hir, observation.target_scheme().owner())
                .unwrap()
        );
        assert_eq!(
            use_.receiving_position(),
            &source
                .definition_source_position(&hir, observation.receiving_scheme().owner())
                .unwrap()
        );
        assert!(
            !observation
                .target_scheme()
                .same_identity(observation.receiving_scheme())
        );
        assert_eq!(observation.unresolved(), UNRESOLVED);
        let export = observation.receiving_export().unwrap();
        assert!(export.scheme().same_identity(observation.receiving_scheme()));
        assert_eq!(
            export.scheme().owner(),
            observation.receiving_scheme().owner()
        );
        assert_eq!(export.unresolved, UNRESOLVED);
        assert_eq!(export.value, SolvedValue::Unknown);
        assert!(export.unresolved.contains(
            &yu_solver::shadow_apply::UnresolvedPremise::ModuleNameSourceTypingAndAdmission
        ));
        assert!(export.unresolved.contains(
            &yu_solver::shadow_apply::UnresolvedPremise::ModuleUseReceivingExportCorrespondence
        ));
        assert!(matches!(
            observation.target_scheme().current_generalization_origins(),
            GeneralizationOriginState::Captured(_)
        ));
        assert!(matches!(
            observation
                .receiving_scheme()
                .current_generalization_origins(),
            GeneralizationOriginState::Captured(_)
        ));
        assert!(observation.provenance_causes().next().is_some());
    }
    let first = crosswalk.uses()[1].observation();
    let second = crosswalk.uses()[2].observation();
    assert!(!first.same_identity(second));
    assert!(first.target_scheme().same_identity(second.target_scheme()));
    let FreshCaptureState::Captured(first_route) = first.fresh_instantiation() else {
        panic!("first route")
    };
    let FreshCaptureState::Captured(second_route) = second.fresh_instantiation() else {
        panic!("second route")
    };
    assert!(first_route.scheme().same_identity(first.target_scheme()));
    let first_rows: Vec<_> = first_route.bindings().collect();
    let second_rows: Vec<_> = second_route.bindings().collect();
    assert!(!first_rows.is_empty());
    assert_eq!(first_rows.len(), second_rows.len());
    use yu_solver::shadow_f5::FreshBinderRef;
    for ((first_binder, a), (second_binder, b)) in first_rows.iter().zip(&second_rows) {
        assert!(!a.same_identity(*b));
        match (first_binder, second_binder) {
            (FreshBinderRef::Quantified(a), FreshBinderRef::Quantified(b)) => {
                assert!(a.same_identity(*b));
                assert_eq!(a.ordinal(), b.ordinal());
                assert!(a.scheme().same_identity(first.target_scheme()));
            }
            (FreshBinderRef::Recursive(a), FreshBinderRef::Recursive(b)) => {
                assert!(a.same_identity(*b));
                assert_eq!(a.ordinal(), b.ordinal());
                assert!(a.scheme().same_identity(first.target_scheme()));
            }
            _ => panic!("route changes source binder kind"),
        }
    }
    let retained_rows = candidate.fresh_rows(first.occurrence()).unwrap();
    assert_eq!(retained_rows.len(), first_rows.len());
    for (row, (binder, _)) in retained_rows.iter().zip(&first_rows) {
        match (row.source_binder(), binder) {
            (FreshBinderRef::Quantified(a), FreshBinderRef::Quantified(b)) => {
                assert!(a.same_identity(*b))
            }
            (FreshBinderRef::Recursive(a), FreshBinderRef::Recursive(b)) => {
                assert!(a.same_identity(*b))
            }
            _ => panic!("retained row changes source binder kind"),
        }
    }
    let foreign = CandidateValueObservation::solve(hir.clone()).unwrap();
    let foreign_use = foreign.definition_use(first.occurrence()).unwrap();
    assert!(!first.same_identity(foreign_use));
    assert!(
        !first
            .receiving_export()
            .unwrap()
            .scheme()
            .same_identity(foreign_use.receiving_export().unwrap().scheme())
    );
    let foreign_hir = module(text, true);
    assert!(CandidateSourceModuleUses::new(&source, &foreign_hir, &candidate).is_err());
}

#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn empty_module_fresh_route_differs_from_no_module_use() {
    use yu_solver::shadow_f5::FreshCaptureState;
    let hir = module("my n = 1; pub out = n", true);
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    let use_ = candidate.definition_uses().next().unwrap();
    let FreshCaptureState::Captured(route) = use_.fresh_instantiation() else {
        panic!("empty complete route")
    };
    assert_eq!(route.bindings().count(), 0);
    assert!(candidate.fresh_rows(use_.occurrence()).unwrap().is_empty());
    let export = use_.receiving_export().unwrap();
    assert!(export.scheme().same_identity(use_.receiving_scheme()));
    assert_eq!(export.scheme().owner(), root(&hir, 1));
    assert_eq!(export.value, SolvedValue::Int);
    assert_eq!(export.unresolved, UNRESOLVED);
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    assert!(
        candidate
            .definition_use(binding.value().occurrence())
            .is_none()
    );
}

#[cfg(feature = "shadow-apply-candidate")]
#[test]
fn module_use_crosswalk_checks_owners_even_when_inventory_is_empty() {
    use source_crosswalk::CandidateSourceModuleUses;
    let parse = |text: &str| {
        let source: Arc<SourceText> = Arc::from(text);
        parse_file(
            source.clone(),
            Arc::new(scan_header(source)),
            Arc::new(SyntaxEnvironment::empty()),
        )
    };
    let parsed = parse("pub out = 1");
    let source = yu_hir::shadow::ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new("candidate", "empty-use.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert!(
        CandidateSourceModuleUses::new(&source, &hir, &candidate)
            .unwrap()
            .uses()
            .is_empty()
    );

    let foreign_source = yu_hir::shadow::ShadowArtifact::from_parsed(parse("pub out = 2")).unwrap();
    assert!(CandidateSourceModuleUses::new(&foreign_source, &hir, &candidate).is_err());
    let foreign_hir = module("pub out = 1", true);
    let foreign_candidate = CandidateValueObservation::solve(foreign_hir.clone()).unwrap();
    assert!(CandidateSourceModuleUses::new(&source, &hir, &foreign_candidate).is_err());

    let expression_parsed = parse("1");
    let expression_source =
        yu_hir::shadow::ShadowArtifact::from_parsed(expression_parsed.clone()).unwrap();
    let expression_hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "candidate",
                "expression-use.yu",
            ))),
            &expression_parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let expression_candidate = CandidateValueObservation::solve(expression_hir.clone()).unwrap();
    assert!(
        CandidateSourceModuleUses::new(&expression_source, &expression_hir, &expression_candidate)
            .unwrap()
            .uses()
            .is_empty()
    );
    assert!(
        CandidateSourceModuleUses::new(&source, &expression_hir, &expression_candidate).is_err()
    );

    let empty_parsed = parse("");
    let empty_source = yu_hir::shadow::ShadowArtifact::from_parsed(empty_parsed.clone()).unwrap();
    let empty_hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new("candidate", "empty.yu"))),
            &empty_parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let empty_candidate = CandidateValueObservation::solve(empty_hir.clone()).unwrap();
    assert!(CandidateSourceModuleUses::new(&empty_source, &empty_hir, &empty_candidate).is_err());
}
