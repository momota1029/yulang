use super::*;

fn parsed(source: &str) -> yu_syntax::ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn source_hir(parsed: &yu_syntax::ParsedFile) -> Arc<HirModule> {
    Arc::new(
        yu_hir::shadow::lower_module_with_source_identity(
            ModuleIdentity::source_root(FileId::new(FileKey::new("test", "shadow-f5.yu"))),
            parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}

fn roots(hir: &HirModule) -> impl Iterator<Item = &DefinitionRootId> {
    hir.items().iter().map(|item| match item {
        HirItem::Binding(binding) => binding.definition_root(),
        _ => panic!("test binding"),
    })
}

#[test]
fn equal_q_and_r_ordinals_retain_exact_member_scheme_namespaces() {
    for (source, recursive) in [
        ("my f x = x; my g y = y", false),
        ("my f x = g; my g y = f", true),
    ] {
        let hir = module(source, "shadow-f5-owners.yu");
        let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
        let before = solved.counters();
        let observer = solved.shadow_closed_schemes();
        let mut roots = roots(&hir);
        let first = observer.for_root(roots.next().unwrap()).unwrap();
        let second = observer.for_root(roots.next().unwrap()).unwrap();
        assert!(!first.same_identity(second));
        if recursive {
            let a = first.recursive_binders().next().unwrap();
            let b = second.recursive_binders().next().unwrap();
            assert_eq!(a.ordinal(), b.ordinal());
            assert!(!a.same_identity(b));
            assert!(a.same_identity(first.recursive_binders().next().unwrap()));
            for binder in [a, b] {
                let (lower, upper) = binder.endpoints();
                let view = binder.scheme().endpoints();
                assert!(matches!(
                    view.positive_value(lower),
                    Ok(PositiveValueView::Function { .. })
                ));
                assert_eq!(view.negative_value(upper), Ok(NegativeValueView::Top));
                let PositiveValueView::Function { result, .. } =
                    view.positive_value(lower).unwrap()
                else {
                    panic!("recursive function")
                };
                let PositiveValueView::Function { result, .. } =
                    view.positive_value(result).unwrap()
                else {
                    panic!("mutual recursive function")
                };
                assert!(
                    matches!(view.positive_value(result), Ok(PositiveValueView::Recursive(id)) if id.ordinal() == binder.ordinal())
                );
            }
        } else {
            let a = first.quantifiers().next().unwrap();
            let b = second.quantifiers().next().unwrap();
            assert_eq!(a.ordinal(), b.ordinal());
            assert!(!a.same_identity(b));
            assert!(a.same_identity(first.quantifiers().next().unwrap()));
        }
        assert_eq!(solved.counters(), before);
    }
}

#[test]
fn source_resolution_uses_exact_root_and_rejects_foreign_artifacts() {
    use yu_hir::shadow::{ShadowArtifact, SourceIdentityError};
    let parsed = parsed("my head = tail; my tail x = x");
    let hir = source_hir(&parsed);
    let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
    let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let foreign_shadow =
        ShadowArtifact::from_parsed(self::parsed("my head = tail; my tail x = x")).unwrap();
    let foreign_hir = source_hir(&parsed);
    let observer = solved.shadow_closed_schemes();
    let before = solved.counters();
    for root in roots(&hir) {
        let scheme = observer.for_root(root).unwrap();
        assert_eq!(scheme.owner(), root);
        assert_eq!(
            scheme.definition_source_position(&shadow),
            shadow.definition_source_position(&hir, root)
        );
        assert_eq!(
            shadow
                .position(&scheme.definition_source_position(&shadow).unwrap())
                .unwrap()
                .kind(),
            yu_syntax::SyntaxKind::BindingStatement
        );
        assert_eq!(
            scheme.definition_source_position(&foreign_shadow),
            Err(SourceIdentityError::ForeignParse)
        );
    }
    assert!(matches!(
        observer.for_root(roots(&foreign_hir).next().unwrap()),
        Err(ArtifactMismatch)
    ));
    let ordinary = module("my f x = x", "shadow-f5-ordinary.yu");
    let ordinary_solved = SolvedModule::solve(collect(ordinary.clone())).unwrap();
    assert_eq!(
        ordinary_solved
            .shadow_closed_schemes()
            .for_root(roots(&ordinary).next().unwrap())
            .unwrap()
            .definition_source_position(&shadow),
        Err(SourceIdentityError::MissingSource)
    );
    assert_eq!(solved.counters(), before);
}

#[test]
fn fresh_capture_source_repeated_uses_and_enabled_disabled_agree() {
    for source in [
        "my f x = x; my a = f; my b = f",
        "my f x = g; my g y = f; my a = f; my b = f",
        "my f = 1; my a = f; my b = f",
    ] {
        let hir = source_hir(&parsed(source));
        let mut disabled = InferenceSession::new(collect(hir.clone()));
        let mut enabled = InferenceSession::new(collect(hir));
        enabled.shadow_fresh_capture = Some(ShadowFreshCapture::default());
        disabled.admit_all_collected_facts().unwrap();
        enabled.admit_all_collected_facts().unwrap();
        disabled.execute_scc_plan().unwrap();
        enabled.execute_scc_plan().unwrap();
        assert_eq!(disabled.execution_counters, enabled.execution_counters);
        let routes = |session: &InferenceSession| {
            session
                .routed_uses
                .iter()
                .map(|route| (route.use_id.occurrence.clone(), route.fact, route.kind))
                .collect::<Vec<_>>()
        };
        assert_eq!(routes(&disabled), routes(&enabled));
        let capture = enabled.shadow_fresh_capture.take().unwrap();
        assert!(capture.pending.is_none());
        assert!(capture.routes.len() >= 2);
        // Only compare ordinals within this one session's owned capture.
        for (index, route) in capture.routes.iter().enumerate() {
            let use_record = &enabled.batch.definition_uses
                [enabled.batch.definition_use_positions[&route.use_id]];
            assert_eq!(route.target, use_record.target);
            let scheme = enabled.schemes[route.target.ordinal() as usize]
                .as_ref()
                .unwrap();
            let view = enabled
                .finalization
                .as_ref()
                .unwrap()
                .scheme_view(scheme)
                .unwrap();
            assert_eq!(
                route.rows.len(),
                (view.quantifier_count() as usize) + view.recursive_bounds().len()
            );
            for &(kind, ordinal, row) in &route.rows {
                assert!((row as usize) < enabled.bounds.len());
                match kind {
                    ShadowFreshBinderKind::Quantified => assert!(ordinal < view.quantifier_count()),
                    ShadowFreshBinderKind::Recursive => assert!(
                        view.recursive_bounds()
                            .iter()
                            .any(|bound| bound.binder().ordinal() == ordinal)
                    ),
                }
                for previous in &capture.routes[..index] {
                    assert_ne!(previous.use_id, route.use_id);
                    assert!(
                        previous
                            .rows
                            .iter()
                            .all(|&(_, _, previous_row)| previous_row != row)
                    );
                }
            }
        }
        let meter = DraftHeapMeter::default();
        for (a, b) in disabled.schemes.iter().zip(&enabled.schemes) {
            assert_eq!(
                InferenceSession::decode_closed_scheme(
                    &meter,
                    disabled.finalization.as_ref().unwrap(),
                    a.as_ref().unwrap()
                )
                .unwrap(),
                InferenceSession::decode_closed_scheme(
                    &meter,
                    enabled.finalization.as_ref().unwrap(),
                    b.as_ref().unwrap()
                )
                .unwrap()
            );
        }
        let disabled = disabled.finish().unwrap();
        let enabled = enabled.finish().unwrap();
        assert_eq!(disabled.counters(), enabled.counters());
        assert_eq!(
            format!("{:?}", disabled.errors()),
            format!("{:?}", enabled.errors())
        );
        for occurrence in enabled.occurrences() {
            assert_eq!(
                disabled.projection_for(occurrence),
                enabled.projection_for(occurrence)
            );
        }
    }
}

#[cfg(feature = "shadow-scc-observer")]
#[test]
fn fresh_capture_routes_join_exact_scc_use_target_scheme_in_same_session() {
    for source in [
        "my f x = x; my a = f; my b = f",
        "my f x = g; my g y = f; my a = f; my b = f",
    ] {
        let batch = collect(source_hir(&parsed(source)));
        let retained = batch.clone();
        let mut session = InferenceSession::new(batch);
        session.shadow_fresh_capture = Some(ShadowFreshCapture::default());
        session.admit_all_collected_facts().unwrap();
        session.execute_scc_plan().unwrap();
        let capture = session.shadow_fresh_capture.take().unwrap();
        assert!(capture.pending.is_none());
        assert_eq!(capture.routes.len(), 2);
        let row_count = session.bounds.len();
        let solved = session.finish().unwrap();
        let topology = retained.shadow_scc_topology();
        let uses = topology
            .components()
            .flat_map(|component| component.incoming_uses())
            .collect::<Vec<_>>();
        let before = retained.counters();
        let solved_before = solved.counters();
        for (index, route) in capture.routes.iter().enumerate() {
            let matches = uses
                .iter()
                .filter(|occurrence| occurrence.collection_identity() == &route.use_id)
                .collect::<Vec<_>>();
            assert_eq!(matches.len(), 1);
            let occurrence = *matches[0];
            let use_record = &retained.definition_uses
                [retained.definition_use_positions[occurrence.collection_identity()]];
            assert_eq!(route.target, use_record.target);
            let target = topology
                .definitions()
                .find(|definition| definition.collection_identity() == &use_record.target)
                .unwrap();
            let pending = topology
                .pending_use_instantiation(&solved, occurrence)
                .unwrap();
            assert!(pending.occurrence().same_identity(occurrence));
            assert_eq!(pending.parent().collection_identity(), &use_record.parent);
            assert!(pending.target().same_identity(target));
            assert!(
                pending
                    .target_component()
                    .same_identity(topology.component_of(target).unwrap())
            );
            assert_eq!(pending.pending_generalization().premise(), crate::shadow_scc::PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved);
            assert_eq!(pending.qr_correspondence_premise(), crate::shadow_scc::PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved);
            assert_eq!(pending.shared_contract_transport_premise(), crate::shadow_scc::PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved);
            let scheme = pending.current_scheme();
            assert!(
                scheme.same_identity(topology.definition_closed_scheme(&solved, target).unwrap())
            );
            assert_eq!(
                scheme.owner(),
                &retained.definitions[retained.definition_positions[&route.target]].root
            );
            let expected = scheme
                .quantifiers()
                .map(|binder| (ShadowFreshBinderKind::Quantified, binder.ordinal()))
                .chain(
                    scheme
                        .recursive_binders()
                        .map(|binder| (ShadowFreshBinderKind::Recursive, binder.ordinal())),
                )
                .collect::<Vec<_>>();
            let actual = route
                .rows
                .iter()
                .map(|&(kind, ordinal, _)| (kind, ordinal))
                .collect::<Vec<_>>();
            assert!(!expected.is_empty());
            assert_eq!(actual, expected);
            // Fresh rows are compared only inside the session that captured them.
            for &(_, _, row) in &route.rows {
                assert!((row as usize) < row_count);
                for previous in &capture.routes[..index] {
                    assert_ne!(route.use_id, previous.use_id);
                    assert!(previous.rows.iter().all(|&(_, _, prior)| row != prior));
                }
            }
        }
        assert_eq!(before, retained.counters());
        assert_eq!(solved_before, solved.counters());
    }
}

#[test]
fn fresh_capture_synthetic_mixed_binders_preserves_both_bound_relationships() {
    let (mut session, routes) = f5c_shared_closed_incoming_fixture("shadow-f5-mixed");
    let meter = DraftHeapMeter::default();
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: vec![F5cRecursiveBound {
            ordinal: 1,
            lower: F5cPositive::Quantified(0),
            upper: F5cNegative::Recursive(1),
        }],
        predicate: F5cPositive::Function {
            argument: test_tracked_one(&meter, F5cNegative::Quantified(0)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: test_tracked_one(&meter, F5cPositive::Recursive(1)),
        },
    };
    let scheme = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap()
    .into_parts()
    .0;
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(scheme);
    session.shadow_fresh_capture = Some(ShadowFreshCapture::default());
    for route in &routes {
        session.route_incoming(route).unwrap();
    }
    let capture = session.shadow_fresh_capture.as_ref().unwrap();
    assert_eq!(capture.routes.len(), routes.len());
    assert_eq!(
        capture
            .routes
            .iter()
            .map(|route| &route.use_id)
            .collect::<Vec<_>>(),
        routes.iter().collect::<Vec<_>>(),
    );
    for route in &capture.routes {
        assert_eq!(route.rows.len(), 2);
        let (q_kind, q_ordinal, q_row) = route.rows[0];
        let (r_kind, r_ordinal, r_row) = route.rows[1];
        assert_eq!((q_kind, q_ordinal), (ShadowFreshBinderKind::Quantified, 0));
        assert_eq!((r_kind, r_ordinal), (ShadowFreshBinderKind::Recursive, 1));
        assert_ne!(q_row, r_row);
        assert!(
            session.bounds[r_row as usize]
                .direct_lower_rows
                .contains(&q_row)
        );
        assert!(
            session.bounds[r_row as usize]
                .direct_upper_rows
                .contains(&r_row)
        );
    }
}

#[test]
fn fresh_capture_discards_staged_fast_path_on_late_failure_and_retry() {
    // Synthetic installed Int scheme isolates the existing route-exit failure hook.
    let (mut session, routes) = f5c_shared_closed_incoming_fixture("shadow-f5-late-failure");
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(
        session
            .finalization
            .as_mut()
            .unwrap()
            .finalize_scheme(|f| {
                let predicate = f.positive_int()?;
                f.set_scheme(0, &[], predicate)
            })
            .unwrap()
            .into_parts()
            .0,
    );
    session.shadow_fresh_capture = Some(ShadowFreshCapture::default());
    session.instantiation_scratch.work.reserve(1);
    session.inject_no_growth_scratch_request_on_route_exit = true;
    inject_next_f5b_reserve_failure(F5bCapacityLane::InstantiationWork);
    assert_eq!(
        session.route_incoming(&routes[0]),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    let capture = session.shadow_fresh_capture.as_ref().unwrap();
    assert!(capture.pending.is_none());
    assert!(capture.routes.is_empty());
    session.inject_no_growth_scratch_request_on_route_exit = false;
    session.route_incoming(&routes[0]).unwrap();
    let capture = session.shadow_fresh_capture.as_ref().unwrap();
    assert_eq!(capture.routes.len(), 1);
    assert_eq!(capture.routes[0].use_id, routes[0]);
    assert!(capture.routes[0].rows.is_empty());
}

#[cfg(feature = "shadow-scc-observer")]
#[test]
fn fresh_capture_retained_states_and_opaque_rows() {
    use crate::shadow_f5::{FreshBinderRef, FreshCaptureState};
    for source in [
        "my f x = x; my a = f; my b = f",
        "my f x = g; my g y = f; my a = f; my b = f",
        "my f = 1; my a = f; my b = f",
    ] {
        let batch = collect(source_hir(&parsed(source)));
        let topology = batch.shadow_scc_topology();
        let captured = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
        let ordinary = SolvedModule::solve(batch.clone()).unwrap();
        for occurrence in ordinary.occurrences() {
            assert_eq!(
                ordinary.projection_for(occurrence),
                captured.projection_for(occurrence)
            );
        }
        let another = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
        let mut count = 0;
        let mut captures = Vec::new();
        for component in topology.components() {
            for use_ref in component.incoming_uses() {
                let pending = topology
                    .pending_use_instantiation(&captured, use_ref)
                    .unwrap();
                assert!(matches!(
                    topology
                        .pending_use_instantiation(&ordinary, use_ref)
                        .unwrap()
                        .current_fresh_capture(),
                    FreshCaptureState::NotRequested
                ));
                let FreshCaptureState::Captured(trace) = pending.current_fresh_capture() else {
                    panic!("successful incoming use retains complete capture");
                };
                assert!(trace.scheme().same_identity(pending.current_scheme()));
                let expected = trace.scheme().quantifiers().count()
                    + trace.scheme().recursive_binders().count();
                assert_eq!(trace.bindings().count(), expected);
                if source == "my f = 1; my a = f; my b = f" {
                    assert_eq!(expected, 0);
                }
                let FreshCaptureState::Captured(other) = topology
                    .pending_use_instantiation(&another, use_ref)
                    .unwrap()
                    .current_fresh_capture()
                else {
                    panic!()
                };
                let FreshCaptureState::Captured(repeated) = pending.current_fresh_capture() else {
                    panic!("repeated lookup retains the same successful capture");
                };
                assert_eq!(trace.bindings().count(), repeated.bindings().count());
                for (((binder, row), (_, foreign)), (_, repeated_row)) in trace
                    .bindings()
                    .zip(other.bindings())
                    .zip(repeated.bindings())
                {
                    let owner = match binder {
                        FreshBinderRef::Quantified(q) => q.scheme(),
                        FreshBinderRef::Recursive(r) => r.scheme(),
                    };
                    assert!(owner.same_identity(pending.current_scheme()));
                    assert!(row.same_identity(repeated_row));
                    assert!(!row.same_identity(foreign));
                }
                captures.push((use_ref, trace));
                count += 1;
            }
            for use_ref in component.internal_uses() {
                assert!(matches!(
                    topology
                        .pending_use_instantiation(&captured, use_ref)
                        .unwrap()
                        .current_fresh_capture(),
                    FreshCaptureState::NoClosedInstantiation
                ));
            }
        }
        assert!(count >= 2);
        let mut distinct_use_row_checks = 0;
        for (index, (use_ref, trace)) in captures.iter().enumerate() {
            for (previous_use, previous) in &captures[..index] {
                if !trace.scheme().same_identity(previous.scheme()) {
                    continue;
                }
                assert!(!use_ref.same_identity(*previous_use));
                assert_eq!(trace.bindings().count(), previous.bindings().count());
                for ((binder, row), (previous_binder, previous_row)) in
                    trace.bindings().zip(previous.bindings())
                {
                    match (binder, previous_binder) {
                        (FreshBinderRef::Quantified(q), FreshBinderRef::Quantified(previous_q)) => {
                            assert!(q.same_identity(previous_q));
                        }
                        (FreshBinderRef::Recursive(r), FreshBinderRef::Recursive(previous_r)) => {
                            assert!(r.same_identity(previous_r));
                        }
                        _ => panic!("same-scheme inventories retain the same binder order"),
                    }
                    assert!(!row.same_identity(previous_row));
                    distinct_use_row_checks += 1;
                }
            }
        }
        if source != "my f = 1; my a = f; my b = f" {
            assert!(distinct_use_row_checks > 0);
        }
        // Missing evidence in a requested capture must not look like zero binders.
        let mut unavailable = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
        let use_ref = topology
            .components()
            .flat_map(|c| c.incoming_uses())
            .next()
            .unwrap();
        unavailable.shadow_fresh_capture.as_mut().unwrap().routes[0].complete = false;
        assert!(matches!(
            topology
                .pending_use_instantiation(&unavailable, use_ref)
                .unwrap()
                .current_fresh_capture(),
            FreshCaptureState::Unavailable
        ));
        unavailable
            .shadow_fresh_capture
            .as_mut()
            .unwrap()
            .positions
            .clear();
        let use_ref = topology
            .components()
            .flat_map(|c| c.incoming_uses())
            .next()
            .unwrap();
        assert!(matches!(
            topology
                .pending_use_instantiation(&unavailable, use_ref)
                .unwrap()
                .current_fresh_capture(),
            FreshCaptureState::Unavailable
        ));
    }
}
