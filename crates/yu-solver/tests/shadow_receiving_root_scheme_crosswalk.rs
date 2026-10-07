#![cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]

// Current-solver ownership characterization only: visibility is retained
// metadata, and supplies no successor export-eligibility judgment.
use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirItem, HirVisibility, ModuleIdentity, ResolvedExpr, SemanticImports,
    shadow::{ShadowArtifact, lower_module_with_source_identity},
};
use yu_solver::{
    ConstraintBatch, SolvedModule,
    shadow_f5::{FreshBinderRef, FreshCaptureState, GeneralizationOriginState},
    shadow_scc::{
        CurrentUseRouteKind, PendingSccGeneralizationPremise, PendingUseInstantiationLookupError,
        PendingUseInstantiationPremise, SccClosedSchemeLookupError,
    },
};
use yu_syntax::{SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

#[test]
fn alias_source_uses_join_target_captures_and_distinct_receiving_scheme_owners() {
    let source: Arc<SourceText> =
        Arc::from("my id x = x; pub public_alias = id; our our_alias = id; my private_alias = id");
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let hir = Arc::new(
        lower_module_with_source_identity(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "shadow-receiving",
                "aliases.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let ordinary = SolvedModule::solve(batch.clone()).unwrap();
    let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    let foreign = SolvedModule::solve_with_shadow_fresh_capture(
        ConstraintBatch::collect(hir.clone()).unwrap(),
    )
    .unwrap();
    assert!(solved.errors().is_empty());
    assert_eq!(ordinary.errors(), solved.errors());
    let before = batch.counters();
    let solved_before = solved.counters();
    let ordinary_before = ordinary.counters();
    let foreign_before = foreign.counters();
    let topology = batch.shadow_scc_topology();

    // Obtain the three original Name occurrences from the shared parse, rather
    // than inferring an occurrence from a collection ordinal or scheme shape.
    let mut source_positions = Vec::new();
    let mut stack = vec![parsed.source_root()];
    while let Some(node) = stack.pop() {
        if node.syntax().kind() == SyntaxKind::IdentifierExpression
            && node.syntax().text().to_string() == "id"
        {
            source_positions.push(shadow.source_position(&node.key()).unwrap());
        }
        stack.extend(node.children());
    }
    assert_eq!(source_positions.len(), 3);
    let uses = topology
        .components()
        .flat_map(|component| component.incoming_uses())
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 3);
    let bindings = hir
        .items()
        .iter()
        .map(|item| match item {
            HirItem::Binding(binding) => binding,
            _ => panic!("fixture contains only bindings"),
        })
        .collect::<Vec<_>>();
    assert_eq!(bindings.len(), 4);
    let source_binding = bindings[0];
    let mut captures = Vec::new();
    let mut receiving_schemes = Vec::new();
    let mut receiving_origins = Vec::new();
    let mut joined_positions = Vec::new();
    for (alias, visibility) in bindings[1..].iter().zip([
        HirVisibility::Public,
        HirVisibility::Our,
        HirVisibility::Private,
    ]) {
        assert_eq!(alias.visibility(), visibility);
        assert!(matches!(alias.value(), ResolvedExpr::Name { .. }));
        let position = shadow
            .occurrence_source_position(&hir, alias.value().occurrence())
            .unwrap();
        assert!(source_positions.contains(&position));
        assert!(!joined_positions.contains(&position));
        joined_positions.push(position.clone());
        let matches = uses
            .iter()
            .copied()
            .filter(|&occurrence| {
                topology.use_source_position(&shadow, occurrence).unwrap() == position
            })
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1);
        let occurrence = matches[0];
        let pending = topology
            .pending_use_instantiation(&solved, occurrence)
            .unwrap();
        assert!(pending.occurrence().same_identity(occurrence));
        let route = pending
            .current_route()
            .expect("alias has a committed route");
        assert_eq!(route.kind(), CurrentUseRouteKind::IncomingStructured);
        let fact = route
            .fact()
            .expect("structured route has a representative fact");
        assert!(
            solved
                .store()
                .facts()
                .iter()
                .any(|stored| std::ptr::eq(stored, fact))
        );
        let edges = route.provenance().collect::<Vec<_>>();
        assert!(!edges.is_empty());
        for edge in edges {
            assert_eq!(edge.fact(), fact.id());
            assert_eq!(
                edge.cause().occurrence().occurrence(),
                alias.value().occurrence()
            );
            assert!(
                solved
                    .store()
                    .provenance()
                    .iter()
                    .any(|stored| std::ptr::eq(stored, edge))
            );
        }
        let ordinary_route = topology
            .pending_use_instantiation(&ordinary, occurrence)
            .unwrap()
            .current_route()
            .unwrap();
        assert_eq!(ordinary_route.kind(), route.kind());
        // Fresh terms and FactIds belong to their own solve/store; compare
        // retained coverage without equating handles from different attempts.
        assert!(ordinary_route.fact().is_some());
        assert_eq!(
            ordinary_route.provenance().count(),
            route.provenance().count()
        );
        let (parent, target) = topology.use_definitions(occurrence).unwrap();
        assert!(pending.parent().same_identity(parent));
        assert!(pending.target().same_identity(target));
        let receiving = topology
            .definition_closed_scheme(&solved, pending.parent())
            .unwrap();
        assert_eq!(receiving.owner(), alias.definition_root());
        assert_eq!(
            topology
                .definition_source_position(&shadow, parent)
                .unwrap(),
            shadow
                .definition_source_position(&hir, alias.definition_root())
                .unwrap()
        );
        let target_scheme = pending.current_scheme();
        assert_eq!(target_scheme.owner(), source_binding.definition_root());
        assert!(
            target_scheme
                .same_identity(topology.definition_closed_scheme(&solved, target).unwrap())
        );
        assert_ne!(target_scheme.owner(), receiving.owner());
        assert!(!target_scheme.same_identity(receiving));
        assert_eq!(
            pending.pending_generalization().premise(),
            PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
        );
        assert_eq!(
            pending.qr_correspondence_premise(),
            PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved
        );
        assert_eq!(
            pending.shared_contract_transport_premise(),
            PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved
        );
        assert!(matches!(
            topology
                .pending_use_instantiation(&ordinary, occurrence)
                .unwrap()
                .current_fresh_capture(),
            FreshCaptureState::NotRequested
        ));
        let FreshCaptureState::Captured(capture) = pending.current_fresh_capture() else {
            panic!("requested successful alias route retains its current capture");
        };
        assert!(capture.scheme().same_identity(target_scheme));
        let inventory = target_scheme
            .quantifiers()
            .map(FreshBinderRef::Quantified)
            .chain(
                target_scheme
                    .recursive_binders()
                    .map(FreshBinderRef::Recursive),
            )
            .collect::<Vec<_>>();
        assert!(!inventory.is_empty());
        let rows = capture.bindings().collect::<Vec<_>>();
        assert_eq!(rows.len(), inventory.len());
        for (index, (binder, row)) in rows.iter().enumerate() {
            assert!(same_binder(*binder, inventory[index]));
            for (earlier_binder, earlier_row) in &rows[..index] {
                assert!(!same_binder(*binder, *earlier_binder));
                assert!(!row.same_identity(*earlier_row));
            }
        }
        assert!(matches!(
            topology.pending_use_instantiation(&foreign, occurrence),
            Err(PendingUseInstantiationLookupError::ClosedScheme(
                SccClosedSchemeLookupError::ForeignCollection
            ))
        ));
        assert!(matches!(
            topology.definition_closed_scheme(&foreign, parent),
            Err(SccClosedSchemeLookupError::ForeignCollection)
        ));
        let GeneralizationOriginState::Captured(origins) =
            receiving.current_generalization_origins()
        else {
            panic!("successful receiving scheme has complete generalizer origins");
        };
        assert!(origins.scheme().same_identity(receiving));
        let origin_rows = origins.bindings().collect::<Vec<_>>();
        assert_eq!(origin_rows.len(), rows.len());
        let repeated = receiving.current_generalization_origins();
        let GeneralizationOriginState::Captured(repeated) = repeated else {
            panic!("stable capture");
        };
        for ((binder, origin), (other_binder, other_origin)) in
            origin_rows.iter().zip(repeated.bindings())
        {
            assert!(same_binder(*binder, other_binder));
            assert!(origin.same_identity(other_origin));
            assert_eq!(
                rows.iter()
                    .filter(|(_, fresh)| origin.same_identity(*fresh))
                    .count(),
                1
            );
        }
        assert!(matches!(
            topology
                .definition_closed_scheme(&ordinary, parent)
                .unwrap()
                .current_generalization_origins(),
            GeneralizationOriginState::NotRequested
        ));
        let foreign_scheme = foreign
            .shadow_closed_schemes()
            .for_root(receiving.owner())
            .unwrap();
        let GeneralizationOriginState::Captured(foreign_origins) =
            foreign_scheme.current_generalization_origins()
        else {
            panic!("foreign complete origins");
        };
        for (_, origin) in &origin_rows {
            assert!(
                foreign_origins
                    .bindings()
                    .all(|(_, other)| !origin.same_identity(other))
            );
        }
        receiving_origins.push(origin_rows);
        captures.push(capture);
        receiving_schemes.push(receiving);
    }
    for index in 0..captures.len() {
        for earlier in 0..index {
            assert!(!receiving_schemes[index].same_identity(receiving_schemes[earlier]));
            for ((binder, row), (other_binder, other_row)) in receiving_origins[index]
                .iter()
                .zip(&receiving_origins[earlier])
            {
                assert_eq!(binder_ordinal(*binder), binder_ordinal(*other_binder));
                assert!(!same_binder(*binder, *other_binder));
                assert!(!row.same_identity(*other_row));
            }
            assert!(
                captures[index]
                    .scheme()
                    .same_identity(captures[earlier].scheme())
            );
            for ((binder, row), (other_binder, other_row)) in
                captures[index].bindings().zip(captures[earlier].bindings())
            {
                assert!(same_binder(binder, other_binder));
                assert!(!row.same_identity(other_row));
            }
        }
    }
    assert_eq!(batch.counters(), before);
    assert_eq!(solved.counters(), solved_before);
    assert_eq!(ordinary.counters(), ordinary_before);
    assert_eq!(foreign.counters(), foreign_before);
}

#[test]
fn recursive_alias_receiving_origin_retains_exact_incoming_fresh_row() {
    let source: Arc<SourceText> = Arc::from("my f x = f; pub alias = f");
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let hir = Arc::new(
        lower_module_with_source_identity(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "shadow-receiving",
                "recursive-alias.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let shadow = ShadowArtifact::from_parsed(parsed).unwrap();
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    let foreign = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    assert!(solved.errors().is_empty());
    assert!(foreign.errors().is_empty());
    let before = solved.counters();
    let batch_before = batch.counters();
    let HirItem::Binding(alias) = &hir.items()[1] else {
        panic!("receiving alias binding");
    };
    assert!(matches!(alias.value(), ResolvedExpr::Name { .. }));
    let position = shadow
        .occurrence_source_position(&hir, alias.value().occurrence())
        .unwrap();
    let topology = batch.shadow_scc_topology();
    let uses = topology
        .components()
        .flat_map(|component| component.incoming_uses())
        .filter(|&occurrence| {
            topology.use_source_position(&shadow, occurrence).unwrap() == position
        })
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 1);
    let occurrence = uses[0];
    let pending = topology
        .pending_use_instantiation(&solved, occurrence)
        .unwrap();
    assert!(pending.occurrence().same_identity(occurrence));
    assert_eq!(
        pending.current_route().unwrap().kind(),
        CurrentUseRouteKind::IncomingStructured
    );
    let (parent, target) = topology.use_definitions(occurrence).unwrap();
    assert!(pending.parent().same_identity(parent));
    assert!(pending.target().same_identity(target));
    let receiving = topology.definition_closed_scheme(&solved, parent).unwrap();
    assert_eq!(receiving.owner(), alias.definition_root());
    assert!(
        pending
            .current_scheme()
            .same_identity(topology.definition_closed_scheme(&solved, target).unwrap())
    );
    assert!(!receiving.same_identity(pending.current_scheme()));
    let recursive = receiving.recursive_binders().collect::<Vec<_>>();
    assert!(!recursive.is_empty());
    let GeneralizationOriginState::Captured(origins) = receiving.current_generalization_origins()
    else {
        panic!("complete receiving recursive origins");
    };
    assert!(origins.scheme().same_identity(receiving));
    let FreshCaptureState::Captured(capture) = pending.current_fresh_capture() else {
        panic!("incoming recursive alias capture");
    };
    assert!(capture.scheme().same_identity(pending.current_scheme()));
    let rows = capture.bindings().collect::<Vec<_>>();
    let origin_rows = origins.bindings().collect::<Vec<_>>();
    for binder in recursive {
        let matching = origin_rows
            .iter()
            .filter(|(origin_binder, _)| {
                same_binder(*origin_binder, FreshBinderRef::Recursive(binder))
            })
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 1);
        let (_, historical) = *matching[0];
        assert_eq!(
            rows.iter()
                .filter(|(fresh_binder, fresh)| {
                    matches!(fresh_binder, FreshBinderRef::Recursive(_))
                        && historical.same_identity(*fresh)
                })
                .count(),
            1
        );
    }
    let GeneralizationOriginState::Captured(repeated) = receiving.current_generalization_origins()
    else {
        panic!("stable receiving origins");
    };
    assert_eq!(origin_rows.len(), repeated.bindings().count());
    for ((binder, row), (other_binder, other_row)) in origin_rows.iter().zip(repeated.bindings()) {
        assert!(same_binder(*binder, other_binder));
        assert!(row.same_identity(other_row));
    }
    let foreign_receiving = topology.definition_closed_scheme(&foreign, parent).unwrap();
    assert!(!receiving.same_identity(foreign_receiving));
    let GeneralizationOriginState::Captured(foreign_origins) =
        foreign_receiving.current_generalization_origins()
    else {
        panic!("foreign complete origins");
    };
    for (binder, row) in origin_rows {
        assert!(foreign_origins.bindings().all(|(other_binder, other_row)| {
            !same_binder(binder, other_binder) && !row.same_identity(other_row)
        }));
    }
    assert_eq!(
        pending.pending_generalization().premise(),
        PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
    );
    assert_eq!(
        pending.qr_correspondence_premise(),
        PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved
    );
    assert_eq!(
        pending.shared_contract_transport_premise(),
        PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved
    );
    assert_eq!(solved.counters(), before);
    assert_eq!(batch.counters(), batch_before);
}

#[test]
fn recursive_and_integer_uses_observe_recorded_routes_including_factless_bottom() {
    for (text, incoming_kind) in [
        (
            "my a = b; my b = a; my alias = a",
            CurrentUseRouteKind::IncomingBottomTrivial,
        ),
        ("my a = 42; my alias = a", CurrentUseRouteKind::IncomingInt),
    ] {
        let source: Arc<SourceText> = Arc::from(text);
        let parsed = parse_file(
            source.clone(),
            Arc::new(scan_header(source)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        let hir = Arc::new(
            lower_module_with_source_identity(
                ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "shadow-receiving",
                    "routes.yu",
                ))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        let batch = ConstraintBatch::collect(hir).unwrap();
        let ordinary = SolvedModule::solve(batch.clone()).unwrap();
        let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
        assert!(solved.errors().is_empty());
        assert_eq!(ordinary.errors(), solved.errors());
        let before = solved.counters();
        let batch_before = batch.counters();
        let topology = batch.shadow_scc_topology();
        let mut incoming_count = 0;
        let mut internal_count = 0;
        for component in topology.components() {
            for occurrence in component.internal_uses().chain(component.incoming_uses()) {
                let pending = topology
                    .pending_use_instantiation(&solved, occurrence)
                    .unwrap();
                let GeneralizationOriginState::Captured(origins) =
                    pending.current_scheme().current_generalization_origins()
                else {
                    panic!("complete zero-binder generalization");
                };
                assert_eq!(origins.bindings().count(), 0);
                assert!(matches!(
                    topology
                        .pending_use_instantiation(&ordinary, occurrence)
                        .unwrap()
                        .current_scheme()
                        .current_generalization_origins(),
                    GeneralizationOriginState::NotRequested
                ));
                let route = pending.current_route().expect("retained successful route");
                if route.kind() == CurrentUseRouteKind::Internal {
                    internal_count += 1;
                } else {
                    incoming_count += 1;
                    assert_eq!(route.kind(), incoming_kind);
                }
                if route.kind() == CurrentUseRouteKind::IncomingBottomTrivial {
                    assert!(route.fact().is_none());
                    assert_eq!(route.provenance().count(), 0);
                } else {
                    let fact = route.fact().unwrap();
                    assert!(
                        solved
                            .store()
                            .facts()
                            .iter()
                            .any(|stored| std::ptr::eq(stored, fact))
                    );
                    let edges = route.provenance().collect::<Vec<_>>();
                    assert!(!edges.is_empty());
                    assert!(edges.iter().all(|edge| edge.fact() == fact.id()));
                }
                assert_eq!(
                    pending.qr_correspondence_premise(),
                    PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved
                );
                assert_eq!(
                    pending.shared_contract_transport_premise(),
                    PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved
                );
                assert_eq!(
                    pending.pending_generalization().premise(),
                    PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
                );
            }
        }
        assert_eq!(incoming_count, 1);
        assert_eq!(
            internal_count,
            if incoming_kind == CurrentUseRouteKind::IncomingBottomTrivial {
                2
            } else {
                0
            }
        );
        assert_eq!(solved.counters(), before);
        assert_eq!(batch.counters(), batch_before);
    }
}

fn same_binder(a: FreshBinderRef<'_>, b: FreshBinderRef<'_>) -> bool {
    match (a, b) {
        (FreshBinderRef::Quantified(a), FreshBinderRef::Quantified(b)) => a.same_identity(b),
        (FreshBinderRef::Recursive(a), FreshBinderRef::Recursive(b)) => a.same_identity(b),
        _ => false,
    }
}

fn binder_ordinal(binder: FreshBinderRef<'_>) -> u32 {
    match binder {
        FreshBinderRef::Quantified(binder) => binder.ordinal(),
        FreshBinderRef::Recursive(binder) => binder.ordinal(),
    }
}
