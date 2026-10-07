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
    shadow_f5::{FreshBinderRef, FreshCaptureState},
    shadow_scc::{
        PendingSccGeneralizationPremise, PendingUseInstantiationLookupError,
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
        captures.push(capture);
        receiving_schemes.push(receiving);
    }
    for index in 0..captures.len() {
        for earlier in 0..index {
            assert!(!receiving_schemes[index].same_identity(receiving_schemes[earlier]));
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

fn same_binder(a: FreshBinderRef<'_>, b: FreshBinderRef<'_>) -> bool {
    match (a, b) {
        (FreshBinderRef::Quantified(a), FreshBinderRef::Quantified(b)) => a.same_identity(b),
        (FreshBinderRef::Recursive(a), FreshBinderRef::Recursive(b)) => a.same_identity(b),
        _ => false,
    }
}
