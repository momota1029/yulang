use super::{collect, module};

#[test]
fn outgoing_uses_preserve_reverse_chain_and_repeated_occurrences_without_shadow() {
    use crate::shadow_scc::PendingSccGeneralizationPremise;
    let parsed = parsed(
        "my head = middle; my middle = tail; my tail = 42; my repeat = head; my again = head",
    );
    let batch = source_batch(&parsed);
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed).unwrap();
    assert!(shadow.skeleton().is_err());
    let crosswalk = shadow.skeleton_source_crosswalk();
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    let components = topology.components().collect::<Vec<_>>();
    let mut observed = Vec::new();
    for component in &components {
        let outgoing = topology
            .outgoing_uses(*component)
            .unwrap()
            .collect::<Vec<_>>();
        let mut endpoints = Vec::new();
        for occurrence in &outgoing {
            let (parent, target) = topology.use_definitions(*occurrence).unwrap();
            assert!(component.same_identity(topology.component_of(parent).unwrap()));
            let target_component = topology.component_of(target).unwrap();
            assert!(!component.same_identity(target_component));
            assert!(
                target_component
                    .incoming_uses()
                    .any(|u| u.same_identity(*occurrence))
            );
            assert!(
                topology
                    .use_shadow_ref(&crosswalk, *occurrence)
                    .unwrap()
                    .is_none()
            );
            endpoints.push((parent.collection_ordinal(), target.collection_ordinal()));
        }
        for (index, occurrence) in outgoing.iter().enumerate() {
            assert!(
                !outgoing[..index]
                    .iter()
                    .any(|u| u.same_identity(*occurrence))
            );
        }
        assert_eq!(
            component.pending_successor_generalization().premise(),
            PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
        );
        observed.push((
            component.canonical_definition().collection_ordinal(),
            endpoints,
        ));
    }
    assert_eq!(
        observed,
        vec![
            (2, vec![]),
            (1, vec![(1, 2)]),
            (0, vec![(0, 1)]),
            (3, vec![(3, 0)]),
            (4, vec![(4, 0)])
        ]
    );
    assert_eq!(before, batch.counters());
}

#[test]
fn outgoing_uses_preserve_distinct_occurrences_in_a_synthetic_shared_parent_inventory() {
    let source = collect(module(
        "my a = 42; my b = a; my c = a",
        "shadow-scc-outgoing-synthetic-repeat.yu",
    ));
    let mut batch = source.clone();
    assert_eq!(batch.definition_uses.len(), 2);
    assert_eq!(
        batch.definition_uses[0].target,
        batch.definition_uses[1].target
    );
    assert_ne!(
        batch.definition_uses[0].parent,
        batch.definition_uses[1].parent
    );
    // This synthetic retained inventory isolates occurrence preservation:
    // current source collection emits at most one use per parent. The frozen
    // plan is deliberately unchanged; this is not a source-collection fixture.
    batch.definition_uses[1].parent = batch.definition_uses[0].parent.clone();
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    let parent = topology
        .definitions()
        .find(|d| d.collection_identity() == &batch.definition_uses[0].parent)
        .unwrap();
    let component = topology.component_of(parent).unwrap();
    let outgoing = topology
        .outgoing_uses(component)
        .unwrap()
        .collect::<Vec<_>>();
    assert_eq!(outgoing.len(), 2);
    assert!(!outgoing[0].same_identity(outgoing[1]));
    for (occurrence, record) in outgoing.iter().zip(&batch.definition_uses) {
        assert_eq!(occurrence.collection_identity(), record.id());
        let (observed_parent, target) = topology.use_definitions(*occurrence).unwrap();
        assert!(observed_parent.same_identity(parent));
        assert_eq!(target.collection_identity(), record.target());
    }
    assert_eq!(batch.definition_uses[0].id, source.definition_uses[0].id);
    assert_eq!(batch.definition_uses[1].id, source.definition_uses[1].id);
    assert_eq!(
        batch.definition_uses[0].occurrence,
        source.definition_uses[0].occurrence
    );
    assert_eq!(
        batch.definition_uses[1].occurrence,
        source.definition_uses[1].occurrence
    );
    assert_eq!(before, batch.counters());
}

#[test]
fn outgoing_uses_exclude_mutual_and_isolated_components_and_reject_foreign() {
    use crate::shadow_scc::SccTopologyLookupError;
    let hir = module(
        "my a = b; my b = a; my c = 42; my d = a",
        "shadow-scc-outgoing.yu",
    );
    let batch = collect(hir.clone());
    let foreign = collect(hir);
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    let components = topology.components().collect::<Vec<_>>();
    assert_eq!(topology.outgoing_uses(components[0]).unwrap().count(), 0);
    assert_eq!(topology.outgoing_uses(components[1]).unwrap().count(), 0);
    let outgoing = topology
        .outgoing_uses(components[2])
        .unwrap()
        .collect::<Vec<_>>();
    assert_eq!(outgoing.len(), 1);
    assert!(outgoing[0].same_identity(components[0].incoming_uses().next().unwrap()));
    let foreign_component = foreign.shadow_scc_topology().components().next().unwrap();
    assert!(matches!(
        topology.outgoing_uses(foreign_component),
        Err(SccTopologyLookupError::ForeignArtifact)
    ));
    assert_eq!(before, batch.counters());
}

#[test]
fn outgoing_uses_reject_missing_endpoint_identity_before_iteration() {
    use crate::shadow_scc::SccTopologyLookupError;
    let batch = collect(module(
        "my a = 42; my b = a",
        "shadow-scc-outgoing-missing.yu",
    ));
    let component = batch.shadow_scc_topology().components().last().unwrap();
    for parent in [true, false] {
        let mut missing = batch.clone();
        let absent = crate::DefinitionOrderId::new(missing.collection_artifact.clone(), u32::MAX);
        if parent {
            missing.definition_uses[0].parent = absent;
        } else {
            missing.definition_uses[0].target = absent;
        }
        let before = missing.counters();
        assert!(matches!(
            missing.shadow_scc_topology().outgoing_uses(component),
            Err(SccTopologyLookupError::MissingIdentity)
        ));
        assert_eq!(before, missing.counters());
    }
}

#[test]
fn pending_successor_generalization_preserves_singleton_without_uses() {
    use crate::shadow_scc::{PendingSccGeneralizationPremise, SccTopologyLookupError};
    let hir = module("my a = 42", "shadow-scc-pending-singleton.yu");
    let batch = collect(hir.clone());
    let foreign = collect(hir);
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    let component = topology.components().next().unwrap();
    let pending = component.pending_successor_generalization();
    assert_eq!(
        pending.premise(),
        PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
    );
    assert!(pending.component().same_identity(component));
    let member = pending.component().members().next().unwrap();
    assert!(member.same_identity(component.canonical_definition()));
    assert!(
        pending
            .component()
            .same_identity(topology.component_of(member).unwrap())
    );
    assert_eq!(pending.component().members().count(), 1);
    assert_eq!(pending.component().internal_uses().count(), 0);
    assert_eq!(pending.component().incoming_uses().count(), 0);
    let foreign_pending = foreign
        .shadow_scc_topology()
        .components()
        .next()
        .unwrap()
        .pending_successor_generalization();
    assert!(
        !pending
            .component()
            .same_identity(foreign_pending.component())
    );
    assert!(matches!(
        topology.component_of(foreign_pending.component().canonical_definition()),
        Err(SccTopologyLookupError::ForeignArtifact)
    ));
    assert_eq!(before, batch.counters());
}

#[test]
fn pending_successor_generalization_borrows_mutual_component_without_skeleton() {
    use crate::shadow_scc::{PendingSccGeneralizationPremise, SccTopologyLookupError};
    let parsed = parsed("my a = b; my b = a; my caller = a");
    let batch = source_batch(&parsed);
    let foreign = source_batch(&parsed);
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed).unwrap();
    assert!(shadow.skeleton().is_err());
    let crosswalk = shadow.skeleton_source_crosswalk();
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    for component in topology.components() {
        let pending = component.pending_successor_generalization();
        assert_eq!(
            pending.premise(),
            PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
        );
        assert!(pending.component().same_identity(component));
        let members = component.members().collect::<Vec<_>>();
        let retained = pending.component().members().collect::<Vec<_>>();
        assert_eq!(retained.len(), members.len());
        for (member, original) in retained.iter().zip(&members) {
            assert!(member.same_identity(*original));
            assert!(component.same_identity(topology.component_of(*member).unwrap()));
            assert!(
                topology
                    .definition_shadow_ref(&crosswalk, *member)
                    .unwrap()
                    .is_none()
            );
        }
        let original_uses = component
            .internal_uses()
            .chain(component.incoming_uses())
            .collect::<Vec<_>>();
        let retained_uses = pending
            .component()
            .internal_uses()
            .chain(pending.component().incoming_uses())
            .collect::<Vec<_>>();
        assert_eq!(retained_uses.len(), original_uses.len());
        for (occurrence, original) in retained_uses.iter().zip(&original_uses) {
            assert!(occurrence.same_identity(*original));
            let (parent, target) = topology.use_definitions(*occurrence).unwrap();
            let (original_parent, original_target) = topology.use_definitions(*original).unwrap();
            assert!(parent.same_identity(original_parent));
            assert!(target.same_identity(original_target));
            assert!(component.same_identity(topology.component_of(target).unwrap()));
            assert!(
                topology
                    .use_shadow_ref(&crosswalk, *occurrence)
                    .unwrap()
                    .is_none()
            );
        }
    }
    let mutual = topology
        .components()
        .next()
        .unwrap()
        .pending_successor_generalization();
    assert_eq!(mutual.component().members().count(), 2);
    assert_eq!(mutual.component().internal_uses().count(), 2);
    assert_eq!(mutual.component().incoming_uses().count(), 1);
    let foreign_use = foreign
        .shadow_scc_topology()
        .components()
        .next()
        .unwrap()
        .pending_successor_generalization()
        .component()
        .internal_uses()
        .next()
        .unwrap();
    assert!(matches!(
        topology.use_definitions(foreign_use),
        Err(SccTopologyLookupError::ForeignArtifact)
    ));
    assert_eq!(before, batch.counters());
}

#[test]
fn borrows_current_component_and_use_topology_without_solver_queries() {
    let batch = collect(module(
        "my a = b; my b = a; my c = 42; my d = a",
        "shadow-scc-observer.yu",
    ));
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();

    let components = topology.components().collect::<Vec<_>>();
    let observed = components
        .iter()
        .map(|component| {
            let members = component
                .members()
                .map(|definition| definition.collection_ordinal())
                .collect::<Vec<_>>();
            (
                members,
                component.internal_uses().count(),
                component.incoming_uses().count(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        observed,
        vec![(vec![0, 1], 2, 1), (vec![2], 0, 0), (vec![3], 0, 0),]
    );
    let members = components[0].members().collect::<Vec<_>>();
    assert!(members[0].same_identity(components[0].canonical_definition()));
    assert!(components[0].same_identity(topology.component_of(members[1]).unwrap()));
    let internal_uses = components[0].internal_uses().collect::<Vec<_>>();
    assert_eq!(
        internal_uses
            .iter()
            .map(|use_id| use_id.occurrence_ordinal())
            .collect::<std::collections::HashSet<_>>()
            .len(),
        2
    );
    assert!(!internal_uses[0].same_identity(internal_uses[1]));

    let chain = collect(module(
        "my head = middle; my middle = tail; my tail = 42",
        "shadow-scc-order.yu",
    ));
    assert_eq!(
        chain
            .shadow_scc_topology()
            .definitions()
            .map(|definition| definition.collection_ordinal())
            .collect::<Vec<_>>(),
        vec![2, 1, 0]
    );
    assert_eq!(before, batch.counters());
}

#[test]
fn rejects_definition_handles_from_a_different_collection() {
    let first = collect(module("my a = 1", "shadow-scc-first.yu"));
    let second = collect(module("my b = 2", "shadow-scc-second.yu"));
    let foreign = second.shadow_scc_topology().definitions().next().unwrap();

    assert!(matches!(
        first.shadow_scc_topology().component_of(foreign),
        Err(crate::shadow_scc::SccTopologyLookupError::ForeignArtifact)
    ));
}

#[test]
fn retained_use_endpoints_preserve_exact_parent_target_and_component_identity() {
    let batch = collect(module(
        "my a = b; my b = a; my c = 42; my d = a",
        "shadow-scc-use-endpoints.yu",
    ));
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    let components = topology.components().collect::<Vec<_>>();
    let members = components[0].members().collect::<Vec<_>>();
    let incoming_parent = components[2].members().next().unwrap();
    let mut internal_endpoints = Vec::new();
    for occurrence in components[0].internal_uses() {
        let (parent, target) = topology.use_definitions(occurrence).unwrap();
        let record = batch
            .definition_uses()
            .iter()
            .find(|record| record.id() == occurrence.collection_identity())
            .unwrap();
        assert_eq!(parent.collection_identity(), record.parent());
        assert_eq!(target.collection_identity(), record.target());
        assert!(components[0].same_identity(topology.component_of(parent).unwrap()));
        assert!(components[0].same_identity(topology.component_of(target).unwrap()));
        internal_endpoints.push((parent.collection_ordinal(), target.collection_ordinal()));
        assert!(
            (parent.same_identity(members[0]) && target.same_identity(members[1]))
                || (parent.same_identity(members[1]) && target.same_identity(members[0]))
        );
    }
    internal_endpoints.sort_unstable();
    assert_eq!(internal_endpoints, vec![(0, 1), (1, 0)]);

    let incoming = components[0].incoming_uses().collect::<Vec<_>>();
    assert_eq!(incoming.len(), 1);
    let (parent, target) = topology.use_definitions(incoming[0]).unwrap();
    assert!(parent.same_identity(incoming_parent));
    assert!(target.same_identity(members[0]));
    assert!(components[2].same_identity(topology.component_of(parent).unwrap()));
    assert!(components[0].same_identity(topology.component_of(target).unwrap()));
    assert_eq!(before, batch.counters());
}

#[test]
fn use_endpoint_lookup_rejects_another_collection_with_the_same_source() {
    let hir = module("my a = b; my b = a", "shadow-scc-use-brand.yu");
    let first = collect(hir.clone());
    let second = collect(hir);
    let before = first.counters();
    let foreign = second
        .shadow_scc_topology()
        .components()
        .next()
        .unwrap()
        .internal_uses()
        .next()
        .unwrap();
    assert!(matches!(
        first.shadow_scc_topology().use_definitions(foreign),
        Err(crate::shadow_scc::SccTopologyLookupError::ForeignArtifact)
    ));
    assert_eq!(before, first.counters());
}

fn parsed(source: &str) -> yu_syntax::ParsedFile {
    let source: std::sync::Arc<yu_syntax::SourceText> = std::sync::Arc::from(source);
    let header = std::sync::Arc::new(yu_syntax::scan_header(source.clone()));
    yu_syntax::parse_file(
        source,
        header,
        std::sync::Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    )
}

fn source_batch(parsed: &yu_syntax::ParsedFile) -> crate::ConstraintBatch {
    collect(std::sync::Arc::new(
        yu_hir::shadow::lower_module_with_source_identity(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "test",
                "shadow-scc-source.yu",
            ))),
            parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    ))
}

#[test]
fn joins_exact_source_nodes_for_current_scc_and_dag_without_queries() {
    use yu_syntax::SyntaxKind;
    let parsed = parsed("my a = b; my b = a; my c = 42; my d = a; my e = d");
    let batch = source_batch(&parsed);
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    // Expected positions come from exact parse-owned nodes, independently of HIR IDs.
    let mut declarations = Vec::new();
    let mut identifiers = Vec::new();
    let mut stack = vec![parsed.source_root()];
    while let Some(node) = stack.pop() {
        let positions = match node.syntax().kind() {
            SyntaxKind::BindingStatement => Some(&mut declarations),
            SyntaxKind::IdentifierExpression => Some(&mut identifiers),
            _ => None,
        };
        if let Some(positions) = positions {
            positions.push(shadow.source_position(&node.key()).unwrap());
        }
        let children = node.children().collect::<Vec<_>>();
        stack.extend(children.into_iter().rev());
    }
    let definitions = topology.definitions().collect::<Vec<_>>();
    assert_eq!(definitions.len(), 5);
    for (definition, expected) in definitions.iter().zip(&declarations) {
        assert_eq!(
            topology
                .definition_source_position(&shadow, *definition)
                .unwrap(),
            *expected
        );
        assert_eq!(
            shadow.position(expected).unwrap().kind(),
            SyntaxKind::BindingStatement
        );
    }
    let components = topology.components().collect::<Vec<_>>();
    let uses = components
        .iter()
        .flat_map(|component| component.internal_uses().chain(component.incoming_uses()))
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 4);
    for (use_id, expected) in uses.iter().zip(&identifiers) {
        assert_eq!(
            topology.use_source_position(&shadow, *use_id).unwrap(),
            *expected
        );
        assert_eq!(
            shadow.position(expected).unwrap().kind(),
            SyntaxKind::IdentifierExpression
        );
    }
    assert_ne!(identifiers[1], identifiers[2]);
    assert_eq!(before, batch.counters());
}

#[test]
fn source_join_rejects_foreign_collection_parse_and_absent_sidecar() {
    use crate::shadow_scc::SccSourceLookupError;
    use yu_hir::shadow::{ShadowArtifact, SourceIdentityError};
    let source = "my a = b; my b = a";
    let parsed = parsed(source);
    let batch = source_batch(&parsed);
    let foreign_batch = source_batch(&parsed);
    let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let reparsed = self::parsed(source);
    let foreign_shadow = ShadowArtifact::from_parsed(reparsed).unwrap();
    let ordinary_batch = collect(std::sync::Arc::new(
        yu_hir::lower_module(
            batch.hir().identity().clone(),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    ));
    // Enabling the bridge leaves ordinary collection evidence unchanged.
    assert_eq!(batch.hir(), ordinary_batch.hir());
    assert_eq!(batch.counters(), ordinary_batch.counters());
    let before = batch.counters();
    let foreign_before = foreign_batch.counters();
    let ordinary_before = ordinary_batch.counters();
    let topology = batch.shadow_scc_topology();
    let definition = topology.definitions().next().unwrap();
    let use_id = topology
        .components()
        .next()
        .unwrap()
        .internal_uses()
        .next()
        .unwrap();
    let foreign_topology = foreign_batch.shadow_scc_topology();
    let foreign_definition = foreign_topology.definitions().next().unwrap();
    let foreign_use = foreign_topology
        .components()
        .next()
        .unwrap()
        .internal_uses()
        .next()
        .unwrap();
    assert_eq!(
        topology.definition_source_position(&shadow, foreign_definition),
        Err(SccSourceLookupError::ForeignCollection)
    );
    assert_eq!(
        topology.use_source_position(&shadow, foreign_use),
        Err(SccSourceLookupError::ForeignCollection)
    );
    assert_eq!(
        topology.definition_source_position(&foreign_shadow, definition),
        Err(SccSourceLookupError::SourceIdentity(
            SourceIdentityError::ForeignParse
        ))
    );
    assert_eq!(
        topology.use_source_position(&foreign_shadow, use_id),
        Err(SccSourceLookupError::SourceIdentity(
            SourceIdentityError::ForeignParse
        ))
    );
    let ordinary_topology = ordinary_batch.shadow_scc_topology();
    assert_eq!(
        ordinary_topology
            .definition_source_position(&shadow, ordinary_topology.definitions().next().unwrap()),
        Err(SccSourceLookupError::SourceIdentity(
            SourceIdentityError::MissingSource
        ))
    );
    assert_eq!(
        ordinary_topology.use_source_position(
            &shadow,
            ordinary_topology
                .components()
                .next()
                .unwrap()
                .internal_uses()
                .next()
                .unwrap()
        ),
        Err(SccSourceLookupError::SourceIdentity(
            SourceIdentityError::MissingSource
        ))
    );
    assert_eq!(before, batch.counters());
    assert_eq!(foreign_before, foreign_batch.counters());
    assert_eq!(ordinary_before, ordinary_batch.counters());
}

#[test]
fn reverse_dag_joins_source_by_identity_despite_dependency_first_order() {
    use yu_syntax::SyntaxKind;
    let parsed = parsed("my head = middle; my middle = tail; my tail = 42");
    let batch = source_batch(&parsed);
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();
    let mut parse_positions = Vec::new();
    let mut stack = vec![parsed.source_root()];
    while let Some(node) = stack.pop() {
        if matches!(
            node.syntax().kind(),
            SyntaxKind::BindingStatement | SyntaxKind::IdentifierExpression
        ) {
            parse_positions.push((
                shadow.source_position(&node.key()).unwrap(),
                node.syntax().kind(),
            ));
        }
        stack.extend(node.children());
    }
    let definitions = topology.definitions().collect::<Vec<_>>();
    // These assertions check ordering only; ordinals never select source positions.
    assert_eq!(
        definitions
            .iter()
            .map(|definition| definition.collection_ordinal())
            .collect::<Vec<_>>(),
        vec![2, 1, 0]
    );
    for definition in definitions {
        let record =
            &batch.definitions[batch.definition_positions[definition.collection_identity()]];
        let expected = shadow
            .definition_source_position(batch.hir(), &record.root)
            .unwrap();
        assert_eq!(
            parse_positions
                .iter()
                .find(|(position, _)| position == &expected)
                .map(|(_, kind)| kind),
            Some(&SyntaxKind::BindingStatement)
        );
        assert_eq!(
            topology
                .definition_source_position(&shadow, definition)
                .unwrap(),
            expected
        );
    }
    let uses = topology
        .components()
        .flat_map(|component| component.internal_uses().chain(component.incoming_uses()))
        .collect::<Vec<_>>();
    assert_eq!(
        uses.iter()
            .map(|use_id| use_id.occurrence_ordinal())
            .collect::<Vec<_>>(),
        vec![1, 0]
    );
    for use_id in uses {
        let record =
            &batch.definition_uses[batch.definition_use_positions[use_id.collection_identity()]];
        let expected = shadow
            .occurrence_source_position(batch.hir(), &record.occurrence)
            .unwrap();
        assert_eq!(
            parse_positions
                .iter()
                .find(|(position, _)| position == &expected)
                .map(|(_, kind)| kind),
            Some(&SyntaxKind::IdentifierExpression)
        );
        assert_eq!(
            topology.use_source_position(&shadow, use_id).unwrap(),
            expected
        );
    }
    assert_eq!(before, batch.counters());
}

#[test]
fn skeleton_crosswalk_maps_admitted_unary_definition_and_rejects_foreign_inputs() {
    use crate::shadow_scc::{SccShadowLookupError, SccSourceLookupError};
    use yu_hir::shadow::{Form, ShadowArtifact, SourceIdentityError};
    let parsed = parsed("my f x = x");
    let batch = source_batch(&parsed);
    let topology = batch.shadow_scc_topology();
    let shadow = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let crosswalk = shadow.skeleton_source_crosswalk();
    let before = batch.counters();
    let definition = topology.definitions().next().unwrap();
    let (expression, binder) = topology
        .definition_shadow_ref(&crosswalk, definition)
        .unwrap()
        .unwrap();
    assert!(matches!(expression.form(), Form::Lambda { binding, .. } if binding == binder));
    assert_eq!(
        expression.position(),
        &topology
            .definition_source_position(&shadow, definition)
            .unwrap()
    );
    let foreign = source_batch(&parsed);
    assert!(matches!(
        topology.definition_shadow_ref(
            &crosswalk,
            foreign.shadow_scc_topology().definitions().next().unwrap()
        ),
        Err(SccShadowLookupError::Source(
            SccSourceLookupError::ForeignCollection
        ))
    ));
    let reparsed = ShadowArtifact::from_parsed(self::parsed("my f x = x")).unwrap();
    assert!(matches!(
        topology.definition_shadow_ref(&reparsed.skeleton_source_crosswalk(), definition),
        Err(SccShadowLookupError::Source(
            SccSourceLookupError::SourceIdentity(SourceIdentityError::ForeignParse)
        ))
    ));
    assert_eq!(before, batch.counters());
}

#[test]
fn skeleton_crosswalk_absence_preserves_reverse_dag_and_repeated_scc_uses() {
    let parsed = parsed(
        "my head = middle; my middle = tail; my tail = 42; my repeat = head; my again = head",
    );
    let batch = source_batch(&parsed);
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    assert!(shadow.skeleton().is_err());
    let crosswalk = shadow.skeleton_source_crosswalk();
    let topology = batch.shadow_scc_topology();
    let before = batch.counters();
    let definitions = topology.definitions().collect::<Vec<_>>();
    assert_eq!(
        definitions
            .iter()
            .map(|d| d.collection_ordinal())
            .collect::<Vec<_>>(),
        vec![2, 1, 0, 3, 4]
    );
    for definition in definitions {
        assert!(
            topology
                .definition_shadow_ref(&crosswalk, definition)
                .unwrap()
                .is_none()
        );
    }
    let uses = topology
        .components()
        .flat_map(|c| c.internal_uses().chain(c.incoming_uses()))
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 4);
    let positions = uses
        .iter()
        .map(|u| topology.use_source_position(&shadow, *u).unwrap())
        .collect::<Vec<_>>();
    for (index, occurrence) in uses.iter().enumerate() {
        assert!(
            topology
                .use_shadow_ref(&crosswalk, *occurrence)
                .unwrap()
                .is_none()
        );
        assert!(!positions[..index].contains(&positions[index]));
    }
    assert_eq!(before, batch.counters());
}

#[test]
fn nested_skeleton_candidates_do_not_add_current_scc_members() {
    let parsed = parsed("my apply f = { my step x = f x; step }");
    let batch = source_batch(&parsed);
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let skeleton = shadow.skeleton().unwrap();
    let crosswalk = shadow.skeleton_source_crosswalk();
    assert_eq!(
        skeleton
            .expressions()
            .iter()
            .filter(|e| matches!(
                e.form(),
                yu_hir::shadow::Form::Lambda { .. } | yu_hir::shadow::Form::Bind { .. }
            ))
            .count(),
        3
    );
    let topology = batch.shadow_scc_topology();
    let definitions = topology.definitions().collect::<Vec<_>>();
    assert_eq!(definitions.len(), 1);
    assert!(
        topology
            .definition_shadow_ref(&crosswalk, definitions[0])
            .unwrap()
            .is_some()
    );
    assert_eq!(
        topology
            .components()
            .flat_map(|c| c.internal_uses().chain(c.incoming_uses()))
            .count(),
        0
    );
}

#[cfg(feature = "shadow-f5")]
#[test]
fn exact_collection_member_joins_finalized_identity_scheme_and_local_q() {
    use yu_hir::shadow::{Form, ShadowArtifact};
    let parsed = parsed("my f x = x");
    let batch = source_batch(&parsed);
    let cloned = batch.clone();
    let solved = crate::SolvedModule::solve(cloned.clone()).unwrap();
    let shadow = ShadowArtifact::from_parsed(parsed).unwrap();
    let crosswalk = shadow.skeleton_source_crosswalk();
    let before = batch.counters();
    let solved_before = solved.counters();
    let topology = batch.shadow_scc_topology();
    let definition = topology.definitions().next().unwrap();
    let (expression, binder) = topology
        .definition_shadow_ref(&crosswalk, definition)
        .unwrap()
        .unwrap();
    assert!(matches!(expression.form(), Form::Lambda { binding, .. } if binding == binder));
    let scheme = topology
        .definition_closed_scheme(&solved, definition)
        .unwrap();
    let root =
        &batch.definitions[batch.definition_positions[definition.collection_identity()]].root;
    assert_eq!(scheme.owner(), root);
    let direct = solved.shadow_closed_schemes().for_root(root).unwrap();
    assert!(scheme.same_identity(direct));
    assert_eq!(scheme.quantifiers().count(), 1);
    assert_eq!(scheme.recursive_binders().count(), 0);
    let q = scheme.quantifiers().next().unwrap();
    assert!(q.scheme().same_identity(scheme));
    assert!(q.same_identity(direct.quantifiers().next().unwrap()));
    let cloned_topology = cloned.shadow_scc_topology();
    let cloned_definition = cloned_topology.definitions().next().unwrap();
    assert!(definition.same_identity(cloned_definition));
    assert!(
        cloned_topology
            .definition_closed_scheme(&solved, definition)
            .unwrap()
            .same_identity(scheme)
    );
    assert!(
        topology
            .definition_closed_scheme(&solved, cloned_definition)
            .unwrap()
            .same_identity(scheme)
    );
    assert_eq!(before, batch.counters());
    assert_eq!(before, cloned.counters());
    assert_eq!(solved_before, solved.counters());
}

#[cfg(feature = "shadow-f5")]
#[test]
fn closed_scheme_join_rejects_recollected_equal_roots_and_missing_identity() {
    use crate::shadow_scc::SccClosedSchemeLookupError;
    let parsed = parsed("my f x = x");
    let batch = source_batch(&parsed);
    let recollected = collect(batch.hir().clone());
    let solved = crate::SolvedModule::solve(batch.clone()).unwrap();
    let foreign_solved = crate::SolvedModule::solve(recollected.clone()).unwrap();
    let topology = batch.shadow_scc_topology();
    let foreign_topology = recollected.shadow_scc_topology();
    let definition = topology.definitions().next().unwrap();
    let foreign_definition = foreign_topology.definitions().next().unwrap();
    let root =
        &batch.definitions[batch.definition_positions[definition.collection_identity()]].root;
    let foreign_root = &recollected.definitions
        [recollected.definition_positions[foreign_definition.collection_identity()]]
    .root;
    assert_eq!(root, foreign_root);
    // Root ownership alone cannot distinguish independent collection attempts.
    assert!(
        foreign_solved
            .shadow_closed_schemes()
            .for_root(root)
            .is_ok()
    );
    let before = batch.counters();
    let foreign_before = recollected.counters();
    let solved_before = solved.counters();
    let foreign_solved_before = foreign_solved.counters();
    assert!(matches!(
        topology.definition_closed_scheme(&foreign_solved, definition),
        Err(SccClosedSchemeLookupError::ForeignCollection)
    ));
    assert!(matches!(
        topology.definition_closed_scheme(&solved, foreign_definition),
        Err(SccClosedSchemeLookupError::ForeignCollection)
    ));
    assert!(matches!(
        foreign_topology.definition_closed_scheme(&solved, foreign_definition),
        Err(SccClosedSchemeLookupError::ForeignCollection)
    ));
    let mut missing = batch.clone();
    missing
        .definition_positions
        .remove(definition.collection_identity());
    assert!(matches!(
        missing
            .shadow_scc_topology()
            .definition_closed_scheme(&solved, definition),
        Err(SccClosedSchemeLookupError::MissingIdentity)
    ));
    assert_eq!(before, batch.counters());
    assert_eq!(foreign_before, recollected.counters());
    assert_eq!(solved_before, solved.counters());
    assert_eq!(foreign_solved_before, foreign_solved.counters());
}

#[cfg(feature = "shadow-f5")]
#[test]
fn use_closed_scheme_join_rejects_foreign_collection_and_missing_identities() {
    use crate::shadow_scc::SccClosedSchemeLookupError;
    let parsed = parsed("my f x = x; my a = f");
    let batch = source_batch(&parsed);
    let foreign = collect(batch.hir().clone());
    let solved = crate::SolvedModule::solve(batch.clone()).unwrap();
    let foreign_solved = crate::SolvedModule::solve(foreign.clone()).unwrap();
    let topology = batch.shadow_scc_topology();
    let occurrence = topology
        .components()
        .flat_map(|c| c.incoming_uses())
        .next()
        .unwrap();
    let foreign_topology = foreign.shadow_scc_topology();
    let foreign_use = foreign_topology
        .components()
        .flat_map(|c| c.incoming_uses())
        .next()
        .unwrap();
    let before = batch.counters();
    let solved_before = solved.counters();
    assert!(matches!(
        topology.use_closed_scheme(&foreign_solved, occurrence),
        Err(SccClosedSchemeLookupError::ForeignCollection)
    ));
    assert!(matches!(
        topology.use_closed_scheme(&solved, foreign_use),
        Err(SccClosedSchemeLookupError::ForeignCollection)
    ));
    assert!(matches!(
        foreign_topology.use_closed_scheme(&solved, occurrence),
        Err(SccClosedSchemeLookupError::ForeignCollection)
    ));
    let mut missing_use = batch.clone();
    missing_use
        .definition_use_positions
        .remove(occurrence.collection_identity());
    assert!(matches!(
        missing_use
            .shadow_scc_topology()
            .use_closed_scheme(&solved, occurrence),
        Err(SccClosedSchemeLookupError::MissingIdentity)
    ));
    let target = &batch.definition_uses
        [batch.definition_use_positions[occurrence.collection_identity()]]
    .target;
    let mut missing_target = batch.clone();
    missing_target.definition_positions.remove(target);
    assert!(matches!(
        missing_target
            .shadow_scc_topology()
            .use_closed_scheme(&solved, occurrence),
        Err(SccClosedSchemeLookupError::MissingIdentity)
    ));
    assert_eq!(before, batch.counters());
    assert_eq!(solved_before, solved.counters());
}

#[cfg(feature = "shadow-f5")]
#[test]
fn closed_scheme_join_does_not_supply_absent_mutual_recursive_skeleton() {
    let parsed = parsed("my a = b; my b = a");
    let batch = source_batch(&parsed);
    let solved = crate::SolvedModule::solve(batch.clone()).unwrap();
    let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed).unwrap();
    let crosswalk = shadow.skeleton_source_crosswalk();
    let topology = batch.shadow_scc_topology();
    let before = batch.counters();
    let solved_before = solved.counters();
    assert!(shadow.skeleton().is_err());
    assert_eq!(topology.components().count(), 1);
    assert_eq!(topology.definitions().count(), 2);
    for definition in topology.definitions() {
        assert!(
            topology
                .definition_closed_scheme(&solved, definition)
                .is_ok()
        );
        assert!(
            topology
                .definition_shadow_ref(&crosswalk, definition)
                .unwrap()
                .is_none()
        );
    }
    for occurrence in topology
        .components()
        .flat_map(|component| component.internal_uses())
    {
        let record = &batch.definition_uses
            [batch.definition_use_positions[occurrence.collection_identity()]];
        let target = topology
            .definitions()
            .find(|definition| definition.collection_identity() == &record.target)
            .unwrap();
        assert!(
            topology
                .use_closed_scheme(&solved, occurrence)
                .unwrap()
                .same_identity(topology.definition_closed_scheme(&solved, target).unwrap())
        );
    }
    assert_eq!(before, batch.counters());
    assert_eq!(solved_before, solved.counters());
}

#[cfg(feature = "shadow-f5")]
#[test]
fn pending_use_instantiation_preserves_distinct_uses_and_empty_premises() {
    use crate::shadow_scc::{PendingSccGeneralizationPremise, PendingUseInstantiationPremise};
    for source in ["my a = 42; my b = a; my c = a", "my a = b; my b = a"] {
        let parsed = parsed(source);
        let batch = source_batch(&parsed);
        let solved = crate::SolvedModule::solve(batch.clone()).unwrap();
        let shadow = yu_hir::shadow::ShadowArtifact::from_parsed(parsed).unwrap();
        assert!(shadow.skeleton().is_err());
        let crosswalk = shadow.skeleton_source_crosswalk();
        let before = batch.counters();
        let solved_before = solved.counters();
        let topology = batch.shadow_scc_topology();
        let carriers = topology
            .components()
            .flat_map(|c| c.internal_uses().chain(c.incoming_uses()))
            .map(|u| topology.pending_use_instantiation(&solved, u).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(carriers.len(), 2);
        assert!(
            !carriers[0]
                .occurrence()
                .same_identity(carriers[1].occurrence())
        );
        for carrier in &carriers {
            let (parent, target) = topology.use_definitions(carrier.occurrence()).unwrap();
            assert!(carrier.parent().same_identity(parent));
            assert!(carrier.target().same_identity(target));
            assert!(
                carrier
                    .target_component()
                    .same_identity(topology.component_of(target).unwrap())
            );
            assert!(
                carrier.current_scheme().same_identity(
                    topology
                        .use_closed_scheme(&solved, carrier.occurrence())
                        .unwrap()
                )
            );
            assert_eq!(carrier.current_scheme().quantifiers().count(), 0);
            assert_eq!(carrier.current_scheme().recursive_binders().count(), 0);
            assert_eq!(
                carrier.pending_generalization().premise(),
                PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
            );
            assert_eq!(
                carrier.qr_correspondence_premise(),
                PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved
            );
            assert_eq!(
                carrier.shared_contract_transport_premise(),
                PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved
            );
            assert!(
                topology
                    .use_shadow_ref(&crosswalk, carrier.occurrence())
                    .unwrap()
                    .is_none()
            );
        }
        assert!(
            carriers[0]
                .target_component()
                .same_identity(carriers[1].target_component())
        );
        if source.starts_with("my a = 42") {
            assert!(carriers[0].target().same_identity(carriers[1].target()));
            assert!(
                carriers[0]
                    .current_scheme()
                    .same_identity(carriers[1].current_scheme())
            );
        }
        assert_eq!(before, batch.counters());
        assert_eq!(solved_before, solved.counters());
    }
}

#[cfg(feature = "shadow-f5")]
#[test]
fn pending_use_instantiation_rejects_foreign_and_missing_evidence() {
    use crate::shadow_scc::{
        PendingUseInstantiationLookupError as Error, SccClosedSchemeLookupError,
        SccTopologyLookupError,
    };
    let batch = source_batch(&parsed("my a = 42; my b = a"));
    let foreign = collect(batch.hir().clone());
    let solved = crate::SolvedModule::solve(batch.clone()).unwrap();
    let foreign_solved = crate::SolvedModule::solve(foreign.clone()).unwrap();
    let topology = batch.shadow_scc_topology();
    let occurrence = topology
        .components()
        .flat_map(|c| c.incoming_uses())
        .next()
        .unwrap();
    let foreign_use = foreign
        .shadow_scc_topology()
        .components()
        .flat_map(|c| c.incoming_uses())
        .next()
        .unwrap();
    assert!(matches!(
        topology.pending_use_instantiation(&solved, foreign_use),
        Err(Error::Topology(SccTopologyLookupError::ForeignArtifact))
    ));
    assert!(matches!(
        topology.pending_use_instantiation(&foreign_solved, occurrence),
        Err(Error::ClosedScheme(
            SccClosedSchemeLookupError::ForeignCollection
        ))
    ));
    let mut missing = batch.clone();
    missing
        .definition_use_positions
        .remove(occurrence.collection_identity());
    assert!(matches!(
        missing
            .shadow_scc_topology()
            .pending_use_instantiation(&solved, occurrence),
        Err(Error::Topology(SccTopologyLookupError::MissingIdentity))
    ));
    let mut missing = batch.clone();
    missing.definition_uses[0].target =
        crate::DefinitionOrderId::new(missing.collection_artifact.clone(), u32::MAX);
    assert!(matches!(
        missing
            .shadow_scc_topology()
            .pending_use_instantiation(&solved, occurrence),
        Err(Error::Topology(SccTopologyLookupError::MissingIdentity))
    ));
    let mut missing = batch.clone();
    missing
        .definition_positions
        .remove(&batch.definition_uses[0].target);
    assert!(matches!(
        missing
            .shadow_scc_topology()
            .pending_use_instantiation(&solved, occurrence),
        Err(Error::ClosedScheme(
            SccClosedSchemeLookupError::MissingIdentity
        ))
    ));
}
