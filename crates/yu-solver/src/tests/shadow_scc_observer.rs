use super::{collect, module};

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
