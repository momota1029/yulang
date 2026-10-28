#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact};
use yu_core::shadow_call_formation::{
    Address, UnresolvedPremise, generate_captured_singleton, generate_source_calls,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn artifact(text: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(text);
    let header = Arc::new(scan_header(source.clone()));
    ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap()
}

#[test]
fn ordinary_source_calls_retain_branded_ids_and_unresolved_source_base() {
    for text in ["my apply f = f 1", "my apply f x = f x"] {
        let source = artifact(text);
        let declaration = source.raw_declaration_positions().next().unwrap();
        let skeleton = source.declaration_skeleton(&declaration).unwrap();
        let records = generate_source_calls(&source, &declaration).unwrap();
        let inputs: Vec<_> = skeleton.source_call_use_inputs().collect();
        assert_eq!(records.len(), 1);
        assert_eq!(records.len(), inputs.len());
        for (record, input) in records.iter().zip(inputs.iter()) {
            assert_eq!(record.call(), input.application().expression());
            assert_eq!(record.callee_use(), input.occurrence());
            assert_eq!(record.argument(), input.argument());
            let expected_use = match skeleton.expression(input.argument()).unwrap().form() {
                Form::Use { occurrence, .. } => Some(occurrence),
                _ => None,
            };
            assert_eq!(record.argument_use(), expected_use);
            assert_eq!(
                record.unresolved_premises(),
                &[
                    UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
                    UnresolvedPremise::InitialSourceDescriptorRelation,
                    UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
                    UnresolvedPremise::CompleteInvocationInterpretation,
                ]
            );
            let foreign = artifact(text);
            assert!(
                foreign
                    .skeleton()
                    .unwrap()
                    .expression(record.call())
                    .is_err()
            );
            assert!(generate_source_calls(&foreign, &declaration).is_none());
        }
    }
}

#[test]
fn ordinary_source_call_projection_is_partial_and_scopes_annotation_rejection() {
    for (text, expected_calls) in [("my grouped f = (f) 1", 0), ("my computed f = (f 1) 2", 1)] {
        let source = artifact(text);
        let declaration = source.raw_declaration_positions().next().unwrap();
        let records = generate_source_calls(&source, &declaration).unwrap();
        assert_eq!(records.len(), expected_calls, "{text}");
    }

    // A sibling annotation does not alter the exact selected declaration's
    // structural inventory.
    let source = artifact("my apply f = f 1; my annotated = 1 as int");
    let declarations: Vec<_> = source.raw_declaration_positions().collect();
    assert_eq!(declarations.len(), 2);
    assert!(!source.annotations().is_empty());
    assert_eq!(
        generate_source_calls(&source, &declarations[0])
            .unwrap()
            .len(),
        1
    );

    // An annotation inside an otherwise projectable selected call remains
    // unresolved and blocks this partial generator.
    let annotated_call = artifact("my apply (f: T) = f 1");
    let declaration = annotated_call.raw_declaration_positions().next().unwrap();
    assert_eq!(
        annotated_call
            .declaration_skeleton(&declaration)
            .unwrap()
            .source_call_use_inputs()
            .count(),
        1
    );
    assert!(
        !yu_core::shadow_annotation_boundaries::annotation_boundaries(
            &annotated_call,
            &declaration
        )
        .unwrap()
        .is_empty()
    );
    assert!(generate_source_calls(&annotated_call, &declaration).is_none());

    // A selected declaration containing only an annotation also remains
    // fail-closed, even when this partial call projection has no source calls.
    assert!(generate_source_calls(&source, &declarations[1]).is_none());
}

#[test]
fn captured_singleton_retains_distinct_static_incidence_and_pending_bridges() {
    let source = artifact("my apply f = { my step x = f x; step }");
    let [record] = generate_captured_singleton(&source).unwrap();
    let skeleton = source.skeleton().unwrap();
    let input = skeleton.captured_call_input().unwrap();
    assert_eq!(
        record.demand().registration.declaration,
        input.outer_parameter()
    );
    assert_eq!(record.demand().registration.outer_scope, skeleton.body());
    assert_eq!(record.demand().local_scope, input.local_lambda());
    assert_eq!(record.callee_use(), Address::CalleeUse(input.callee_use()));
    assert_eq!(record.returned_use(), input.returned_use());
    let addresses = [
        record.callee_use(),
        record.upper_checking(),
        record.source_position(),
        record.invocation_output(),
    ];
    for (index, address) in addresses.iter().enumerate() {
        assert!(!addresses[index + 1..].contains(address));
    }
    let effect = record.call_effect();
    assert!(std::ptr::eq(effect.record(), &record));
    assert!(std::ptr::eq(effect.root().demand(), record.demand()));
    assert_eq!(record.unresolved_premises().len(), 10);
    for premise in [
        UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
        UnresolvedPremise::InitialSourceDescriptorRelation,
        UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
    ] {
        assert!(record.unresolved_premises().contains(&premise));
    }
    assert!(
        record
            .unresolved_premises()
            .contains(&UnresolvedPremise::EmittedGenCall0Membership)
    );
    assert!(
        record
            .unresolved_premises()
            .contains(&UnresolvedPremise::CompleteInvocationInterpretation)
    );
    assert!(
        record
            .unresolved_premises()
            .contains(&UnresolvedPremise::LegalOldWholeTupleSubstitution)
    );
    // Formation does not discharge missing original assumptions.
    assert_eq!(
        effect.record().unresolved_premises(),
        record.unresolved_premises()
    );
}

#[test]
fn retained_topology_accepts_whitespace_and_ordinary_apply_is_not_promoted() {
    let spaced = artifact("my apply f = {  my step x = f x;  step }");
    assert!(generate_captured_singleton(&spaced).is_some());
    for source in [
        "my apply f x = f x",
        "my apply f = { my step x = f x; step 0 }",
    ] {
        assert!(generate_captured_singleton(&artifact(source)).is_none());
    }
}

#[test]
fn formation_has_no_string_or_solver_semantic_evidence() {
    let implementation = include_str!("../src/shadow_call_formation.rs");
    for shortcut in [
        "artifact.source(",
        "interpret_old(",
        "solver::",
        "my apply f =",
        "parse_file(",
    ] {
        assert!(
            !implementation.contains(shortcut),
            "unexpected semantic shortcut: {shortcut}"
        );
    }
}

#[test]
fn resolved_source_calls_transport_direct_and_captured_inventory_without_evidence() {
    use yu_core::shadow_call_formation::generate_resolved_source_calls;
    use yu_hir::shadow::{
        ResolvedCallInventoryError, lower_module_with_shadow_applications,
        lower_module_with_shadow_local_binding,
    };
    use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, SemanticImports};

    for (text, captured) in [
        ("my apply f = f 1; my other g = g 2", false),
        (
            "my apply f = { my step x = f x; step }; my other g = g 2",
            true,
        ),
    ] {
        let source = Arc::new(artifact(text));
        let parsed = source.parsed().clone();
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new("test", "pending.yu")));
        let hir = if captured {
            lower_module_with_shadow_local_binding(
                identity.clone(),
                &parsed,
                SemanticImports::empty(),
                source.clone(),
            )
        } else {
            lower_module_with_shadow_applications(
                identity.clone(),
                &parsed,
                SemanticImports::empty(),
            )
        }
        .unwrap();
        let roots: Vec<_> = hir
            .items()
            .iter()
            .filter_map(|item| match item {
                HirItem::Binding(binding) => Some(binding.definition_root()),
                _ => None,
            })
            .collect();
        let mut calls = Vec::new();
        for root in &roots {
            let inventory = hir.shadow_resolved_call_inventory(root).unwrap();
            let pending = generate_resolved_source_calls(&hir, root).unwrap();
            assert_eq!(pending.len(), 1);
            assert_eq!(pending.len(), inventory.len());
            for (stub, row) in pending.iter().zip(&inventory) {
                assert!(std::ptr::eq(stub.root(), *root));
                assert!(std::ptr::eq(stub.call().occurrence, row.occurrence));
                assert!(std::ptr::eq(stub.call().callee, row.callee));
                assert!(std::ptr::eq(stub.call().argument, row.argument));
                assert_eq!(stub.call().source_form, row.source_form);
                assert!(std::ptr::eq(stub.call().errors, row.errors));
                let declaration = source.raw_declaration_positions().next().unwrap();
                let source_calls = generate_source_calls(&source, &declaration).unwrap();
                assert_eq!(
                    stub.unresolved_premises(),
                    source_calls[0].unresolved_premises()
                );
                calls.push(stub.call().occurrence);
            }
        }
        assert_ne!(calls[0], calls[1]);
        let foreign = if captured {
            lower_module_with_shadow_local_binding(
                identity.clone(),
                &parsed,
                SemanticImports::empty(),
                source,
            )
        } else {
            lower_module_with_shadow_applications(
                identity.clone(),
                &parsed,
                SemanticImports::empty(),
            )
        }
        .unwrap();
        assert_eq!(
            generate_resolved_source_calls(&foreign, roots[0]).unwrap_err(),
            ResolvedCallInventoryError::ForeignRoot
        );
        let ordinary = yu_hir::lower_module(identity, &parsed, SemanticImports::empty()).unwrap();
        let HirItem::Binding(binding) = &ordinary.items()[0] else {
            panic!("binding")
        };
        assert_eq!(
            generate_resolved_source_calls(&ordinary, binding.definition_root()).unwrap_err(),
            ResolvedCallInventoryError::UnsupportedProjection
        );
    }
}
