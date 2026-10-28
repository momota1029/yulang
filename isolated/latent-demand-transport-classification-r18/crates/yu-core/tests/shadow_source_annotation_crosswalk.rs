#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Correspondence, ShadowArtifact};
use yu_core::shadow_source_annotation_crosswalk::{
    CallProjection, CrosswalkError, UnresolvedPremise, source_annotation_crosswalk,
};
use yu_hir::shadow::{
    ResolvedCallInventoryError, SourceIdentityError, lower_module_with_shadow_applications,
    lower_module_with_shadow_local_binding,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn artifact(text: &str) -> Arc<ShadowArtifact> {
    let source: Arc<SourceText> = Arc::from(text);
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    Arc::new(ShadowArtifact::from_parsed(parsed).unwrap())
}

fn identity() -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("test", "crosswalk.yu")))
}

fn hir(source: &Arc<ShadowArtifact>, local: bool) -> HirModule {
    if local {
        lower_module_with_shadow_local_binding(
            identity(),
            source.parsed(),
            SemanticImports::empty(),
            source.clone(),
        )
    } else {
        lower_module_with_shadow_applications(identity(), source.parsed(), SemanticImports::empty())
    }
    .unwrap()
}

fn roots(module: &HirModule) -> Vec<&yu_hir::DefinitionRootId> {
    module
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding.definition_root()),
            _ => None,
        })
        .collect()
}

#[test]
fn leaf_nested_and_cold_local_calls_retain_exact_ids_diagnostics_and_ancestry() {
    for (text, local, count) in [
        ("my apply f = f 1", false, 1),
        ("my apply f = f(f 1)", false, 2),
        ("my apply f = f 1 2", false, 2),
        ("my apply f = { my step x = f x; step }", true, 1),
    ] {
        let source = artifact(text);
        let module = hir(&source, local);
        let root = roots(&module)[0];
        let crosswalk = source_annotation_crosswalk(&module, root, &source).unwrap();
        let inventory = module.shadow_resolved_call_inventory(root).unwrap();
        let CallProjection::Retained(calls) = &crosswalk.calls else {
            panic!("retained calls")
        };
        assert_eq!(calls.len(), count);
        assert_eq!(calls.len(), inventory.len());
        for left in 0..calls.len() {
            for right in left + 1..calls.len() {
                assert_ne!(
                    calls[left].identity.occurrence, calls[right].identity.occurrence,
                    "{text}"
                );
                assert_ne!(calls[left].call.id, calls[right].call.id, "{text}");
            }
        }
        assert_eq!(
            crosswalk.boundary.id,
            source.definition_source_position(&module, root).unwrap()
        );
        for (call, expected) in calls.iter().zip(inventory) {
            assert!(std::ptr::eq(call.identity.occurrence, expected.occurrence));
            assert!(std::ptr::eq(call.identity.callee, expected.callee));
            assert!(std::ptr::eq(call.identity.argument, expected.argument));
            assert!(std::ptr::eq(call.identity.errors, expected.errors));
            assert!(!call.identity.errors.is_empty());
            assert!(call.identity.errors.iter().any(|id| {
                module.errors().iter().any(|error| {
                    error.id() == *id && error.kind() == yu_hir::HirErrorKind::UnsupportedExpression
                })
            }));
            for id in call.identity.errors {
                assert!(module.errors().iter().any(|error| error.id() == *id));
            }
            assert_eq!(call.identity.source_form, expected.source_form);
            for (position, occurrence) in [
                (&call.call, expected.occurrence),
                (&call.callee, expected.callee),
                (&call.argument, expected.argument),
            ] {
                assert_eq!(
                    position.id,
                    source
                        .occurrence_source_position(&module, occurrence)
                        .unwrap()
                );
                assert!(std::ptr::eq(
                    position.position,
                    source.position(&position.id).unwrap()
                ));
                let mut parent = position.position.parent();
                while parent != Some(&crosswalk.boundary.id) {
                    parent = source
                        .position(parent.expect("exact retained ancestry"))
                        .unwrap()
                        .parent();
                }
            }
        }
        assert_eq!(crosswalk.unresolved_premises().len(), 9);
        assert!(
            crosswalk
                .unresolved_premises()
                .contains(&UnresolvedPremise::SourceCallCompleteness)
        );
    }
}

#[test]
fn annotations_are_definition_inventory_and_siblings_remain_isolated() {
    let source = artifact("my first f = f 1; my second x = x as T");
    let module = hir(&source, false);
    let roots = roots(&module);
    let first = source_annotation_crosswalk(&module, roots[0], &source).unwrap();
    assert!(matches!(&first.calls, CallProjection::Retained(calls) if calls.len() == 1));
    assert!(first.annotations.is_empty());
    assert_eq!(source.annotations().len(), 1);
    let second_crosswalk = source_annotation_crosswalk(&module, roots[1], &source).unwrap();
    assert!(matches!(
        second_crosswalk.calls,
        CallProjection::Unsupported(ResolvedCallInventoryError::UnsupportedProjection)
    ));
    assert_eq!(second_crosswalk.annotations.len(), 1);
    let second_boundary = source
        .definition_source_position(&module, roots[1])
        .unwrap();
    let second =
        yu_core::shadow_annotation_boundaries::annotation_boundaries(&source, &second_boundary)
            .unwrap();
    assert_eq!(second.len(), 1);
    assert_eq!(
        second[0].position.kind(),
        yu_syntax::SyntaxKind::TypeAnnotationTail
    );
    assert_eq!(
        second[0].occurrence.correspondence(),
        &Correspondence::PendingTypedPortAndProfile
    );
}

#[test]
fn nested_annotations_are_retained_and_unsupported_hir_projection_fails_closed() {
    let source = artifact("my outer f = { my inner (x: T) = f x as T; inner }");
    let module = hir(&source, false);
    let root = roots(&module)[0];
    let boundary = source.definition_source_position(&module, root).unwrap();
    let annotations =
        yu_core::shadow_annotation_boundaries::annotation_boundaries(&source, &boundary).unwrap();
    assert_eq!(annotations.len(), 2);
    assert_eq!(
        annotations[0].position.kind(),
        yu_syntax::SyntaxKind::PatternTypeAnnotation
    );
    assert_eq!(
        annotations[1].position.kind(),
        yu_syntax::SyntaxKind::TypeAnnotationTail
    );
    for annotation in annotations {
        assert_eq!(annotation.boundary, &boundary);
        assert_eq!(
            annotation.occurrence.correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
        let mut ancestor = annotation.position.parent().unwrap();
        while source.position(ancestor).unwrap().kind() != yu_syntax::SyntaxKind::BindingStatement {
            ancestor = source.position(ancestor).unwrap().parent().unwrap();
        }
        assert_ne!(ancestor, &boundary);
    }
    let crosswalk = source_annotation_crosswalk(&module, root, &source).unwrap();
    assert!(matches!(
        crosswalk.calls,
        CallProjection::Unsupported(ResolvedCallInventoryError::UnsupportedProjection)
    ));
    assert_eq!(crosswalk.annotations.len(), 2);
    assert!(matches!(
        lower_module_with_shadow_local_binding(
            identity(),
            source.parsed(),
            SemanticImports::empty(),
            source.clone()
        ),
        Err(yu_hir::HirAvailabilityError::StructuralProjection)
    ));
}

#[test]
fn foreign_roots_and_separately_parsed_equal_source_fail_closed() {
    let source = artifact("my apply f = f 1");
    let module = hir(&source, false);
    let foreign_module = hir(&source, false);
    let foreign_source = artifact("my apply f = f 1");
    assert_eq!(
        source_annotation_crosswalk(&module, roots(&foreign_module)[0], &source).unwrap_err(),
        CrosswalkError::Identity(SourceIdentityError::ForeignHirArtifact)
    );
    assert_eq!(
        source_annotation_crosswalk(&module, roots(&module)[0], &foreign_source).unwrap_err(),
        CrosswalkError::Identity(SourceIdentityError::ForeignParse)
    );
    let ordinary =
        yu_hir::lower_module(identity(), source.parsed(), SemanticImports::empty()).unwrap();
    assert_eq!(
        source_annotation_crosswalk(&ordinary, roots(&ordinary)[0], &source).unwrap_err(),
        CrosswalkError::Identity(SourceIdentityError::MissingSource)
    );
}

#[test]
fn empty_retained_inventory_keeps_source_completeness_pending_and_ordinary_lowering_unchanged() {
    for text in ["my id x = x", "my apply f = f 1"] {
        let source = artifact(text);
        let before = yu_hir::lower_module(identity(), source.parsed(), SemanticImports::empty());
        let module = hir(&source, false);
        let crosswalk = source_annotation_crosswalk(&module, roots(&module)[0], &source).unwrap();
        if text == "my id x = x" {
            assert!(
                matches!(&crosswalk.calls, CallProjection::Retained(calls) if calls.is_empty())
            );
            assert!(
                crosswalk
                    .unresolved_premises()
                    .contains(&UnresolvedPremise::SourceCallCompleteness)
            );
        }
        let after = yu_hir::lower_module(identity(), source.parsed(), SemanticImports::empty());
        assert_eq!(before, after);
    }
}
