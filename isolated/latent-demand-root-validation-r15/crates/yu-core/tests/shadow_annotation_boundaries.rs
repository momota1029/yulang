#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Correspondence, ShadowArtifact, ShadowError};
use yu_core::shadow_annotation_boundaries::{AnnotationBoundaryError, annotation_boundaries};
use yu_syntax::{SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

fn artifact(source: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    ShadowArtifact::from_parsed(parsed).unwrap()
}

#[test]
fn exact_declarations_preserve_both_annotation_families_and_repeated_occurrences() {
    let source = artifact("my first (x: T) (y: T) = x as T; my second (x: T) = x as T");
    let roots = source.raw_declaration_positions().collect::<Vec<_>>();
    assert_eq!(roots.len(), 2);
    let first = annotation_boundaries(&source, &roots[0]).unwrap();
    let second = annotation_boundaries(&source, &roots[1]).unwrap();
    assert_eq!(first.len(), 3);
    assert_eq!(second.len(), 2);
    assert_eq!(source.annotations().len(), 5);
    for (inventory, root) in [(&first, &roots[0]), (&second, &roots[1])] {
        assert_eq!(
            inventory.last().unwrap().position.kind(),
            SyntaxKind::TypeAnnotationTail
        );
        for item in &inventory[..inventory.len() - 1] {
            assert_eq!(item.position.kind(), SyntaxKind::PatternTypeAnnotation);
        }
        for item in inventory {
            assert_eq!(item.boundary, root);
            assert!(std::ptr::eq(
                item.occurrence,
                source.annotation(item.occurrence.id()).unwrap()
            ));
            assert!(std::ptr::eq(
                item.position,
                source.position(item.occurrence.position()).unwrap()
            ));
            assert_eq!(
                item.occurrence.correspondence(),
                &Correspondence::PendingTypedPortAndProfile
            );
            let mut parent = item.position.parent();
            while parent != Some(root) {
                parent = source
                    .position(parent.expect("ancestor boundary"))
                    .unwrap()
                    .parent();
            }
        }
        for pair in inventory.windows(2) {
            assert!(pair[0].position.range().start < pair[1].position.range().start);
            assert_ne!(pair[0].occurrence.id(), pair[1].occurrence.id());
            assert_ne!(pair[0].occurrence.position(), pair[1].occurrence.position());
        }
    }
    for left in &first {
        for right in &second {
            assert_ne!(left.occurrence.id(), right.occurrence.id());
        }
    }
    for (item, retained) in first.iter().chain(&second).zip(source.annotations()) {
        assert!(std::ptr::eq(item.occurrence, retained));
    }
}

#[test]
fn foreign_and_non_binding_roots_fail_closed_and_empty_inventory_is_exact() {
    let source = artifact("my first (x: T) = x; my second x = x");
    let foreign = artifact("my first (x: T) = x; my second x = x");
    let roots = source.raw_declaration_positions().collect::<Vec<_>>();
    let foreign_root = foreign.raw_declaration_positions().next().unwrap();
    assert_eq!(
        annotation_boundaries(&source, &foreign_root).unwrap_err(),
        AnnotationBoundaryError::Source(ShadowError::ForeignArtifact)
    );
    assert_eq!(
        annotation_boundaries(&source, source.annotations()[0].position()).unwrap_err(),
        AnnotationBoundaryError::NonBindingRoot
    );
    assert!(
        annotation_boundaries(&source, &roots[1])
            .unwrap()
            .is_empty()
    );
}

#[test]
fn selected_nested_boundary_uses_exact_ancestry() {
    let source = artifact("my outer (x: T) = { my inner (y: T) = y as T; x as T }");
    let outer = source.raw_declaration_positions().next().unwrap();
    let outer_inventory = annotation_boundaries(&source, &outer).unwrap();
    assert_eq!(outer_inventory.len(), 4);
    let mut ancestor = outer_inventory[1].position.parent().unwrap();
    while source.position(ancestor).unwrap().kind() != SyntaxKind::BindingStatement {
        ancestor = source.position(ancestor).unwrap().parent().unwrap();
    }
    assert_ne!(ancestor, &outer);
    let nested = annotation_boundaries(&source, ancestor).unwrap();
    assert_eq!(nested.len(), 2);
    for (item, retained) in nested.iter().zip(&outer_inventory[1..3]) {
        assert_eq!(item.boundary, ancestor);
        assert!(std::ptr::eq(item.occurrence, retained.occurrence));
    }
}
