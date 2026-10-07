#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{ShadowArtifact, ShadowError};
use yu_core::shadow_derivation::RawStructuralArena;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn artifact(source: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap()
}

#[test]
fn repeated_calls_share_exact_binder_and_preserve_each_registration() {
    let artifact = artifact("my repeated f x = f (f x)");
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
    let retained = arena
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    assert_eq!(retained.len(), 2);
    let binder = retained[0].source_use_input.binder();
    let groups = arena.pending_binder_use_groups();
    let grouped = groups
        .registrations_for_binder(binder)
        .unwrap()
        .collect::<Vec<_>>();
    assert_eq!(grouped.len(), 2);
    assert_ne!(grouped[0].source, grouped[1].source);
    assert_ne!(
        grouped[0].source_use_input.occurrence(),
        grouped[1].source_use_input.occurrence()
    );
    for (actual, expected) in grouped.iter().zip(&retained) {
        assert_eq!(actual.source_use_input.binder(), binder);
        assert!(std::ptr::eq(actual.source, expected.source));
        assert!(std::ptr::eq(actual.application, expected.application));
        assert!(std::ptr::eq(
            actual.source_use_input,
            expected.source_use_input
        ));
        assert!(std::ptr::eq(
            actual.application_premises,
            expected.application_premises
        ));
        assert_eq!(
            actual.capture.map(std::ptr::from_ref),
            expected.capture.map(std::ptr::from_ref)
        );
        // This existing projection lacks a declaration join; grouping supplies none.
        assert!(actual.parameter_declaration.is_none());
        assert!(actual.source_view_premise_locator().is_none());
        assert_eq!(actual.application_premises.len(), 8);
    }
}

#[test]
fn distinct_binders_keep_exact_annotation_incidences_separate() {
    let artifact = artifact("my apply x (f: T) (g: T) = f (g x)");
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
    let retained = arena
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    assert_eq!(retained.len(), 2);
    assert_ne!(
        retained[0].source_use_input.binder(),
        retained[1].source_use_input.binder()
    );
    let groups = arena.pending_binder_use_groups();
    for expected in retained {
        let mut grouped = groups
            .registrations_for_binder(expected.source_use_input.binder())
            .unwrap();
        let actual = grouped.next().unwrap();
        assert!(grouped.next().is_none());
        assert!(std::ptr::eq(
            actual.source_use_input,
            expected.source_use_input
        ));
        let mut annotations = actual.source_use_input.parameter_annotations();
        let incidence = annotations.next().unwrap();
        assert!(annotations.next().is_none());
        assert_eq!(incidence.parameter(), actual.source_use_input.binder());
        assert!(std::ptr::eq(
            incidence,
            expected
                .source_use_input
                .parameter_annotations()
                .next()
                .unwrap()
        ));
    }
}

#[test]
fn grouped_and_computed_callees_keep_only_existing_direct_use_registrations() {
    for (source, count) in [("my grouped f = (f) 1", 0), ("my computed f = (f 1) 1", 1)] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        let binder = skeleton
            .expressions()
            .iter()
            .find_map(|expression| {
                if let yu_core::shadow::Form::Use { binder, .. } = expression.form() {
                    Some(binder)
                } else {
                    None
                }
            })
            .unwrap();
        let groups = arena.pending_binder_use_groups();
        let grouped = groups
            .registrations_for_binder(binder)
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(grouped.len(), count);
        if let Some(registration) = grouped.first() {
            assert_eq!(
                skeleton.expression(registration.source).unwrap().range(),
                &(17..20)
            );
        }
        // Both raw Apply inventories retain calls without a direct-use registration.
        assert!(
            arena.nodes().iter().any(
                |node| node.call.is_some() && node.pending_source_call_registration().is_none()
            )
        );
    }
}

#[test]
fn foreign_binder_is_rejected_and_retained_registration_stays_branded() {
    let first = artifact("my apply f = f 1");
    let foreign = artifact("my apply f = f 1");
    let arena = RawStructuralArena::from_artifact(&first).unwrap();
    let foreign_arena = RawStructuralArena::from_artifact(&foreign).unwrap();
    let retained = arena
        .nodes()
        .iter()
        .find_map(|node| node.pending_source_call_registration())
        .unwrap();
    let foreign_registration = foreign_arena
        .nodes()
        .iter()
        .find_map(|node| node.pending_source_call_registration())
        .unwrap();
    let groups = arena.pending_binder_use_groups();
    assert!(
        groups
            .registrations_for_binder(foreign_registration.source_use_input.binder())
            .is_none()
    );
    let registration = groups
        .registrations_for_binder(retained.source_use_input.binder())
        .unwrap()
        .next()
        .unwrap();
    assert_eq!(
        foreign
            .skeleton()
            .unwrap()
            .binder(registration.source_use_input.binder())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        foreign
            .skeleton()
            .unwrap()
            .use_expression(registration.source_use_input.occurrence())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        foreign
            .skeleton()
            .unwrap()
            .expression(registration.source)
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
    let unsupported = artifact("my constant x = \"unsupported\"");
    assert!(RawStructuralArena::from_artifact(&unsupported).is_none());
}
