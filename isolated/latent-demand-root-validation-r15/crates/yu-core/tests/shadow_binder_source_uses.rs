#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact, ShadowError};
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
fn inventory_preserves_argument_returned_grouped_and_direct_use_identities() {
    for (source, occurrences, registrations) in [
        ("my argument f = f f", 2, 1),
        ("my returned f = f", 1, 0),
        ("my grouped f = (f) 1", 1, 0),
        ("my repeated f x = f (f x)", 2, 2),
        ("my computed f = (f 1) 1", 1, 1),
        ("my apply f = { my step x = f x; step }", 1, 1),
    ] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        let binder = arena
            .nodes()
            .iter()
            .find_map(|node| match node.form {
                Form::Use { binder, .. } => Some(binder),
                _ => None,
            })
            .unwrap();
        let expected = arena
            .nodes()
            .iter()
            .filter_map(|node| match node.form {
                Form::Use {
                    binder: retained,
                    occurrence,
                } if retained == binder => Some((&node.source, retained, occurrence)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(expected.len(), occurrences, "{source}");
        let groups = arena.source_binder_use_groups();
        let actual = groups.uses_for_binder(binder).unwrap().collect::<Vec<_>>();
        assert_eq!(actual.len(), occurrences, "{source}");
        for (actual, (source, binder, occurrence)) in actual.iter().zip(expected) {
            assert!(std::ptr::eq(actual.source, source));
            assert!(std::ptr::eq(actual.binder, binder));
            assert!(std::ptr::eq(actual.occurrence, occurrence));
            assert!(std::ptr::eq(
                skeleton.expression(actual.source).unwrap(),
                skeleton.use_expression(actual.occurrence).unwrap()
            ));
        }
        for (index, current) in actual.iter().enumerate() {
            for earlier in &actual[..index] {
                assert_ne!(current.source, earlier.source);
                assert_ne!(current.occurrence, earlier.occurrence);
            }
        }
        assert_eq!(
            arena
                .pending_binder_use_groups()
                .registrations_for_binder(binder)
                .unwrap()
                .count(),
            registrations,
            "{source}"
        );
    }
}

#[test]
fn exact_binders_separate_retained_parameters_and_allow_empty_inventory() {
    let nested = artifact("my apply f = { my step x = f x; step }");
    let skeleton = nested.skeleton().unwrap();
    let arena = RawStructuralArena::from_artifact(&nested).unwrap();
    let groups = arena.source_binder_use_groups();
    let parameters = arena
        .nodes()
        .iter()
        .filter_map(|node| match node.form {
            Form::Lambda { parameter, .. } => Some(parameter),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(parameters.len(), 2);
    assert_ne!(parameters[0], parameters[1]);
    for parameter in parameters {
        let uses = groups
            .uses_for_binder(parameter)
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(uses.len(), 1);
        assert_eq!(uses[0].binder, parameter);
        skeleton.use_expression(uses[0].occurrence).unwrap();
    }

    let unused = artifact("my unused f = 1");
    let arena = RawStructuralArena::from_artifact(&unused).unwrap();
    let parameter = arena
        .nodes()
        .iter()
        .find_map(|node| match node.form {
            Form::Lambda { parameter, .. } => Some(parameter),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        arena
            .source_binder_use_groups()
            .uses_for_binder(parameter)
            .unwrap()
            .count(),
        0
    );
}

#[test]
fn foreign_binder_is_rejected_and_returned_identities_keep_artifact_brand() {
    let first = artifact("my returned f = f");
    let foreign = artifact("my returned f = f");
    let arena = RawStructuralArena::from_artifact(&first).unwrap();
    let foreign_arena = RawStructuralArena::from_artifact(&foreign).unwrap();
    let binder = |node: &yu_core::shadow_derivation::RawNode<'_>| match node.form {
        Form::Use { binder, .. } => Some(binder.clone()),
        _ => None,
    };
    let retained = arena.nodes().iter().find_map(binder).unwrap();
    let other = foreign_arena.nodes().iter().find_map(binder).unwrap();
    let groups = arena.source_binder_use_groups();
    assert!(groups.uses_for_binder(&other).is_none());
    let actual = groups.uses_for_binder(&retained).unwrap().next().unwrap();
    let foreign_skeleton = foreign.skeleton().unwrap();
    assert_eq!(
        foreign_skeleton.binder(actual.binder).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        foreign_skeleton.expression(actual.source).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        foreign_skeleton
            .use_expression(actual.occurrence)
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}
