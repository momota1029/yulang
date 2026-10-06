#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact};
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
fn raw_inventory_borrows_every_form_and_exact_ordered_call_premises() {
    for source in [
        "my identity x = x",
        "my compose f g x = f (g x)",
        "my repeated f x = f (f x)",
        "my chain f x = f x x",
        "my grouped f x = (f) x",
        "my literal x = 007",
        "my call f x = f(x)",
        "my apply f = { my step x = f x; step }",
    ] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        assert_eq!(arena.body(), skeleton.body());
        assert_eq!(arena.nodes().len(), skeleton.expressions().len());
        for node in arena.nodes() {
            assert!(std::ptr::eq(
                node.form,
                skeleton.expression(&node.source).unwrap().form()
            ));
            let Form::Apply { callee, .. } = node.form else {
                assert!(node.call.is_none());
                continue;
            };
            let call = node.call.as_ref().unwrap();
            let expected = skeleton
                .pending()
                .iter()
                .filter(|p| p.call() == &node.source)
                .collect::<Vec<_>>();
            assert_eq!(call.application_premises.len(), expected.len());
            for (actual, expected) in call.application_premises.iter().zip(expected) {
                assert!(std::ptr::eq(*actual, expected));
            }
            assert_eq!(
                call.direct_use.is_some(),
                matches!(
                    skeleton.expression(callee).unwrap().form(),
                    Form::Use { .. }
                )
            );
            if let Some(direct) = call.direct_use.as_ref() {
                let Form::Use {
                    binder: retained_binder,
                    occurrence: retained_occurrence,
                } = skeleton
                    .expression(callee)
                    .expect("retained direct-use callee")
                    .form()
                else {
                    panic!("direct-use incidence targets an immediate Use")
                };
                assert_eq!(direct.application().expression(), &node.source);
                assert_eq!(direct.binder(), retained_binder);
                assert_eq!(direct.occurrence(), retained_occurrence);
            }
            if let Some(capture) = call.capture {
                assert_eq!(skeleton.capture_call(capture).unwrap(), &node.source);
                assert_eq!(
                    call.direct_use.as_ref().unwrap().occurrence(),
                    capture.occurrence()
                );
            }
        }
        if source == "my repeated f x = f (f x)" {
            let direct_calls = arena
                .nodes()
                .iter()
                .filter_map(|node| node.call.as_ref()?.direct_use.as_ref())
                .collect::<Vec<_>>();
            assert_eq!(direct_calls.len(), 2);
            assert_eq!(direct_calls[0].binder(), direct_calls[1].binder());
            assert_ne!(direct_calls[0].occurrence(), direct_calls[1].occurrence());
        }
    }
}

#[test]
fn raw_inventory_attaches_only_the_existing_capture_and_preserves_parse_identity() {
    let source = "my apply f = { my step x = f x; step }";
    let first = artifact(source);
    let second = artifact(source);
    let arena = RawStructuralArena::from_artifact(&first).unwrap();
    assert_eq!(
        arena
            .nodes()
            .iter()
            .filter(|node| node
                .call
                .as_ref()
                .is_some_and(|call| call.capture.is_some()))
            .count(),
        1
    );
    for node in arena.nodes() {
        assert!(second.skeleton().unwrap().expression(&node.source).is_err());
    }
    let unsupported = artifact("my constant x = \"unsupported\"");
    assert!(RawStructuralArena::from_artifact(&unsupported).is_none());
}
