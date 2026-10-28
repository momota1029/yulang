#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact};
use yu_core::shadow_derivation::{ApplyStructuralPosition as Position, RawStructuralArena};
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
fn every_apply_has_eight_distinct_borrowed_addresses_and_unchanged_joins() {
    for source in [
        "my apply f x = f x",
        "my repeated f x = f (f x)",
        "my computed f x = (f x) x",
        "my grouped f x = (f) x",
        "my apply x (f: T) (g: T) = f (g x)",
        "my apply f = { my step x = f x; step }",
    ] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        let mut premise_count = 0;
        let mut capture_count = 0;
        for node in arena.nodes() {
            let view = arena.pending_apply_endpoint_skeleton(&node.source);
            let Form::Apply {
                callee, argument, ..
            } = node.form
            else {
                assert!(view.is_none());
                continue;
            };
            let view = view.unwrap();
            assert!(std::ptr::eq(view.source(), &node.source));
            assert!(std::ptr::eq(view.callee(), callee));
            assert!(std::ptr::eq(view.argument(), argument));
            let call = node.call.as_ref().unwrap();
            assert!(std::ptr::eq(view.call(), call));
            assert_eq!(
                view.addresses().map(|address| address.position()),
                [
                    Position::CalleeValue,
                    Position::CalleeEffect,
                    Position::ArgumentValue,
                    Position::ArgumentEffect,
                    Position::CandidateFunctionReturnEffect,
                    Position::CandidateFunctionResult,
                    Position::WholeApplyValue,
                    Position::WholeApplyEffect,
                ]
            );
            for (index, address) in view.addresses().iter().enumerate() {
                assert!(std::ptr::eq(address.application(), &node.source));
                assert_eq!(address.application(), &node.source);
                for previous in &view.addresses()[..index] {
                    assert_ne!(address, previous);
                }
            }
            let pending = skeleton
                .pending()
                .iter()
                .filter(|premise| premise.call() == view.source())
                .collect::<Vec<_>>();
            assert_eq!(view.call().application_premises.len(), pending.len());
            for (actual, expected) in view.call().application_premises.iter().zip(pending) {
                assert!(std::ptr::eq(*actual, expected));
                premise_count += 1;
            }
            if let Some(input) = view.call().source_use_input.as_ref() {
                assert_eq!(input.application().expression(), view.source());
                assert!(std::ptr::eq(input.application().callee(), view.callee()));
                assert!(std::ptr::eq(input.argument(), view.argument()));
            }
            if let Some(capture) = view.call().capture {
                capture_count += 1;
                assert_eq!(skeleton.capture_call(capture).unwrap(), view.source());
                let registration = node.pending_source_call_registration().unwrap();
                let locator = registration.source_view_premise_locator().unwrap();
                assert_eq!(
                    locator.unresolved_premises(),
                    skeleton
                        .captured_call_input()
                        .unwrap()
                        .source_view_premise_locator()
                        .unresolved_premises()
                );
            }
        }
        assert_eq!(premise_count, skeleton.pending().len());
        assert_eq!(capture_count, skeleton.capture_uses().len());
    }
}

#[test]
fn nested_same_binder_calls_keep_occurrence_addresses_distinct() {
    let artifact = artifact("my repeated f x = f (f x)");
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
    let calls = arena
        .nodes()
        .iter()
        .filter_map(|node| arena.pending_apply_endpoint_skeleton(&node.source))
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    let first = calls[0].call().direct_use.as_ref().unwrap();
    let second = calls[1].call().direct_use.as_ref().unwrap();
    assert_eq!(first.binder(), second.binder());
    assert_ne!(first.occurrence(), second.occurrence());
    assert_ne!(calls[0].source(), calls[1].source());
    for first in calls[0].addresses() {
        for second in calls[1].addresses() {
            assert_ne!(first, second);
        }
    }
    let skeleton = artifact.skeleton().unwrap();
    let outer = calls
        .iter()
        .find(|call| {
            matches!(
                skeleton.expression(call.argument()).unwrap().form(),
                Form::Group { inner }
                    if matches!(skeleton.expression(inner).unwrap().form(), Form::Apply { .. })
            )
        })
        .unwrap();
    let Form::Group { inner } = skeleton.expression(outer.argument()).unwrap().form() else {
        panic!("retained grouping")
    };
    let child = arena.pending_apply_endpoint_skeleton(inner).unwrap();
    assert_ne!(outer.addresses()[2], child.addresses()[6]);
    assert_eq!(outer.addresses()[2].application(), outer.source());
    assert_eq!(child.addresses()[6].application(), child.source());
}

#[test]
fn foreign_and_non_apply_identities_cannot_create_a_view() {
    let retained = artifact("my apply f x = f x");
    let foreign = artifact("my apply f x = f x");
    let arena = RawStructuralArena::from_artifact(&retained).unwrap();
    for (source, expression) in foreign.skeleton().unwrap().retained_expressions() {
        assert!(arena.pending_apply_endpoint_skeleton(&source).is_none());
        if matches!(expression.form(), Form::Apply { .. }) {
            assert!(retained.skeleton().unwrap().expression(&source).is_err());
        }
    }
    for node in arena.nodes() {
        assert_eq!(
            arena
                .pending_apply_endpoint_skeleton(&node.source)
                .is_some(),
            matches!(node.form, Form::Apply { .. })
        );
    }
    let unsupported = artifact("my constant x = \"unsupported\"");
    assert!(RawStructuralArena::from_artifact(&unsupported).is_none());
}
