#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{BinderId, Form, ShadowArtifact};
use yu_core::shadow_derivation::{IncompleteDerivation, Node};
use yu_core::shadow_derivation::{
    PendingStructuralForm, PendingStructuralProjection, RawStructuralArena,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

const SOURCE: &str = "my apply f = { my step x = f x; step }";

fn artifact(source: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    let parsed: ParsedFile = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    ShadowArtifact::from_parsed(parsed).unwrap()
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Structure {
    Lambda(BinderId, Box<Self>),
    Bind(BinderId, Box<Self>, Box<Self>),
    Result(Box<Self>),
    Name(BinderId),
    Call(Box<Self>, Box<Self>),
}

fn erased(arena: &IncompleteDerivation<'_>, offset: usize) -> Structure {
    use Structure::*;
    let child = |offset| Box::new(erased(arena, offset));
    match &arena.nodes()[offset] {
        Node::Lambda {
            parameter, body, ..
        } => Lambda((*parameter).clone(), child(*body)),
        Node::Bind {
            binder,
            value,
            body,
            ..
        } => Bind((*binder).clone(), child(*value), child(*body)),
        Node::Result { value } => Result(child(*value)),
        Node::Name { binder, .. } => Name((*binder).clone()),
        Node::PendingCall(call) => Call(child(call.callee), child(call.argument)),
    }
}

#[test]
fn exact_candidate_matches_approved_template_and_detects_structural_mutations() {
    use Structure::*;
    let artifact = artifact(SOURCE);
    let skeleton = artifact.skeleton().unwrap();
    let input = skeleton.captured_call_input().unwrap();
    let pending_before = skeleton
        .pending()
        .iter()
        .map(|p| (p.call().clone(), p.premise()))
        .collect::<Vec<_>>();
    let arena = IncompleteDerivation::from_captured_call(&artifact, &input).unwrap();
    let Form::Lambda { parameter: x, .. } =
        skeleton.expression(input.local_lambda()).unwrap().form()
    else {
        panic!("local lambda")
    };
    let f = input.outer_parameter().clone();
    let step = input.local_binding().clone();
    let result = |value| Box::new(Result(Box::new(value)));
    let template = Lambda(
        f.clone(),
        Box::new(Bind(
            step.clone(),
            result(Lambda(
                x.clone(),
                Box::new(Call(result(Name(f.clone())), result(Name(x.clone())))),
            )),
            result(Name(step.clone())),
        )),
    );
    let observed = erased(&arena, arena.root());
    assert_eq!(observed, template);
    assert_eq!(arena.nodes().len(), 11);
    let calls = arena
        .nodes()
        .iter()
        .filter_map(|node| {
            if let Node::PendingCall(call) = node {
                Some(call)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let [call] = calls.as_slice() else {
        panic!("one pending call")
    };
    assert_eq!(call.source, input.call());
    assert!(std::ptr::eq(call.application_premises, skeleton.pending()));
    assert_eq!(
        call.source_view_premises,
        input.source_view_premise_locator().unresolved_premises()
    );
    assert_eq!(call.capture.occurrence(), input.callee_use());
    for node in arena.nodes() {
        match node {
            Node::Name {
                source,
                binder,
                occurrence,
            } => {
                let Form::Use {
                    binder: retained,
                    occurrence: retained_use,
                } = skeleton.expression(source).unwrap().form()
                else {
                    panic!("retained name")
                };
                assert!(std::ptr::eq(*binder, retained));
                assert!(std::ptr::eq(*occurrence, retained_use));
            }
            Node::Lambda {
                source,
                parameter,
                captures,
                correspondence,
                ..
            } => {
                let Form::Lambda {
                    parameter: retained,
                    captures: retained_captures,
                    correspondence: retained_correspondence,
                    ..
                } = skeleton.expression(source).unwrap().form()
                else {
                    panic!("retained lambda")
                };
                assert!(std::ptr::eq(*parameter, retained));
                assert!(std::ptr::eq(*captures, retained_captures.as_slice()));
                assert!(std::ptr::eq(*correspondence, retained_correspondence));
            }
            _ => {}
        }
    }
    for mutation in 0..3 {
        let mut changed = template.clone();
        let Lambda(_, block) = &mut changed else {
            unreachable!()
        };
        let Bind(_, local, returned) = block.as_mut() else {
            unreachable!()
        };
        if mutation == 2 {
            *returned = Box::new(Call(result(Name(step.clone())), result(Name(x.clone()))));
        } else {
            let Result(local) = local.as_mut() else {
                unreachable!()
            };
            let Lambda(_, body) = local.as_mut() else {
                unreachable!()
            };
            let Call(callee, argument) = body.as_mut() else {
                unreachable!()
            };
            if mutation == 0 {
                *body = callee.clone();
            } else {
                *callee = argument.clone();
            }
        }
        assert_ne!(observed, changed, "mutation {mutation}");
    }
    assert_eq!(
        pending_before,
        skeleton
            .pending()
            .iter()
            .map(|p| (p.call().clone(), p.premise()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn foreign_input_and_unapproved_sources_publish_no_arena() {
    let first = artifact(SOURCE);
    let foreign = artifact(SOURCE);
    let input = foreign.skeleton().unwrap().captured_call_input().unwrap();
    assert!(IncompleteDerivation::from_captured_call(&first, &input).is_none());
    for source in [
        "my apply f x = f x",
        "my apply f = { my step x = f x; step x }",
    ] {
        let unsupported = artifact(source);
        assert!(IncompleteDerivation::from_captured_call(&unsupported, &input).is_none());
    }
    let unsupported = artifact("my apply f = { my step x = f x; step } ");
    let own_input = unsupported
        .skeleton()
        .unwrap()
        .captured_call_input()
        .expect("trailing whitespace preserves the validated topology");
    assert!(IncompleteDerivation::from_captured_call(&unsupported, &own_input).is_none());
}

#[test]
fn ordinary_unary_projection_preserves_body_declaration_and_call_rows() {
    for (source, expected_calls) in [("my call f = f 1", 1), ("my twice f = f (f 1)", 2)] {
        let artifact = artifact(source);
        let raw = RawStructuralArena::from_artifact(&artifact).unwrap();
        let projection = PendingStructuralProjection::from_raw(&raw).unwrap();
        assert_eq!(projection.nodes().len(), raw.nodes().len());
        assert_eq!(*projection.nodes()[projection.body()].source, *raw.body());
        assert_eq!(projection.declarations().len(), 1);
        let declaration = projection.declarations()[0];
        assert_ne!(declaration, projection.body());
        let PendingStructuralForm::Lambda { body, .. } = projection.nodes()[declaration].form
        else {
            panic!("retained declaration")
        };
        assert_eq!(body, projection.body());
        let calls = projection
            .nodes()
            .iter()
            .filter_map(|node| {
                let PendingStructuralForm::PendingApply { call, .. } = &node.form else {
                    return None;
                };
                assert!(
                    call.application_premises
                        .iter()
                        .all(|row| row.call() == node.source)
                );
                assert_eq!(call.application_premises.len(), 7);
                assert!(call.capture.is_none());
                Some(node.source)
            })
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), expected_calls);
        if expected_calls == 2 {
            assert_ne!(calls[0], calls[1]);
        }
    }
}

#[test]
fn captured_candidate_projection_keeps_exact_lambda_bind_and_call_joins() {
    let artifact = artifact(SOURCE);
    let raw = RawStructuralArena::from_artifact(&artifact).unwrap();
    let projection = PendingStructuralProjection::from_raw(&raw).unwrap();
    assert_eq!(projection.nodes().len(), raw.nodes().len());
    assert_eq!(projection.declarations().len(), 2);
    assert_eq!(projection.nodes()[projection.body()].source, raw.body());

    for (projected, retained) in projection.nodes().iter().zip(raw.nodes()) {
        assert!(std::ptr::eq(projected.source, &retained.source));
        match (&projected.form, retained.form) {
            (
                PendingStructuralForm::Lambda {
                    binding,
                    parameter,
                    body,
                    captures,
                    correspondence,
                },
                Form::Lambda {
                    binding: expected_binding,
                    parameter: expected_parameter,
                    body: expected_body,
                    captures: expected_captures,
                    correspondence: expected_correspondence,
                },
            ) => {
                assert!(std::ptr::eq(*binding, expected_binding));
                assert!(std::ptr::eq(*parameter, expected_parameter));
                assert!(std::ptr::eq(*captures, expected_captures.as_slice()));
                assert!(std::ptr::eq(*correspondence, expected_correspondence));
                assert_eq!(projection.nodes()[*body].source, expected_body);
            }
            (
                PendingStructuralForm::Bind {
                    binder,
                    value,
                    body,
                },
                Form::Bind {
                    binder: expected_binder,
                    value: expected_value,
                    body: expected_body,
                },
            ) => {
                assert!(std::ptr::eq(*binder, expected_binder));
                assert_eq!(projection.nodes()[*value].source, expected_value);
                assert_eq!(projection.nodes()[*body].source, expected_body);
            }
            (PendingStructuralForm::PendingApply { call, .. }, Form::Apply { .. }) => {
                let expected = retained.call.as_ref().unwrap();
                assert!(std::ptr::eq(*call, expected));
                assert!(call.capture.is_some());
                let registration = retained.pending_source_call_registration().unwrap();
                let captured = registration.captured_input.unwrap();
                assert_eq!(captured.call(), projected.source);
                assert_eq!(
                    registration
                        .source_view_premise_locator()
                        .unwrap()
                        .unresolved_premises()
                        .len(),
                    7
                );
            }
            (
                PendingStructuralForm::PendingUseNormalization { binder, occurrence },
                Form::Use {
                    binder: expected_binder,
                    occurrence: expected_occurrence,
                },
            ) => {
                assert_eq!(*binder, expected_binder);
                assert_eq!(*occurrence, expected_occurrence);
            }
            _ => panic!("projection form must match the retained HIR form"),
        }
    }
}

#[test]
fn annotations_leave_use_normalization_pending_and_groups_remain_explicit() {
    for source in ["my annotated (f: T) = f 1", "my grouped f = (f) 1"] {
        let artifact = artifact(source);
        let raw = RawStructuralArena::from_artifact(&artifact).unwrap();
        let projection = PendingStructuralProjection::from_raw(&raw).unwrap();
        assert!(projection.nodes().iter().any(|node| matches!(
            node.form,
            PendingStructuralForm::PendingUseNormalization { .. }
        )));
        if source.contains(": T") {
            assert_eq!(projection.annotations().len(), 1);
            assert!(std::ptr::eq(
                &projection.annotations()[0],
                &raw.annotations()[0]
            ));
        } else {
            assert!(
                projection
                    .nodes()
                    .iter()
                    .any(|node| matches!(node.form, PendingStructuralForm::Group { .. }))
            );
        }
    }
}

#[test]
fn missing_multi_parameter_declarations_and_unsupported_sources_are_rejected() {
    let multi = artifact("my call f x = f x");
    let raw = RawStructuralArena::from_artifact(&multi).unwrap();
    assert!(PendingStructuralProjection::from_raw(&raw).is_none());
    let unsupported = artifact("my record f = { field: f }");
    assert!(RawStructuralArena::from_artifact(&unsupported).is_none());
}

#[test]
fn bounded_flat_application_chain_projects_without_recursive_traversal() {
    let source = format!("my chain f = f{}", " 1".repeat(256));
    let artifact = artifact(&source);
    let raw = RawStructuralArena::from_artifact(&artifact).unwrap();
    let projection = PendingStructuralProjection::from_raw(&raw).unwrap();
    assert_eq!(
        projection
            .nodes()
            .iter()
            .filter(|node| matches!(node.form, PendingStructuralForm::PendingApply { .. }))
            .count(),
        256
    );
    assert_eq!(projection.nodes().len(), raw.nodes().len());
}
