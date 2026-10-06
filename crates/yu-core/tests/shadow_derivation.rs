#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{BinderId, Form, ShadowArtifact};
use yu_core::shadow_derivation::{IncompleteDerivation, Node};
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
