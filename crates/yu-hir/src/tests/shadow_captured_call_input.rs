//! Exact structural joins only; all semantic obligations remain pending.
use super::*;
use crate::shadow::*;

const SOURCE: &str = "my apply f = { my step x = f x; step }";

#[test]
fn shadow_captured_call_input_retains_exact_edges_and_pending_inventory() {
    let artifact = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let before = skeleton
        .pending()
        .iter()
        .map(|p| (p.call().clone(), p.premise()))
        .collect::<Vec<_>>();
    let row = skeleton.captured_call_input().unwrap();
    let [capture] = skeleton.capture_uses() else {
        panic!("one capture")
    };
    assert_eq!(row.outer_parameter(), capture.captured());
    assert_eq!(row.local_lambda(), capture.lambda());
    assert_eq!(row.callee_use(), capture.occurrence());
    assert_eq!(row.capture_position(), capture.position());
    let call = skeleton.source_call_use_inputs().next().unwrap();
    assert_eq!(row.call(), call.application().expression());
    assert_eq!(row.callee_use(), call.occurrence());
    assert_eq!(skeleton.binder(row.local_binding()).unwrap().name(), "step");
    let Form::Use { binder, .. } = skeleton.use_expression(row.returned_use()).unwrap().form()
    else {
        panic!("returned Use")
    };
    assert_eq!(binder, row.local_binding());
    assert_eq!(before.len(), 8);
    assert_eq!(
        before,
        skeleton
            .pending()
            .iter()
            .map(|p| (p.call().clone(), p.premise()))
            .collect::<Vec<_>>()
    );
    let foreign = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
    assert_eq!(
        foreign
            .skeleton()
            .unwrap()
            .expression(row.call())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn shadow_captured_call_input_absent_for_other_topology() {
    for source in [
        "my apply f x = f x",
        "my apply f x = (f) x",
        "my apply f x = f(f x)",
    ] {
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        assert!(artifact.skeleton().unwrap().captured_call_input().is_none());
    }
}

#[test]
fn shadow_captured_call_input_absent_for_broken_or_foreign_edges() {
    for mutation in 0..5 {
        let mut skeleton = ShadowArtifact::from_parsed(parsed(SOURCE))
            .unwrap()
            .into_skeleton()
            .unwrap();
        let foreign = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
        let foreign_root = foreign.skeleton().unwrap().body().clone();
        let root = skeleton.body.clone();
        let extra_capture = skeleton
            .captured_call_input()
            .unwrap()
            .local_binding()
            .clone();
        let call = skeleton.captured_call_input().unwrap().call().clone();
        let call_index = skeleton
            .expressions
            .iter()
            .position(|e| std::ptr::eq(e, skeleton.expression(&call).unwrap()))
            .unwrap();
        match mutation {
            0 => {
                let Form::Apply { callee, .. } = &mut skeleton.expressions[call_index].form else {
                    panic!("Apply")
                };
                *callee = foreign_root;
            }
            1 => {
                let Form::Apply { argument, .. } = &mut skeleton.expressions[call_index].form
                else {
                    panic!("Apply")
                };
                *argument = root;
            }
            2 => {
                let Form::Apply {
                    callee, argument, ..
                } = &mut skeleton.expressions[call_index].form
                else {
                    panic!("Apply")
                };
                *argument = callee.clone();
            }
            _ => {
                let local = skeleton.expressions.iter().position(|e| matches!(&e.form, Form::Lambda { captures, .. } if !captures.is_empty())).unwrap();
                let Form::Lambda { captures, .. } = &mut skeleton.expressions[local].form else {
                    panic!("Lambda")
                };
                if mutation == 3 {
                    captures.clear();
                } else {
                    captures.push(extra_capture);
                }
            }
        }
        assert!(skeleton.captured_call_input().is_none());
        assert_eq!(skeleton.pending().len(), 8);
    }
}
