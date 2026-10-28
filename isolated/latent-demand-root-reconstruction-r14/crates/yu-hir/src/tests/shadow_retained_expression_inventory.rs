use super::*;
use crate::shadow::*;

#[test]
fn shadow_retained_expression_inventory_keeps_all_nodes_and_rejects_foreign_ids() {
    let first = ShadowArtifact::from_parsed(parsed("my identity x = x")).unwrap();
    let second = ShadowArtifact::from_parsed(parsed("my identity x = x")).unwrap();
    let skeleton = first.skeleton().unwrap();
    let records = skeleton.retained_expressions().collect::<Vec<_>>();
    assert_eq!(records.len(), skeleton.expressions().len());
    assert!(records.iter().any(|(id, expression)| {
        id != skeleton.body() && matches!(expression.form(), Form::Lambda { .. })
    }));
    for (offset, (id, expression)) in records.iter().enumerate() {
        assert_eq!(skeleton.expression_offset(id), Ok(offset));
        assert!(std::ptr::eq(skeleton.expression(id).unwrap(), *expression));
        assert_eq!(
            second.skeleton().unwrap().expression_offset(id),
            Err(ShadowError::ForeignArtifact)
        );
    }
}

#[test]
fn shadow_retained_expression_inventory_capture_join_checks_artifact_brand() {
    let source = "my apply f = { my step x = f x; step }";
    let first = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let second = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let skeleton = first.skeleton().unwrap();
    let capture = &skeleton.capture_uses()[0];
    assert_eq!(
        skeleton.capture_call(capture).unwrap(),
        skeleton.captured_call_input().unwrap().call()
    );
    assert_eq!(
        second.skeleton().unwrap().capture_call(capture),
        Err(ShadowError::ForeignArtifact)
    );
}
