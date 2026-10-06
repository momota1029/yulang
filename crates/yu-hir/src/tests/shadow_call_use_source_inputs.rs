//! Source references only: no formal classification or semantic premise discharge.
use super::*;
use crate::shadow::*;

fn assert_pending(skeleton: &Skeleton, row: &SourceCallUseInput<'_>) {
    assert_eq!(
        skeleton
            .pending()
            .iter()
            .filter(|pending| pending.call() == row.application().expression())
            .map(PendingPremise::premise)
            .collect::<Vec<_>>(),
        [
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
            Premise::QIndependentSourceCallViewFormation,
            Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
            Premise::SourceDirectionalOutputEffectProtectionIntroduction
        ]
    );
}

#[test]
fn shadow_call_use_source_inputs_retains_nested_capture_and_whole_argument() {
    let source = "my apply f = { my step x = f x; step }";
    let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let foreign = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let before = skeleton.pending().len();
    let rows = skeleton.source_call_use_inputs().collect::<Vec<_>>();
    let [row] = rows.as_slice() else {
        panic!("one nested direct call")
    };
    let [capture] = skeleton.capture_uses() else {
        panic!("one captured use")
    };
    assert_eq!(row.binder(), capture.captured());
    assert_eq!(row.occurrence(), capture.occurrence());
    assert_eq!(skeleton.binder(row.binder()).unwrap().name(), "f");
    let call = skeleton.expression(row.application().expression()).unwrap();
    let Form::Apply {
        callee,
        argument,
        source_form,
    } = call.form()
    else {
        panic!("Apply")
    };
    assert_eq!(callee, row.application().callee());
    assert_eq!(argument, row.argument());
    assert_eq!(*source_form, row.application().source_form());
    assert_eq!(call.position(), row.application().position());
    let Form::Use { binder, occurrence } = skeleton.expression(callee).unwrap().form() else {
        panic!("Use")
    };
    assert_eq!(binder, row.binder());
    assert_eq!(occurrence, row.occurrence());
    let argument = skeleton.expression(row.argument()).unwrap();
    assert_eq!(&source[argument.range().clone()], "x");
    assert!(row.parameter_annotations().next().is_none());
    assert_pending(skeleton, row);
    assert_eq!(before, 6);
    assert_eq!(skeleton.pending().len(), before);
    let other = foreign.skeleton().unwrap();
    for id in [
        row.application().expression(),
        row.application().callee(),
        row.argument(),
    ] {
        assert_eq!(
            other.expression(id).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }
    assert_eq!(
        other.binder(row.binder()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        other.use_expression(row.occurrence()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn shadow_call_use_source_inputs_repeated_calls_preserve_occurrences() {
    let artifact = ShadowArtifact::from_parsed(parsed("my apply f x = f(f x)")).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let rows = skeleton.source_call_use_inputs().collect::<Vec<_>>();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].binder(), rows[1].binder());
    assert_ne!(rows[0].occurrence(), rows[1].occurrence());
    assert_ne!(
        rows[0].application().expression(),
        rows[1].application().expression()
    );
    assert_ne!(rows[0].argument(), rows[1].argument());
    for row in &rows {
        assert_pending(skeleton, row);
    }
    assert_eq!(skeleton.pending().len(), 12);
}

#[test]
fn shadow_call_use_source_inputs_joins_exact_noninitial_annotation_incidence() {
    let source = "my apply x (f: T) (g: T) = f (g x)";
    let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let foreign = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let rows = skeleton.source_call_use_inputs().collect::<Vec<_>>();
    assert_eq!(rows.len(), 2);
    for row in &rows {
        let incidences = row.parameter_annotations().collect::<Vec<_>>();
        let [incidence] = incidences.as_slice() else {
            panic!("one exact retained annotation")
        };
        let expected = skeleton
            .parameter_annotations()
            .iter()
            .find(|incidence| incidence.parameter() == row.binder())
            .unwrap();
        assert!(std::ptr::eq(*incidence, expected));
        assert_eq!(incidence.parameter(), row.binder());
        assert_eq!(incidence.annotation(), expected.annotation());
        let index = if skeleton.binder(row.binder()).unwrap().name() == "f" {
            0
        } else {
            1
        };
        assert_eq!(incidence.annotation(), artifact.annotations()[index].id());
        assert_eq!(
            foreign.annotation(incidence.annotation()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_pending(skeleton, row);
    }
    assert_eq!(skeleton.pending().len(), 12);
}

#[test]
fn shadow_call_use_source_inputs_excludes_grouped_and_computed_callees() {
    for source in ["my apply f x = (f) x", "my apply f x = 42 x"] {
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let skeleton = artifact.skeleton().unwrap();
        assert_eq!(skeleton.application_source_occurrences().count(), 1);
        assert_eq!(skeleton.source_call_use_inputs().count(), 0);
        assert_eq!(skeleton.pending().len(), 4);
        assert!(skeleton.pending().iter().all(|pending| {
            pending.premise() != Premise::SourceDirectionalOutputEffectProtectionIntroduction
        }));
    }
    let artifact = ShadowArtifact::from_parsed(parsed("my apply f x = (f x) x")).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    assert_eq!(skeleton.application_source_occurrences().count(), 2);
    let rows = skeleton.source_call_use_inputs().collect::<Vec<_>>();
    assert_eq!(rows.len(), 1);
    assert_pending(skeleton, &rows[0]);
    assert_eq!(skeleton.pending().len(), 10);
    let directional = skeleton
        .pending()
        .iter()
        .filter(|pending| {
            pending.premise() == Premise::SourceDirectionalOutputEffectProtectionIntroduction
        })
        .collect::<Vec<_>>();
    assert_eq!(directional.len(), 1);
    assert_eq!(directional[0].call(), rows[0].application().expression());
}
