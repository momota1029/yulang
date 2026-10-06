//! Resolved lexical incidence only; semantic call premises remain pending.
use super::*;
use crate::shadow::*;

#[test]
fn shadow_resolved_call_incidence_distinguishes_nested_uses_of_one_binder() {
    let source = "my f x = x(x x)";
    let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let foreign = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let incidences = skeleton.resolved_call_incidences().collect::<Vec<_>>();
    assert_eq!(incidences.len(), 2);
    assert_eq!(skeleton.application_source_occurrences().count(), 2);
    assert_eq!(incidences[0].binder(), incidences[1].binder());
    assert_eq!(skeleton.binder(incidences[0].binder()).unwrap().name(), "x");
    assert_ne!(incidences[0].occurrence(), incidences[1].occurrence());
    assert_ne!(
        incidences[0].application().expression(),
        incidences[1].application().expression()
    );
    assert_ne!(
        incidences[0].application().position(),
        incidences[1].application().position()
    );
    let mut forms = Vec::new();
    for incidence in &incidences {
        let application = incidence.application();
        let callee = skeleton.expression(application.callee()).unwrap();
        let Form::Use { binder, occurrence } = callee.form() else {
            panic!("direct resolved callee use")
        };
        assert_eq!(binder, incidence.binder());
        assert_eq!(occurrence, incidence.occurrence());
        assert!(std::ptr::eq(
            callee,
            skeleton.use_expression(occurrence).unwrap()
        ));
        assert_eq!(
            callee.position(),
            skeleton.use_position(occurrence).unwrap()
        );
        let call = skeleton.expression(application.expression()).unwrap();
        assert_eq!(call.position(), application.position());
        let Form::Apply {
            source_form,
            callee,
            argument,
        } = call.form()
        else {
            panic!("retained application")
        };
        assert_eq!(*source_form, application.source_form());
        assert_eq!(callee, application.callee());
        assert_eq!(argument, application.argument());
        assert_eq!(
            artifact.position(application.position()).unwrap().kind(),
            *source_form
        );
        forms.push(*source_form);
        assert_eq!(
            skeleton
                .pending()
                .iter()
                .filter(|pending| pending.call() == application.expression())
                .map(PendingPremise::premise)
                .collect::<Vec<_>>(),
            [
                Premise::CallableRole,
                Premise::FullFunctionMembership,
                Premise::CallViewRealization,
                Premise::QIndependentSourceCallViewFormation,
                Premise::SourceFormalUseRuleApplicabilityAndInterpretation
            ]
        );
        let other = foreign.skeleton().unwrap();
        for id in [
            application.expression(),
            application.callee(),
            application.argument(),
        ] {
            assert_eq!(
                other.expression(id).unwrap_err(),
                ShadowError::ForeignArtifact
            );
        }
        assert_eq!(
            other.binder(incidence.binder()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            other.use_expression(incidence.occurrence()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            foreign.position(application.position()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }
    assert!(forms.contains(&SyntaxKind::MlArgument));
    assert!(forms.contains(&SyntaxKind::CallTail));
    assert_eq!(skeleton.pending().len(), 10);
    let stubs = skeleton
        .pending()
        .iter()
        .filter(|pending| {
            pending.premise() == Premise::SourceFormalUseRuleApplicabilityAndInterpretation
        })
        .collect::<Vec<_>>();
    assert_eq!(stubs.len(), 2);
    assert_ne!(stubs[0].call(), stubs[1].call());
}

#[test]
fn shadow_resolved_call_incidence_filters_integer_callee_without_dropping_apply() {
    let artifact = ShadowArtifact::from_parsed(parsed("my f x = 42 x")).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    assert_eq!(skeleton.application_source_occurrences().count(), 1);
    assert_eq!(skeleton.resolved_call_incidences().count(), 0);
    assert_eq!(skeleton.pending().len(), 4);
}

#[test]
fn shadow_resolved_call_incidence_keeps_grouped_callee_applicability_unrecorded() {
    let artifact = ShadowArtifact::from_parsed(parsed("my f x = (x) x")).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    assert_eq!(skeleton.application_source_occurrences().count(), 1);
    assert_eq!(skeleton.resolved_call_incidences().count(), 0);
    assert_eq!(skeleton.pending().len(), 4);
    assert!(skeleton.pending().iter().all(|pending| {
        pending.premise() != Premise::SourceFormalUseRuleApplicabilityAndInterpretation
    }));
}
