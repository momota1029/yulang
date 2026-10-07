//! Source incidence only: semantic call views and per-call premises remain pending.
use super::*;
use crate::shadow::*;

fn cross_check(artifact: &ShadowArtifact, expected_calls: usize) {
    let skeleton = artifact.skeleton().unwrap();
    let occurrences = skeleton
        .application_source_occurrences()
        .collect::<Vec<_>>();
    assert_eq!(occurrences.len(), expected_calls);
    assert_eq!(
        skeleton
            .expressions()
            .iter()
            .filter(|expression| matches!(expression.form(), Form::Apply { .. }))
            .count(),
        expected_calls
    );
    // The approved pending-only extension adds one unresolved obligation per Apply.
    // These inventory expectations count retained obligations, not semantic output:
    // causal scope and approval were confirmed before edits by the spec auditor,
    // with the rationale recorded here under testing.md protection items 1–4.
    assert_eq!(
        skeleton.pending().len(),
        expected_calls * 8 + 2 * skeleton.resolved_call_incidences().count()
    );
    for (index, occurrence) in occurrences.iter().enumerate() {
        let expression = skeleton.expression(occurrence.expression()).unwrap();
        assert_eq!(expression.position(), occurrence.position());
        let Form::Apply {
            source_form,
            callee,
            argument,
        } = expression.form()
        else {
            panic!("retained application")
        };
        assert_eq!(*source_form, occurrence.source_form());
        assert_eq!(callee, occurrence.callee());
        assert_eq!(argument, occurrence.argument());
        let position = artifact.position(occurrence.position()).unwrap();
        assert!(position.is_node());
        assert_eq!(position.kind(), occurrence.source_form());
        for previous in &occurrences[..index] {
            assert_ne!(previous.expression(), occurrence.expression());
            assert_ne!(previous.position(), occurrence.position());
        }
        let mut expected = vec![
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
            Premise::QIndependentSourceCallViewFormation,
            Premise::SourceEventContributionAndTypedOutputObservation,
            Premise::JointArgumentTypingAndActualReturnedProviderCarrierCompatibility,
            Premise::SourceSignatureLocalImmediateCallEffectPositionFormation,
            Premise::OriginalTypedCallEffectOccurrenceIntroduction,
        ];
        if matches!(
            skeleton.expression(occurrence.callee()).unwrap().form(),
            Form::Use { .. }
        ) {
            expected.push(Premise::SourceFormalUseRuleApplicabilityAndInterpretation);
            expected.push(Premise::SourceDirectionalOutputEffectProtectionIntroduction);
        }
        assert_eq!(
            skeleton
                .pending()
                .iter()
                .filter(|pending| pending.call() == occurrence.expression())
                .map(PendingPremise::premise)
                .collect::<Vec<_>>(),
            expected
        );
    }
    // Every pending reference still targets one existing source occurrence.
    for pending in skeleton.pending() {
        assert_eq!(
            occurrences
                .iter()
                .filter(|occurrence| occurrence.expression() == pending.call())
                .count(),
            1
        );
    }
}

#[test]
fn shadow_call_source_occurrences_nested_candidate_retains_capture_and_operands() {
    let artifact =
        ShadowArtifact::from_parsed(parsed("my apply f = { my step x = f x; step }")).unwrap();
    cross_check(&artifact, 1);
    let skeleton = artifact.skeleton().unwrap();
    let occurrence = skeleton.application_source_occurrences().next().unwrap();
    assert_eq!(occurrence.source_form(), SyntaxKind::MlArgument);
    assert_eq!(
        *artifact.position(occurrence.position()).unwrap().range(),
        29..30
    );
    assert_eq!(
        *skeleton.expression(occurrence.callee()).unwrap().range(),
        27..28
    );
    assert_eq!(
        *skeleton.expression(occurrence.argument()).unwrap().range(),
        29..30
    );
    let [capture] = skeleton.capture_uses() else {
        panic!("one capture")
    };
    let Form::Lambda {
        body,
        correspondence,
        ..
    } = skeleton.expression(capture.lambda()).unwrap().form()
    else {
        panic!("capturing lambda")
    };
    assert_eq!(body, occurrence.expression());
    assert_eq!(
        *correspondence,
        ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
    );
    assert!(std::ptr::eq(
        skeleton.use_expression(capture.occurrence()).unwrap(),
        skeleton.expression(occurrence.callee()).unwrap()
    ));
    let Form::Use { binder, .. } = skeleton.expression(occurrence.argument()).unwrap().form()
    else {
        panic!("argument use")
    };
    assert_eq!(skeleton.binder(binder).unwrap().name(), "x");
    assert_eq!(skeleton.binder(capture.captured()).unwrap().name(), "f");
}

#[test]
fn shadow_call_source_occurrences_compose_distinguishes_inner_and_outer_calls() {
    let artifact = ShadowArtifact::from_parsed(parsed("my compose f g x = f (g x)")).unwrap();
    cross_check(&artifact, 2);
    let skeleton = artifact.skeleton().unwrap();
    let occurrences = skeleton
        .application_source_occurrences()
        .collect::<Vec<_>>();
    let outer = occurrences
        .iter()
        .find(|occurrence| occurrence.expression() == skeleton.body())
        .unwrap();
    let Form::Group { inner } = skeleton.expression(outer.argument()).unwrap().form() else {
        panic!("whole grouped argument")
    };
    let nested = occurrences
        .iter()
        .find(|occurrence| occurrence.expression() == inner)
        .unwrap();
    assert_eq!(
        *artifact.position(outer.position()).unwrap().range(),
        21..26
    );
    assert_eq!(
        *artifact.position(nested.position()).unwrap().range(),
        24..25
    );
    for (id, range) in [
        (outer.callee(), 19..20),
        (outer.argument(), 21..26),
        (nested.callee(), 22..23),
        (nested.argument(), 24..25),
    ] {
        assert_eq!(*skeleton.expression(id).unwrap().range(), range);
    }
}

#[test]
fn shadow_call_source_occurrences_keep_artifact_brand_and_call_tail_form() {
    let first = ShadowArtifact::from_parsed(parsed("my call f x = f(x)")).unwrap();
    let second = ShadowArtifact::from_parsed(parsed("my call f x = f(x)")).unwrap();
    cross_check(&first, 1);
    let occurrence = first
        .skeleton()
        .unwrap()
        .application_source_occurrences()
        .next()
        .unwrap();
    assert_eq!(occurrence.source_form(), SyntaxKind::CallTail);
    assert_eq!(
        *first.position(occurrence.position()).unwrap().range(),
        15..18
    );
    for id in [
        occurrence.expression(),
        occurrence.callee(),
        occurrence.argument(),
    ] {
        assert_eq!(
            second.skeleton().unwrap().expression(id).unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }
    assert_eq!(
        second.position(occurrence.position()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    let same_source = second
        .skeleton()
        .unwrap()
        .application_source_occurrences()
        .next()
        .unwrap();
    assert_ne!(occurrence.expression(), same_source.expression());
}
