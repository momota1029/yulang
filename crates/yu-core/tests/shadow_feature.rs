#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{
    CaptureUseIncidence, ClosureCorrespondence, Form, Premise, ShadowArtifact, ShadowError,
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

#[test]
fn facade_reads_the_hir_snapshot_without_resolving_pending_judgments() {
    let input = parsed("my compose f g x = f (g x)");
    let revision = input.revision();
    let environment = input.syntax_environment();
    let selected = input.selected_syntax_environment().clone();
    let artifact = ShadowArtifact::from_parsed(input).unwrap();
    assert_eq!(artifact.parsed().revision(), revision);
    assert_eq!(artifact.parsed().syntax_environment(), environment);
    assert!(Arc::ptr_eq(
        artifact.parsed().selected_syntax_environment(),
        &selected
    ));
    let skeleton = artifact.skeleton().unwrap();
    assert!(skeleton.capture_uses().is_empty());
    assert!(matches!(
        skeleton.expression(skeleton.body()).unwrap().form(),
        Form::Apply { .. }
    ));
    assert_eq!(skeleton.pending().len(), 14);
    assert!(
        skeleton
            .pending()
            .iter()
            .any(|p| p.premise() == Premise::FullFunctionMembership)
    );
    let other = ShadowArtifact::from_parsed(artifact.parsed().clone()).unwrap();
    assert_eq!(
        artifact.position(&other.root()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        skeleton
            .expression(other.skeleton().unwrap().body())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn facade_retains_annotations_when_the_narrow_skeleton_is_unavailable() {
    let artifact = ShadowArtifact::from_parsed(parsed("x as int; x as int")).unwrap();
    assert_eq!(artifact.annotations().len(), 2);
    assert!(artifact.skeleton().is_err());
    assert_eq!(artifact.source(), "x as int; x as int");
}

#[test]
fn facade_exposes_lexical_capture_use_without_semantic_discharge() {
    let artifact =
        ShadowArtifact::from_parsed(parsed("my apply f = { my step x = f x; step }")).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let [incidence]: &[CaptureUseIncidence] = skeleton.capture_uses() else {
        panic!("one lexical incidence")
    };
    let Form::Lambda {
        parameter: outer_f,
        body: block,
        ..
    } = skeleton.expression(skeleton.body()).unwrap().form()
    else {
        panic!("outer lambda")
    };
    let Form::Bind { value, .. } = skeleton.expression(block).unwrap().form() else {
        panic!("sequential bind")
    };
    assert_eq!(incidence.lambda(), value);
    assert_eq!(incidence.captured(), outer_f);
    let Form::Lambda {
        body: call,
        captures,
        correspondence,
        ..
    } = skeleton.expression(incidence.lambda()).unwrap().form()
    else {
        panic!("local lambda")
    };
    assert_eq!(captures.as_slice(), std::slice::from_ref(outer_f));
    assert_eq!(
        *correspondence,
        ClosureCorrespondence::PendingTypedCaptureProviderReceiverAndSemanticDischarge
    );
    let Form::Apply { callee, .. } = skeleton.expression(call).unwrap().form() else {
        panic!("inner call")
    };
    let callee = skeleton.expression(callee).unwrap();
    let Form::Use { binder, occurrence } = callee.form() else {
        panic!("callee use")
    };
    assert_eq!(binder, incidence.captured());
    assert_eq!(occurrence, incidence.occurrence());
    assert_eq!(callee.position(), incidence.position());
    assert_eq!(
        skeleton.use_position(occurrence).unwrap(),
        incidence.position()
    );
    let position = artifact.position(incidence.position()).unwrap();
    assert_eq!(position.kind(), yu_syntax::SyntaxKind::IdentifierExpression);
    assert_eq!(*position.range(), 27..28);
    assert_eq!(skeleton.pending().len(), 7);
    for (pending, expected) in skeleton.pending().iter().zip([
        Premise::CallableRole,
        Premise::FullFunctionMembership,
        Premise::CallViewRealization,
        Premise::QIndependentSourceCallViewFormation,
        Premise::SourceEventContributionAndTypedOutputObservation,
        Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
        Premise::SourceDirectionalOutputEffectProtectionIntroduction,
    ]) {
        assert_eq!(pending.call(), call);
        assert_eq!(pending.premise(), expected);
    }
}
