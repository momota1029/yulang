//! Theorem requirements located by validated structure, without discharge.
use super::*;
use crate::shadow::*;

const SOURCE: &str = "my apply f = { my step x = f x; step }";

#[test]
fn shadow_source_view_premise_locator_borrows_exact_input_and_preserves_pending() {
    let artifact = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let before = skeleton
        .pending()
        .iter()
        .map(|p| (p.call().clone(), p.premise()))
        .collect::<Vec<_>>();
    let input = skeleton.captured_call_input().unwrap();
    let locator = input.source_view_premise_locator();
    assert!(std::ptr::eq(locator.input(), &input));
    assert!(std::ptr::eq(locator.input().call(), input.call()));
    assert!(std::ptr::eq(
        locator.input().outer_parameter(),
        input.outer_parameter()
    ));
    assert!(std::ptr::eq(
        locator.input().callee_use(),
        input.callee_use()
    ));
    use UnresolvedSourceViewPremise::*;
    assert_eq!(
        locator.unresolved_premises(),
        &[
            CompatibleCompleteOriginalRoleIndexedProfile,
            IndependentlyTypedOriginalInvocationAndWholeRowCarrierPrefixResumptionInterpretation,
            JointlyScopedOriginalConstraints,
            SourceSlotCallbackBoundaryInputsAndCorrespondingTypedPaths,
            IndependentInitialCallerProviderWorldAdmission,
            SourceSeedRefinedRelationExistenceAndCoverage,
        ]
    );
    assert_eq!(before.len(), 7);
    assert_eq!(
        before,
        skeleton
            .pending()
            .iter()
            .map(|p| (p.call().clone(), p.premise()))
            .collect::<Vec<_>>()
    );
    let foreign = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
    let foreign = foreign.skeleton().unwrap();
    assert_eq!(
        foreign.expression(locator.input().call()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        foreign
            .binder(locator.input().outer_parameter())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        foreign
            .use_expression(locator.input().callee_use())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn shadow_source_view_premise_locator_absent_for_unrelated_topology() {
    for source in ["my apply f x = f x", "my apply f x = (f) x"] {
        let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
        let input = artifact.skeleton().unwrap().captured_call_input();
        assert!(
            input
                .as_ref()
                .map(|i| i.source_view_premise_locator())
                .is_none()
        );
    }
}
