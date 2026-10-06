#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact};
use yu_core::shadow_derivation::{IncompleteDerivation, Node, RawStructuralArena};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

// Frozen Oracle a58eefc31e22141574b6f20c6a5748151c6d79f1, old infer:
// exact 38-byte input (SHA-256 09bdb9b3f976e40c70990336c3d7358909a3fe2cc3a1e7224425520bd21e8177), no LF;
// errors=[]; one ApplicationProvenance entry.
// Module 0: ExprId(8396) = App(ExprId(8394), ExprId(8395));
// callee Var(RefId(3452)) resolves DefId(2286), label f.
// Whole span 47..50, callee 47..48 include the 20-byte implicit prelude.
// Opaque root scheme metadata: ('a -> ['b] 'c) -> 'a -> ['b] 'c.
// This test joins source incidence only; it does not compare inferred schemes.
const SOURCE: &str = "my apply f = { my step x = f x; step }";
const LEGACY_PREFIX_BYTES: usize = 20;

#[test]
fn frozen_old_infer_application_joins_shadow_source_and_pending_call() {
    assert_eq!(SOURCE.len(), 38);
    assert!(!SOURCE.ends_with('\n'));
    let artifact = build_artifact(SOURCE);
    let skeleton = artifact.skeleton().unwrap();
    let input = skeleton.captured_call_input().unwrap();
    let pending_before = skeleton
        .pending()
        .iter()
        .map(|premise| (premise.call().clone(), premise.premise()))
        .collect::<Vec<_>>();
    assert_eq!(pending_before.len(), 7);

    let applications = skeleton
        .application_source_occurrences()
        .collect::<Vec<_>>();
    let [application] = applications.as_slice() else {
        panic!("the frozen capture has exactly one source application")
    };
    assert_eq!(application.expression(), input.call());
    let callee = skeleton.expression(application.callee()).unwrap();
    let Form::Use { binder, occurrence } = callee.form() else {
        panic!("the frozen callee joins a direct resolved use")
    };
    assert_eq!(binder, input.outer_parameter());
    assert_eq!(occurrence, input.callee_use());
    assert_eq!(skeleton.binder(binder).unwrap().name(), "f");

    let legacy_whole = (47 - LEGACY_PREFIX_BYTES)..(50 - LEGACY_PREFIX_BYTES);
    let legacy_callee = (47 - LEGACY_PREFIX_BYTES)..(48 - LEGACY_PREFIX_BYTES);
    let apply = skeleton.expression(application.expression()).unwrap();
    // Current Apply retains a call-tail position, while its cumulative range
    // and the direct callee jointly identify the old whole-application span.
    assert_eq!(legacy_whole.start, callee.range().start);
    assert_eq!(legacy_whole.end, apply.range().end);
    assert_eq!(callee.range(), &legacy_callee);
    assert_eq!(
        artifact.position(callee.position()).unwrap().range(),
        &legacy_callee
    );
    assert_eq!(&artifact.source()[legacy_whole], "f x");
    assert_eq!(&artifact.source()[legacy_callee], "f");

    let arena = IncompleteDerivation::from_captured_call(&artifact, &input).unwrap();
    let calls = arena
        .nodes()
        .iter()
        .filter_map(|node| match node {
            Node::PendingCall(call) => Some(call),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [call] = calls.as_slice() else {
        panic!("one source application joins one pending call")
    };
    assert_eq!(call.source, application.expression());
    assert_eq!(call.capture.occurrence(), occurrence);
    assert_eq!(call.capture.captured(), binder);
    let Node::Result { value } = &arena.nodes()[call.callee] else {
        panic!("callee result wrapper")
    };
    let Node::Name {
        source,
        binder: core_binder,
        occurrence: core_use,
    } = &arena.nodes()[*value]
    else {
        panic!("direct callee name")
    };
    assert_eq!(*source, application.callee());
    assert_eq!(*core_binder, binder);
    assert_eq!(*core_use, occurrence);
    assert!(std::ptr::eq(call.application_premises, skeleton.pending()));
    assert_eq!(call.application_premises.len(), 7);
    assert!(
        call.application_premises
            .iter()
            .all(|p| p.call() == input.call())
    );

    // Carry the same historical source crosswalk into the raw registration;
    // these borrowed inputs and unresolved rows supply no inferred call view.
    let raw = RawStructuralArena::from_artifact(&artifact).unwrap();
    let registrations = raw
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    let [registration] = registrations.as_slice() else {
        panic!("one historical application joins one pending source registration")
    };
    assert_eq!(registration.source, application.expression());
    assert_eq!(registration.source, input.call());
    assert_eq!(registration.source, call.source);
    assert!(std::ptr::eq(registration.application, apply.form()));
    let source_input = registration.source_use_input;
    assert_eq!(source_input.application().expression(), registration.source);
    assert!(std::ptr::eq(
        source_input.application().position(),
        application.position()
    ));
    assert!(std::ptr::eq(
        source_input.application().callee(),
        application.callee()
    ));
    assert!(std::ptr::eq(source_input.occurrence(), occurrence));
    assert!(std::ptr::eq(source_input.binder(), binder));
    assert!(std::ptr::eq(
        source_input.argument(),
        application.argument()
    ));
    let Node::Result { value } = &arena.nodes()[call.argument] else {
        panic!("argument result wrapper")
    };
    let Node::Name { source, .. } = &arena.nodes()[*value] else {
        panic!("direct argument name")
    };
    assert_eq!(source_input.argument(), *source);
    assert!(std::ptr::eq(registration.capture.unwrap(), call.capture));
    assert_eq!(registration.application_premises.len(), 7);
    for (registered, original) in registration
        .application_premises
        .iter()
        .zip(call.application_premises)
    {
        assert!(std::ptr::eq(*registered, original));
    }
    let locator = registration.source_view_premise_locator().unwrap();
    let registered_input = locator.input();
    assert!(std::ptr::eq(
        registered_input,
        registration.captured_input.unwrap()
    ));
    assert!(std::ptr::eq(registered_input.call(), input.call()));
    assert!(std::ptr::eq(
        registered_input.callee_use(),
        input.callee_use()
    ));
    assert!(std::ptr::eq(
        registered_input.outer_parameter(),
        input.outer_parameter()
    ));
    assert!(std::ptr::eq(
        registered_input.local_lambda(),
        input.local_lambda()
    ));
    assert!(std::ptr::eq(
        registered_input.local_binding(),
        input.local_binding()
    ));
    assert!(std::ptr::eq(
        registered_input.returned_use(),
        input.returned_use()
    ));
    assert!(std::ptr::eq(
        registered_input.capture_position(),
        input.capture_position()
    ));
    use yu_hir::shadow::UnresolvedSourceViewPremise::*;
    assert_eq!(
        locator.unresolved_premises(),
        &[
            CompatibleCompleteOriginalRoleIndexedProfile,
            IndependentlyTypedOriginalInvocationAndWholeRowCarrierPrefixResumptionInterpretation,
            JointlyScopedOriginalConstraints,
            SourceSlotCallbackBoundaryInputsAndCorrespondingTypedPaths,
            IndependentInitialCallerProviderWorldAdmission,
            SourceSeedRefinedRelationExistenceAndCoverage,
            OriginalSignatureApplicabilityAndContributionFormation,
        ]
    );
    assert_eq!(
        locator.unresolved_premises(),
        input.source_view_premise_locator().unresolved_premises()
    );
    assert_eq!(locator.unresolved_premises(), call.source_view_premises);
    assert_eq!(
        pending_before,
        skeleton
            .pending()
            .iter()
            .map(|premise| (premise.call().clone(), premise.premise()))
            .collect::<Vec<_>>()
    );

    // Each mutation uses its own branded input, so rejection tests exact bytes
    // rather than a foreign-identity mismatch. No legacy result is claimed.
    for source in [
        "my apply f = { my step x = f x; step }\n",
        "my apply f = { my step x = f x; step } ",
    ] {
        assert_ne!(source.as_bytes(), SOURCE.as_bytes());
        let changed = build_artifact(source);
        let own_input = changed.skeleton().unwrap().captured_call_input().unwrap();
        assert!(IncompleteDerivation::from_captured_call(&changed, &own_input).is_none());
    }
}

fn build_artifact(source: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    ShadowArtifact::from_parsed(parsed).unwrap()
}
