#![cfg(feature = "shadow-f5")]

use std::sync::Arc;
use yu_core::shadow_derivation::RawStructuralArena;
use yu_hir::{
    FileId, FileKey, HirErrorKind, HirItem, ModuleIdentity, ResolvedExpr, SemanticImports,
    lower_module,
    shadow::{Form, Premise, ShadowArtifact},
};
use yu_solver::{ConstraintBatch, SolvedModule};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

// Frozen Oracle a58eefc31e22141574b6f20c6a5748151c6d79f1, old infer:
// exact no-LF 38-byte source, SHA-256
// 09bdb9b3f976e40c70990336c3d7358909a3fe2cc3a1e7224425520bd21e8177.
// One App ExprId(8396), children ExprIds(8394,8395); direct callee
// Var RefId(3452) -> DefId(2286), named f. Whole/callee spans 47..50 / 47..48
// include a 20-byte implicit prefix. Legacy IDs and scheme metadata remain
// opaque: this joins source incidence, not inferred semantic correspondence.
const SOURCE: &str = "my apply f = { my step x = f x; step }";

#[test]
fn frozen_legacy_application_joins_local_sidecar_and_unsolved_solver_row() {
    use yu_core::shadow_derivation::{PendingStructuralForm, PendingStructuralProjection};
    use yu_hir::{NameResolution, shadow::lower_module_with_shadow_local_binding};
    use yu_solver::PendingApplicationState;

    assert_eq!(SOURCE.len(), 38);
    assert!(!SOURCE.ends_with('\n'));
    let text: Arc<SourceText> = Arc::from(SOURCE);
    let header = Arc::new(scan_header(text.clone()));
    let parsed = parse_file(text, header, Arc::new(SyntaxEnvironment::empty()));
    let identity = || ModuleIdentity::source_root(FileId::new(FileKey::new("shadow", "join.yu")));
    let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
    let hir = Arc::new(
        lower_module_with_shadow_local_binding(
            identity(),
            &parsed,
            SemanticImports::empty(),
            artifact.clone(),
        )
        .unwrap(),
    );
    let ordinary = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    assert_eq!(hir.as_ref(), &ordinary);
    assert_eq!(hir.diagnostics(), ordinary.diagnostics());
    let [HirItem::Binding(binding)] = hir.items() else {
        panic!("root binding");
    };
    let root = binding.definition_root();
    let ResolvedExpr::Lambda {
        parameter: f,
        body: refused,
        ..
    } = binding.value()
    else {
        panic!("outer lambda");
    };
    assert!(matches!(refused.as_ref(), ResolvedExpr::Error { .. }));
    assert!(
        hir.errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );
    let local = hir.shadow_local_binding(root).unwrap().unwrap();
    let ResolvedExpr::Lambda {
        parameter: x,
        body: application,
        ..
    } = &local.initializer
    else {
        panic!("local lambda");
    };
    let ResolvedExpr::Apply {
        callee, argument, ..
    } = application.as_ref()
    else {
        panic!("local application");
    };
    assert_ne!(f, x);
    assert_eq!(
        hir.shadow_parameter_local_owner(x).unwrap(),
        Some(&local.local)
    );
    assert_eq!(local.captures.as_ref(), std::slice::from_ref(f));
    assert_eq!(local.continuation.local, local.local);

    let skeleton = artifact.skeleton().unwrap();
    let input = skeleton.captured_call_input().unwrap();
    let Form::Lambda {
        parameter: source_f,
        body: bound,
        ..
    } = skeleton.expression(skeleton.body()).unwrap().form()
    else {
        panic!("source root lambda");
    };
    let Form::Bind {
        binder: source_step,
        value: initializer,
        body: returned,
    } = skeleton.expression(bound).unwrap().form()
    else {
        panic!("source bind");
    };
    let Form::Lambda {
        parameter: source_x,
        body: source_call,
        captures,
        ..
    } = skeleton.expression(initializer).unwrap().form()
    else {
        panic!("source local lambda");
    };
    let Form::Apply {
        callee: source_callee,
        argument: source_argument,
        ..
    } = skeleton.expression(source_call).unwrap().form()
    else {
        panic!("source application");
    };
    let applications = skeleton
        .application_source_occurrences()
        .collect::<Vec<_>>();
    let [legacy_join] = applications.as_slice() else {
        panic!("one frozen legacy application joins one current application");
    };
    assert_eq!(legacy_join.expression(), source_call);
    assert_eq!(legacy_join.callee(), source_callee);
    assert_eq!(legacy_join.argument(), source_argument);
    assert_eq!(source_call, input.call());
    assert_eq!(initializer, input.local_lambda());
    assert_eq!(source_step, input.local_binding());
    assert_eq!(source_f, input.outer_parameter());
    let source_callee_expr = skeleton.expression(source_callee).unwrap();
    let source_argument_expr = skeleton.expression(source_argument).unwrap();
    let Form::Use {
        binder: callee_binder,
        occurrence: f_use,
    } = source_callee_expr.form()
    else {
        panic!("legacy direct callee joins a captured Use");
    };
    let Form::Use {
        binder: argument_binder,
        occurrence: x_use,
    } = source_argument_expr.form()
    else {
        panic!("argument joins a distinct local Use");
    };
    assert_eq!(callee_binder, source_f);
    assert_eq!(argument_binder, source_x);
    assert_eq!(f_use, input.callee_use());
    assert_ne!(f_use, x_use);
    assert_eq!(skeleton.binder(callee_binder).unwrap().name(), "f");
    let legacy_whole = (47 - 20)..(50 - 20);
    let legacy_callee = (47 - 20)..(48 - 20);
    // Apply retains a call-tail range; its end and the callee start recover
    // the historical cumulative whole-application range.
    assert_eq!(source_callee_expr.range().start, legacy_whole.start);
    assert_eq!(
        skeleton.expression(source_call).unwrap().range().end,
        legacy_whole.end
    );
    assert_eq!(source_callee_expr.range(), &legacy_callee);
    assert_eq!(
        artifact
            .position(source_callee_expr.position())
            .unwrap()
            .range(),
        &legacy_callee
    );
    assert_eq!(&artifact.source()[legacy_whole], "f x");
    assert_eq!(&artifact.source()[legacy_callee], "f");
    assert_eq!(skeleton.uses().len(), 3);
    assert_eq!(
        skeleton
            .pending()
            .iter()
            .map(|p| p.premise())
            .collect::<Vec<_>>(),
        [
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
            Premise::QIndependentSourceCallViewFormation,
            Premise::SourceEventContributionAndTypedOutputObservation,
            Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
            Premise::SourceDirectionalOutputEffectProtectionIntroduction,
        ]
    );
    let position = |id| artifact.occurrence_source_position(&hir, id).unwrap();
    assert_eq!(
        position(&local.occurrence),
        *skeleton.expression(bound).unwrap().position()
    );
    assert_eq!(
        artifact.local_source_position(&hir, &local.local).unwrap(),
        *skeleton.binder(source_step).unwrap().position()
    );
    assert_eq!(
        position(local.initializer.occurrence()),
        *skeleton.expression(initializer).unwrap().position()
    );
    assert_eq!(
        artifact.parameter_source_position(&hir, x).unwrap(),
        *skeleton.binder(source_x).unwrap().position()
    );
    assert_eq!(
        artifact.parameter_source_position(&hir, f).unwrap(),
        *skeleton.binder(source_f).unwrap().position()
    );
    assert_eq!(captures.as_slice(), std::slice::from_ref(source_f));
    assert_eq!(
        position(&local.continuation.occurrence),
        *skeleton.expression(returned).unwrap().position()
    );
    let Form::Use {
        binder: returned_binder,
        occurrence: returned_use,
    } = skeleton.expression(returned).unwrap().form()
    else {
        panic!("returned use");
    };
    assert_eq!(returned_binder, source_step);
    assert_eq!(returned_use, input.returned_use());
    assert_ne!(returned_use, f_use);
    assert_ne!(returned_use, x_use);
    assert_eq!(
        position(&local.continuation.occurrence),
        *skeleton.use_position(returned_use).unwrap()
    );
    assert_eq!(
        position(application.occurrence()),
        *skeleton.expression(source_call).unwrap().position()
    );
    assert_eq!(
        position(callee.occurrence()),
        *skeleton.expression(source_callee).unwrap().position()
    );
    assert_eq!(
        position(argument.occurrence()),
        *skeleton.expression(source_argument).unwrap().position()
    );
    assert_eq!(position(callee.occurrence()), *input.capture_position());

    let raw = RawStructuralArena::from_artifact(&artifact).unwrap();
    let projection = PendingStructuralProjection::from_raw(&raw).unwrap();
    let projected = |source| {
        projection
            .nodes()
            .iter()
            .find(|node| node.source == source)
            .unwrap()
    };
    let PendingStructuralForm::Bind {
        binder,
        value,
        body,
    } = &projected(bound).form
    else {
        panic!("projected bind");
    };
    assert_eq!(*binder, source_step);
    assert_eq!(projection.nodes()[*value].source, initializer);
    assert_eq!(projection.nodes()[*body].source, returned);
    let PendingStructuralForm::Lambda {
        parameter,
        body,
        captures,
        ..
    } = &projected(initializer).form
    else {
        panic!("projected local lambda");
    };
    assert_eq!(*parameter, source_x);
    assert_eq!(projection.nodes()[*body].source, source_call);
    assert_eq!(*captures, std::slice::from_ref(source_f));
    let PendingStructuralForm::PendingUseNormalization { binder, occurrence } =
        &projected(returned).form
    else {
        panic!("projected returned use");
    };
    assert_eq!(*binder, source_step);
    assert_eq!(*occurrence, returned_use);
    let PendingStructuralForm::PendingApply {
        callee: callee_offset,
        argument: argument_offset,
        call,
    } = &projected(source_call).form
    else {
        panic!("projected pending application");
    };
    assert_eq!(projection.nodes()[*callee_offset].source, source_callee);
    assert_eq!(projection.nodes()[*argument_offset].source, source_argument);
    let raw_call = raw
        .nodes()
        .iter()
        .find(|node| &node.source == source_call)
        .unwrap()
        .call
        .as_ref()
        .unwrap();
    assert!(std::ptr::eq(*call, raw_call));
    assert_eq!(call.application_premises.len(), 7);
    assert!(
        call.application_premises
            .iter()
            .all(|premise| premise.call() == source_call)
    );
    let premises = skeleton
        .pending()
        .iter()
        .map(|premise| (premise.call().clone(), premise.premise()))
        .collect::<Vec<_>>();
    assert_eq!(
        call.application_premises
            .iter()
            .map(|premise| (premise.call().clone(), premise.premise()))
            .collect::<Vec<_>>(),
        premises
    );
    assert_eq!(call.capture.unwrap().captured(), source_f);
    assert_eq!(call.capture.unwrap().occurrence(), f_use);
    let registrations = raw
        .nodes()
        .iter()
        .filter_map(|node| node.pending_source_call_registration())
        .collect::<Vec<_>>();
    let [registration] = registrations.as_slice() else {
        panic!("one source registration");
    };
    assert_eq!(registration.source, source_call);
    assert_eq!(registration.source_use_input.binder(), source_f);
    assert_eq!(registration.source_use_input.occurrence(), f_use);
    let locator = registration.source_view_premise_locator().unwrap();
    assert_eq!(locator.input().call(), source_call);
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

    let sidecar = local as *const _;
    let assert_row = |rows: &[yu_solver::PendingApplicationOccurrence]| {
        let [row] = rows else {
            panic!("one pending application");
        };
        assert_eq!(&row.occurrence, application.occurrence());
        assert_eq!(row.enclosing_root.as_ref(), Some(root));
        assert_eq!(&row.callee.occurrence, callee.occurrence());
        assert_eq!(&row.argument.occurrence, argument.occurrence());
        assert!(
            matches!(&row.callee.direct_name_resolution, Some(NameResolution::Parameter(id)) if id == f)
        );
        assert!(
            matches!(&row.argument.direct_name_resolution, Some(NameResolution::Parameter(id)) if id == x)
        );
        assert_eq!(
            row.state,
            PendingApplicationState::ApplicationTypingRuleUnresolved
        );
    };
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    assert_row(batch.pending_applications());
    assert!(batch.occurrences().is_empty());
    assert!(Arc::ptr_eq(batch.hir(), &hir));
    assert_eq!(
        batch.hir().shadow_local_binding(root).unwrap().unwrap() as *const _,
        sidecar
    );
    let solved = SolvedModule::solve(batch).unwrap();
    assert_row(solved.pending_applications());
    assert!(solved.store().facts().is_empty());
    assert!(Arc::ptr_eq(solved.hir(), &hir));
    assert_eq!(
        solved.hir().shadow_local_binding(root).unwrap().unwrap() as *const _,
        sidecar
    );
    assert!(Arc::ptr_eq(
        solved.shadow_captured_source(root).unwrap().unwrap(),
        &artifact
    ));
    assert_eq!(
        skeleton
            .pending()
            .iter()
            .map(|premise| (premise.call().clone(), premise.premise()))
            .collect::<Vec<_>>(),
        premises
    );
}
