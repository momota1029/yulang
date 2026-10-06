#![cfg(feature = "shadow-f5")]

use std::sync::Arc;
use yu_core::shadow_derivation::{IncompleteDerivation, RawStructuralArena};
use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirErrorKind, HirItem, ModuleIdentity, ResolvedExpr,
    SemanticImports, lower_module,
    shadow::{
        Form, Premise, ShadowArtifact, SourceIdentityError, lower_module_with_captured_source,
        lower_module_with_source_identity,
    },
};
use yu_solver::{ConstraintBatch, SolvedModule};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn approved_captured_source_survives_refused_collection_and_solve() {
    const SOURCE: &str = "my apply f = { my step x = f x; step }";
    let parse = || {
        let source: Arc<SourceText> = Arc::from(SOURCE);
        let header = Arc::new(scan_header(source.clone()));
        parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
    };
    let identity =
        || ModuleIdentity::source_root(FileId::new(FileKey::new("shadow", "capture.yu")));
    let parsed = parse();
    let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
    let hir = Arc::new(
        lower_module_with_captured_source(
            identity(),
            &parsed,
            SemanticImports::empty(),
            artifact.clone(),
        )
        .unwrap(),
    );
    let baseline = Arc::new(
        lower_module_with_source_identity(identity(), &parsed, SemanticImports::empty()).unwrap(),
    );
    assert_eq!(hir, baseline);
    let default = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    assert_eq!(hir.as_ref(), &default);
    let [HirItem::Binding(binding)] = hir.items() else {
        panic!("approved root")
    };
    let root = binding.definition_root().clone();
    let ResolvedExpr::Lambda { body, .. } = binding.value() else {
        panic!("outer lambda")
    };
    assert!(matches!(body.as_ref(), ResolvedExpr::Error { .. }));
    assert!(
        hir.errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );
    assert!(Arc::ptr_eq(
        hir.shadow_captured_source(&root).unwrap().unwrap(),
        &artifact
    ));
    let skeleton = artifact.skeleton().unwrap();
    let input = skeleton.captured_call_input().unwrap();
    let Form::Lambda {
        parameter: f,
        body,
        captures,
        ..
    } = skeleton.expression(skeleton.body()).unwrap().form()
    else {
        panic!("root lambda")
    };
    assert!(captures.is_empty());
    assert_eq!(f, input.outer_parameter());
    let Form::Bind {
        binder: step,
        value,
        body: returned,
    } = skeleton.expression(body).unwrap().form()
    else {
        panic!("local bind")
    };
    let Form::Lambda {
        parameter: x,
        captures,
        body: call,
        ..
    } = skeleton.expression(value).unwrap().form()
    else {
        panic!("local lambda")
    };
    assert_eq!(captures.as_slice(), std::slice::from_ref(f));
    let Form::Use {
        binder,
        occurrence: step_use,
    } = skeleton.expression(returned).unwrap().form()
    else {
        panic!("returned use")
    };
    assert_eq!(binder, step);
    let Form::Apply {
        callee, argument, ..
    } = skeleton.expression(call).unwrap().form()
    else {
        panic!("structural call")
    };
    let Form::Use {
        binder,
        occurrence: f_use,
    } = skeleton.expression(callee).unwrap().form()
    else {
        panic!("captured use")
    };
    assert_eq!(binder, f);
    let Form::Use {
        binder,
        occurrence: x_use,
    } = skeleton.expression(argument).unwrap().form()
    else {
        panic!("local use")
    };
    assert_eq!(binder, x);
    assert_ne!(f_use, x_use);
    assert_ne!(f_use, step_use);
    assert_ne!(x_use, step_use);
    assert_eq!(skeleton.uses().len(), 3);
    assert_eq!(skeleton.pending().len(), 7);
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
    assert!(skeleton.pending().iter().all(|p| p.call() == call));
    let premises = skeleton
        .pending()
        .iter()
        .map(|p| (p.call().clone(), p.premise()))
        .collect::<Vec<_>>();
    assert!(RawStructuralArena::from_artifact(&artifact).is_some());
    assert!(IncompleteDerivation::from_captured_call(&artifact, &input).is_some());
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let refusal = ConstraintBatch::collect(baseline.clone()).unwrap();
    assert_eq!(batch.counters(), refusal.counters());
    assert!(batch.pending_applications().is_empty());
    assert!(
        batch
            .shadow_pending_application_source_uses()
            .next()
            .is_none()
    );
    assert!(Arc::ptr_eq(
        batch.shadow_captured_source(&root).unwrap().unwrap(),
        &artifact
    ));
    let solved = SolvedModule::solve(batch).unwrap();
    let refused = SolvedModule::solve(refusal).unwrap();
    assert_eq!(solved.counters(), refused.counters());
    assert_eq!(solved.store().facts().len(), refused.store().facts().len());
    assert!(solved.store().facts().is_empty());
    assert!(solved.pending_applications().is_empty());
    assert!(
        solved
            .shadow_pending_application_source_uses()
            .next()
            .is_none()
    );
    assert!(Arc::ptr_eq(solved.hir(), &hir));
    assert!(Arc::ptr_eq(
        solved.shadow_captured_source(&root).unwrap().unwrap(),
        &artifact
    ));
    assert_eq!(
        artifact
            .skeleton()
            .unwrap()
            .pending()
            .iter()
            .map(|p| (p.call().clone(), p.premise()))
            .collect::<Vec<_>>(),
        premises
    );
    let [HirItem::Binding(foreign)] = baseline.items() else {
        panic!("baseline root")
    };
    assert!(matches!(
        solved.shadow_captured_source(foreign.definition_root()),
        Err(SourceIdentityError::ForeignHirArtifact)
    ));
    assert!(
        baseline
            .shadow_captured_source(foreign.definition_root())
            .unwrap()
            .is_none()
    );
    let foreign_artifact = Arc::new(ShadowArtifact::from_parsed(parse()).unwrap());
    assert!(matches!(
        lower_module_with_captured_source(
            identity(),
            &parsed,
            SemanticImports::empty(),
            foreign_artifact
        ),
        Err(HirAvailabilityError::StructuralProjection)
    ));
}

#[test]
fn captured_source_wrapper_rejects_adjacent_structural_shapes() {
    for source in [
        "my apply f x = f x",
        "my apply f g = { my step x = f x; step }",
        "my apply f = { my step x y = f x; step }",
        "my apply f = { my step x = f(x); step }",
        "my apply f = { my step x = f x x; step }",
        "my apply f = { my step x = f x; step x }",
    ] {
        let text: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(text.clone()));
        let parsed = parse_file(text, header, Arc::new(SyntaxEnvironment::empty()));
        // These siblings reach the public retention wrapper: construction of
        // their source artifacts succeeds even when the captured locator fails.
        let artifact = Arc::new(
            ShadowArtifact::from_parsed(parsed.clone())
                .unwrap_or_else(|error| panic!("source artifact for {source}: {error:?}")),
        );
        assert!(
            matches!(
                lower_module_with_captured_source(
                    ModuleIdentity::source_root(FileId::new(FileKey::new("shadow", "sibling.yu"))),
                    &parsed,
                    SemanticImports::empty(),
                    artifact,
                ),
                Err(HirAvailabilityError::StructuralProjection)
            ),
            "{source}"
        );
    }
}
