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
    assert_eq!(skeleton.pending().len(), 10);
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
            Premise::JointArgumentTypingAndActualReturnedProviderCarrierCompatibility,
            Premise::SourceSignatureLocalImmediateCallEffectPositionFormation,
            Premise::OriginalTypedCallEffectOccurrenceIntroduction,
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

#[test]
fn shadow_local_bind_rejects_foreign_parse_and_adjacent_candidates() {
    use yu_hir::shadow::lower_module_with_shadow_local_binding;
    let parse = |source: &str| {
        let text: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(text.clone()));
        parse_file(text, header, Arc::new(SyntaxEnvironment::empty()))
    };
    let identity = || ModuleIdentity::source_root(FileId::new(FileKey::new("shadow", "local.yu")));
    let source = "my apply f = { my step x = f x; step }";
    let parsed = parse(source);
    let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
    let hir = lower_module_with_shadow_local_binding(
        identity(),
        &parsed,
        SemanticImports::empty(),
        artifact.clone(),
    )
    .unwrap();
    let foreign = lower_module_with_shadow_local_binding(
        identity(),
        &parsed,
        SemanticImports::empty(),
        artifact.clone(),
    )
    .unwrap();
    let local = |hir: &yu_hir::HirModule| {
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding");
        };
        let ResolvedExpr::Lambda { body, .. } = binding.value() else {
            panic!("lambda");
        };
        assert!(matches!(body.as_ref(), ResolvedExpr::Error { .. }));
        hir.shadow_local_binding(binding.definition_root())
            .unwrap()
            .unwrap()
            .local
            .clone()
    };
    assert_ne!(local(&hir), local(&foreign));
    assert!(matches!(
        artifact.local_source_position(&hir, &local(&foreign)),
        Err(SourceIdentityError::ForeignHirArtifact)
    ));
    let foreign_artifact = Arc::new(ShadowArtifact::from_parsed(parse(source)).unwrap());
    assert!(matches!(
        lower_module_with_shadow_local_binding(
            identity(),
            &parsed,
            SemanticImports::empty(),
            foreign_artifact
        ),
        Err(HirAvailabilityError::StructuralProjection)
    ));
    for source in [
        "my apply f x = f x",
        "my apply f g = { my step x = f x; step }",
        "my apply f = { my step x y = f x; step }",
        "my apply f = { my step x = f(x); step }",
        "my apply f = { my step x = f x x; step }",
        "my apply f = { my step x = f x; step x }",
    ] {
        let parsed = parse(source);
        let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
        assert!(
            matches!(
                lower_module_with_shadow_local_binding(
                    identity(),
                    &parsed,
                    SemanticImports::empty(),
                    artifact
                ),
                Err(HirAvailabilityError::StructuralProjection)
            ),
            "{source}"
        );
    }
}

#[test]
fn shadow_local_bind_joins_pending_structural_projection_without_discharge() {
    use yu_core::shadow_derivation::{PendingStructuralForm, PendingStructuralProjection};
    use yu_hir::{NameResolution, shadow::lower_module_with_shadow_local_binding};
    use yu_solver::PendingApplicationState;

    let text: Arc<SourceText> = Arc::from("my apply f = { my step x = f x; step }");
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
    assert_eq!(call.application_premises.len(), 10);
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
    #[cfg(feature = "shadow-scc-observer")]
    let collected = batch.clone();
    // Recollect the same immutable HIR so the solves have independent SCC
    // query accounting; each later SCC join uses its own collection brand.
    let capture_batch = ConstraintBatch::collect(hir.clone()).unwrap();
    #[cfg(feature = "shadow-scc-observer")]
    let captured_collected = capture_batch.clone();
    let solved = SolvedModule::solve(batch).unwrap();
    let captured = SolvedModule::solve_with_shadow_fresh_capture(capture_batch).unwrap();
    assert_row(solved.pending_applications());
    assert_row(captured.pending_applications());
    assert_eq!(captured.store().facts(), solved.store().facts());
    assert_eq!(captured.errors(), solved.errors());
    let baseline_counters = solved.counters();
    assert_eq!(captured.counters(), baseline_counters);
    assert_eq!(captured.occurrences(), solved.occurrences());
    assert!(Arc::ptr_eq(captured.hir(), &hir));
    assert_eq!(
        captured.hir().shadow_local_binding(root).unwrap().unwrap() as *const _,
        sidecar
    );
    assert!(Arc::ptr_eq(
        captured.shadow_captured_source(root).unwrap().unwrap(),
        &artifact
    ));
    let retained_root = solved.pending_applications()[0]
        .enclosing_root
        .as_ref()
        .unwrap();
    let current_scheme = solved
        .shadow_closed_schemes()
        .for_root(retained_root)
        .unwrap();
    assert_eq!(retained_root, root);
    assert_eq!(current_scheme.owner(), retained_root);
    assert!(current_scheme.same_identity(solved.shadow_closed_schemes().for_root(root).unwrap()));
    // This is the enclosing apply root's current finalized scheme, not a
    // generalized local step scheme or an application typing judgment.
    let captured_root = captured.pending_applications()[0]
        .enclosing_root
        .as_ref()
        .unwrap();
    let captured_scheme = captured
        .shadow_closed_schemes()
        .for_root(captured_root)
        .unwrap();
    assert_eq!(captured_root, retained_root);
    let mut associations = solved.shadow_pending_application_closed_schemes();
    let association = associations.next().unwrap();
    assert!(associations.next().is_none());
    assert!(std::ptr::eq(
        association.application(),
        &solved.pending_applications()[0]
    ));
    assert!(std::ptr::eq(association.enclosing_root(), retained_root));
    assert!(association.scheme().same_identity(current_scheme));
    assert!(
        association.same_identity(
            solved
                .shadow_pending_application_closed_schemes()
                .next()
                .unwrap()
        )
    );
    let captured_association = captured
        .shadow_pending_application_closed_schemes()
        .next()
        .unwrap();
    assert!(std::ptr::eq(
        captured_association.application(),
        &captured.pending_applications()[0]
    ));
    assert!(std::ptr::eq(
        captured_association.enclosing_root(),
        captured_root
    ));
    assert!(captured_association.scheme().same_identity(captured_scheme));
    // Shared HIR root identities do not identify rows or finalized schemes
    // across independent solves, even when their endpoint views are equal.
    assert!(!association.same_identity(captured_association));
    assert!(
        !association
            .scheme()
            .same_identity(captured_association.scheme())
    );
    assert_eq!(
        association.application().state,
        yu_solver::PendingApplicationState::ApplicationTypingRuleUnresolved
    );
    assert_eq!(
        captured_association.application().state,
        yu_solver::PendingApplicationState::ApplicationTypingRuleUnresolved
    );
    assert_eq!(captured_scheme.owner(), captured_root);
    assert!(
        captured_scheme.same_identity(captured.shadow_closed_schemes().for_root(root).unwrap())
    );
    assert!(
        captured_scheme
            .endpoints()
            .alpha_eq(current_scheme.endpoints())
    );
    assert_eq!(
        captured_scheme
            .definition_source_position(&artifact)
            .unwrap(),
        artifact.definition_source_position(&hir, root).unwrap()
    );
    assert!(!solved.occurrences().contains(callee.occurrence()));
    assert!(!solved.occurrences().contains(argument.occurrence()));
    assert!(!captured.occurrences().contains(callee.occurrence()));
    assert!(!captured.occurrences().contains(argument.occurrence()));
    #[cfg(feature = "shadow-scc-observer")]
    {
        use yu_solver::shadow_scc::PendingSccGeneralizationPremise;

        for (retained, result, scheme) in [
            (&collected, &solved, current_scheme),
            (&captured_collected, &captured, captured_scheme),
        ] {
            let topology = retained.shadow_scc_topology();
            let definitions = topology.definitions().collect::<Vec<_>>();
            let [definition] = definitions.as_slice() else {
                panic!("only the enclosing root is a current SCC member");
            };
            let joined = topology
                .definition_closed_scheme(result, *definition)
                .unwrap();
            assert_eq!(joined.owner(), retained_root);
            assert!(joined.same_identity(scheme));
            let component = topology.component_of(*definition).unwrap();
            let components = topology.components().collect::<Vec<_>>();
            let [only_component] = components.as_slice() else {
                panic!("one current SCC component");
            };
            assert!(component.same_identity(*only_component));
            assert!(component.canonical_definition().same_identity(*definition));
            let generalization = component.pending_successor_generalization();
            assert!(generalization.component().same_identity(component));
            assert_eq!(
                generalization.premise(),
                PendingSccGeneralizationPremise::SuccessorGeneralizationRuleUnresolved
            );
            // Both operands are parameters, and local step has no current SCC
            // member. Capture is requested, but there is no DefinitionUseId for
            // either operand to query: no fresh use or Q/R correspondence follows.
            assert_eq!(component.internal_uses().count(), 0);
            assert_eq!(component.incoming_uses().count(), 0);
            assert_eq!(topology.outgoing_uses(component).unwrap().count(), 0);
        }
    }
    let source: Arc<SourceText> = Arc::from("missing 1");
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let no_root_hir = Arc::new(
        yu_hir::shadow::lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new("shadow", "no-root.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let no_root = SolvedModule::solve(ConstraintBatch::collect(no_root_hir).unwrap()).unwrap();
    let [no_root_row] = no_root.pending_applications() else {
        panic!("one retained top-level application")
    };
    assert!(no_root_row.enclosing_root.is_none());
    assert_eq!(
        no_root_row.state,
        yu_solver::PendingApplicationState::ApplicationTypingRuleUnresolved
    );
    assert!(
        no_root
            .shadow_pending_application_closed_schemes()
            .next()
            .is_none()
    );
    assert_eq!(solved.counters(), baseline_counters);
    assert_eq!(captured.counters(), baseline_counters);
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
