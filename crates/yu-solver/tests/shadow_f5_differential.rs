#![cfg(feature = "shadow-f5")]

//! Structural differential between bounded shadow applications and current F5.
//! Parsing is shared; shadow projection and current production F5 lowering are
//! separate paths. Compare source spelling/ranges and lexical resolution within
//! each artifact, never IDs across artifacts. This does not establish old-infer
//! parity, scheme equality, Apply typing, callable roles, Function membership,
//! call views, soundness, or principality.

use std::sync::Arc;
use yu_core::shadow_derivation::RawStructuralArena;
use yu_hir::{
    FileId, FileKey, HirErrorKind, HirItem, ModuleIdentity, NameResolution, ResolvedExpr,
    SemanticImports, lower_module,
    shadow::lower_module_with_shadow_applications,
    shadow::{Form, ShadowArtifact},
};
use yu_solver::{ConstraintBatch, PendingApplicationState, SolvedModule};
use yu_syntax::{SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

#[test]
fn shadow_and_current_f5_preserve_leaf_parameter_source_and_resolution() {
    let source: Arc<SourceText> = Arc::from("my f x = x");
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let hir = Arc::new(
        lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "shadow-f5-differential",
                "leaf.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .expect("current F5 HIR is available for the common leaf input"),
    );
    let shadow = ShadowArtifact::from_parsed(parsed).expect("shadow artifact is available");
    let skeleton = shadow.skeleton().expect("leaf skeleton is supported");
    assert!(skeleton.pending().is_empty());
    assert!(
        skeleton
            .expressions()
            .iter()
            .all(|expression| !matches!(expression.form(), Form::Apply { .. }))
    );
    // Shadow retains a distinct declaration binder after the original parameter.
    assert_eq!(skeleton.binders().len(), 2);
    assert_eq!(skeleton.uses().len(), 1);
    let shadow_body = skeleton.expression(skeleton.body()).unwrap();
    let Form::Use { binder, occurrence } = shadow_body.form() else {
        panic!("shadow leaf body must be a lexical use");
    };
    let shadow_parameter = skeleton.binder(binder).unwrap();
    assert_eq!(shadow_parameter.name(), "x");
    assert_eq!(shadow_parameter.range(), &(5..6));
    assert_eq!(shadow_body.range(), &(9..10));
    assert_eq!(
        skeleton.use_expression(occurrence).unwrap().range(),
        shadow_body.range()
    );
    assert_eq!(
        skeleton.expression(&skeleton.uses()[0]).unwrap().range(),
        shadow_body.range()
    );

    assert!(hir.errors().is_empty());
    assert!(hir.diagnostics().is_empty());
    let [HirItem::Binding(binding)] = hir.items() else {
        panic!("current F5 must retain the single binding");
    };
    let [parameter] = binding.parameters() else {
        panic!("current F5 must retain the single formal parameter");
    };
    let ResolvedExpr::Lambda {
        parameter: lambda_parameter,
        body,
        ..
    } = binding.value()
    else {
        panic!("current F5 must lower the binding to a lambda");
    };
    let ResolvedExpr::Name {
        name,
        resolution: NameResolution::Parameter(resolved_parameter),
        ..
    } = body.as_ref()
    else {
        panic!("current F5 leaf body must resolve to its formal parameter");
    };
    assert_eq!(lambda_parameter, parameter.id());
    assert_eq!(resolved_parameter, parameter.id());
    assert!(hir.owns_parameter(resolved_parameter));
    assert_eq!(parameter.name().spelling(), shadow_parameter.name());
    assert_eq!(parameter.name().range(), shadow_parameter.range());
    assert_eq!(name.spelling(), shadow_parameter.name());
    assert_eq!(name.range(), shadow_body.range());
    let binder_position = shadow.position(shadow_parameter.position()).unwrap();
    assert_eq!(binder_position.kind(), SyntaxKind::IdentifierPattern);
    assert_eq!(binder_position.range(), parameter.name().range());
    let use_position = shadow
        .position(skeleton.use_position(occurrence).unwrap())
        .unwrap();
    assert_eq!(use_position.kind(), SyntaxKind::IdentifierExpression);
    assert_eq!(use_position.range(), name.range());
    assert_eq!(body.range(), shadow_body.range());

    let body_occurrence = body.occurrence().clone();
    let batch = ConstraintBatch::collect(hir).expect("current F5 collection is available");
    assert!(
        batch
            .occurrences()
            .iter()
            .any(|constraint| { constraint.cause().occurrence().occurrence() == &body_occurrence })
    );
    let solved = SolvedModule::solve(batch).expect("current F5 solving is available");
    assert!(solved.errors().is_empty());
    assert!(
        solved
            .store()
            .provenance()
            .iter()
            .any(|edge| { edge.cause().occurrence().occurrence() == &body_occurrence })
    );
}

#[test]
fn shadow_and_current_f5_preserve_integer_leaf_source_and_provenance() {
    let source: Arc<SourceText> = Arc::from("my f x = 42");
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let hir = Arc::new(
        lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "shadow-f5-differential",
                "integer.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .expect("current F5 HIR is available for the common integer leaf input"),
    );
    let shadow = ShadowArtifact::from_parsed(parsed).expect("shadow artifact is available");
    let skeleton = shadow
        .skeleton()
        .expect("integer leaf skeleton is supported");
    assert!(skeleton.pending().is_empty());
    // Shadow retains a distinct declaration binder after the original parameter.
    assert_eq!(skeleton.binders().len(), 2);
    assert!(skeleton.uses().is_empty());
    let shadow_parameter = &skeleton.binders()[0];
    assert_eq!(shadow_parameter.name(), "x");
    assert_eq!(shadow_parameter.range(), &(5..6));
    let shadow_body = skeleton.expression(skeleton.body()).unwrap();
    assert_eq!(shadow_body.range(), &(9..11));
    let Form::IntegerLiteral { spelling } = shadow_body.form() else {
        panic!("shadow body must retain the integer literal");
    };
    assert_eq!(spelling, "42");

    assert!(hir.errors().is_empty());
    assert!(hir.diagnostics().is_empty());
    let [HirItem::Binding(binding)] = hir.items() else {
        panic!("current F5 must retain the single binding");
    };
    let [parameter] = binding.parameters() else {
        panic!("current F5 must retain the single formal parameter");
    };
    let ResolvedExpr::Lambda {
        parameter: lambda_parameter,
        body,
        ..
    } = binding.value()
    else {
        panic!("current F5 must lower the binding to a lambda");
    };
    let ResolvedExpr::Integer {
        spelling, range, ..
    } = body.as_ref()
    else {
        panic!("current F5 integer leaf must remain an integer");
    };
    assert_eq!(lambda_parameter, parameter.id());
    assert_eq!(parameter.name().spelling(), shadow_parameter.name());
    assert_eq!(parameter.name().range(), shadow_parameter.range());
    assert_eq!(spelling, "42");
    assert_eq!(range, shadow_body.range());
    assert_eq!(body.range(), shadow_body.range());

    let body_occurrence = body.occurrence().clone();
    let batch = ConstraintBatch::collect(hir).expect("current F5 collection is available");
    assert!(
        batch
            .occurrences()
            .iter()
            .any(|constraint| { constraint.cause().occurrence().occurrence() == &body_occurrence })
    );
    let solved = SolvedModule::solve(batch).expect("current F5 solving is available");
    assert!(solved.errors().is_empty());
    assert!(
        solved
            .store()
            .provenance()
            .iter()
            .any(|edge| edge.cause().occurrence().occurrence() == &body_occurrence)
    );
}

#[test]
fn pending_solver_applications_join_exact_shadow_call_and_use_occurrences() {
    for text in [
        "my apply x = x(x 1)",
        "my apply x = x (x 1)",
        "my apply x = x (x(1,))",
    ] {
        assert_pending_solver_application_source_join(text);
    }
}

fn assert_pending_solver_application_source_join(text: &str) {
    let source: Arc<SourceText> = Arc::from(text);
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "shadow-f5-differential",
        "nested-pending-application.yu",
    )));
    let shadow_hir = Arc::new(
        lower_module_with_shadow_applications(identity.clone(), &parsed, SemanticImports::empty())
            .expect("opt-in HIR retains the nested application structure"),
    );
    let current_hir = lower_module(identity, &parsed, SemanticImports::empty())
        .expect("current HIR characterizes the production support boundary");
    assert!(
        current_hir
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );
    assert!(
        current_hir
            .diagnostics()
            .iter()
            .any(|diagnostic| { diagnostic.kind() == HirErrorKind::UnsupportedExpression })
    );

    let current_batch = ConstraintBatch::collect(Arc::new(current_hir)).unwrap();
    assert!(current_batch.pending_applications().is_empty());
    assert!(
        SolvedModule::solve(current_batch)
            .unwrap()
            .hir()
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );

    let shadow = ShadowArtifact::from_parsed(parsed).expect("shared parse shadow artifact");
    let skeleton = shadow.skeleton().expect("nested application skeleton");
    let crosswalk = shadow.skeleton_source_crosswalk();
    let raw = RawStructuralArena::from_artifact(&shadow)
        .expect("the same source artifact retains its raw structural inventory");
    let batch = ConstraintBatch::collect(shadow_hir.clone())
        .expect("shadow applications remain collectible as pending structure");
    let rows = batch.pending_applications();
    assert_eq!(rows.len(), 2);
    assert!(
        rows.iter()
            .all(|row| { row.state == PendingApplicationState::ApplicationTypingRuleUnresolved })
    );
    assert!(batch.occurrences().is_empty());

    if text.contains("x (x") {
        let [HirItem::Binding(binding)] = shadow_hir.items() else {
            panic!("binding");
        };
        let ResolvedExpr::Lambda { body, .. } = binding.value() else {
            panic!("lambda");
        };
        let ResolvedExpr::Apply { argument, .. } = body.as_ref() else {
            panic!("outer Apply");
        };
        let ResolvedExpr::Group { inner, .. } = argument.as_ref() else {
            panic!("retained Group");
        };
        assert_eq!(&rows[0].argument.occurrence, argument.occurrence());
        assert!(rows[0].argument.direct_name_resolution.is_none());
        assert_eq!(&rows[1].occurrence, inner.occurrence());
    }
    let mut parameter_ids = Vec::new();
    let mut use_ids = Vec::new();
    for row in rows {
        let application_position = shadow
            .occurrence_source_position(&shadow_hir, &row.occurrence)
            .expect("solver retains a HIR identity from the shared parse");
        let application = crosswalk
            .application_at_position(&application_position)
            .expect("application position belongs to this source artifact")
            .expect("the retained source position is an Apply");
        let Form::Apply {
            callee, argument, ..
        } = application.form()
        else {
            panic!("crosswalk returns an Apply");
        };
        for (operand, retained) in [(&row.callee, callee), (&row.argument, argument)] {
            let operand_position = shadow
                .occurrence_source_position(&shadow_hir, &operand.occurrence)
                .expect("operand identity belongs to the shared parse");
            assert_eq!(
                skeleton.expression(retained).unwrap().position(),
                &operand_position
            );
        }

        let callee_position = shadow
            .occurrence_source_position(&shadow_hir, &row.callee.occurrence)
            .unwrap();
        let use_id = crosswalk
            .use_at_position(&callee_position)
            .expect("callee position is in the source artifact")
            .expect("each nested callee is a distinct retained source use");
        let (registered_use, binder) = crosswalk
            .application_direct_use_at_position(&application_position)
            .expect("application position is in the source artifact")
            .expect("the retained application is a direct resolved Use");
        assert_eq!(use_id, registered_use);
        let Some(NameResolution::Parameter(parameter)) = row.callee.direct_name_resolution.as_ref()
        else {
            panic!("the source callee resolves to the formal parameter");
        };
        parameter_ids.push(parameter.clone());
        let parameter_position = shadow
            .parameter_source_position(&shadow_hir, parameter)
            .expect("formal parameter identity belongs to this HIR artifact");
        let (source_lambda, source_binder) = crosswalk
            .parameter_at_position(&parameter_position)
            .expect("parameter position is in the source artifact")
            .expect("formal parameter has a retained shadow binder");
        assert_eq!(binder, source_binder);
        let registration = raw
            .nodes()
            .iter()
            .find(|node| std::ptr::eq(skeleton.expression(&node.source).unwrap(), application))
            .expect("the exact Apply source expression is retained in the raw arena")
            .pending_source_call_registration()
            .expect("the direct source use has a pending structural registration");
        assert!(std::ptr::eq(
            skeleton.expression(registration.source).unwrap(),
            application
        ));
        assert_eq!(registration.source_use_input.occurrence(), use_id);
        assert_eq!(
            registration.source_use_input.application().expression(),
            registration.source
        );
        assert_eq!(registration.source_use_input.binder(), source_binder);
        // Optional declaration metadata is syntactic ownership only. This fixture
        // retains the root Lambda; missing metadata supplies no semantic judgment.
        let Some(declaration) = registration.parameter_declaration else {
            panic!("this fixture retains the root Lambda parameter declaration");
        };
        assert!(std::ptr::eq(declaration.lambda, source_lambda));
        assert!(std::ptr::eq(declaration.parameter, source_binder));
        let Form::Lambda { parameter, .. } = declaration.lambda.form() else {
            panic!("the syntactic declaration owner is a retained Lambda");
        };
        assert_eq!(parameter, source_binder);
        use_ids.push(use_id);
    }
    assert_ne!(use_ids[0], use_ids[1]);
    assert_eq!(parameter_ids[0], parameter_ids[1]);
    assert!(
        SolvedModule::solve(batch)
            .unwrap()
            .hir()
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );
}
