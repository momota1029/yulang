#![cfg(feature = "shadow-f5")]

//! Structural differential between bounded shadow applications and current F5.
//! Parsing is shared; shadow projection and current production F5 lowering are
//! separate paths. Compare source spelling/ranges and lexical resolution within
//! each artifact, never IDs across artifacts. This does not establish old-infer
//! parity, scheme equality, Apply typing, callable roles, Function membership,
//! call views, soundness, or principality.

use std::sync::Arc;
use yu_core::shadow_derivation::{ApplyStructuralPosition, RawStructuralArena};
use yu_hir::{
    FileId, FileKey, HirErrorKind, HirItem, ModuleIdentity, NameResolution, ResolvedExpr,
    SemanticImports, lower_module,
    shadow::lower_module_with_shadow_applications,
    shadow::{Form, ShadowArtifact},
};
use yu_solver::shadow_f5::PendingApplicationOperandPosition;
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
    assert!(batch.occurrences().is_empty());
    let retained_row_addresses: Vec<_> = batch
        .pending_applications()
        .iter()
        .map(|row| row as *const _)
        .collect();
    let solved = SolvedModule::solve(batch).unwrap();
    assert!(Arc::ptr_eq(solved.hir(), &shadow_hir));
    let rows = solved.pending_applications();
    assert_eq!(
        rows.iter().map(|row| row as *const _).collect::<Vec<_>>(),
        retained_row_addresses
    );
    assert_eq!(rows.len(), 2);
    assert!(
        rows.iter()
            .all(|row| { row.state == PendingApplicationState::ApplicationTypingRuleUnresolved })
    );

    let [HirItem::Binding(binding)] = shadow_hir.items() else {
        panic!("binding");
    };
    let root = binding.definition_root();
    let root_position = shadow
        .definition_source_position(&shadow_hir, root)
        .unwrap();
    let counters = solved.counters();
    let direct_uses: Vec<_> = solved.shadow_pending_application_source_uses().collect();
    assert_eq!(direct_uses.len(), 2);
    for (row, source_use) in rows.iter().zip(&direct_uses) {
        assert_eq!(row.enclosing_root.as_ref(), Some(root));
        assert!(std::ptr::eq(source_use.application(), row));
        assert_eq!(
            source_use.position(),
            PendingApplicationOperandPosition::Callee
        );
        assert!(std::ptr::eq(
            source_use.occurrence(),
            &row.callee.occurrence
        ));
        assert!(std::ptr::eq(
            source_use.resolution(),
            row.callee.direct_name_resolution.as_ref().unwrap()
        ));
        assert_eq!(
            shadow
                .definition_source_position(&shadow_hir, source_use.enclosing_root().unwrap())
                .unwrap(),
            root_position
        );
    }
    assert!(!direct_uses[0].same_identity(direct_uses[1]));
    assert_ne!(direct_uses[0].occurrence(), direct_uses[1].occurrence());
    assert_eq!(solved.counters(), counters);

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
    let mut endpoint_views = Vec::new();
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
        let node = raw
            .nodes()
            .iter()
            .find(|node| std::ptr::eq(skeleton.expression(&node.source).unwrap(), application))
            .expect("the exact solver Apply has a retained raw node");
        let endpoints = raw
            .pending_apply_endpoint_skeleton(&node.source)
            .expect("the supported Apply retains its structural endpoint skeleton");
        assert!(std::ptr::eq(endpoints.source(), &node.source));
        assert_eq!(
            skeleton.expression(endpoints.source()).unwrap().position(),
            &application_position
        );
        assert!(std::ptr::eq(endpoints.callee(), callee));
        assert!(std::ptr::eq(endpoints.argument(), argument));
        assert!(std::ptr::eq(
            endpoints.call(),
            node.call
                .as_ref()
                .expect("the retained Apply has raw call metadata")
        ));
        assert_eq!(
            endpoints.addresses().map(|address| address.position()),
            [
                ApplyStructuralPosition::CalleeValue,
                ApplyStructuralPosition::CalleeEffect,
                ApplyStructuralPosition::ArgumentValue,
                ApplyStructuralPosition::ArgumentEffect,
                ApplyStructuralPosition::CandidateFunctionReturnEffect,
                ApplyStructuralPosition::CandidateFunctionResult,
                ApplyStructuralPosition::WholeApplyValue,
                ApplyStructuralPosition::WholeApplyEffect,
            ]
        );
        for (index, address) in endpoints.addresses().iter().enumerate() {
            assert!(std::ptr::eq(address.application(), endpoints.source()));
            for previous in &endpoints.addresses()[..index] {
                assert_ne!(address, previous);
            }
        }
        let pending = skeleton
            .pending()
            .iter()
            .filter(|premise| premise.call() == endpoints.source())
            .collect::<Vec<_>>();
        assert_eq!(pending.len(), 7);
        assert_eq!(endpoints.call().application_premises.len(), pending.len());
        for (actual, expected) in endpoints.call().application_premises.iter().zip(pending) {
            assert!(std::ptr::eq(*actual, expected));
        }
        let source_input = endpoints
            .call()
            .source_use_input
            .as_ref()
            .expect("each supported direct callee retains its source call input");
        assert_eq!(source_input.application().expression(), endpoints.source());
        assert!(std::ptr::eq(source_input.application().callee(), callee));
        assert!(std::ptr::eq(source_input.argument(), argument));
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
        let registration = node
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
        endpoint_views.push(endpoints);
    }
    // Retained solver order is outer then inner. These addresses label syntax
    // bookkeeping only; they establish no typed endpoint or port equality.
    let [outer, inner] = endpoint_views.as_slice() else {
        panic!("exactly two retained Apply rows");
    };
    let outer_argument = skeleton.expression(outer.argument()).unwrap();
    let inner_source = match outer_argument.form() {
        Form::Group { inner } => inner,
        Form::Apply { .. } => outer.argument(),
        _ => panic!("the outer argument retains the inner Apply, optionally grouped"),
    };
    assert_eq!(inner_source, inner.source());
    assert_ne!(outer.source(), inner.source());
    for outer_address in outer.addresses() {
        for inner_address in inner.addresses() {
            assert_ne!(outer_address, inner_address);
        }
    }
    assert_ne!(outer.addresses()[2], inner.addresses()[6]);
    assert_ne!(outer.addresses()[3], inner.addresses()[7]);
    assert_eq!(outer.addresses()[2].application(), outer.source());
    assert_eq!(outer.addresses()[3].application(), outer.source());
    assert_eq!(inner.addresses()[6].application(), inner.source());
    assert_eq!(inner.addresses()[7].application(), inner.source());
    assert!(
        rows.iter()
            .all(|row| { row.state == PendingApplicationState::ApplicationTypingRuleUnresolved })
    );
    assert_eq!(solved.counters(), counters);
    assert_ne!(use_ids[0], use_ids[1]);
    assert_eq!(parameter_ids[0], parameter_ids[1]);
    assert!(
        solved
            .hir()
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
    );
}

#[test]
fn pending_application_direct_names_preserve_positions_and_resolution_variants() {
    for text in ["my invoke x = x(x)", "missing 1"] {
        let source: Arc<SourceText> = Arc::from(text);
        let header = Arc::new(scan_header(source.clone()));
        let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "shadow-f5-differential",
            "direct-name-operands.yu",
        )));
        let hir = Arc::new(
            lower_module_with_shadow_applications(
                identity.clone(),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        let foreign_hir = Arc::new(
            lower_module_with_shadow_applications(identity, &parsed, SemanticImports::empty())
                .unwrap(),
        );
        let shadow = ShadowArtifact::from_parsed(parsed).unwrap();
        let batch = ConstraintBatch::collect(hir.clone()).unwrap();
        let cloned = batch.clone();
        let recollected = ConstraintBatch::collect(hir.clone()).unwrap();
        let retained_row_address = &batch.pending_applications()[0] as *const _;
        let solved = SolvedModule::solve(batch).unwrap();
        let rows = solved.pending_applications();
        assert_eq!(rows.len(), 1);
        assert_eq!(&rows[0] as *const _, retained_row_address);
        assert_eq!(
            rows[0].state,
            PendingApplicationState::ApplicationTypingRuleUnresolved
        );
        let uses: Vec<_> = solved.shadow_pending_application_source_uses().collect();
        let foreign = SolvedModule::solve(ConstraintBatch::collect(foreign_hir).unwrap()).unwrap();
        let foreign_uses: Vec<_> = foreign.shadow_pending_application_source_uses().collect();
        assert_eq!(uses.len(), foreign_uses.len());
        for (retained, other) in uses.iter().zip(foreign_uses) {
            assert!(!retained.same_identity(other));
            assert_ne!(retained.occurrence(), other.occurrence());
            assert!(
                shadow
                    .occurrence_source_position(solved.hir(), other.occurrence())
                    .is_err()
            );
            // Independently lowered rows still describe the same parsed position.
            assert_eq!(
                shadow
                    .occurrence_source_position(solved.hir(), retained.occurrence())
                    .unwrap(),
                shadow
                    .occurrence_source_position(foreign.hir(), other.occurrence())
                    .unwrap()
            );
        }
        for other in [&cloned, &recollected] {
            let other_uses: Vec<_> = other.shadow_pending_application_source_uses().collect();
            assert_eq!(uses.len(), other_uses.len());
            for (retained, other) in uses.iter().zip(other_uses) {
                // Shared HIR coordinates do not identify another retained row.
                assert_eq!(retained.occurrence(), other.occurrence());
                assert!(!retained.same_identity(other));
            }
        }
        assert_eq!(
            uses[0].position(),
            PendingApplicationOperandPosition::Callee
        );
        for source_use in &uses {
            assert!(std::ptr::eq(source_use.application(), &rows[0]));
            shadow
                .occurrence_source_position(&hir, source_use.occurrence())
                .unwrap();
        }
        match &hir.items()[0] {
            HirItem::Binding(binding) => {
                assert_eq!(uses.len(), 2);
                assert_eq!(
                    uses[1].position(),
                    PendingApplicationOperandPosition::Argument
                );
                assert!(!uses[0].same_identity(uses[1]));
                assert_ne!(uses[0].occurrence(), uses[1].occurrence());
                for source_use in &uses {
                    assert_eq!(source_use.enclosing_root(), Some(binding.definition_root()));
                }
                let (NameResolution::Parameter(callee), NameResolution::Parameter(argument)) =
                    (uses[0].resolution(), uses[1].resolution())
                else {
                    panic!("both direct Names retain parameter resolution");
                };
                assert_eq!(callee, argument);
                // Join each operand separately; missing shadow metadata supplies
                // no declaration or application typing judgment.
                let skeleton = shadow
                    .skeleton()
                    .expect("the supported unary fixture retains its source skeleton");
                let crosswalk = shadow.skeleton_source_crosswalk();
                let application_position = shadow
                    .occurrence_source_position(solved.hir(), &rows[0].occurrence)
                    .unwrap();
                let application = crosswalk
                    .application_at_position(&application_position)
                    .unwrap()
                    .expect("the supported unary fixture retains its source Apply");
                let Form::Apply {
                    callee: source_callee,
                    argument: source_argument,
                    ..
                } = application.form()
                else {
                    panic!("crosswalk application retains its Apply form");
                };
                let mut source_uses = Vec::new();
                let mut source_binders = Vec::new();
                for (source_use, expression) in uses.iter().zip([source_callee, source_argument]) {
                    let position = shadow
                        .occurrence_source_position(solved.hir(), source_use.occurrence())
                        .unwrap();
                    let expression = skeleton.expression(expression).unwrap();
                    assert_eq!(expression.position(), &position);
                    let exact_use = crosswalk.use_at_position(&position).unwrap().unwrap();
                    let Form::Use { occurrence, binder } = expression.form() else {
                        panic!("each direct Name retains its own source Use form");
                    };
                    assert_eq!(exact_use, occurrence);
                    source_uses.push(exact_use);
                    source_binders.push(binder);
                    let NameResolution::Parameter(parameter) = source_use.resolution() else {
                        panic!("direct operand retains parameter resolution");
                    };
                    let parameter_position = shadow
                        .parameter_source_position(solved.hir(), parameter)
                        .unwrap();
                    let (lambda, declared_parameter) = crosswalk
                        .parameter_at_position(&parameter_position)
                        .unwrap()
                        .expect("the supported unary fixture retains its Lambda declaration");
                    assert_eq!(binder, declared_parameter);
                    let Form::Lambda { parameter, .. } = lambda.form() else {
                        panic!("retained syntactic declaration is a Lambda");
                    };
                    assert_eq!(parameter, binder);
                }
                assert_ne!(source_uses[0], source_uses[1]);
                assert_eq!(source_binders[0], source_binders[1]);
            }
            HirItem::Expression(_) => {
                assert_eq!(uses.len(), 1);
                assert!(uses[0].enclosing_root().is_none());
                assert!(matches!(uses[0].resolution(), NameResolution::Unresolved));
            }
            HirItem::Error { .. } => panic!("existing fixture retains an application"),
        }
    }
}
