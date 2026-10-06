#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_core::shadow::{Correspondence, Form, ShadowArtifact, ShadowError};
use yu_core::shadow_derivation::RawStructuralArena;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn artifact(source: &str) -> ShadowArtifact {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    ShadowArtifact::from_parsed(parse_file(
        source,
        header,
        Arc::new(SyntaxEnvironment::empty()),
    ))
    .unwrap()
}

#[test]
fn source_call_registration_borrows_exact_parameter_declaration_owner() {
    for source in [
        "my apply f = f 1",
        "my repeated f = f (f 1)",
        "my repeated f x = f (f x)",
        "my apply f = { my step x = f x; step }",
        "my apply f x = f x",
    ] {
        let first = artifact(source);
        let foreign = artifact(source);
        let skeleton = first.skeleton().unwrap();
        let crosswalk = first.skeleton_source_crosswalk();
        let arena = RawStructuralArena::from_artifact(&first).unwrap();
        let mut owners = Vec::new();
        let mut absent = 0;
        for registration in arena
            .nodes()
            .iter()
            .filter_map(|node| node.pending_source_call_registration())
        {
            let binder = registration.source_use_input.binder();
            let expected = crosswalk
                .parameter_at_position(skeleton.binder(binder).unwrap().position())
                .unwrap();
            let Some(declaration) = registration.parameter_declaration else {
                assert!(expected.is_none());
                absent += 1;
                continue;
            };
            let (lambda, parameter) = expected.unwrap();
            assert!(std::ptr::eq(declaration.lambda, lambda));
            assert!(std::ptr::eq(declaration.parameter, parameter));
            assert_eq!(parameter, binder);
            let Form::Lambda {
                parameter: declared,
                ..
            } = lambda.form()
            else {
                panic!("parameter owner is a retained Lambda")
            };
            assert!(std::ptr::eq(parameter, declared));
            assert_eq!(
                foreign.skeleton().unwrap().binder(parameter).unwrap_err(),
                ShadowError::ForeignArtifact
            );
            assert_eq!(
                foreign
                    .skeleton_source_crosswalk()
                    .parameter_at_position(skeleton.binder(parameter).unwrap().position())
                    .unwrap_err(),
                ShadowError::ForeignArtifact
            );
            for (previous_binder, previous_lambda) in &owners {
                if *previous_binder == binder {
                    assert!(std::ptr::eq(*previous_lambda, lambda));
                }
            }
            if source.contains("my step") {
                assert_eq!(skeleton.binder(parameter).unwrap().name(), "f");
                assert_eq!(lambda.range().start, 0);
            }
            owners.push((binder, lambda));
        }
        // These existing projections retain source binders but no Lambda
        // declaration. Missing metadata does not establish semantic absence.
        if source == "my repeated f x = f (f x)" {
            assert_eq!(absent, 2);
            assert!(owners.is_empty());
            let registrations = arena
                .nodes()
                .iter()
                .filter_map(|node| node.pending_source_call_registration())
                .collect::<Vec<_>>();
            assert_eq!(
                registrations[0].source_use_input.binder(),
                registrations[1].source_use_input.binder()
            );
            assert!(
                registrations
                    .iter()
                    .all(|registration| registration.parameter_declaration.is_none())
            );
        } else if source == "my apply f x = f x" {
            assert_eq!(absent, 1);
            assert!(owners.is_empty());
        } else {
            assert_eq!(absent, 0);
            assert!(!owners.is_empty());
            if source == "my repeated f = f (f 1)" {
                assert_eq!(owners.len(), 2);
                assert_eq!(owners[0].0, owners[1].0);
                assert!(std::ptr::eq(owners[0].1, owners[1].1));
                let registrations = arena
                    .nodes()
                    .iter()
                    .filter_map(|node| node.pending_source_call_registration())
                    .collect::<Vec<_>>();
                assert_ne!(
                    registrations[0].source_use_input.occurrence(),
                    registrations[1].source_use_input.occurrence()
                );
                for registration in registrations {
                    assert_eq!(
                        registration
                            .parameter_declaration
                            .as_ref()
                            .unwrap()
                            .lambda
                            .range(),
                        &(0..23)
                    );
                    let input = &registration.source_use_input;
                    assert_eq!(
                        foreign
                            .skeleton()
                            .unwrap()
                            .use_expression(input.occurrence())
                            .unwrap_err(),
                        ShadowError::ForeignArtifact
                    );
                    let expected = skeleton
                        .pending()
                        .iter()
                        .filter(|row| row.call() == input.application().expression())
                        .collect::<Vec<_>>();
                    assert_eq!(registration.application_premises.len(), 7);
                    assert_eq!(registration.application_premises.len(), expected.len());
                    for (actual, expected) in registration.application_premises.iter().zip(expected)
                    {
                        assert!(std::ptr::eq(*actual, expected));
                    }
                }
            }
        }
    }
}

#[test]
fn raw_inventory_carries_exact_hir_source_call_use_inputs_without_discharge() {
    for source in [
        "my apply x (f: T) (g: T) = f (g x)",
        "my grouped f x = (f) x",
        "my computed f x = (f x) x",
    ] {
        let first = artifact(source);
        let foreign = artifact(source);
        let skeleton = first.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&first).unwrap();
        let expected = skeleton.source_call_use_inputs().collect::<Vec<_>>();
        let actual = arena
            .nodes()
            .iter()
            .filter_map(|node| node.call.as_ref()?.source_use_input.as_ref())
            .collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len());
        if source == "my apply x (f: T) (g: T) = f (g x)" {
            assert_eq!(actual.len(), 2);
        }
        for (raw, retained) in actual.iter().zip(&expected) {
            assert_eq!(
                raw.application().expression(),
                retained.application().expression()
            );
            assert!(std::ptr::eq(
                raw.application().position(),
                retained.application().position()
            ));
            assert!(std::ptr::eq(
                raw.application().callee(),
                retained.application().callee()
            ));
            assert!(std::ptr::eq(raw.occurrence(), retained.occurrence()));
            assert!(std::ptr::eq(raw.binder(), retained.binder()));
            assert!(std::ptr::eq(raw.argument(), retained.argument()));
            let annotations = raw.parameter_annotations().collect::<Vec<_>>();
            let retained_annotations = retained.parameter_annotations().collect::<Vec<_>>();
            assert_eq!(annotations.len(), retained_annotations.len());
            if source == "my apply x (f: T) (g: T) = f (g x)" {
                assert_eq!(annotations.len(), 1);
            }
            for (incidence, retained) in annotations.iter().zip(retained_annotations) {
                assert!(std::ptr::eq(*incidence, retained));
                assert_eq!(incidence.parameter(), raw.binder());
                assert_eq!(
                    foreign.annotation(incidence.annotation()).unwrap_err(),
                    ShadowError::ForeignArtifact
                );
            }
            assert_eq!(
                foreign.position(raw.application().position()).unwrap_err(),
                ShadowError::ForeignArtifact
            );
            assert_eq!(
                foreign
                    .skeleton()
                    .unwrap()
                    .expression(raw.argument())
                    .unwrap_err(),
                ShadowError::ForeignArtifact
            );
            assert_eq!(
                foreign
                    .skeleton()
                    .unwrap()
                    .binder(raw.binder())
                    .unwrap_err(),
                ShadowError::ForeignArtifact
            );
            assert_eq!(
                foreign
                    .skeleton()
                    .unwrap()
                    .use_expression(raw.occurrence())
                    .unwrap_err(),
                ShadowError::ForeignArtifact
            );
        }
        for node in arena.nodes() {
            let Form::Apply { callee, .. } = node.form else {
                continue;
            };
            let call = node.call.as_ref().unwrap();
            assert_eq!(
                call.source_use_input.is_some(),
                matches!(
                    skeleton.expression(callee).unwrap().form(),
                    Form::Use { .. }
                )
            );
            let pending = skeleton
                .pending()
                .iter()
                .filter(|row| row.call() == &node.source)
                .collect::<Vec<_>>();
            assert_eq!(call.application_premises.len(), pending.len());
            for (actual, expected) in call.application_premises.iter().zip(pending) {
                assert!(std::ptr::eq(*actual, expected));
            }
        }
    }
}

#[test]
fn unary_grouped_and_computed_callees_do_not_create_outer_use_registrations() {
    for (source, expected_calls) in [("my grouped f = (f) 1", 0), ("my computed f = (f 1) 1", 1)] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        let registrations = arena
            .nodes()
            .iter()
            .filter_map(|node| node.pending_source_call_registration())
            .collect::<Vec<_>>();
        assert_eq!(registrations.len(), expected_calls, "{source}");
        if source == "my computed f = (f 1) 1" {
            let [registration] = registrations.as_slice() else {
                panic!("only the inner direct-Use call is registered")
            };
            let input = &registration.source_use_input;
            assert_eq!(
                skeleton
                    .expression(input.application().expression())
                    .unwrap()
                    .range(),
                &(17..20)
            );
            assert_eq!(
                skeleton.use_expression(input.occurrence()).unwrap().range(),
                &(17..18)
            );
        }
    }
}

#[test]
fn raw_inventory_retains_exact_annotation_occurrences_and_parameter_incidence() {
    let source = "my apply (f: T) x = f x";
    let first = artifact(source);
    let second = artifact(source);
    let skeleton = first.skeleton().unwrap();
    let arena = RawStructuralArena::from_artifact(&first).unwrap();
    assert_eq!(arena.annotations().len(), first.annotations().len());
    assert_eq!(arena.annotations().len(), 1);
    for (index, (raw, occurrence)) in arena
        .annotations()
        .iter()
        .zip(first.annotations())
        .enumerate()
    {
        assert!(std::ptr::eq(raw.occurrence, occurrence));
        assert!(std::ptr::eq(
            raw.position,
            first.position(occurrence.position()).unwrap()
        ));
        assert_eq!(raw.position.range(), &(11..14));
        assert_eq!(&source[raw.position.range().clone()], ": T");
        assert_eq!(
            raw.occurrence.correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
        for previous in &arena.annotations()[..index] {
            assert_ne!(previous.occurrence.id(), occurrence.id());
        }
        let incidence = raw.parameter.unwrap();
        assert!(std::ptr::eq(
            incidence,
            &skeleton.parameter_annotations()[0]
        ));
        assert_eq!(incidence.annotation(), occurrence.id());
        assert_eq!(skeleton.binder(incidence.parameter()).unwrap().name(), "f");
        assert_eq!(
            second.annotation(occurrence.id()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            second.position(occurrence.position()).unwrap_err(),
            ShadowError::ForeignArtifact
        );
        assert_eq!(
            second
                .skeleton()
                .unwrap()
                .binder(incidence.parameter())
                .unwrap_err(),
            ShadowError::ForeignArtifact
        );
    }
    let plain = artifact("my apply f x = f x");
    assert!(
        RawStructuralArena::from_artifact(&plain)
            .unwrap()
            .annotations()
            .is_empty()
    );
}

#[test]
fn raw_inventory_preserves_order_of_multiple_annotation_incidences() {
    let source = "my apply x (f: T) (g: T) = f (g x)";
    let artifact = artifact(source);
    let skeleton = artifact.skeleton().unwrap();
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
    assert_eq!(arena.annotations().len(), 2);
    assert_eq!(skeleton.parameter_annotations().len(), 2);
    for (index, ((raw, occurrence), incidence)) in arena
        .annotations()
        .iter()
        .zip(artifact.annotations())
        .zip(skeleton.parameter_annotations())
        .enumerate()
    {
        assert!(std::ptr::eq(raw.occurrence, occurrence));
        assert!(std::ptr::eq(raw.parameter.unwrap(), incidence));
        assert!(std::ptr::eq(
            raw.position,
            artifact.position(occurrence.position()).unwrap()
        ));
        assert_eq!(source[raw.position.range().clone()].trim(), ": T");
        assert_eq!(raw.occurrence.id(), occurrence.id());
        assert_eq!(raw.parameter.unwrap().annotation(), occurrence.id());
        assert_eq!(
            skeleton.binder(incidence.parameter()).unwrap().name(),
            ["f", "g"][index]
        );
        assert_eq!(
            raw.occurrence.correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
        if index > 0 {
            assert!(
                arena.annotations()[index - 1].position.range().start < raw.position.range().start
            );
            assert_ne!(
                arena.annotations()[index - 1].occurrence.id(),
                raw.occurrence.id()
            );
        }
    }
}

#[test]
fn raw_inventory_borrows_every_form_and_exact_ordered_call_premises() {
    for source in [
        "my identity x = x",
        "my compose f g x = f (g x)",
        "my repeated f x = f (f x)",
        "my chain f x = f x x",
        "my grouped f x = (f) x",
        "my literal x = 007",
        "my call f x = f(x)",
        "my apply f = { my step x = f x; step }",
    ] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        assert_eq!(arena.body(), skeleton.body());
        assert_eq!(arena.nodes().len(), skeleton.expressions().len());
        for node in arena.nodes() {
            assert!(std::ptr::eq(
                node.form,
                skeleton.expression(&node.source).unwrap().form()
            ));
            let Form::Apply { callee, .. } = node.form else {
                assert!(node.call.is_none());
                continue;
            };
            let call = node.call.as_ref().unwrap();
            let expected = skeleton
                .pending()
                .iter()
                .filter(|p| p.call() == &node.source)
                .collect::<Vec<_>>();
            assert_eq!(call.application_premises.len(), expected.len());
            for (actual, expected) in call.application_premises.iter().zip(expected) {
                assert!(std::ptr::eq(*actual, expected));
            }
            assert_eq!(
                call.direct_use.is_some(),
                matches!(
                    skeleton.expression(callee).unwrap().form(),
                    Form::Use { .. }
                )
            );
            if let Some(direct) = call.direct_use.as_ref() {
                let Form::Use {
                    binder: retained_binder,
                    occurrence: retained_occurrence,
                } = skeleton
                    .expression(callee)
                    .expect("retained direct-use callee")
                    .form()
                else {
                    panic!("direct-use incidence targets an immediate Use")
                };
                assert_eq!(direct.application().expression(), &node.source);
                assert_eq!(direct.binder(), retained_binder);
                assert_eq!(direct.occurrence(), retained_occurrence);
            }
            if let Some(capture) = call.capture {
                assert_eq!(skeleton.capture_call(capture).unwrap(), &node.source);
                assert_eq!(
                    call.direct_use.as_ref().unwrap().occurrence(),
                    capture.occurrence()
                );
            }
        }
        if source == "my repeated f x = f (f x)" {
            let direct_calls = arena
                .nodes()
                .iter()
                .filter_map(|node| node.call.as_ref()?.direct_use.as_ref())
                .collect::<Vec<_>>();
            assert_eq!(direct_calls.len(), 2);
            assert_eq!(direct_calls[0].binder(), direct_calls[1].binder());
            assert_ne!(direct_calls[0].occurrence(), direct_calls[1].occurrence());
        }
    }
}

#[test]
fn raw_inventory_attaches_only_the_existing_capture_and_preserves_parse_identity() {
    let source = "my apply f = { my step x = f x; step }";
    let first = artifact(source);
    let second = artifact(source);
    let arena = RawStructuralArena::from_artifact(&first).unwrap();
    assert_eq!(
        arena
            .nodes()
            .iter()
            .filter(|node| node
                .call
                .as_ref()
                .is_some_and(|call| call.capture.is_some()))
            .count(),
        1
    );
    for node in arena.nodes() {
        assert!(second.skeleton().unwrap().expression(&node.source).is_err());
    }
    let unsupported = artifact("my constant x = \"unsupported\"");
    assert!(RawStructuralArena::from_artifact(&unsupported).is_none());
}

#[test]
fn frozen_oracle_nested_apply_provenance_joins_raw_shadow_occurrences() {
    // Frozen Oracle a58eefc31e22141574b6f20c6a5748151c6d79f1 recorded
    // these old source spans with a 20-byte implicit prelude. This is a source
    // provenance join only; the two inference results are not compared.
    const SOURCE: &str = "my repeated f x = f (f x)";
    const OLD_PRELUDE_BYTES: usize = 20;
    let artifact = artifact(SOURCE);
    let skeleton = artifact.skeleton().unwrap();
    let arena = RawStructuralArena::from_artifact(&artifact).unwrap();

    let mut current_apps = skeleton
        .application_source_occurrences()
        .map(|application| {
            let whole = skeleton
                .expression(application.expression())
                .unwrap()
                .range()
                .clone();
            let callee = skeleton
                .expression(application.callee())
                .unwrap()
                .range()
                .clone();
            (whole, callee, application.expression().clone())
        })
        .collect::<Vec<_>>();
    current_apps.sort_by_key(|(whole, _, _)| whole.start);
    let old_spans = [(38..45, 38..39), (41..44, 41..42)];
    assert_eq!(current_apps.len(), old_spans.len());
    for ((whole, callee, _), (old_whole, old_callee)) in current_apps.iter().zip(old_spans) {
        assert_eq!(
            whole,
            &(old_whole.start - OLD_PRELUDE_BYTES..old_whole.end - OLD_PRELUDE_BYTES)
        );
        assert_eq!(
            callee,
            &(old_callee.start - OLD_PRELUDE_BYTES..old_callee.end - OLD_PRELUDE_BYTES)
        );
    }

    // Old poly erases the grouping layer; current HIR keeps it around the
    // inner call. The retained spans still distinguish both source Apps.
    let Form::Apply { argument, .. } = skeleton.expression(&current_apps[0].2).unwrap().form()
    else {
        panic!("outer source application")
    };
    assert!(matches!(
        skeleton.expression(argument).unwrap().form(),
        Form::Group { inner }
            if matches!(skeleton.expression(inner).unwrap().form(), Form::Apply { .. })
    ));

    let mut direct_uses = arena
        .nodes()
        .iter()
        .filter_map(|node| {
            let call = node.call.as_ref()?;
            let direct = call.direct_use.as_ref()?;
            let Form::Apply { .. } = node.form else {
                return None;
            };
            Some((
                node.source.clone(),
                direct.binder().clone(),
                direct.occurrence().clone(),
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(direct_uses.len(), 2);
    direct_uses.sort_by_key(|(source, _, _)| skeleton.expression(source).unwrap().range().start);
    assert_eq!(direct_uses[0].1, direct_uses[1].1);
    assert_ne!(direct_uses[0].2, direct_uses[1].2);
    assert_eq!(skeleton.binder(&direct_uses[0].1).unwrap().name(), "f");
    for ((call, _, _), (_, _, current_call)) in direct_uses.iter().zip(current_apps.iter()) {
        assert_eq!(call, current_call);
    }
}

#[test]
fn pending_source_registration_preserves_exact_references_and_scoped_locator() {
    use yu_hir::shadow::UnresolvedSourceViewPremise::*;
    let categories = [
        CompatibleCompleteOriginalRoleIndexedProfile,
        IndependentlyTypedOriginalInvocationAndWholeRowCarrierPrefixResumptionInterpretation,
        JointlyScopedOriginalConstraints,
        SourceSlotCallbackBoundaryInputsAndCorrespondingTypedPaths,
        IndependentInitialCallerProviderWorldAdmission,
        SourceSeedRefinedRelationExistenceAndCoverage,
        OriginalSignatureApplicabilityAndContributionFormation,
    ];
    for source in [
        "my repeated f x = f (f x)",
        "my apply x (f: T) (g: T) = f (g x)",
        "my apply f = { my step x = f x; step }",
        "my apply f x = f x",
        "my grouped f x = (f) x",
        "my computed f x = (f x) x",
    ] {
        let artifact = artifact(source);
        let skeleton = artifact.skeleton().unwrap();
        let arena = RawStructuralArena::from_artifact(&artifact).unwrap();
        let scoped = skeleton.captured_call_input();
        let mut registered = Vec::new();
        let mut locator_count = 0;
        for node in arena.nodes() {
            let registration = node.pending_source_call_registration();
            assert_eq!(
                registration.is_some(),
                node.call
                    .as_ref()
                    .is_some_and(|call| call.source_use_input.is_some())
            );
            let Some(registration) = registration else {
                continue;
            };
            let raw = node.call.as_ref().unwrap();
            assert!(std::ptr::eq(registration.source, &node.source));
            assert!(std::ptr::eq(registration.application, node.form));
            assert!(std::ptr::eq(
                registration.source_use_input,
                raw.source_use_input.as_ref().unwrap()
            ));
            assert!(std::ptr::eq(
                registration.application_premises,
                raw.application_premises.as_slice()
            ));
            let pending = skeleton
                .pending()
                .iter()
                .filter(|row| row.call() == registration.source)
                .collect::<Vec<_>>();
            assert_eq!(registration.application_premises.len(), pending.len());
            for (actual, expected) in registration.application_premises.iter().zip(pending) {
                assert!(std::ptr::eq(*actual, expected));
            }
            assert_eq!(
                registration.capture.map(std::ptr::from_ref),
                raw.capture.map(std::ptr::from_ref)
            );
            let locator = registration.source_view_premise_locator();
            assert_eq!(
                locator.is_some(),
                scoped
                    .as_ref()
                    .is_some_and(|input| input.call() == registration.source)
            );
            if let Some(locator) = locator {
                locator_count += 1;
                let input = locator.input();
                let expected = scoped.as_ref().unwrap();
                assert!(std::ptr::eq(input, registration.captured_input.unwrap()));
                assert!(std::ptr::eq(input.call(), expected.call()));
                assert!(std::ptr::eq(input.callee_use(), expected.callee_use()));
                assert!(std::ptr::eq(
                    input.outer_parameter(),
                    expected.outer_parameter()
                ));
                assert!(std::ptr::eq(input.local_lambda(), expected.local_lambda()));
                assert!(std::ptr::eq(
                    input.local_binding(),
                    expected.local_binding()
                ));
                assert!(std::ptr::eq(input.returned_use(), expected.returned_use()));
                assert!(std::ptr::eq(
                    input.capture_position(),
                    expected.capture_position()
                ));
                assert_eq!(locator.unresolved_premises(), categories);
                let capture = registration.capture.unwrap();
                assert_eq!(capture.lambda(), input.local_lambda());
                assert_eq!(capture.occurrence(), input.callee_use());
            } else {
                assert!(registration.captured_input.is_none());
            }
            registered.push((
                registration.source.clone(),
                registration.source_use_input.binder().clone(),
                registration.source_use_input.occurrence().clone(),
            ));
        }
        assert_eq!(locator_count, usize::from(scoped.is_some()));
        if source == "my repeated f x = f (f x)" {
            assert_eq!(registered.len(), 2);
            assert_ne!(registered[0].0, registered[1].0);
            assert_eq!(registered[0].1, registered[1].1);
            assert_ne!(registered[0].2, registered[1].2);
        }
        if source == "my grouped f x = (f) x" {
            assert!(registered.is_empty());
        }
        if source == "my computed f x = (f x) x" {
            assert_eq!(registered.len(), 1);
        }
        if source == "my apply x (f: T) (g: T) = f (g x)" {
            assert_eq!(registered.len(), 2);
            for registration in arena
                .nodes()
                .iter()
                .filter_map(|node| node.pending_source_call_registration())
            {
                let annotations = registration
                    .source_use_input
                    .parameter_annotations()
                    .collect::<Vec<_>>();
                assert_eq!(annotations.len(), 1);
                assert!(std::ptr::eq(
                    annotations[0],
                    skeleton
                        .parameter_annotations()
                        .iter()
                        .find(|incidence| incidence.parameter()
                            == registration.source_use_input.binder())
                        .unwrap()
                ));
            }
        }
    }
}

#[test]
fn header_membership_is_distinct_from_lambda_declaration_and_foreign_identity() {
    let first = artifact("my apply f x = f x");
    let foreign = artifact("my apply f x = f x");
    let raw = RawStructuralArena::from_artifact(&first).unwrap();
    let call = raw
        .nodes()
        .iter()
        .find_map(|node| node.call.as_ref())
        .unwrap();
    let member = call.header_parameter.as_ref().unwrap();
    assert!(call.parameter_declaration.is_none());
    assert_eq!(member.parameter, &member.header.parameters()[0]);
    let foreign_skeleton = foreign.skeleton().unwrap();
    let foreign_parameter = &foreign_skeleton
        .root_declaration_header()
        .unwrap()
        .parameters()[0];
    assert!(
        raw.pending_binder_use_groups()
            .registrations_for_binder(foreign_parameter)
            .is_none()
    );
    assert!(RawStructuralArena::from_artifact(&artifact("my absent = 1")).is_none());
}
