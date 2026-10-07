#![cfg(feature = "shadow-apply-candidate")]
//! Structural correspondence on one artifact and solve only. Successful joins
//! discharge no original membership, interpretation, scope or typing premise.

#[path = "../src/shadow_candidate_source_crosswalk.rs"]
mod crosswalk;

use crosswalk::{CandidateSourceCrosswalk, CandidateSourceModuleUses};
use std::sync::Arc;
use yu_core::shadow_call_formation::{
    Address, UnresolvedPremise, generate_captured_declaration, generate_captured_singleton,
    generate_resolved_source_calls, generate_source_calls,
};
use yu_hir::shadow::{
    Form, ShadowArtifact, lower_module_with_shadow_applications,
    lower_module_with_shadow_local_binding,
};
use yu_hir::{FileId, FileKey, HirItem, ModuleIdentity, ResolvedExpr, SemanticImports};
use yu_solver::shadow_apply::{CandidateValueObservation, UNRESOLVED};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn captured_call_formation_and_candidate_borrow_the_same_source_records() {
    check_captured_call_correspondence("my apply f = { my step x = f x; step }", false);
}

#[test]
fn declaration_call_formation_and_candidate_borrow_the_same_source_records() {
    check_captured_call_correspondence(
        "my apply f = { my step x = f x; step }; my alias = apply",
        true,
    );
}

#[test]
fn captured_declaration_call_formation_ignores_sibling_annotations() {
    let source: Arc<SourceText> =
        Arc::from("my apply f = { my step x = f x; step }; my alias = 1 as int");
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = ShadowArtifact::from_parsed(parsed).unwrap();
    assert!(!artifact.annotations().is_empty());
    let declaration = artifact.raw_declaration_positions().next().unwrap();
    assert!(
        artifact
            .declaration_skeleton(&declaration)
            .unwrap()
            .captured_call_input()
            .is_some()
    );
    // The retained annotation belongs to the sibling declaration, so it does
    // not suppress this exact captured declaration's structural projection.
    assert!(generate_captured_declaration(&artifact, &declaration).is_some());
}

#[test]
fn ordinary_call_stub_joins_the_candidate_and_export_without_discharging_premises() {
    let source: Arc<SourceText> = Arc::from("my apply f = f 1");
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new("crosswalk", "ordinary-call.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("outer binding")
    };
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    let joined =
        CandidateSourceCrosswalk::new(&artifact, &hir, &candidate, binding.definition_root())
            .unwrap();
    assert_resolved_hir_calls_match_candidate(&hir, binding.definition_root(), &candidate);
    let declaration = artifact
        .definition_source_position(&hir, binding.definition_root())
        .unwrap();
    let stubs = generate_source_calls(&artifact, &declaration).unwrap();
    let [stub] = stubs.as_slice() else {
        panic!("one direct-Use Apply stub")
    };
    let mut calls = joined.calls();
    let call = calls.next().expect("candidate/source call correspondence");
    assert!(calls.next().is_none());
    assert!(call.matches_source_call_stub(stub));
    assert_eq!(stub.call(), call.source_input().application().expression());
    assert_eq!(stub.callee_use(), call.source_input().occurrence());
    assert_eq!(stub.argument(), call.source_input().argument());
    assert_eq!(call.candidate_call().unresolved, UNRESOLVED);
    assert_eq!(joined.export().unresolved, UNRESOLVED);
    assert!(
        joined.export().endpoints().alpha_eq(
            candidate
                .export(binding.definition_root())
                .unwrap()
                .endpoints()
        )
    );
    assert_eq!(
        stub.unresolved_premises(),
        &[
            UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
            UnresolvedPremise::InitialSourceDescriptorRelation,
            UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
            UnresolvedPremise::CompleteInvocationInterpretation,
        ],
        "source identity does not discharge source-base semantics"
    );
}

#[test]
fn source_stub_matcher_rejects_other_calls_and_foreign_artifacts() {
    let text = "my apply f = f (f 1)";
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let source_artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let hir = Arc::new(
        lower_module_with_shadow_applications(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "crosswalk",
                "nested-call-matcher.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("source function")
    };
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    assert_resolved_hir_calls_match_candidate(&hir, binding.definition_root(), &candidate);
    let joined = CandidateSourceCrosswalk::new(
        &source_artifact,
        &hir,
        &candidate,
        binding.definition_root(),
    )
    .unwrap();
    let declaration = source_artifact
        .definition_source_position(&hir, binding.definition_root())
        .unwrap();
    let stubs = generate_source_calls(&source_artifact, &declaration).unwrap();
    let calls = joined.calls().collect::<Vec<_>>();
    assert_eq!(stubs.len(), 2);
    assert_eq!(calls.len(), 2);
    assert_eq!(joined.export().unresolved, UNRESOLVED);
    assert!(
        joined.export().endpoints().alpha_eq(
            candidate
                .export(binding.definition_root())
                .unwrap()
                .endpoints()
        )
    );
    for call in &calls {
        let own = stubs
            .iter()
            .find(|stub| stub.call() == call.source_input().application().expression())
            .unwrap();
        assert!(call.matches_source_call_stub(own));
        let other = stubs.iter().find(|stub| stub.call() != own.call()).unwrap();
        assert!(!call.matches_source_call_stub(other));
    }

    let foreign_text: Arc<SourceText> = Arc::from(text);
    let foreign_parsed = parse_file(
        foreign_text.clone(),
        Arc::new(scan_header(foreign_text)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let foreign = ShadowArtifact::from_parsed(foreign_parsed).unwrap();
    let foreign_declaration = foreign.raw_declaration_positions().next().unwrap();
    let foreign_stubs = generate_source_calls(&foreign, &foreign_declaration).unwrap();
    assert_eq!(foreign_stubs.len(), 2);
    for call in calls {
        assert!(
            foreign_stubs
                .iter()
                .all(|stub| !call.matches_source_call_stub(stub))
        );
    }
}

fn assert_resolved_hir_calls_match_candidate(
    hir: &yu_hir::HirModule,
    root: &yu_hir::DefinitionRootId,
    candidate: &CandidateValueObservation,
) {
    let source_calls = hir.shadow_resolved_call_inventory(root).unwrap();
    assert_eq!(source_calls.len(), candidate.calls().len());
    let pending_calls = generate_resolved_source_calls(hir, root).unwrap();
    assert_eq!(pending_calls.len(), source_calls.len());
    for call in candidate.calls() {
        let mut matches = source_calls
            .iter()
            .filter(|source| source.occurrence == &call.occurrence);
        let source = matches.next().expect("same resolved HIR Apply occurrence");
        assert!(matches.next().is_none(), "one inventory row per Apply");
        assert_eq!(source.callee, &call.callee);
        assert_eq!(source.argument, &call.argument);
        assert!(!source.errors.is_empty());
        assert!(
            source
                .errors
                .iter()
                .all(|error| hir.errors().iter().any(|entry| entry.id() == *error))
        );
        assert_eq!(call.unresolved, UNRESOLVED);

        let mut matching_pending = pending_calls
            .iter()
            .filter(|pending| pending.call().occurrence == source.occurrence);
        let pending = matching_pending
            .next()
            .expect("same HIR call in Core premise carrier");
        assert!(
            matching_pending.next().is_none(),
            "one Core carrier per HIR call"
        );
        assert!(std::ptr::eq(pending.root(), root));
        assert!(std::ptr::eq(pending.call().occurrence, source.occurrence));
        assert!(std::ptr::eq(pending.call().callee, source.callee));
        assert!(std::ptr::eq(pending.call().argument, source.argument));
        assert!(std::ptr::eq(pending.call().errors, source.errors));
        assert_eq!(pending.call().source_form, source.source_form);
        assert_eq!(
            pending.unresolved_premises(),
            &[
                UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
                UnresolvedPremise::InitialSourceDescriptorRelation,
                UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
                UnresolvedPremise::CompleteInvocationInterpretation,
            ]
        );
    }
}

fn check_captured_call_correspondence(source: &str, multiple_bindings: bool) {
    let source: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
    let hir = Arc::new(
        lower_module_with_shadow_local_binding(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "crosswalk",
                "call-formation.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
            artifact.clone(),
        )
        .unwrap(),
    );
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("outer binding")
    };
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    let joined =
        CandidateSourceCrosswalk::new(&artifact, &hir, &candidate, binding.definition_root())
            .unwrap();
    assert_resolved_hir_calls_match_candidate(&hir, binding.definition_root(), &candidate);
    let declaration = artifact
        .definition_source_position(&hir, binding.definition_root())
        .unwrap();
    let [record] = generate_captured_declaration(&artifact, &declaration)
        .expect("captured declaration topology");
    if multiple_bindings {
        assert!(generate_captured_singleton(&artifact).is_none());
        let HirItem::Binding(alias) = &hir.items()[1] else {
            panic!("second binding")
        };
        let alias_position = artifact
            .definition_source_position(&hir, alias.definition_root())
            .unwrap();
        assert!(generate_captured_declaration(&artifact, &alias_position).is_none());
    } else {
        let [singleton] = generate_captured_singleton(&artifact).unwrap();
        assert!(std::ptr::eq(singleton.demand().call, record.demand().call));
        assert!(std::ptr::eq(
            singleton.source_base_stub().call(),
            record.source_base_stub().call(),
        ));
        assert!(std::ptr::eq(
            singleton.source_base_stub().callee_use(),
            record.source_base_stub().callee_use(),
        ));
        assert!(std::ptr::eq(
            singleton.source_base_stub().argument_use(),
            record.source_base_stub().argument_use(),
        ));
        assert_eq!(
            singleton.source_base_stub().unresolved_premises(),
            record.source_base_stub().unresolved_premises(),
        );
    }
    assert!(generate_captured_declaration(&artifact, &artifact.root()).is_none());
    let foreign = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    assert!(generate_captured_declaration(&foreign, &declaration).is_none());
    let captured = joined.captured_input().unwrap();
    let mut calls = joined.calls();
    let row = calls.next().expect("one retained call");
    assert!(calls.next().is_none());
    let source_call_stubs = generate_source_calls(&artifact, &declaration).unwrap();
    let [source_call_stub] = source_call_stubs.as_slice() else {
        panic!("one direct-Use source-call stub")
    };
    assert!(row.matches_source_call_stub(source_call_stub));
    let [candidate_call] = candidate.calls() else {
        panic!("one candidate call; returning step adds no invocation")
    };
    assert!(std::ptr::eq(row.candidate_call(), candidate_call));

    let skeleton = artifact.declaration_skeleton(&declaration).unwrap();
    let demand = record.demand();
    let input = row.source_input();
    assert_eq!(demand.call, input.application().expression());
    assert!(std::ptr::eq(
        skeleton.expression(demand.call).unwrap(),
        skeleton
            .expression(input.application().expression())
            .unwrap(),
    ));
    assert!(std::ptr::eq(demand.call, captured.call()));
    assert!(std::ptr::eq(
        demand.registration.declaration,
        input.binder(),
    ));
    assert_eq!(demand.registration.declaration, captured.outer_parameter());
    assert!(std::ptr::eq(
        demand.registration.outer_scope,
        skeleton.body()
    ));
    assert!(std::ptr::eq(demand.local_scope, captured.local_lambda()));
    let Form::Lambda { parameter, .. } = skeleton.expression(demand.local_scope).unwrap().form()
    else {
        panic!("retained local lambda")
    };
    assert!(std::ptr::eq(demand.argument_declaration, parameter));
    let Address::CalleeUse(callee_use) = record.callee_use() else {
        panic!("callee use address")
    };
    assert!(std::ptr::eq(callee_use, input.occurrence()));
    assert!(std::ptr::eq(callee_use, captured.callee_use()));
    let Form::Use { binder, occurrence } = skeleton.expression(input.argument()).unwrap().form()
    else {
        panic!("retained argument use")
    };
    assert!(std::ptr::eq(record.argument_use(), occurrence));
    let stub = record.source_base_stub();
    assert!(std::ptr::eq(stub.call(), demand.call));
    assert!(std::ptr::eq(stub.call(), captured.call()));
    assert!(std::ptr::eq(stub.callee_use(), input.occurrence()));
    assert!(std::ptr::eq(stub.callee_use(), callee_use));
    assert!(std::ptr::eq(stub.argument_use(), occurrence));
    assert!(std::ptr::eq(stub.argument_use(), record.argument_use()));
    assert_eq!(
        stub.unresolved_premises(),
        &[
            UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
            UnresolvedPremise::InitialSourceDescriptorRelation,
            UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
            UnresolvedPremise::CompleteInvocationInterpretation,
        ]
    );
    assert_eq!(binder, demand.argument_declaration);
    assert!(std::ptr::eq(record.returned_use(), captured.returned_use()));

    let local = hir
        .shadow_local_binding(binding.definition_root())
        .unwrap()
        .unwrap();
    let ResolvedExpr::Lambda {
        parameter: local_parameter,
        body,
        ..
    } = &local.initializer
    else {
        panic!("retained HIR local lambda")
    };
    let ResolvedExpr::Apply {
        occurrence,
        callee,
        argument,
        ..
    } = body.as_ref()
    else {
        panic!("retained HIR call")
    };
    assert_eq!(&candidate_call.occurrence, occurrence);
    assert_eq!(&candidate_call.callee, callee.occurrence());
    assert_eq!(&candidate_call.argument, argument.occurrence());
    for (hir_occurrence, source_position) in [
        (occurrence, input.application().position()),
        (
            callee.occurrence(),
            skeleton.use_position(callee_use).unwrap(),
        ),
        (
            argument.occurrence(),
            skeleton.use_position(record.argument_use()).unwrap(),
        ),
        (
            &local.continuation.occurrence,
            skeleton.use_position(record.returned_use()).unwrap(),
        ),
        (
            local.initializer.occurrence(),
            skeleton.expression(demand.local_scope).unwrap().position(),
        ),
    ] {
        assert_eq!(
            artifact
                .occurrence_source_position(&hir, hir_occurrence)
                .unwrap(),
            *source_position,
        );
    }
    let export = candidate.export(binding.definition_root()).unwrap();
    assert!(std::ptr::eq(
        joined.export().scheme().owner(),
        export.scheme().owner()
    ));
    assert!(joined.export().endpoints().alpha_eq(export.endpoints()));
    if multiple_bindings {
        let HirItem::Binding(alias) = &hir.items()[1] else {
            panic!("second binding")
        };
        let uses = CandidateSourceModuleUses::new(&artifact, &hir, &candidate).unwrap();
        let [use_] = uses.uses() else {
            panic!("one retained top-level use")
        };
        let observation = use_.observation();
        assert_eq!(use_.target_position(), &declaration);
        assert_eq!(
            *use_.receiving_position(),
            artifact
                .definition_source_position(&hir, alias.definition_root())
                .unwrap(),
        );
        assert_eq!(observation.occurrence(), alias.value().occurrence());
        assert_eq!(
            *use_.position(),
            artifact
                .occurrence_source_position(&hir, observation.occurrence())
                .unwrap(),
        );
        assert!(observation.target_scheme().same_identity(export.scheme()));
        let receiving = observation.receiving_export().unwrap();
        let alias_export = candidate.export(alias.definition_root()).unwrap();
        assert!(receiving.scheme().same_identity(alias_export.scheme()));
        assert!(
            observation
                .receiving_scheme()
                .same_identity(receiving.scheme())
        );
        assert!(receiving.endpoints().alpha_eq(alias_export.endpoints()));
        let yu_solver::shadow_f5::FreshCaptureState::Captured(route) =
            observation.fresh_instantiation()
        else {
            panic!("actual current Q/R fresh route")
        };
        assert!(route.scheme().same_identity(export.scheme()));
        let expected: std::collections::BTreeSet<_> = export
            .scheme()
            .quantifiers()
            .map(|binder| (false, binder.ordinal()))
            .chain(
                export
                    .scheme()
                    .recursive_binders()
                    .map(|binder| (true, binder.ordinal())),
            )
            .collect();
        let inventory: Vec<_> = route
            .bindings()
            .map(|(binder, _)| match binder {
                yu_solver::shadow_f5::FreshBinderRef::Quantified(binder) => {
                    assert!(binder.scheme().same_identity(export.scheme()));
                    (false, binder.ordinal())
                }
                yu_solver::shadow_f5::FreshBinderRef::Recursive(binder) => {
                    assert!(binder.scheme().same_identity(export.scheme()));
                    (true, binder.ordinal())
                }
            })
            .collect();
        assert!(!inventory.is_empty());
        assert_eq!(inventory.len(), expected.len());
        assert_eq!(
            inventory
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>(),
            expected
        );
        assert_eq!(observation.unresolved(), UNRESOLVED);
        assert_eq!(receiving.unresolved, UNRESOLVED);
        // Joining the same Call to the alias's Q/R route and export leaves
        // every source-base stub premise pending.
        assert!(std::ptr::eq(stub, record.source_base_stub()));
        assert_eq!(stub.unresolved_premises().len(), 4);
    }

    // The local source formal reaches an actual current-generalizer origin;
    // ordinal or syntax shape alone supplies no row or binder identity.
    assert_eq!(
        artifact
            .parameter_source_position(&hir, local_parameter)
            .unwrap(),
        *skeleton.binder(parameter).unwrap().position(),
    );
    let yu_solver::shadow_f5::ParameterRowState::Captured(startup) =
        candidate.parameter_row(local_parameter).unwrap()
    else {
        panic!("retained local parameter startup row")
    };
    let yu_solver::shadow_f5::GeneralizationOriginState::Captured(origins) =
        export.scheme().current_generalization_origins()
    else {
        panic!("retained current generalization origins")
    };
    assert!(origins.scheme().same_identity(export.scheme()));
    let mut matching = origins
        .bindings()
        .filter(|(_, origin)| startup.same_identity(*origin));
    let (binder, origin) = matching.next().expect("local startup row origin");
    assert!(matching.next().is_none());
    assert!(startup.same_identity(origin));
    match binder {
        yu_solver::shadow_f5::FreshBinderRef::Quantified(binder) => {
            assert!(binder.scheme().same_identity(export.scheme()));
            assert!(
                export
                    .scheme()
                    .quantifiers()
                    .any(|q| q.same_identity(binder))
            );
        }
        yu_solver::shadow_f5::FreshBinderRef::Recursive(binder) => {
            assert!(binder.scheme().same_identity(export.scheme()));
            assert!(
                export
                    .scheme()
                    .recursive_binders()
                    .any(|r| r.same_identity(binder))
            );
        }
    }

    // A root here is a symbolic term, never an original Inv membership witness.
    let effect = record.call_effect();
    assert!(std::ptr::eq(effect.record(), &record));
    assert!(std::ptr::eq(effect.root().demand(), demand));
    assert_eq!(
        record.unresolved_premises(),
        &[
            UnresolvedPremise::OriginalBX,
            UnresolvedPremise::OriginalXi,
            UnresolvedPremise::OriginalTypes,
            UnresolvedPremise::OriginalScopes,
            UnresolvedPremise::EmittedGenCall0Membership,
            UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
            UnresolvedPremise::InitialSourceDescriptorRelation,
            UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
            UnresolvedPremise::CompleteInvocationInterpretation,
            UnresolvedPremise::LegalOldWholeTupleSubstitution,
        ]
    );
    assert_eq!(row.candidate_call().unresolved, UNRESOLVED);
    assert_eq!(joined.export().unresolved, UNRESOLVED);
    assert!(row.ordinary_incoming_rows().is_none());
    let pending = row.pending().collect::<Vec<_>>();
    let original = skeleton
        .pending()
        .iter()
        .filter(|premise| premise.call() == demand.call)
        .collect::<Vec<_>>();
    assert!(!original.is_empty());
    assert_eq!(pending.len(), original.len());
    for (retained, original) in pending.into_iter().zip(original) {
        assert!(std::ptr::eq(retained, original));
    }
}

#[test]
fn ordinary_call_use_spine_keeps_each_receiving_root_and_pending_premises() {
    let text = "my id x = x; my first = id 1; my second = id 2; pub exported = first";
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
    let identity =
        ModuleIdentity::source_root(FileId::new(FileKey::new("crosswalk", "ordinary-spine.yu")));
    let hir = Arc::new(
        lower_module_with_shadow_applications(identity.clone(), &parsed, SemanticImports::empty())
            .unwrap(),
    );
    let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
    let roots: Vec<_> = hir
        .items()
        .iter()
        .map(|item| {
            let HirItem::Binding(binding) = item else {
                panic!("binding")
            };
            binding.definition_root()
        })
        .collect();
    let first = generate_resolved_source_calls(&hir, roots[1]).unwrap();
    let second = generate_resolved_source_calls(&hir, roots[2]).unwrap();
    let [first_pending] = first.as_slice() else {
        panic!("one first Call")
    };
    let [second_pending] = second.as_slice() else {
        panic!("one second Call")
    };
    let first_join = crosswalk::CandidateSourceCallUseSpine::new(
        &artifact,
        &hir,
        &candidate,
        roots[1],
        first_pending,
    )
    .unwrap();
    let second_join = crosswalk::CandidateSourceCallUseSpine::new(
        &artifact,
        &hir,
        &candidate,
        roots[2],
        second_pending,
    )
    .unwrap();
    let first_use = first_join.module_use().observation();
    let second_use = second_join.module_use().observation();
    assert!(
        first_use
            .target_scheme()
            .same_identity(second_use.target_scheme())
    );
    assert!(
        !first_use
            .receiving_scheme()
            .same_identity(second_use.receiving_scheme())
    );
    assert!(!first_use.same_identity(second_use));
    for (join, pending, root) in [
        (&first_join, first_pending, roots[1]),
        (&second_join, second_pending, roots[2]),
    ] {
        assert!(std::ptr::eq(join.pending(), pending));
        assert_eq!(&join.candidate_call().occurrence, pending.call().occurrence);
        assert_eq!(&join.candidate_call().callee, pending.call().callee);
        assert_eq!(&join.candidate_call().argument, pending.call().argument);
        let use_ = join.module_use().observation();
        assert_eq!(use_.occurrence(), pending.call().callee);
        assert_eq!(use_.receiving_scheme().owner(), root);
        assert!(
            use_.receiving_scheme()
                .same_identity(join.export().scheme())
        );
        assert!(
            use_.receiving_export()
                .unwrap()
                .scheme()
                .same_identity(join.export().scheme())
        );
        assert_eq!(
            *join.module_use().position(),
            artifact
                .occurrence_source_position(&hir, pending.call().callee)
                .unwrap()
        );
        assert_eq!(
            *join.module_use().receiving_position(),
            artifact.definition_source_position(&hir, root).unwrap()
        );
        let yu_solver::shadow_f5::FreshCaptureState::Captured(route) = join.fresh_instantiation()
        else {
            panic!("actual generic target capture")
        };
        assert!(route.scheme().same_identity(use_.target_scheme()));
        assert!(route.bindings().next().is_some());
        assert_eq!(
            pending.unresolved_premises(),
            &[
                UnresolvedPremise::CompleteEmittedOriginalCallClauseAndJointWitness,
                UnresolvedPremise::InitialSourceDescriptorRelation,
                UnresolvedPremise::FiniteSourceBaseEmissionConformanceCertificate,
                UnresolvedPremise::CompleteInvocationInterpretation,
            ]
        );
        assert_eq!(join.candidate_call().unresolved, UNRESOLVED);
        assert_eq!(use_.unresolved(), UNRESOLVED);
        assert_eq!(join.export().unresolved, UNRESOLVED);
    }
    assert!(
        crosswalk::CandidateSourceCallUseSpine::new(
            &artifact,
            &hir,
            &candidate,
            roots[2],
            first_pending
        )
        .is_err()
    );
    assert!(
        crosswalk::CandidateSourceCallUseSpine::new(
            &artifact,
            &hir,
            &candidate,
            roots[1],
            second_pending
        )
        .is_err()
    );
    // Identical source reparsed into a foreign artifact/HIR cannot substitute
    // its pending inventory or candidate observation for this exact join.
    let foreign_source: Arc<SourceText> = Arc::from(text);
    let foreign_parsed = parse_file(
        foreign_source.clone(),
        Arc::new(scan_header(foreign_source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let foreign_artifact = ShadowArtifact::from_parsed(foreign_parsed.clone()).unwrap();
    let foreign_hir = Arc::new(
        lower_module_with_shadow_applications(identity, &foreign_parsed, SemanticImports::empty())
            .unwrap(),
    );
    let foreign_candidate = CandidateValueObservation::solve(foreign_hir.clone()).unwrap();
    assert!(
        crosswalk::CandidateSourceCallUseSpine::new(
            &foreign_artifact,
            &hir,
            &candidate,
            roots[1],
            first_pending
        )
        .is_err()
    );
    assert!(
        crosswalk::CandidateSourceCallUseSpine::new(
            &artifact,
            &hir,
            &foreign_candidate,
            roots[1],
            first_pending
        )
        .is_err()
    );
    assert!(
        crosswalk::CandidateSourceCallUseSpine::new(
            &artifact,
            &foreign_hir,
            &candidate,
            roots[1],
            first_pending
        )
        .is_err()
    );
}
