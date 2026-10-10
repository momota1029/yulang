use super::*;
use yu_hir::shadow::lower_module_with_local_source;

fn session() -> InferenceSession {
    session_with_source("act E\nmy seed = 1")
}
fn session_with_source(text: &str) -> InferenceSession {
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let parsed = yu_syntax::parse_file(
        source.clone(),
        Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()),
    );
    let hir = Arc::new(
        lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "context",
                "source.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .unwrap(),
    );
    let mut session = InferenceSession::try_new(
        ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap(),
    )
    .unwrap();
    session.start_candidate_graph().unwrap();
    session
}
fn cause(session: &InferenceSession, slot: u8) -> (ConstraintOccurrenceId, CauseId) {
    let binding = session
        .batch
        .hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) => Some(binding),
            _ => None,
        })
        .expect("binding");
    let occurrence = ConstraintOccurrenceId::new(binding.value().occurrence().clone(), slot);
    let cause = CauseId::for_occurrence(occurrence.clone());
    (occurrence, cause)
}
fn state(session: &InferenceSession) -> &State {
    &session
        .candidate_graph
        .as_ref()
        .unwrap()
        .intrusion
        .effect_algebra
        .context
}
fn value(row: u32) -> ExtrusionEndpoint {
    ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(row))
}
fn task(lower: u32, upper: u32) -> LiveConstraintTask {
    LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::ValueRow(lower),
        upper: ValueEndpointKey::ValueRow(upper),
    })
}

#[test]
fn distinct_source_origins_survive_identity_memo_and_self_omission() {
    let mut session = session();
    let row = session.fresh_value_at_level(0).unwrap();
    let before = state(&session).origins.len();
    for slot in [0, 1] {
        let (occurrence, cause) = cause(&session, slot);
        session
            .constrain_live(task(row, row), &occurrence, &cause)
            .unwrap();
        let origin = state(&session).origins.last().unwrap();
        assert_eq!(origin.occurrence, occurrence);
        assert_eq!(
            state(&session).relations[origin.relation.0 as usize]
                .key
                .pair,
            task_pair(task(row, row))
        );
    }
    let context = state(&session);
    assert_eq!(context.origins.len(), before + 2);
    assert_eq!(
        context.origins[before].relation,
        context.origins[before + 1].relation
    );
    assert!(context.contains(task_pair(task(row, row))));
}

#[test]
fn opposite_replay_keeps_lower_upper_order_and_shared_bound_identity() {
    let mut session = session();
    let owner = session.fresh_value_at_level(0).unwrap();
    let lower = session.fresh_value_at_level(0).unwrap();
    let upper = session.fresh_value_at_level(0).unwrap();
    let (occurrence, cause) = cause(&session, 0);
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    session
        .candidate_restore_bound(
            value(owner),
            Polarity::Negative,
            value(upper),
            &occurrence,
            &cause,
        )
        .unwrap();
    session
        .candidate_restore_bound(
            value(owner),
            Polarity::Positive,
            value(lower),
            &occurrence,
            &cause,
        )
        .unwrap();
    let context = state(&session);
    let lower_relation = context.bound(lower_input).unwrap();
    let upper_relation = context.bound(upper_input).unwrap();
    assert!(context.dependencies.iter().any(|dependency| matches!(dependency,
        Dependency::Replay { lower, upper, lower_input: l, upper_input: u, .. }
        if *lower == lower_relation && *upper == upper_relation && *l == lower_input && *u == upper_input)));
    assert!(
        context
            .children(bound_pair(lower_input))
            .any(|pair| pair == task_pair(task(lower, upper)))
    );
    assert!(
        context
            .children(bound_pair(upper_input))
            .any(|pair| pair == task_pair(task(lower, upper)))
    );
}

#[test]
fn captured_relation_inputs_survive_independent_fresh_uses() {
    let mut session = session();
    let row = session.fresh_value_at_level(2).unwrap();
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let (occurrence, cause) = cause(&session, 0);
    session
        .candidate_restore_bound(value(row), Polarity::Positive, lower, &occurrence, &cause)
        .unwrap();
    let source = state(&session)
        .bound(BoundKey(value(row), Polarity::Positive, lower))
        .unwrap();
    let graph = session.capture_candidate_graph(row, 0).unwrap();
    assert!(
        graph
            .bounds
            .iter()
            .any(|bound| bound.relation == Some(source))
    );
    let (_, first) = session
        .freshen_candidate_graph(&graph, 3, &occurrence, &cause)
        .unwrap();
    let (_, second) = session
        .freshen_candidate_graph(&graph, 3, &occurrence, &cause)
        .unwrap();
    assert_ne!(first, second);
    let context = state(&session);
    let transported: Vec<_> = context
        .dependencies
        .iter()
        .filter_map(|dependency| match dependency {
            Dependency::Transport {
                child,
                parent,
                use_origin,
            } if *parent == source && *use_origin != 0 => Some((*child, *use_origin)),
            _ => None,
        })
        .collect();
    assert_eq!(transported.len(), 2);
    assert_ne!(transported[0].0, transported[1].0);
    assert_ne!(transported[0].1, transported[1].1);
}

#[test]
fn real_extrusion_and_qualifying_intrusion_transport_identity_dependencies() {
    for effect in [false, true] {
        let mut session = session();
        let (occurrence, cause) = cause(&session, 0);
        let parent = if effect {
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(
                session.fresh_effect_at_level(2).unwrap(),
            ))
        } else {
            value(session.fresh_value_at_level(2).unwrap())
        };
        let upper = if effect {
            let binding = session
                .batch
                .hir
                .items()
                .iter()
                .find_map(|item| match item {
                    HirItem::Binding(binding) => Some(binding),
                    _ => None,
                })
                .expect("binding");
            let owner = binding.definition_root().clone();
            let declaration = session.batch.hir.source_effect_declarations()[0].id.clone();
            let tail = session.fresh_effect_at_level(2).unwrap();
            let view = session
                .candidate_effect_view(
                    owner,
                    declaration.declaration.clone(),
                    vec![declaration],
                    Some(tail),
                )
                .unwrap();
            ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view))
        } else {
            ExtrusionEndpoint::Value(ValueEndpointKey::IntNegative)
        };
        session
            .candidate_restore_bound(parent, Polarity::Negative, upper, &occurrence, &cause)
            .unwrap();
        let source = state(&session)
            .bound(BoundKey(parent, Polarity::Negative, upper))
            .unwrap();
        let copy = session
            .candidate_extrude(parent, Polarity::Negative, 0)
            .unwrap();
        assert_ne!(copy, parent);
        if let (
            ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(original_view)),
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copy_row)),
        ) = (upper, copy)
        {
            let copied_view = session.effect_bounds[copy_row as usize]
                .exact_non_variable_uppers
                .iter()
                .find_map(|endpoint| match endpoint {
                    EffectEndpointKey::Allowance(view) => Some(*view),
                    _ => None,
                })
                .expect("negative Allowance bound transfers through negative extrusion");
            assert_ne!(copied_view, original_view);
            assert!(
                session
                    .candidate_graph
                    .as_ref()
                    .unwrap()
                    .intrusion
                    .effect_algebra
                    .views[copied_view as usize]
                    .tail
                    .is_some()
            );
        }
        assert!(
            state(&session)
                .dependencies
                .iter()
                .any(|dependency| matches!(dependency,
            Dependency::Transport { parent, .. } if *parent == source))
        );
        session
            .candidate_restore_bound(copy, Polarity::Positive, parent, &occurrence, &cause)
            .unwrap();
        let self_task = match copy {
            ExtrusionEndpoint::Value(row) => LiveConstraintTask::Value(CanonicalValuePairKey {
                lower: row,
                upper: row,
            }),
            ExtrusionEndpoint::Effect(row) => LiveConstraintTask::Effect(row, row),
        };
        session
            .constrain_live(self_task, &occurrence, &cause)
            .unwrap();
        assert_eq!(
            session.canonical_extrusion(copy),
            session.canonical_extrusion(parent)
        );
        assert!(state(&session).contains(session.candidate_context_pair(task_pair(self_task))));
        assert!(
            state(&session)
                .bound(BoundKey(
                    session.canonical_extrusion(parent),
                    Polarity::Negative,
                    upper
                ))
                .is_some()
        );
    }
}

#[test]
fn route_rollback_restores_relation_origin_dependency_graph_then_retries() {
    let mut session = session();
    let row = session.fresh_value_at_level(2).unwrap();
    let (occurrence, cause) = cause(&session, 0);
    let before = state(&session).checkpoint();
    let run = |session: &mut InferenceSession| {
        session.constrain_live(task(row, row), &occurrence, &cause)?;
        let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
        session.candidate_restore_bound(
            value(row),
            Polarity::Positive,
            lower,
            &occurrence,
            &cause,
        )?;
        let graph = session.capture_candidate_graph(row, 0)?;
        session.freshen_candidate_graph(&graph, 3, &occurrence, &cause)?;
        Ok::<_, SolveAvailabilityError>(())
    };
    let result = session.with_route_transaction(|session| {
        run(session)?;
        Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
    });
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    let context = state(&session);
    assert_eq!(context.relations.len(), before.relations);
    assert_eq!(context.dependencies.len(), before.dependencies);
    assert_eq!(context.origins.len(), before.origins);
    assert_eq!(context.bound_keys.len(), before.bounds);
    assert_eq!(context.edge_log.len(), before.edges);
    assert_eq!(context.uses, before.uses);
    assert_eq!(context.keys.len(), before.relations);
    assert_eq!(context.dependency_keys.len(), before.dependencies);
    assert_eq!(context.edge_keys.len(), before.edges);
    session.with_route_transaction(run).unwrap();
    assert!(state(&session).origins.len() > before.origins);
    assert!(state(&session).dependencies.len() > before.dependencies);
    assert!(state(&session).bytes().unwrap() > 0);
}

#[test]
fn same_endpoints_keep_distinct_context_handles_and_intern_each_key_once() {
    let mut context = State::default();
    let pair = task_pair(task(0, 0));
    let identity = context.relation(pair, IDENTITY).unwrap();
    let operation = context
        .context(ContextExpr::Swap { input: IDENTITY })
        .unwrap();
    let distinct = context.relation(pair, operation).unwrap();
    assert_ne!(identity, distinct);
    assert_eq!(context.relation(pair, IDENTITY).unwrap(), identity);
    assert_eq!(context.relation(pair, operation).unwrap(), distinct);
    assert_eq!(context.relations.len(), 2);
    assert_eq!(context.keys.len(), 2);
}

#[test]
fn transport_provenance_is_retained_without_a_conflict_replay_edge() {
    let mut context = State::default();
    let template_pair = task_pair(task(0, 1));
    let fresh_pair = task_pair(task(2, 3));
    let template = context.relation(template_pair, IDENTITY).unwrap();
    let fresh = context.relation(fresh_pair, IDENTITY).unwrap();
    let checkpoint = context.checkpoint();
    let transport = Dependency::Transport {
        child: fresh,
        parent: template,
        use_origin: 1,
    };
    context.dependency(transport).unwrap();
    context.dependency(transport).unwrap();
    assert_eq!(context.dependencies, vec![transport]);
    assert!(context.dependency_keys.contains(&transport));
    assert_eq!(context.children(template_pair).count(), 0);
    assert_eq!(context.children(fresh_pair).count(), 0);
    assert!(context.edge_keys.is_empty());
    context.rollback(checkpoint);
    assert!(context.dependencies.is_empty());
    assert!(context.dependency_keys.is_empty());
    context.dependency(transport).unwrap();
    assert_eq!(context.dependencies, vec![transport]);
    assert_eq!(context.children(template_pair).count(), 0);
}

#[test]
fn contextual_adjacency_retained_bytes_match_owned_capacity_across_rollback() {
    let mut context = State::default();
    let parent_pair = task_pair(task(0, 0));
    let child_pair = task_pair(task(1, 1));
    let parent = context.relation(parent_pair, IDENTITY).unwrap();
    let first_child = context.relation(child_pair, IDENTITY).unwrap();
    context
        .dependency(Dependency::Derived {
            child: first_child,
            parent,
        })
        .unwrap();
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    let before_bytes = context.bytes().unwrap();
    let checkpoint = context.checkpoint();
    for row in 2..24 {
        let child = context
            .relation(task_pair(task(row, row)), IDENTITY)
            .unwrap();
        context
            .dependency(Dependency::Derived { child, parent })
            .unwrap();
    }
    let route_parent = context.relation(task_pair(task(24, 24)), IDENTITY).unwrap();
    context
        .dependency(Dependency::Derived {
            child: first_child,
            parent: route_parent,
        })
        .unwrap();
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    context.rollback(checkpoint);
    assert_eq!(context.checkpoint(), checkpoint);
    assert_eq!(
        context.children(parent_pair).collect::<Vec<_>>(),
        vec![child_pair]
    );
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    assert!(
        context.bytes().unwrap() >= before_bytes,
        "rollback accounts retained capacity growth"
    );
    let retried = context.relation(task_pair(task(2, 2)), IDENTITY).unwrap();
    context
        .dependency(Dependency::Derived {
            child: retried,
            parent,
        })
        .unwrap();
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn exact_context_operations_intern_ordered_payloads_and_shared_children() {
    let mut context = State::default();
    let first = ContextExpr::PrefixLeft {
        weight: LocalWeightId(0),
        input: IDENTITY,
    };
    let left = context.context(first).unwrap();
    assert_eq!(context.context(first).unwrap(), left);
    let different_payload = context
        .context(ContextExpr::PrefixLeft {
            weight: LocalWeightId(1),
            input: IDENTITY,
        })
        .unwrap();
    assert_ne!(left, different_payload);
    let right = context
        .context(ContextExpr::SuffixRightPops {
            input: IDENTITY,
            weight: LocalWeightId(0),
        })
        .unwrap();
    assert_ne!(left, right);
    let left_then_right = context
        .context(ContextExpr::SuffixRightPops {
            input: left,
            weight: LocalWeightId(0),
        })
        .unwrap();
    let right_then_left = context
        .context(ContextExpr::PrefixLeft {
            weight: LocalWeightId(0),
            input: right,
        })
        .unwrap();
    assert_ne!(left_then_right, right_then_left);
    let shared = ContextExpr::Replay {
        lower: left,
        upper: left,
    };
    let shared_id = context.context(shared).unwrap();
    assert_eq!(context.context(shared).unwrap(), shared_id);
    assert_eq!(context.contexts[shared_id.0 as usize - 1], shared);
    let ordered = context
        .context(ContextExpr::Replay {
            lower: left,
            upper: right,
        })
        .unwrap();
    let reversed = context
        .context(ContextExpr::Replay {
            lower: right,
            upper: left,
        })
        .unwrap();
    assert_ne!(ordered, reversed);
    assert_ne!(ordered, shared_id);
    let swap = context.context(ContextExpr::Swap { input: left }).unwrap();
    let both = context
        .context(ContextExpr::BothFromRight {
            input: left,
            certificate: EntryCertificateId(0),
        })
        .unwrap();
    let without = context
        .context(ContextExpr::WithoutLeftFilter { input: left })
        .unwrap();
    let different_certificate = context
        .context(ContextExpr::BothFromRight {
            input: left,
            certificate: EntryCertificateId(1),
        })
        .unwrap();
    assert_ne!(both, different_certificate);
    let pair = task_pair(task(0, 0));
    let first_relation = context.relation(pair, both).unwrap();
    let second_relation = context.relation(pair, different_certificate).unwrap();
    assert_ne!(first_relation, second_relation);
    assert_ne!(swap, both);
    assert_ne!(both, without);
    assert_ne!(swap, without);
}

#[test]
fn context_nodes_rollback_atomically_with_relations_and_retain_capacity_accounting() {
    let mut session = session();
    let before = state(&session).checkpoint();
    let before_bytes = state(&session).bytes().unwrap();
    let run = |session: &mut InferenceSession| {
        let context = &mut session
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let mut input = IDENTITY;
        for payload in 0..24 {
            input = context.context(ContextExpr::PrefixLeft {
                weight: LocalWeightId(payload),
                input,
            })?;
            context.relation(task_pair(task(0, 0)), input)?;
        }
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(input)
    };
    let result = session.with_route_transaction(|session| {
        run(session)?;
        Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
    });
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    let context = state(&session);
    assert_eq!(context.checkpoint(), before);
    assert_eq!(context.context_keys.len(), before.contexts);
    assert_eq!(context.keys.len(), before.relations);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    assert!(context.bytes().unwrap() >= before_bytes);
    let retried = session.with_route_transaction(run).unwrap();
    assert_eq!(retried, ContextId(before.contexts as u32 + 24));
    let context = state(&session);
    assert_eq!(context.contexts.len(), before.contexts + 24);
    assert_eq!(context.context_keys.len(), context.contexts.len());
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
#[should_panic(expected = "context must be identity or an already interned node")]
fn context_construction_rejects_nonexistent_child() {
    let mut context = State::default();
    let _ = context.context(ContextExpr::Swap {
        input: ContextId(1),
    });
}

#[test]
#[should_panic(expected = "context must be identity or an already interned node")]
fn relation_construction_rejects_nonexistent_context() {
    let mut context = State::default();
    let _ = context.relation(task_pair(task(0, 0)), ContextId(1));
}


#[test]
fn source_closed_annotation_filters_execute_and_keep_resolved_members() {
    for (allowed, errors) in [("E", 0), ("", 1)] {
        let mut session = session_with_source(&format!(
            "act E:\n    our emit: () -> int\n\nmy answer:[{allowed}] int = E::emit()"
        ));
        let owner = session.batch.hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        session.execute_candidate_source_root(&owner).unwrap();
        assert_eq!(session.errors.len(), errors);
        let context = state(&session);
        assert!(!context.discharge_log.is_empty(), "actual annotation filters have an executable consumer");
        for &id in &context.discharge_log {
            let relation = context.relations[id.0 as usize].key;
            let ContextExpr::ClosedAllowance { view, input: IDENTITY } = context.contexts[relation.context.0 as usize - 1] else { panic!("closed source filter"); };
            let view = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize];
            assert!(matches!(view.provenance, candidate_effect::ViewOrigin::Annotation));
            assert!(view.tail.is_none());
            if !allowed.is_empty() {
                assert_eq!(view.allowed, vec![session.batch.hir.source_effect_declarations()[0].id.clone()]);
            }
        }
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    }
}

#[test]
fn equal_endpoint_filters_register_both_obligations_before_memo_and_self_omission() {
    let mut session = session();
    let receiver = session.fresh_effect_at_level(1).unwrap();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()),
        _ => None,
    }).unwrap();
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let first = session.candidate_effect_view(owner.clone(), effect.declaration.clone(), vec![effect.clone()], None).unwrap();
    let second = session.candidate_effect_view(owner, effect.declaration.clone(), Vec::new(), None).unwrap();
    let task = LiveConstraintTask::Effect(EffectEndpointKey::EffectRow(receiver), EffectEndpointKey::EffectRow(receiver));
    // Complete the ordinary endpoint pair first: contextual admission must
    // still execute each new, source-owned filter on this receiver.
    session.constrain_live(task, &occurrence, &cause).unwrap();
    let before = state(&session).checkpoint();
    let run = |session: &mut InferenceSession| {
        for view in [first, second] {
            let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            let filter = context.context(ContextExpr::ClosedAllowance { view, input: IDENTITY })?;
            let relation = context.relation(task_pair(task), filter)?;
            session.constrain_live_item(TypedWorkItem { task, relation: Some(relation) }, &occurrence, &cause)?;
            assert!(state(session).discharged.contains(&relation));
        }
        let uppers = &session.effect_bounds[receiver as usize].exact_non_variable_uppers;
        assert!(uppers.contains(&EffectEndpointKey::Allowance(first)));
        assert!(uppers.contains(&EffectEndpointKey::Allowance(second)));
        assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        run(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert!(!session.effect_bounds[receiver as usize].exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(first)));
    assert!(!session.effect_bounds[receiver as usize].exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(second)));
    session.with_route_transaction(run).unwrap();
    let contribution = session.candidate_effect_contribution(effect, session.batch.hir.source_effect_declarations()[0].id.declaration.clone()).unwrap();
    session.constrain_live(LiveConstraintTask::Effect(contribution, EffectEndpointKey::EffectRow(receiver)), &occurrence, &cause).unwrap();
    assert_eq!(session.errors.len(), 1, "the second filter rejects a future E lower although the first allows it");
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn pre_registered_filter_replays_current_conflict_at_new_relation_and_rolls_back() {
    let mut session = session();
    let receiver = session.fresh_effect_at_level(1).unwrap();
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()),
        _ => None,
    }).unwrap();
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let view = session.candidate_effect_view(
        owner,
        effect.declaration.clone(),
        Vec::new(),
        None,
    ).unwrap();
    let row = EffectEndpointKey::EffectRow(receiver);
    let allowance = EffectEndpointKey::Allowance(view);
    // The bound exists before this contextual relation is admitted.
    session.candidate_apply_effect(row, allowance).unwrap();
    let (first_occurrence, first_cause) = cause(&session, 0);
    let contribution = session.candidate_effect_contribution(
        effect,
        session.batch.hir.source_effect_declarations()[0].id.declaration.clone(),
    ).unwrap();
    session.constrain_live(
        LiveConstraintTask::Effect(contribution, row),
        &first_occurrence,
        &first_cause,
    ).unwrap();
    let prior_errors = session.errors.len();
    assert!(prior_errors > 0, "the existing bound records the current conflict");

    let task = LiveConstraintTask::Effect(row, row);
    let (occurrence, cause) = cause(&session, 1);
    let before = state(&session).checkpoint();
    let admit = |session: &mut InferenceSession| {
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let filtered = context.context(ContextExpr::ClosedAllowance { view, input: IDENTITY })?;
        let relation = context.relation(task_pair(task), filtered)?;
        session.constrain_live_item(
            TypedWorkItem { task, relation: Some(relation) },
            &occurrence,
            &cause,
        )
    };
    assert_eq!(session.with_route_transaction(|session| {
        admit(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(session.errors.len(), prior_errors);

    session.with_route_transaction(admit).unwrap();
    assert_eq!(session.errors.len(), prior_errors + 1, "the new relation replays the current conflict");
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}
