use super::*;
use yu_hir::shadow::lower_module_with_local_source;

#[test]
fn detached_fold_retains_shared_nodes_order_bracketing_and_certificates() {
    let mut context = State::default();
    let shared = context.context(ContextExpr::BothFromRight {
        input: IDENTITY, certificate: EntryCertificateId(17),
    }).unwrap();
    let other = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let pair = context.context(ContextExpr::Replay { lower: shared, upper: other }).unwrap();
    let root = context.context(ContextExpr::Replay { lower: pair, upper: shared }).unwrap();
    let before = context.checkpoint();
    let mut visits = HashMap::new();
    let result = context.fold_context(root, |id, expression, children: &[&String]| {
        *visits.entry(id).or_insert(0) += 1;
        Ok(match expression {
            None => "I".to_owned(),
            Some(ContextExpr::BothFromRight { certificate, .. }) => {
                assert_eq!(certificate, EntryCertificateId(17));
                format!("B17({})", children[0])
            }
            Some(ContextExpr::Swap { .. }) => format!("S({})", children[0]),
            Some(ContextExpr::Replay { .. }) => format!("({};{})", children[0], children[1]),
            _ => unreachable!(),
        })
    }).unwrap();
    assert_eq!(result, "((B17(I);S(I));B17(I))");
    assert_eq!(visits.len(), 5);
    assert!(visits.values().all(|&count| count == 1));
    assert_eq!(context.checkpoint(), before);
    assert!(context.relations.is_empty());
    assert!(context.weights.is_empty(), "fold does not resolve or execute source weights");
    assert!(context.discharged.is_empty());
}

#[test]
fn detached_fold_terminates_iteratively_and_preserves_weight_tokens() {
    let mut context = State::default();
    let mut root = IDENTITY;
    for _ in 0..4096 {
        root = context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(123), input: root }).unwrap();
    }
    root = context.context(ContextExpr::SuffixRightPops { input: root, weight: LocalWeightId(456) }).unwrap();
    root = context.context(ContextExpr::WithoutLeftFilter { input: root }).unwrap();
    let depth = context.fold_context(root, |_, expression, children: &[&usize]| {
        match expression {
            Some(ContextExpr::PrefixLeft { weight, .. }) => assert_eq!(weight, LocalWeightId(123)),
            Some(ContextExpr::SuffixRightPops { weight, .. }) => assert_eq!(weight, LocalWeightId(456)),
            _ => {},
        }
        Ok(children.first().map_or(0, |depth| **depth + 1))
    }).unwrap();
    assert_eq!(depth, 4098);
}

#[test]
fn detached_fold_invalid_handles_use_internal_availability() {
    let mut context = State::default();
    assert_eq!(context.fold_context(ContextId(1), |_, _, _: &[&()]| Ok(())), Err(exhausted()));
    // Invalid forward/self inputs violate the append-only construction DAG.
    context.contexts.push(ContextExpr::Swap { input: ContextId(1) });
    assert_eq!(context.fold_context(ContextId(1), |_, _, _: &[&()]| Ok(())), Err(exhausted()));
    context.contexts[0] = ContextExpr::Swap { input: ContextId(99) };
    assert_eq!(context.fold_context(ContextId(1), |_, _, _: &[&()]| Ok(())), Err(exhausted()));
}

fn numeric_family() -> DetachedPushFamily {
    DetachedPushFamily(vec![session().batch.hir.source_effect_declarations()[0].id.clone()])
}
fn numeric_entry(id: u32, pops: u32, pushes: u32, family: DetachedPushFamily) -> DetachedLeftEntry {
    DetachedLeftEntry { id: DetachedAttachmentId(id), pops: ExactCount::from_u32(pops).unwrap(),
        pushes: ExactCount::from_u32(pushes).unwrap(), family: (pushes != 0).then_some(family) }
}
fn numeric_weight(entry: DetachedLeftEntry) -> DetachedWeight {
    DetachedWeight { left: vec![entry], filter: DetachedFilter::All, right: vec![] }
}
fn numeric_node(context: &mut State, slot: u32) -> ContextId {
    context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(slot), input: IDENTITY }).unwrap()
}

#[test]
fn detached_numeric_exact_counts_cross_limb_boundaries() {
    let family = numeric_family();
    let max = ExactCount::from_u32(u32::MAX).unwrap();
    let one = ExactCount::from_u32(1).unwrap();
    let boundary = max.add(&one).unwrap();
    assert_eq!(boundary.0, [0, 1]);
    assert_eq!(boundary.subtract(&max).unwrap(), one);
    let larger = boundary.add(&boundary).unwrap().add(&one).unwrap();
    assert_eq!(larger.0, [1, 2]);
    assert_eq!(larger.subtract(&boundary).unwrap().0, [1, 1]);
    assert!(one.subtract(&boundary).is_err());
    let mut context = State::default();
    let weights = [
        numeric_weight(numeric_entry(0, 0, u32::MAX, family.copy().unwrap())),
        numeric_weight(numeric_entry(0, 0, 1, family.copy().unwrap())),
        numeric_weight(numeric_entry(0, u32::MAX, 0, family.copy().unwrap())),
    ];
    let a = numeric_node(&mut context, 0); let b = numeric_node(&mut context, 1); let c = numeric_node(&mut context, 2);
    let ab = context.context(ContextExpr::Replay { lower: a, upper: b }).unwrap();
    let root = context.context(ContextExpr::Replay { lower: ab, upper: c }).unwrap();
    let result = context.evaluate_context(root, &weights).unwrap();
    assert_eq!(result.value.left, [numeric_entry(0, 0, 1, family.copy().unwrap())]);
    let large_pop = numeric_weight(DetachedLeftEntry { id: DetachedAttachmentId(0), pops: larger,
        pushes: ExactCount::default(), family: None });
    let mut accumulated = large_pop.copy().unwrap();
    accumulated.append_left(&[numeric_entry(0, 1, 0, family.copy().unwrap())]).unwrap();
    assert_eq!(accumulated.left[0].pops.0, [2, 2]);
    let mut right = DetachedWeight::identity();
    right.append_right(&[DetachedRightEntry { id: DetachedAttachmentId(0), pops: max }]).unwrap();
    right.append_right(&[DetachedRightEntry { id: DetachedAttachmentId(0), pops: one }]).unwrap();
    assert_eq!(right.right[0].pops.0, [0, 1]);
}

#[test]
fn detached_numeric_replay_order_and_directed_mix() {
    let family = numeric_family();
    let mut context = State::default();
    let weights = [
        numeric_weight(numeric_entry(0, 0, 1, family.copy().unwrap())),
        numeric_weight(numeric_entry(0, 1, 0, family.copy().unwrap())),
    ];
    let push = numeric_node(&mut context, 0); let pop = numeric_node(&mut context, 1);
    let cancellation = context.context(ContextExpr::Replay { lower: push, upper: pop }).unwrap();
    assert!(context.evaluate_context(cancellation, &weights).unwrap().value.left.is_empty());
    let reverse = context.context(ContextExpr::Replay { lower: pop, upper: push }).unwrap();
    assert_eq!(context.evaluate_context(reverse, &weights).unwrap().value.left,
        [numeric_entry(0, 1, 1, family.copy().unwrap())]);
    let right = context.context(ContextExpr::SuffixRightPops { input: IDENTITY, weight: LocalWeightId(1) }).unwrap();
    let mixed = context.context(ContextExpr::Replay { lower: push, upper: right }).unwrap();
    assert_eq!(context.evaluate_context(mixed, &weights).unwrap().value, DetachedWeight::identity());
    let pop_right = context.context(ContextExpr::Replay { lower: pop, upper: right }).unwrap();
    let result = context.evaluate_context(pop_right, &weights).unwrap().value;
    assert!(result.left.is_empty()); assert_eq!(result.right[0].pops.0, [2]);
    assert!(context.evaluate_context(right, &weights).unwrap().value.left.is_empty());
}

#[test]
fn detached_numeric_swap_both_and_filter_are_algebra_only() {
    let family = numeric_family();
    let mut context = State::default();
    let mut weight = numeric_weight(numeric_entry(3, 2, 4, family.copy().unwrap()));
    weight.filter = DetachedFilter::Finite(vec![]);
    let weights = [weight, numeric_weight(numeric_entry(7, 5, 0, family.copy().unwrap()))];
    let base = numeric_node(&mut context, 0);
    let right = context.context(ContextExpr::SuffixRightPops { input: base, weight: LocalWeightId(1) }).unwrap();
    let swap = context.context(ContextExpr::Swap { input: right }).unwrap();
    let twice = context.context(ContextExpr::Swap { input: swap }).unwrap();
    let swapped = context.evaluate_context(swap, &weights).unwrap().value;
    assert_eq!(swapped.left, [numeric_entry(7, 5, 0, family.copy().unwrap())]);
    assert_eq!(swapped.right[0].id, DetachedAttachmentId(3));
    assert_eq!(swapped.right[0].pops.0, [2]); assert_eq!(swapped.filter, DetachedFilter::All);
    assert_ne!(context.evaluate_context(twice, &weights).unwrap().value,
        context.evaluate_context(right, &weights).unwrap().value, "swap is not an involution");
    let both = context.context(ContextExpr::BothFromRight { input: right, certificate: EntryCertificateId(999) }).unwrap();
    let result = context.evaluate_context(both, &weights).unwrap();
    assert_eq!(result.value.left, [numeric_entry(7, 5, 0, family.copy().unwrap())]);
    assert_eq!(result.value.right[0].pops.0, [5]);
    assert!(result.nodes.contains(&(both, Some(ContextExpr::BothFromRight { input: right, certificate: EntryCertificateId(999) }))));
    let without = context.context(ContextExpr::WithoutLeftFilter { input: base }).unwrap();
    assert_eq!(context.evaluate_context(without, &weights).unwrap().value.filter, DetachedFilter::All);
    assert!(context.discharged.is_empty()); assert!(context.weights.is_empty());
}

#[test]
fn detached_numeric_families_are_exact_sets_and_ids_remain_distinct() {
    let family = numeric_family();
    let session = session_with_source("act E\nact F\nmy seed = 1");
    let declarations = session.batch.hir.source_effect_declarations();
    let e = declarations[0].id.clone(); let f = declarations[1].id.clone();
    let set = DetachedFilter::Finite(vec![e.clone(), f.clone()]);
    assert_eq!(DetachedFilter::All.intersect(&set).unwrap(), set);
    assert_eq!(DetachedFilter::All.intersect(&DetachedFilter::All).unwrap(), DetachedFilter::All);
    assert_ne!(DetachedFilter::All, DetachedFilter::Finite(vec![e.clone(), f.clone()]));
    assert_eq!(set.intersect(&DetachedFilter::Finite(vec![e.clone()])).unwrap(), DetachedFilter::Finite(vec![e.clone()]));
    assert_eq!(set, DetachedFilter::Finite(vec![f.clone(), e.clone(), e.clone()]));
    let mut word = numeric_weight(numeric_entry(0, 0, 1, DetachedPushFamily(vec![e.clone()])));
    assert!(word.append_left(&[numeric_entry(0, 0, 1, DetachedPushFamily(vec![f]))]).is_err());
    word.append_left(&[numeric_entry(1, 0, 1, DetachedPushFamily(vec![e]))]).unwrap();
    assert_eq!(word.left.len(), 2, "equal nominal family does not equate attachment IDs");
    word.append_left(&[numeric_entry(0, 1, 0, family.copy().unwrap())]).unwrap();
    assert_eq!(word.left.len(), 1);
    assert_eq!(word.left[0].id, DetachedAttachmentId(1));
    let mut context = State::default(); let root = numeric_node(&mut context, 17);
    assert!(matches!(context.evaluate_context(root, &[]), Err(SolveAvailabilityError::IdentityExhausted)));
}

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
            let ContextExpr::PrefixLeft { weight, input: IDENTITY } = context.contexts[relation.context.0 as usize - 1] else { panic!("closed source filter"); };
            let payload = &context.weights[weight.0 as usize];
            let view = payload.boundary;
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
            let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].closed_weight.unwrap();
            let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            let filter = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY })?;
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
        let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].closed_weight.unwrap();
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let filtered = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY })?;
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

#[test]
fn exact_bound_fibers_rollback_and_retry_account_retained_capacity() {
    let mut context = State::default();
    let key = BoundKey(value(0), Polarity::Positive, value(1));
    let first = context.relation(bound_pair(key), IDENTITY).unwrap();
    context.attach(key, first).unwrap();
    let checkpoint = context.checkpoint();
    let bytes = context.bytes().unwrap();
    let operation = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let second = context.relation(bound_pair(key), operation).unwrap();
    context.attach(key, second).unwrap();
    context.attach(key, second).unwrap();
    assert_eq!(context.bound_relations(key).collect::<Vec<_>>(), vec![second, first]);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    context.rollback(checkpoint);
    assert_eq!(context.checkpoint(), checkpoint);
    assert_eq!(context.bound_relations(key).collect::<Vec<_>>(), vec![first]);
    assert!(context.bytes().unwrap() >= bytes);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    let operation = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let second = context.relation(bound_pair(key), operation).unwrap();
    context.attach(key, second).unwrap();
    assert_eq!(context.bound_relations(key).count(), 2);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn replay_retains_order_shared_context_and_explicit_queue_identity() {
    for reverse in [false, true] {
        let mut session = session();
        let owner = session.fresh_value_at_level(1).unwrap();
        let lower = session.fresh_value_at_level(1).unwrap();
        let upper = session.fresh_value_at_level(1).unwrap();
        let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
        let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let shared = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
        let lower_relation = context.relation(bound_pair(lower_input), shared).unwrap();
        let upper_relation = context.relation(bound_pair(upper_input), shared).unwrap();
        let entries = if reverse { [(upper_input, upper_relation), (lower_input, lower_relation)] }
            else { [(lower_input, lower_relation), (upper_input, upper_relation)] };
        for (key, relation) in entries { context.attach(key, relation).unwrap(); }
        let replay_task = task(lower, upper);
        session.candidate_context_replay(lower_input, upper_input, replay_task, |session, replay| {
        assert_eq!(replay.len(), 1);
        let context = state(session);
        let child = replay[0];
        let retained = context.relations[child.0 as usize].key.context;
        assert_eq!(context.contexts[retained.0 as usize - 1], ContextExpr::Replay { lower: shared, upper: shared });
        assert!(context.dependency_keys.contains(&Dependency::Replay {
            child, lower: lower_relation, upper: upper_relation, lower_input, upper_input,
        }));
        session.enqueue_item(TypedWorkItem { task: replay_task, relation: Some(child) }, false).unwrap();
        assert_eq!(session.typed_worklist.pop_front(), Some(TypedWorkItem { task: replay_task, relation: Some(child) }));
        // Carrier construction does not admit the later operation evaluator.
        assert_eq!(session.candidate_context_execute(replay_task, Some(child)), Err(exhausted()));
        assert_eq!(state(session).bytes().unwrap(), state(session).enumerated_bytes());
        Ok(())
        }).unwrap();
    }
}

#[test]
fn capture_and_transport_preserve_every_exact_bound_fiber_without_upstream_edges() {
    let mut session = session();
    let row = session.fresh_value_at_level(2).unwrap();
    let copy = session.fresh_value_at_level(2).unwrap();
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let key = BoundKey(value(row), Polarity::Positive, lower);
    let (occurrence, cause) = cause(&session, 0);
    session.candidate_restore_bound(value(row), Polarity::Positive, lower, &occurrence, &cause).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let identity = context.bound(key).unwrap();
    let operation = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let second = context.relation(bound_pair(key), operation).unwrap();
    context.attach(key, second).unwrap();
    let graph = session.capture_candidate_graph(row, 0).unwrap();
    for parent in [identity, second] {
        assert!(graph.bounds.iter().any(|bound| bound.relation == Some(parent)));
    }
    let copied = BoundKey(value(copy), Polarity::Positive, lower);
    for parent in [identity, second] {
        session.candidate_context_transport(parent, copied, 1).unwrap();
    }
    let context = state(&session);
    assert_eq!(context.bound_relations(copied).count(), 2);
    for parent in [identity, second] {
        assert!(context.dependencies.iter().any(|dependency| matches!(dependency,
            Dependency::Transport { parent: retained, .. } if *retained == parent)));
        assert!(!context.children(bound_pair(key)).any(|pair| pair == bound_pair(copied)),
            "transport does not replay fresh-use conflicts upstream");
    }
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn opposite_replay_schedules_the_cartesian_product_of_exact_bound_contexts() {
    let mut session = session();
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let operation = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    for key in [lower_input, upper_input] {
        for input in [IDENTITY, operation] {
            let relation = context.relation(bound_pair(key), input).unwrap();
            context.attach(key, relation).unwrap();
        }
    }
    session.candidate_context_replay(lower_input, upper_input, task(lower, upper), |session, replay| {
    assert_eq!(replay.len(), 4);
    assert_eq!(replay.iter().copied().collect::<HashSet<_>>().len(), 4);
    let context = state(session);
    assert_eq!(context.dependencies.iter().filter(|dependency| matches!(dependency,
        Dependency::Replay { lower_input: l, upper_input: u, .. } if *l == lower_input && *u == upper_input)).count(), 4);
    assert!(replay.iter().any(|id| context.relations[id.0 as usize].key.context == IDENTITY));
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    Ok(())
    }).unwrap();
}

#[test]
fn third_owner_incoming_bound_survives_parent_copy_intrusion_and_rollback_retry() {
    for effect in [false, true] {
      for restore_after_merge in [false, true] {
        let mut session = session();
        let (occurrence, cause) = cause(&session, 0);
        let (parent, owner, terminal, contribution) = if effect {
            let parent = ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(session.fresh_effect_at_level(2).unwrap()));
            let owner = ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(session.fresh_effect_at_level(3).unwrap()));
            let declaration = session.batch.hir.source_effect_declarations()[0].id.clone();
            let binding = session.batch.hir.items().iter().find_map(|item| match item {
                HirItem::Binding(binding) => Some(binding.definition_root().clone()), _ => None,
            }).unwrap();
            let allowance = session.candidate_effect_view(binding, declaration.declaration.clone(), Vec::new(), None).unwrap();
            let contribution = session.candidate_effect_contribution(declaration.clone(), declaration.declaration).unwrap();
            (parent, owner, ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(allowance)), ExtrusionEndpoint::Effect(contribution))
        } else {
            (value(session.fresh_value_at_level(2).unwrap()), value(session.fresh_value_at_level(3).unwrap()),
                ExtrusionEndpoint::Value(ValueEndpointKey::UnitNegative), ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive))
        };
        session.candidate_restore_bound(parent, Polarity::Negative, terminal, &occurrence, &cause).unwrap();
        let copy = session.candidate_extrude(parent, Polarity::Positive, 0).unwrap();
        if !restore_after_merge {
            session.candidate_restore_bound(owner, Polarity::Negative, copy, &occurrence, &cause).unwrap();
        }
        let original_key = BoundKey(owner, Polarity::Negative, copy);
        let original = state(&session).bound(original_key);
        let before = state(&session).checkpoint();
        let errors = session.errors.len();
        let run = |session: &mut InferenceSession| {
            session.candidate_restore_bound(copy, Polarity::Negative, parent, &occurrence, &cause)?;
            let self_task = match copy {
                ExtrusionEndpoint::Value(row) => LiveConstraintTask::Value(CanonicalValuePairKey { lower: row, upper: row }),
                ExtrusionEndpoint::Effect(row) => LiveConstraintTask::Effect(row, row),
            };
            session.constrain_live(self_task, &occurrence, &cause)?;
            assert_eq!(session.canonical_extrusion(copy), parent);
            let canonical_key = BoundKey(owner, Polarity::Negative, parent);
            if !restore_after_merge { assert!(state(session).bound(canonical_key).is_some()); }
            assert_eq!(state(session).bound(original_key), original);
            let task = match (contribution, owner) {
                (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => LiveConstraintTask::Value(CanonicalValuePairKey { lower, upper }),
                (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) => LiveConstraintTask::Effect(lower, upper),
                _ => unreachable!(),
            };
            if restore_after_merge {
                session.candidate_restore_bound(owner, Polarity::Positive, contribution, &occurrence, &cause)?;
                session.candidate_restore_bound(owner, Polarity::Negative, copy, &occurrence, &cause)?;
                assert!(state(session).bound(canonical_key).is_some());
            } else {
                session.constrain_live(task, &occurrence, &cause)?;
            }
            assert!(session.errors.len() > errors, "third-owner lower reaches the retained terminal conflict");
            assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
            Ok::<_, SolveAvailabilityError>(())
        };
        assert_eq!(session.with_route_transaction(|session| { run(session)?; Err::<(), _>(exhausted()) }), Err(exhausted()));
        assert_eq!(state(&session).checkpoint(), before);
        assert_eq!(session.errors.len(), errors);
        assert_eq!(session.canonical_extrusion(copy), copy);
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        session.with_route_transaction(run).unwrap();
      }
    }
}

#[test]
fn replay_frontier_schedules_only_new_pairs_and_charges_live_output_through_failure() {
    let mut session = session();
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let replay_task = task(lower, upper);
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    for key in [lower_input, upper_input] {
        let relation = context.relation(bound_pair(key), IDENTITY).unwrap();
        context.attach(key, relation).unwrap();
    }
    let before = state(&session).checkpoint();
    let execute = |session: &mut InferenceSession| {
        session.candidate_context_replay(lower_input, upper_input, replay_task, |session, replay| {
            assert_eq!(replay.len(), 1);
            assert!(session.candidate_graph.as_ref().unwrap().scratch_bytes >= std::mem::size_of::<RelationId>());
            session.enqueue_item(TypedWorkItem { task: replay_task, relation: Some(replay[0]) }, false)?;
            session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            assert!(!session.typed_worklist.is_empty());
            session.typed_worklist.pop_front();
            Err::<(), _>(exhausted())
        })
    };
    assert_eq!(session.with_route_transaction(execute), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
    session.candidate_context_replay(lower_input, upper_input, replay_task, |_, replay| {
        assert_eq!(replay.len(), 1); Ok(())
    }).unwrap();
    session.candidate_context_replay(lower_input, upper_input, replay_task, |_, replay| {
        assert!(replay.is_empty()); Ok(())
    }).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let operation = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let relation = context.relation(bound_pair(lower_input), operation).unwrap();
    context.attach(lower_input, relation).unwrap();
    session.candidate_context_replay(lower_input, upper_input, replay_task, |_, replay| {
        assert_eq!(replay.len(), 1); Ok(())
    }).unwrap();
    session.candidate_context_replay(lower_input, upper_input, replay_task, |_, replay| {
        assert!(replay.is_empty()); Ok(())
    }).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let relation = context.relation(bound_pair(upper_input), operation).unwrap();
    context.attach(upper_input, relation).unwrap();
    session.candidate_context_replay(lower_input, upper_input, replay_task, |_, replay| {
        assert_eq!(replay.len(), 2); Ok(())
    }).unwrap();
    session.candidate_context_replay(lower_input, upper_input, replay_task, |_, replay| {
        assert!(replay.is_empty()); Ok(())
    }).unwrap();
    let before_use = state(&session).checkpoint();
    assert_eq!(session.with_route_transaction(|session| {
        session.candidate_context_restore_replay(lower_input, upper_input, replay_task, |session, replay| {
            assert_eq!(replay.len(), 4);
            assert!(session.candidate_graph.as_ref().unwrap().scratch_bytes >= replay.len() * std::mem::size_of::<RelationId>());
            session.enqueue_item(TypedWorkItem { task: replay_task, relation: Some(replay[0]) }, false)?;
            session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            session.typed_worklist.pop_front();
            Err::<(), _>(exhausted())
        })
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before_use);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
}

#[test]
fn repeated_bound_restoration_replays_diagnostics_with_each_use_cause_and_rolls_back() {
    for effect in [false, true] {
        let mut session = session();
        let (first_occurrence, first_cause) = cause(&session, 0);
        let (second_occurrence, second_cause) = cause(&session, 1);
        let (owner, lower, upper) = if effect {
            let owner = ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(session.fresh_effect_at_level(1).unwrap()));
            let declaration = session.batch.hir.source_effect_declarations()[0].id.clone();
            let binding = session.batch.hir.items().iter().find_map(|item| match item {
                HirItem::Binding(binding) => Some(binding.definition_root().clone()), _ => None,
            }).unwrap();
            let view = session.candidate_effect_view(binding, declaration.declaration.clone(), Vec::new(), None).unwrap();
            let lower = session.candidate_effect_contribution(declaration.clone(), declaration.declaration).unwrap();
            (owner, ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view)))
        } else {
            (value(session.fresh_value_at_level(1).unwrap()), ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive),
                ExtrusionEndpoint::Value(ValueEndpointKey::UnitNegative))
        };
        session.candidate_restore_bound(owner, Polarity::Positive, lower, &first_occurrence, &first_cause).unwrap();
        session.candidate_restore_bound(owner, Polarity::Negative, upper, &first_occurrence, &first_cause).unwrap();
        assert!(session.errors.iter().any(|error| error.cause == first_cause));
        let before = state(&session).checkpoint();
        let dependencies = state(&session).dependencies.len();
        let errors = session.errors.len();
        let replay = |session: &mut InferenceSession| {
            session.candidate_restore_bound(owner, Polarity::Negative, upper, &second_occurrence, &second_cause)?;
            assert_eq!(state(session).dependencies.len(), dependencies, "per-use replay does not duplicate persistent certificates");
            assert!(session.errors.len() > errors);
            assert!(session.errors[errors..].iter().all(|error| error.occurrence == second_occurrence && error.cause == second_cause));
            assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
            Ok::<_, SolveAvailabilityError>(())
        };
        assert_eq!(session.with_route_transaction(|session| { replay(session)?; Err::<(), _>(exhausted()) }), Err(exhausted()));
        assert_eq!(state(&session).checkpoint(), before);
        assert_eq!(session.errors.len(), errors);
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        session.with_route_transaction(replay).unwrap();
    }
}

#[test]
fn closed_payloads_keep_boundary_authority_and_fresh_copy_sharing_with_rollback() {
    let mut session = session();
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()),
        _ => None,
    }).unwrap();
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let original = session.candidate_effect_view(owner.clone(), effect.declaration.clone(), vec![effect.clone()], None).unwrap();
    let other = session.candidate_effect_view(owner.clone(), effect.declaration.clone(), vec![effect.clone()], None).unwrap();
    let tail = session.fresh_effect_at_level(1).unwrap();
    let mixed = session.candidate_effect_view(owner, effect.declaration.clone(), vec![effect.clone()], Some(tail)).unwrap();
    let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
    let original_weight = algebra.views[original as usize].closed_weight.unwrap();
    let other_weight = algebra.views[other as usize].closed_weight.unwrap();
    assert_ne!(original_weight, other_weight, "same resolved family at separate boundaries has separate authority");
    assert!(algebra.views[mixed as usize].closed_weight.is_none(), "mixed tail rows remain outside closed-filter evaluation");
    assert_eq!(algebra.context.allowed(original_weight), &[effect]);
    let before = state(&session).checkpoint();
    let copy_and_check = |session: &mut InferenceSession| {
        let first = session.candidate_copy_effect_view(original, None)?;
        let second = session.candidate_copy_effect_view(original, None)?;
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let first_weight = algebra.views[first as usize].closed_weight.unwrap();
        let second_weight = algebra.views[second as usize].closed_weight.unwrap();
        assert_ne!(first_weight, original_weight);
        assert_ne!(first_weight, second_weight, "independent local views own independent filters");
        assert_eq!(algebra.context.allowed(first_weight), algebra.context.allowed(original_weight));
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let expression = ContextExpr::PrefixLeft { weight: first_weight, input: IDENTITY };
        assert_eq!(context.context(expression)?, context.context(expression)?, "one view retains shared context identity");
        assert_eq!(context.bytes()?, context.enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        copy_and_check(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(copy_and_check).unwrap();
}


#[test]
fn written_attachment_sets_retain_members_source_and_fresh_instance_identity() {
    let mut session = session_with_source("act E\nact F\nmy answer:[F, E, F] int = 1");
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()),
        _ => None,
    }).unwrap();
    let annotation = session.batch.candidate_source.schedules.values().flatten().find_map(|action| match action {
        candidate_source::Action::Annotation { annotation, .. } => Some(annotation.clone()),
        _ => None,
    }).unwrap();
    let exact_position = annotation.ty.effects.as_ref().unwrap().position.clone();
    session.execute_candidate_source_root(&owner).unwrap();
    let view = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.iter()
        .position(|view| view.allowed.len() == 3).unwrap() as u32;
    let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].closed_weight.unwrap();
    let payload = &state(&session).weights[weight.0 as usize];
    let source = payload.attachment.as_ref().unwrap();
    assert_eq!(payload.position, exact_position);
    assert_eq!(payload.owner, annotation.owner);
    assert_eq!(source.member_ordinals, [0, 1, 2]);
    assert_eq!(source.composed_polarity, Polarity::Positive);
    assert_eq!(source.lexical_scope, candidate_effect::AnnotationScope::Definition(owner.clone()));
    let families = session.batch.hir.source_effect_declarations();
    assert_eq!(payload.allowed, [families[1].id.clone(), families[0].id.clone(), families[1].id.clone()]);
    assert!(payload.left_word.is_empty() && payload.right_pops.is_empty());
    let before = state(&session).checkpoint();
    let copy_and_check = |session: &mut InferenceSession| {
        let first = session.candidate_copy_effect_view(view, None)?;
        let second = session.candidate_copy_effect_view(view, None)?;
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let first_weight = algebra.views[first as usize].closed_weight.unwrap();
        let second_weight = algebra.views[second as usize].closed_weight.unwrap();
        assert_ne!(first_weight, weight);
        assert_ne!(first_weight, second_weight);
        let original = &algebra.context.weights[weight.0 as usize];
        for copy in [first_weight, second_weight] {
            let copied = &algebra.context.weights[copy.0 as usize];
            assert_eq!((&copied.owner, &copied.position), (&original.owner, &original.position));
            assert_eq!(copied.allowed, original.allowed);
            assert_eq!(copied.attachment.as_ref().unwrap().member_ordinals, original.attachment.as_ref().unwrap().member_ordinals);
            assert_eq!(algebra.context.attachment_source(copy), algebra.context.attachment_source(weight));
            assert!(copied.left_word.is_empty() && copied.right_pops.is_empty());
        }
        assert_eq!(algebra.context.bytes()?, algebra.context.enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        copy_and_check(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(copy_and_check).unwrap();
}

#[test]
fn written_empty_rows_own_sets_and_omitted_rows_keep_only_closed_filters() {
    for (text, written) in [("my answer:[] int = 1", true), ("my answer x:int -> int = x", false)] {
        let mut session = session_with_source(text);
        let owner = session.batch.hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        session.execute_candidate_source_root(&owner).unwrap();
        assert!(!state(&session).weights.is_empty());
        for payload in &state(&session).weights {
            assert_eq!(payload.attachment.is_some(), written);
            assert!(payload.allowed.is_empty());
            if let Some(set) = &payload.attachment { assert!(set.member_ordinals.is_empty()); }
        }
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}


#[test]
fn separate_local_written_occurrences_keep_same_family_authority_independent() {
    let mut session = session_with_source("act E\nmy answer = { my first:[E] int = 1; my second:[E] int = 2; second }");
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()),
        _ => None,
    }).unwrap();
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    let written: Vec<_> = context.weights.iter().enumerate().filter(|(_, payload)| payload.attachment.is_some()).collect();
    assert_eq!(written.len(), 2);
    let (first_id, first) = written[0];
    let (second_id, second) = written[1];
    assert_ne!(first_id, second_id);
    assert_ne!(first.position, second.position);
    assert_eq!(first.allowed, second.allowed);
    let first_source = first.attachment.as_ref().unwrap();
    let second_source = second.attachment.as_ref().unwrap();
    assert!(matches!(first_source.lexical_scope, candidate_effect::AnnotationScope::Local(_)));
    assert!(matches!(second_source.lexical_scope, candidate_effect::AnnotationScope::Local(_)));
    assert_ne!(first_source.lexical_scope, second_source.lexical_scope);
    assert_eq!(first_source.member_ordinals, [0]);
    assert_eq!(second_source.member_ordinals, [0]);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}


#[test]
fn mixed_written_attachment_sets_survive_fresh_copy_and_rollback_without_closed_filters() {
    let mut session = session_with_source("act E\nact F\nmy answer x:'a -> [F, E, 'e] 'a = x");
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()),
        _ => None,
    }).unwrap();
    session.execute_candidate_source_root(&owner).unwrap();
    let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
    let view = algebra.views.iter().position(|view| view.tail.is_some() && view.allowed.len() == 2).unwrap() as u32;
    let original = &algebra.views[view as usize];
    assert!(original.closed_weight.is_none());
    let weight = original.source_weight.unwrap();
    let payload = &algebra.context.weights[weight.0 as usize];
    assert_eq!(payload.attachment.as_ref().unwrap().member_ordinals, [0, 1]);
    assert_eq!(payload.attachment.as_ref().unwrap().composed_polarity, Polarity::Positive);
    let families = session.batch.hir.source_effect_declarations();
    assert_eq!(payload.allowed, [families[1].id.clone(), families[0].id.clone()]);
    let tail = original.tail;
    let before = state(&session).checkpoint();
    let copy_and_check = |session: &mut InferenceSession| {
        let mut remap = HashMap::new();
        remap.try_reserve(1).map_err(|_| exhausted())?;
        let mut charge = 0;
        session.candidate_scratch_growth(&mut charge,
            remap.capacity() * std::mem::size_of::<((u32, Option<u32>), u32)>())?;
        let first = session.candidate_remapped_effect_view(view, tail, &mut remap)?;
        assert_eq!(session.candidate_remapped_effect_view(view, tail, &mut remap)?, first,
            "members share one attachment identity within a fresh use");
        drop(remap);
        session.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        let second = session.candidate_copy_effect_view(view, tail)?;
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let first_weight = algebra.views[first as usize].source_weight.unwrap();
        let second_weight = algebra.views[second as usize].source_weight.unwrap();
        assert_ne!(first_weight, weight);
        assert_ne!(first_weight, second_weight);
        for copy in [first, second] {
            let copied_view = &algebra.views[copy as usize];
            assert!(copied_view.closed_weight.is_none());
            assert_eq!(copied_view.tail, tail);
            let copied_weight = copied_view.source_weight.unwrap();
            let copied = &algebra.context.weights[copied_weight.0 as usize];
            let original = &algebra.context.weights[weight.0 as usize];
            assert_eq!((&copied.owner, &copied.position), (&original.owner, &original.position));
            assert_eq!(copied.allowed, original.allowed);
            assert_eq!(copied.attachment.as_ref().unwrap().member_ordinals, original.attachment.as_ref().unwrap().member_ordinals);
            assert_eq!(algebra.context.attachment_source(copied_weight), algebra.context.attachment_source(weight));
            assert!(copied.left_word.is_empty() && copied.right_pops.is_empty());
        }
        assert_eq!(algebra.context.bytes()?, algebra.context.enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        copy_and_check(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(copy_and_check).unwrap();
}

fn empty_bundle_owner(session: &InferenceSession) -> DefinitionRootId {
    session.batch.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) => Some(binding.definition_root().clone()), _ => None,
    }).unwrap()
}

#[test]
fn negative_written_empty_bundles_preserve_leaf_ports_and_executable_graph() {
    for (written, omitted, local) in [
        ("my answer x:[] int -> int = x", "my answer x:int -> int = x", false),
        ("my answer = { my local x:[] int -> int = x; 1 }", "my answer = { my local x:int -> int = x; 1 }", true),
    ] {
        let mut session = session_with_source(written);
        let owner = empty_bundle_owner(&session);
        session.execute_candidate_source_root(&owner).unwrap();
        let context = state(&session);
        assert_eq!(context.bundles.len(), 1);
        let bundle = &context.bundles[0];
        assert_eq!(bundle.occurrence.local_slot(), 41);
        assert_eq!(bundle.sets.len(), 1);
        let set = &bundle.sets[0];
        assert_eq!(set.owner, owner);
        assert_eq!(set.source.composed_polarity, Polarity::Negative);
        assert_eq!(matches!(set.source.lexical_scope, candidate_effect::AnnotationScope::Local(_)), local);
        let actions: Vec<_> = session.batch.candidate_source.schedules.values().flatten().collect();
        let (annotation, occurrence) = actions.iter().find_map(|action| match action {
            candidate_source::Action::Annotation { annotation, occurrence, .. } if !local => Some((annotation, occurrence)),
            candidate_source::Action::LocalAnnotation { annotation, occurrence, .. } if local => Some((annotation, occurrence)), _ => None,
        }).unwrap();
        let yu_hir::shadow::SourceAnnotationValue::Function { argument, .. } = &annotation.ty.value else { unreachable!() };
        assert_eq!(set.position, argument.effects.as_ref().unwrap().position);
        assert_eq!(bundle.occurrence, ConstraintOccurrenceId::new(occurrence.clone(), 41));
        for slot in [40, 41] {
            let source = ConstraintOccurrenceId::new(occurrence.clone(), slot);
            let origin = context.origins.iter().find(|origin| origin.occurrence == source).unwrap();
            assert!(context.relation_bundles(origin.relation).any(|bundle| bundle == AttachmentBundleId(0)));
        }
        let root = if local { session.candidate_graph.as_ref().unwrap().locals.iter().flatten().next().unwrap().root }
            else { session.live_components[session.batch.root_component_positions[&owner].component].ordinal };
        let graph = session.capture_candidate_graph(root, 0).unwrap();
        assert!(!graph.attachment_bundles.is_empty());
        assert!(graph.nodes.iter().any(|node| matches!(node, candidate_scheme::Node::Function { children, .. }
            if matches!(graph.nodes[children[1]], candidate_scheme::Node::Leaf(candidate_scheme::Atom::EmptyEffect)))));
        let counts = (graph.nodes.len(), graph.rows.len(), graph.bounds.len(),
            session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len(), state(&session).contexts.len());
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
        let mut baseline = session_with_source(omitted);
        let owner = empty_bundle_owner(&baseline);
        baseline.execute_candidate_source_root(&owner).unwrap();
        let root = if local { baseline.candidate_graph.as_ref().unwrap().locals.iter().flatten().next().unwrap().root }
            else { baseline.live_components[baseline.batch.root_component_positions[&owner].component].ordinal };
        let graph = baseline.capture_candidate_graph(root, 0).unwrap();
        assert!(state(&baseline).bundles.is_empty());
        assert_eq!(counts, (graph.nodes.len(), graph.rows.len(), graph.bounds.len(),
            baseline.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len(), state(&baseline).contexts.len()));
    }
}

#[test]
fn negative_written_empty_bundles_share_per_use_and_rollback_retry() {
    let mut session = session_with_source("my answer = { my first x:[] 'a -> 'a = x; my second x:[] 'a -> 'a = x; 1 }");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    assert_eq!(state(&session).bundles.len(), 2);
    let first = &state(&session).bundles[0];
    let second = &state(&session).bundles[1];
    assert_ne!(first.occurrence, second.occurrence);
    assert_ne!(first.sets[0].position, second.sets[0].position);
    assert_ne!(first.sets[0].source.lexical_scope, second.sets[0].source.lexical_scope);
    let local = session.candidate_graph.as_ref().unwrap().locals.iter().flatten().last().unwrap();
    let graph = session.capture_candidate_graph(local.root, local.boundary).unwrap();
    assert!(graph.attachment_bundles.len() > 1, "paired publication relations share their bundle");
    let (occurrence, cause) = cause(&session, 90);
    let before = state(&session).checkpoint();
    let copy = |session: &mut InferenceSession| {
        let count = state(session).bundles.len();
        session.freshen_candidate_graph(&graph, 2, &occurrence, &cause)?;
        assert_eq!(state(session).bundles.len(), count + 1, "all references share one bundle within a use");
        let fresh = AttachmentBundleId(count);
        assert!(state(session).bundle_incidence_log.iter().any(|incidence| incidence.bundle == fresh));
        assert_eq!(state(session).bundles[count].occurrence, state(session).bundles[graph.attachment_bundles[0].1.0].occurrence);
        assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(fresh)
    };
    assert_eq!(session.with_route_transaction(|session| { copy(session)?; Err::<(), _>(exhausted()) }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    let first = session.with_route_transaction(copy).unwrap();
    let second = session.with_route_transaction(copy).unwrap();
    assert_ne!(first, second);
}

#[test]
fn negative_written_empty_bundle_publication_failure_restores_source_links() {
    let mut session = session_with_source("my answer x:[] int -> int = x");
    let owner = empty_bundle_owner(&session);
    let before = state(&session).checkpoint();
    assert_eq!(session.with_route_transaction(|session| {
        session.execute_candidate_source_root(&owner)?;
        assert_eq!(state(session).bundles.len(), 1);
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert!(state(&session).source_bundles.is_empty());
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(|session| session.execute_candidate_source_root(&owner)).unwrap();
    assert_eq!(state(&session).bundles.len(), 1);
}

#[test]
fn negative_formal_written_empty_still_refuses_attachment_registration() {
    let mut session = session_with_source("my answer (cb:int -> ['e] int) = cb");
    let action = session.batch.candidate_source.schedules.values().flatten().find(|action|
        matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
    let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
    let mut annotation = (*annotation).clone();
    let yu_hir::shadow::SourceAnnotationValue::Function { result, .. } = &mut annotation.ty.value else { unreachable!() };
    result.effects.as_mut().unwrap().variables.clear();
    let before = state(&session).checkpoint();
    assert_eq!(session.with_route_transaction(|session|
        session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert!(state(&session).bundles.is_empty());
}

fn indexed_bundle_fixture() -> (State, AttachmentBundle) {
    let mut session = session_with_source("my answer x:[] int -> int = x");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    (State::default(), state(&session).bundles[0].clone())
}
fn indexed_relation(context: &mut State, row: u32) -> RelationId {
    context.relation(task_pair(task(row, row)), IDENTITY).unwrap()
}

#[test]
fn indexed_bundle_provenance_closes_cycles_and_isolates_fresh_transports() {
    let (mut context, template) = indexed_bundle_fixture();
    let rows: Vec<_> = (0..5).map(|row| indexed_relation(&mut context, row)).collect();
    context.dependency(Dependency::Derived { parent: rows[0], child: rows[1] }).unwrap();
    context.dependency(Dependency::Transport { parent: rows[1], child: rows[2], use_origin: 0 }).unwrap();
    context.dependency(Dependency::Transport { parent: rows[2], child: rows[3], use_origin: 1 }).unwrap();
    assert!(context.bundle_transports.is_none(), "never-bundled sessions allocate no transport index");
    assert!(!context.edges.contains_key(&rows[1]), "transport adds no diagnostic adjacency");
    let first = context.retain_bundle(template.clone(), false).unwrap();
    let second = context.retain_bundle(template, false).unwrap();
    let before = context.checkpoint();
    for _ in 0..2 {
        context.bundle_link(rows[0], first).unwrap();
        assert!(context.bundle_transports.is_some());
        for &row in &rows[..3] { assert_eq!(context.relation_bundles(row).collect::<Vec<_>>(), [first]); }
        assert_eq!(context.relation_bundles(rows[3]).count(), 0);
        context.dependency(Dependency::Transport { parent: rows[2], child: rows[4], use_origin: 0 }).unwrap();
        context.dependency(Dependency::Derived { parent: rows[4], child: rows[0] }).unwrap();
        context.bundle_link(rows[2], second).unwrap();
        for &row in &[rows[0], rows[1], rows[2], rows[4]] {
            let bundles: HashSet<_> = context.relation_bundles(row).collect();
            assert_eq!(bundles, HashSet::from([first, second]));
        }
        assert_eq!(context.relation_bundles(rows[3]).count(), 0);
        assert_eq!(context.bundle_incidence_log.len(), 8);
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
        context.rollback(before);
        assert_eq!(context.checkpoint(), before);
        assert!(context.bundle_incidence_heads.is_empty());
        assert!(context.bundle_transports.is_none(), "rollback restores lazy activation");
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    }
    context.bundle_link(rows[0], first).unwrap();
    let activated = context.checkpoint();
    let original_heads = context.bundle_incidence_heads.clone();
    let original_transport_heads = context.bundle_transports.as_ref().unwrap().heads.clone();
    context.dependency(Dependency::Transport { parent: rows[2], child: rows[4], use_origin: 0 }).unwrap();
    context.bundle_link(rows[0], second).unwrap();
    context.rollback(activated);
    assert_eq!(context.bundle_incidence_heads, original_heads);
    assert_eq!(context.bundle_transports.as_ref().unwrap().heads, original_transport_heads);
    assert_eq!(context.checkpoint(), activated);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn indexed_bundle_visits_ignore_unrelated_relations_and_incidences() {
    fn visits(unrelated: u32) -> (usize, usize, usize) {
        let (mut context, template) = indexed_bundle_fixture();
        let first = context.retain_bundle(template.clone(), false).unwrap();
        let second = context.retain_bundle(template, false).unwrap();
        let root = indexed_relation(&mut context, 0);
        let child = indexed_relation(&mut context, 1);
        let late = indexed_relation(&mut context, 2);
        context.bundle_link(root, first).unwrap(); // Activate once before adding sparse unrelated state.
        for row in 10..10 + unrelated {
            let parent = indexed_relation(&mut context, row * 2);
            let child = indexed_relation(&mut context, row * 2 + 1);
            context.dependency(Dependency::Transport { parent, child, use_origin: 0 }).unwrap();
            context.bundle_link(parent, second).unwrap();
        }
        let before = context.bundle_visits;
        context.dependency(Dependency::Derived { parent: root, child }).unwrap();
        let edge_visits = context.bundle_visits - before;
        let before = context.bundle_visits;
        context.bundle_link(root, second).unwrap();
        let incidence_visits = context.bundle_visits - before;
        let before = context.bundle_visits;
        context.dependency(Dependency::Transport { parent: child, child: late, use_origin: 0 }).unwrap();
        let transport_visits = context.bundle_visits - before;
        assert_eq!(context.relation_bundles(root).count(), 2);
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
        (edge_visits, incidence_visits, transport_visits)
    }
    assert_eq!(visits(0), (1, 1, 2));
    assert_eq!(visits(128), (1, 1, 2));
}

#[test]
fn captured_bundle_spans_are_sparse_and_shared_across_reconstruction() {
    let mut session = session_with_source("my answer = { my local x:[] 'a -> 'a = x; 1 }");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let local = session.candidate_graph.as_ref().unwrap().locals.iter().flatten().next().unwrap();
    let graph = session.capture_candidate_graph(local.root, local.boundary).unwrap();
    assert!(!graph.attachment_spans.is_empty());
    let mut referenced = HashSet::new();
    for (&relation, &(start, length)) in &graph.attachment_spans {
        assert!(length > 0);
        let expected: HashSet<_> = state(&session).relation_bundles(relation).collect();
        let actual: HashSet<_> = graph.attachment_bundles[start..start + length].iter().map(|&(owner, bundle)| {
            assert_eq!(owner, relation);
            assert!(referenced.insert((owner, bundle)), "capture resolves each relation once");
            bundle
        }).collect();
        assert_eq!(actual, expected);
    }
    assert_eq!(referenced.len(), graph.attachment_bundles.len());
    assert_eq!(graph.bytes().unwrap(), graph.nodes.capacity() * std::mem::size_of::<candidate_scheme::Node>()
        + graph.rows.capacity() * std::mem::size_of::<candidate_scheme::Row>()
        + graph.bounds.capacity() * std::mem::size_of::<candidate_scheme::Bound>()
        + graph.attachment_bundles.capacity() * std::mem::size_of::<(RelationId, AttachmentBundleId)>()
        + graph.attachment_spans.capacity() * std::mem::size_of::<(RelationId, (usize, usize))>());
    let (occurrence, cause) = cause(&session, 93);
    let bundles = state(&session).bundles.len();
    session.with_route_transaction(|session| session.freshen_candidate_graph(&graph, 2, &occurrence, &cause)).unwrap();
    assert_eq!(state(&session).bundles.len(), bundles + 1);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn source_unit_push_preparation_retains_exact_set_and_evaluates_detached_only() {
    for (text, closed) in [
        ("act E\nact F\nmy answer:[F, E, F] int = 1", true),
        ("act E\nact F\nmy answer x:'a -> [F, E, F, 'e] 'a = x", false),
    ] {
    let mut session = session_with_source(text);
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    assert!(session.errors.is_empty());
    let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
    let view = algebra.views.iter().find(|view| view.allowed.len() == 3).unwrap();
    let weight = view.source_weight.unwrap();
    assert_eq!(view.closed_weight, closed.then_some(weight));
    let before = state(&session).checkpoint();
    let bounds = session.effect_bounds.clone();
    let detached = state(&session).materialize_unit_push(weight).unwrap().unwrap();
    let payload = &state(&session).weights[weight.0 as usize];
    assert_eq!(detached.left[0].id, DetachedAttachmentId(weight.0));
    assert_eq!(detached.left[0].pushes.0, [1]);
    assert_eq!(detached.left[0].family, Some(DetachedPushFamily(payload.allowed.clone())));
    assert_eq!(payload.attachment.as_ref().unwrap().member_ordinals, [0, 1, 2]);
    assert!(payload.left_word.is_empty() && payload.right_pops.is_empty());
    assert_eq!(state(&session).checkpoint(), before);
    let mut table: Vec<_> = (0..state(&session).weights.len()).map(|_| DetachedWeight::identity()).collect();
    table[weight.0 as usize] = detached;
    let pop = LocalWeightId(table.len() as u32);
    table.push(numeric_weight(DetachedLeftEntry {
        id: DetachedAttachmentId(weight.0), pops: ExactCount::from_u32(1).unwrap(),
        pushes: ExactCount::default(), family: None,
    }));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let push_node = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
    let pop_node = context.context(ContextExpr::PrefixLeft { weight: pop, input: IDENTITY }).unwrap();
    let replay = context.context(ContextExpr::Replay { lower: push_node, upper: pop_node }).unwrap();
    assert_eq!(context.evaluate_context(push_node, &table).unwrap().value.left[0].pushes.0, [1]);
    assert_eq!(context.evaluate_context(replay, &table).unwrap().value, DetachedWeight::identity());
    assert_eq!(session.effect_bounds, bounds);
    assert_eq!(state(&session).checkpoint().relations, before.relations);
    assert_eq!(state(&session).checkpoint().discharges, before.discharges);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn source_unit_push_preparation_copies_share_per_use_and_retry_with_fresh_ids() {
    let mut session = session_with_source("act E\nmy answer = { my first:[E] int = 1; my second:[E] int = 2; second }");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let seeds: Vec<_> = state(&session).weights.iter().enumerate().filter_map(|(id, payload)|
        payload.attachment.as_ref().filter(|set| set.unit_push.is_some()).map(|_| LocalWeightId(id as u32))).collect();
    assert_eq!(seeds.len(), 2);
    assert_ne!(seeds[0], seeds[1]);
    assert_eq!(state(&session).allowed(seeds[0]), state(&session).allowed(seeds[1]));
    let view = state(&session).weights[seeds[0].0 as usize].boundary;
    let before = state(&session).checkpoint();
    let copy = |session: &mut InferenceSession| {
        let mut remap = HashMap::new(); remap.try_reserve(1).map_err(|_| exhausted())?;
        let mut charge = 0;
        session.candidate_scratch_growth(&mut charge,
            remap.capacity() * std::mem::size_of::<((u32, Option<u32>), u32)>())?;
        let first = session.candidate_remapped_effect_view(view, None, &mut remap)?;
        assert_eq!(first, session.candidate_remapped_effect_view(view, None, &mut remap)?);
        drop(remap);
        session.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        let second = session.candidate_copy_effect_view(view, None)?;
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let first_weight = algebra.views[first as usize].source_weight.unwrap();
        let second_weight = algebra.views[second as usize].source_weight.unwrap();
        assert_ne!(first_weight, seeds[0]); assert_ne!(first_weight, second_weight);
        for id in [first_weight, second_weight] {
            let original = &algebra.context.weights[seeds[0].0 as usize];
            let copied = &algebra.context.weights[id.0 as usize];
            assert_eq!((&copied.owner, &copied.position), (&original.owner, &original.position));
            assert_eq!(algebra.context.attachment_source(id), algebra.context.attachment_source(seeds[0]));
            let detached = algebra.context.materialize_unit_push(id)?.unwrap();
            assert_eq!(detached.left[0].id, DetachedAttachmentId(id.0));
            assert_eq!(detached.left[0].family, Some(DetachedPushFamily(original.allowed.clone())));
        }
        assert_eq!(algebra.context.bytes()?, algebra.context.enumerated_bytes());
        Ok::<_, SolveAvailabilityError>(first_weight)
    };
    assert_eq!(session.with_route_transaction(|session| { copy(session)?; Err::<(), _>(exhausted()) }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    let first = session.with_route_transaction(copy).unwrap();
    let second = session.with_route_transaction(copy).unwrap();
    assert_ne!(first, second);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn source_unit_push_preparation_excludes_empty_symbolic_operation_and_formal_rows() {
    for text in [
        "my answer:[] int = 1",
        "my answer x:int -> int = x",
        "my answer x:'a -> ['e] 'a = x",
        "my answer x:[] int -> int = x",
        "act E:\n    our emit: () -> int\n\nmy answer = E::emit()",
    ] {
        let mut session = session_with_source(text);
        let owner = empty_bundle_owner(&session);
        session.execute_candidate_source_root(&owner).unwrap();
        for id in 0..state(&session).weights.len() {
            assert!(state(&session).materialize_unit_push(LocalWeightId(id as u32)).unwrap().is_none());
        }
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
    let mut session = session_with_source("act E\nmy answer (cb:int -> ['e] int) = cb");
    let action = session.batch.candidate_source.schedules.values().flatten().find(|action|
        matches!(action, candidate_source::Action::FormalAnnotation { .. })).unwrap().clone();
    let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
    let mut annotation = (*annotation).clone();
    let yu_hir::shadow::SourceAnnotationValue::Function { result, .. } = &mut annotation.ty.value else { unreachable!() };
    result.effects.as_mut().unwrap().concrete.push(session.batch.hir.source_effect_declarations()[0].id.clone());
    let before = state(&session).checkpoint();
    assert_eq!(session.with_route_transaction(|session|
        session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert!(state(&session).weights.is_empty());
}

#[test]
fn exact_relation_completion_keeps_contexts_and_component_kinds_distinct() {
    for task in [
        LiveConstraintTask::Value(CanonicalValuePairKey {
            lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
        }),
        LiveConstraintTask::Effect(EffectEndpointKey::BottomPositive, EffectEndpointKey::EmptyNegative),
    ] {
        let mut session = session();
        let pair = task_pair(task);
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let other = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
        let first = context.relation(pair, IDENTITY).unwrap();
        let second = context.relation(pair, other).unwrap();
        assert_ne!(first, second);
        assert_eq!(context.relation(pair, IDENTITY).unwrap(), first);
        context.processing = Some(first);
        let bytes_before = session.candidate_graph.as_ref().unwrap().intrusion.bytes().unwrap();
        assert!(!session.pair_is_current(pair));
        session.record_typed_pair_admission(pair, match task {
            LiveConstraintTask::Value(_) => TypedPairMemo::Value {
                children: DiagnosticChildren::new(), direct_witness: None, completion: DiagnosticCompletion::Pending,
            },
            LiveConstraintTask::Effect(..) => TypedPairMemo::Effect,
        }).unwrap();
        assert!(session.pair_is_current(pair));
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(second);
        assert!(!session.pair_is_current(pair), "the same endpoints cannot suppress a distinct context");
        session.mark_candidate_pair(pair).unwrap();
        assert!(session.pair_is_current(pair));
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(first);
        assert!(session.pair_is_current(pair), "exact duplicate relations reuse completion");
        let intrusion = &session.candidate_graph.as_ref().unwrap().intrusion;
        assert_eq!(intrusion.completed.len(), 2);
        assert_eq!(intrusion.bytes().unwrap() - bytes_before,
            intrusion.completed.capacity() * std::mem::size_of::<(RelationId, u64)>(),
            "retained completion capacity uses the relation key size");
        assert_eq!(session.typed_pairs.len(), 1, "contexts share pair-owned diagnostic provenance");
        // The nonidentity context above is a detached identity test, never a
        // live operation task or authorization of nonempty source execution.
    }
}
