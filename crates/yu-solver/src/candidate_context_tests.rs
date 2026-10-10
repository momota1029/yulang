use super::*;
use yu_hir::shadow::lower_module_with_local_source;

fn detached_rename_state() -> State {
    let mut session = session_with_source("act E\nmy answer:[E] int = 1");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let payload = state(&session).weights.iter().find(|weight| !weight.allowed.is_empty()).unwrap();
    let mut context = State::default();
    for boundary in 0..6 {
        context.source_weight(boundary, &payload.owner, &payload.position, &payload.allowed, None).unwrap();
    }
    context
}

#[test]
fn detached_rename_preserves_all_constructors_sharing_order_and_per_use_identity() {
    let mut context = detached_rename_state();
    assert_eq!(context.weights[0].allowed, context.weights[1].allowed);
    let a = context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(0), input: IDENTITY }).unwrap();
    let b = context.context(ContextExpr::SuffixRightPops { input: a, weight: LocalWeightId(1) }).unwrap();
    let swap = context.context(ContextExpr::Swap { input: b }).unwrap();
    let both = context.context(ContextExpr::BothFromRight { input: swap, certificate: EntryCertificateId(17) }).unwrap();
    let filter = context.context(ContextExpr::WithoutLeftFilter { input: both }).unwrap();
    let pair = context.context(ContextExpr::Replay { lower: a, upper: filter }).unwrap();
    let root = context.context(ContextExpr::Replay { lower: pair, upper: a }).unwrap();
    let certificates = HashMap::from([(EntryCertificateId(17), EntryCertificateId(999))]);
    let mut first = HashMap::new();
    let mut scratch = 13;
    let weights = HashMap::from([(LocalWeightId(0), LocalWeightId(2)), (LocalWeightId(1), LocalWeightId(3))]);
    let before = context.checkpoint();
    context.rename_contexts(&[root, filter, IDENTITY], &weights, &certificates, &mut first, &mut scratch).unwrap();
    assert_eq!(scratch, 13);
    assert_eq!(first[&IDENTITY], IDENTITY);
    assert_eq!(context.contexts[first[&a].0 as usize - 1], ContextExpr::PrefixLeft { weight: LocalWeightId(2), input: IDENTITY });
    assert_eq!(context.contexts[first[&b].0 as usize - 1], ContextExpr::SuffixRightPops { input: first[&a], weight: LocalWeightId(3) });
    assert_eq!(context.contexts[first[&swap].0 as usize - 1], ContextExpr::Swap { input: first[&b] });
    assert_eq!(context.contexts[first[&both].0 as usize - 1], ContextExpr::BothFromRight { input: first[&swap], certificate: EntryCertificateId(999) });
    assert_eq!(context.contexts[first[&filter].0 as usize - 1], ContextExpr::WithoutLeftFilter { input: first[&both] });
    assert_eq!(context.contexts[first[&pair].0 as usize - 1], ContextExpr::Replay { lower: first[&a], upper: first[&filter] });
    assert_eq!(context.contexts[first[&root].0 as usize - 1], ContextExpr::Replay { lower: first[&pair], upper: first[&a] });
    let after = context.checkpoint();
    context.rename_contexts(&[root, a], &weights, &certificates, &mut first, &mut scratch).unwrap();
    assert_eq!(context.checkpoint(), after);
    let mut second = HashMap::new();
    let other_weights = HashMap::from([(LocalWeightId(0), LocalWeightId(4)), (LocalWeightId(1), LocalWeightId(5))]);
    context.rename_contexts(&[root], &other_weights, &certificates, &mut second, &mut scratch).unwrap();
    assert_ne!(first[&root], second[&root]);
    assert_ne!(first[&a], second[&a]);
    assert!(context.relations.is_empty());
    assert!(context.discharged.is_empty(), "opaque certificate remapping grants no authorization");
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    context.rollback(before);
    first.clear();
    second.clear();
    context.rename_contexts(&[root], &weights, &certificates, &mut first, &mut scratch).unwrap();
    assert_eq!(context.checkpoint(), after);
    assert_eq!(scratch, 13);
}

#[test]
fn detached_rename_missing_substitutions_and_malformed_handles_rollback_and_retry() {
    let mut context = detached_rename_state();
    let a = context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(0), input: IDENTITY }).unwrap();
    let root = context.context(ContextExpr::BothFromRight { input: a, certificate: EntryCertificateId(17) }).unwrap();
    let before = context.checkpoint();
    let weights = HashMap::from([(LocalWeightId(0), LocalWeightId(2))]);
    let certificates = HashMap::from([(EntryCertificateId(17), EntryCertificateId(999))]);
    let mut map = HashMap::from([(IDENTITY, IDENTITY)]);
    let mut scratch = 7;
    for (roots, weights, certificates) in [
        (vec![root], weights.clone(), HashMap::new()),
        (vec![root], HashMap::new(), certificates.clone()),
        (vec![root], HashMap::from([(LocalWeightId(0), LocalWeightId(u32::MAX))]), certificates.clone()),
        (vec![root, ContextId(before.contexts as u32 + 1)], weights.clone(), certificates.clone()),
        (vec![root, ContextId(u32::MAX)], weights.clone(), certificates.clone()),
    ] {
        assert_eq!(context.rename_contexts(&roots, &weights, &certificates, &mut map, &mut scratch), Err(exhausted()));
        assert_eq!(context.checkpoint(), before);
        assert_eq!(map, HashMap::from([(IDENTITY, IDENTITY)]));
        assert_eq!(scratch, 7);
    }
    let malformed = context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(u32::MAX), input: IDENTITY }).unwrap();
    let malformed_before = context.checkpoint();
    assert!(context.rename_contexts(&[malformed], &HashMap::from([(LocalWeightId(u32::MAX), LocalWeightId(0))]), &certificates, &mut map, &mut scratch).is_err());
    assert_eq!(context.checkpoint(), malformed_before);
    // Corrupt retained construction is rejected before descending or interning.
    context.contexts[malformed.0 as usize - 1] = ContextExpr::Swap { input: malformed };
    assert!(context.rename_contexts(&[malformed], &weights, &certificates, &mut map, &mut scratch).is_err());
    assert_eq!(scratch, 7);
    context.rename_contexts(&[root], &weights, &certificates, &mut map, &mut scratch).unwrap();
    assert_eq!(scratch, 7);
}

#[test]
fn detached_rename_validates_cached_roots_and_partial_child_suggestions() {
    let mut context = detached_rename_state();
    let a = context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(0), input: IDENTITY }).unwrap();
    let root = context.context(ContextExpr::BothFromRight { input: a, certificate: EntryCertificateId(17) }).unwrap();
    let weights = HashMap::from([(LocalWeightId(0), LocalWeightId(2))]);
    let certificates = HashMap::from([(EntryCertificateId(17), EntryCertificateId(999))]);
    let mut scratch = 11;
    let mut valid = HashMap::new();
    context.rename_contexts(&[root], &weights, &certificates, &mut valid, &mut scratch).unwrap();
    let before = context.checkpoint();
    for (mut map, weights, certificates) in [
        (valid.clone(), HashMap::new(), certificates.clone()),
        (valid.clone(), weights.clone(), HashMap::new()),
        (HashMap::from([(a, ContextId(u32::MAX))]), weights.clone(), certificates.clone()),
        (HashMap::from([(a, root)]), weights.clone(), certificates.clone()),
        (HashMap::from([(root, valid[&root])]), HashMap::new(), certificates.clone()),
    ] {
        let original = map.clone();
        assert_eq!(context.rename_contexts(&[root], &weights, &certificates, &mut map, &mut scratch), Err(exhausted()));
        assert_eq!(context.checkpoint(), before);
        assert_eq!(map, original);
        assert_eq!(scratch, 11);
    }
    context.rename_contexts(&[root, a], &weights, &certificates, &mut valid, &mut scratch).unwrap();
    assert_eq!(context.checkpoint(), before);
    assert_eq!(scratch, 11);
    let mut partial = HashMap::from([(a, valid[&a])]);
    context.rename_contexts(&[root], &weights, &certificates, &mut partial, &mut scratch).unwrap();
    assert_eq!(partial, valid);
    assert_eq!(context.checkpoint(), before);
    assert_eq!(scratch, 11);
}

#[test]
fn detached_rename_identity_and_scratch_overflow_are_atomic() {
    let mut context = State::default();
    let mut map = HashMap::new();
    let before = context.checkpoint();
    let mut scratch = usize::MAX;
    assert!(context.rename_contexts(&[IDENTITY], &HashMap::new(), &HashMap::new(), &mut map, &mut scratch).is_err());
    assert_eq!(scratch, usize::MAX);
    assert!(map.is_empty());
    assert_eq!(context.checkpoint(), before);
    scratch = 0;
    context.rename_contexts(&[IDENTITY], &HashMap::new(), &HashMap::new(), &mut map, &mut scratch).unwrap();
    assert_eq!(map[&IDENTITY], IDENTITY);
    assert_eq!(context.checkpoint(), before);
    assert_eq!(scratch, 0);
    // Identity cache validation needs no weight or certificate substitution.
    context.rename_contexts(&[IDENTITY], &HashMap::new(), &HashMap::new(), &mut map, &mut scratch).unwrap();
    assert_eq!(map, HashMap::from([(IDENTITY, IDENTITY)]));
    assert_eq!(scratch, 0);
}

#[test]
fn detached_rename_walks_deep_shared_dag_iteratively() {
    let mut context = detached_rename_state();
    let mut root = IDENTITY;
    for _ in 0..4096 {
        root = context.context(ContextExpr::Replay { lower: root, upper: root }).unwrap();
    }
    let before = context.checkpoint();
    let mut map = HashMap::new();
    let mut scratch = 0;
    context.rename_contexts(&[root, root], &HashMap::new(), &HashMap::new(), &mut map, &mut scratch).unwrap();
    assert_eq!(map.len(), 4097);
    assert_eq!(map[&root], root);
    assert_eq!(context.checkpoint(), before);
    assert_eq!(scratch, 0);
}

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
                ..
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
        witness: None,
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
            let mut represented = HashSet::new();
            context.fold_context(relation.context, |_, expression, _: &[&()]| {
                match expression {
                    None | Some(ContextExpr::Replay { .. }) => {},
                    Some(ContextExpr::PrefixLeft { weight, input: IDENTITY }) => { represented.insert(weight); },
                    _ => panic!("closed source filter fragment"),
                }
                Ok(())
            }).unwrap();
            for weight in represented {
                let payload = &context.weights[weight.0 as usize];
                let view = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[payload.boundary as usize];
                assert!(matches!(view.provenance, candidate_effect::ViewOrigin::Annotation));
                assert!(view.tail.is_none());
                assert_eq!(view.closed_weight, Some(weight));
                if !allowed.is_empty() {
                    assert_eq!(view.allowed, vec![session.batch.hir.source_effect_declarations()[0].id.clone()]);
                }
            }
            assert_eq!(context.relation_context(id).unwrap(), IDENTITY);
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
fn zero_word_replay_registers_distinct_boundaries_with_shared_children_and_replays_origins() {
    let mut session = session();
    let receiver = session.fresh_effect_at_level(1).unwrap();
    let row = EffectEndpointKey::EffectRow(receiver);
    let task = LiveConstraintTask::Effect(row, row);
    let owner = empty_bundle_owner(&session);
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let first = session.candidate_effect_view(owner.clone(), effect.declaration.clone(), vec![effect.clone()], None).unwrap();
    let second = session.candidate_effect_view(owner, effect.declaration.clone(), Vec::new(), None).unwrap();
    // A rejecting bound and its conflict predate the new Replay occurrence.
    session.candidate_apply_effect(row, EffectEndpointKey::Allowance(second)).unwrap();
    let (prior_occurrence, prior_cause) = cause(&session, 0);
    let contribution = session.candidate_effect_contribution(effect.clone(), effect.declaration.clone()).unwrap();
    session.constrain_live(LiveConstraintTask::Effect(contribution, row), &prior_occurrence, &prior_cause).unwrap();
    let errors = session.errors.len();
    assert!(errors > 0);
    let (occurrence, cause) = cause(&session, 1);
    let lower_input = BoundKey(ExtrusionEndpoint::Effect(row), Polarity::Positive, ExtrusionEndpoint::Effect(row));
    let upper_input = BoundKey(ExtrusionEndpoint::Effect(row), Polarity::Negative, ExtrusionEndpoint::Effect(row));
    let before = state(&session).checkpoint();
    let run = |session: &mut InferenceSession| {
        let weights = [first, second].map(|view| session.candidate_graph.as_ref().unwrap()
            .intrusion.effect_algebra.views[view as usize].closed_weight.unwrap());
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let a = context.context(ContextExpr::PrefixLeft { weight: weights[0], input: IDENTITY })?;
        let b = context.context(ContextExpr::PrefixLeft { weight: weights[1], input: IDENTITY })?;
        context.contexts.push(ContextExpr::PrefixLeft { weight: weights[1], input: IDENTITY });
        let repeated = ContextId(context.contexts.len() as u32);
        let b = context.context(ContextExpr::Replay { lower: b, upper: repeated })?;
        // Exponential unfolding would revisit the same filter 2^64 times.
        let mut shared = a;
        for _ in 0..64 { shared = context.context(ContextExpr::Replay { lower: shared, upper: shared })?; }
        let lower = context.relation(task_pair(task), shared)?;
        let upper = context.relation(task_pair(task), b)?;
        context.attach(lower_input, lower)?;
        context.attach(upper_input, upper)?;
        session.candidate_context_replay(lower_input, upper_input, task, |session, replay| {
            assert_eq!(replay.len(), 1);
            let root = replay[0];
            let key = state(session).relations[root.0 as usize].key;
            assert_eq!(state(session).contexts[key.context.0 as usize - 1], ContextExpr::Replay { lower: shared, upper: b });
            assert_eq!(state(session).post_check_context(root), key.context);
            session.constrain_live_item(TypedWorkItem { task, relation: Some(root) }, &occurrence, &cause)?;
            assert_eq!(state(session).relations[root.0 as usize].key, key);
            assert_eq!(state(session).post_check_context(root), IDENTITY);
            assert!(state(session).dependency_keys.contains(&Dependency::Replay { child: root, lower, upper, lower_input, upper_input }));
            for view in [first, second] {
                let allowance = EffectEndpointKey::Allowance(view);
                assert!(session.effect_bounds[receiver as usize].exact_non_variable_uppers.contains(&allowance));
                let bound = BoundKey(ExtrusionEndpoint::Effect(row), Polarity::Negative, ExtrusionEndpoint::Effect(allowance));
                assert!(state(session).bound_relations(bound).any(|child| {
                    state(session).relations[child.0 as usize].key.context == IDENTITY
                        && state(session).dependency_keys.contains(&Dependency::Derived { child, parent: root })
                }));
            }
            Ok(())
        })?;
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| { run(session)?; Err::<(), _>(exhausted()) }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(session.errors.len(), errors);
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
    session.with_route_transaction(run).unwrap();
    assert_eq!(session.errors.len(), errors + 1, "one rejecting distinct boundary is replayed once despite shared children");
    assert!(session.errors[errors..].iter().all(|error| error.occurrence == occurrence && error.cause == cause));
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn zero_word_replay_preserves_unequal_receiver_flow_and_distinct_equal_filters() {
    let mut session = session();
    let lower = session.fresh_effect_at_level(1).unwrap();
    let upper = session.fresh_effect_at_level(1).unwrap();
    let lower_row = EffectEndpointKey::EffectRow(lower);
    let upper_row = EffectEndpointKey::EffectRow(upper);
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let owner = empty_bundle_owner(&session);
    let first = session.candidate_effect_view(owner.clone(), effect.declaration.clone(), vec![effect.clone()], None).unwrap();
    let second = session.candidate_effect_view(owner, effect.declaration.clone(), vec![effect.clone()], None).unwrap();
    assert_ne!(first, second);
    let contribution = session.candidate_effect_contribution(effect.clone(), effect.declaration.clone()).unwrap();
    let (occurrence, cause) = cause(&session, 0);
    session.constrain_live(LiveConstraintTask::Effect(contribution, lower_row), &occurrence, &cause).unwrap();
    let task = LiveConstraintTask::Effect(lower_row, upper_row);
    let weights = [first, second].map(|view| session.candidate_graph.as_ref().unwrap()
        .intrusion.effect_algebra.views[view as usize].closed_weight.unwrap());
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let a = context.context(ContextExpr::PrefixLeft { weight: weights[0], input: IDENTITY }).unwrap();
    // A retained noncanonical construction fixture repeats one payload ID in
    // distinct nodes; execution must dedup payloads as well as shared nodes.
    context.contexts.push(ContextExpr::PrefixLeft { weight: weights[0], input: IDENTITY });
    let repeated = ContextId(context.contexts.len() as u32);
    let b = context.context(ContextExpr::PrefixLeft { weight: weights[1], input: IDENTITY }).unwrap();
    // A zero-word prefix remains executable when replayed against identity.
    let a = context.context(ContextExpr::Replay { lower: a, upper: IDENTITY }).unwrap();
    let shared = context.context(ContextExpr::Replay { lower: a, upper: repeated }).unwrap();
    let root = context.context(ContextExpr::Replay { lower: shared, upper: b }).unwrap();
    let relation = context.relation(task_pair(task), root).unwrap();
    session.with_route_transaction(|session| {
        session.constrain_live_item(TypedWorkItem { task, relation: Some(relation) }, &occurrence, &cause)?;
        assert!(session.effect_bounds[upper as usize].exact_non_variable_lowers.contains(&contribution));
        for view in [first, second] {
            assert!(session.effect_bounds[lower as usize].exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(view)));
        }
        assert_eq!(state(session).relations[relation.0 as usize].key.context, root);
        assert_eq!(state(session).post_check_context(relation), IDENTITY);
        assert!(state(session).checking_filters.is_none());
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        Ok(())
    }).unwrap();
    assert!(session.errors.is_empty());
}

#[test]
fn zero_word_validation_scope_restores_outer_scratch_on_nested_failure() {
    let mut session = session();
    let receiver = session.fresh_effect_at_level(1).unwrap();
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let view = session.candidate_effect_view(empty_bundle_owner(&session), effect.declaration.clone(), vec![effect], None).unwrap();
    let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].closed_weight.unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let filter = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
    let outer = context.relation(TypedPairKey::Effect { lower: EffectEndpointKey::EffectRow(receiver), upper: EffectEndpointKey::Allowance(view) }, filter).unwrap();
    let inner = context.relation(TypedPairKey::Effect { lower: EffectEndpointKey::EffectRow(receiver), upper: EffectEndpointKey::EffectRow(receiver) }, filter).unwrap();
    assert_eq!(session.candidate_zero_word_filters(outer, filter, |session, filters, residual| {
        assert_eq!(residual, IDENTITY);
        assert_eq!(filters, &[weight]);
        let outer_scratch = session.candidate_graph.as_ref().unwrap().scratch_bytes;
        assert!(outer_scratch > 0);
        assert_eq!(session.candidate_zero_word_filters(inner, filter, |session, nested, residual| {
            assert_eq!(residual, IDENTITY);
            assert_eq!(nested, &[weight]);
            assert_eq!(state(session).checking_filters.as_ref().unwrap().0, inner);
            assert!(session.candidate_graph.as_ref().unwrap().scratch_bytes > outer_scratch);
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        assert_eq!(state(session).checking_filters.as_ref().unwrap().0, outer);
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, outer_scratch);
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert!(state(&session).checking_filters.is_none());
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
}

#[test]
fn zero_word_consumer_rejects_unsupported_operations_before_registration() {
    for kind in 0..5 {
        let mut session = session();
        let receiver = session.fresh_effect_at_level(1).unwrap();
        let row = EffectEndpointKey::EffectRow(receiver);
        let task = LiveConstraintTask::Effect(row, row);
        let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
        let view = session.candidate_effect_view(empty_bundle_owner(&session), effect.declaration.clone(), vec![effect], None).unwrap();
        let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].closed_weight.unwrap();
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let filter = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
        let unsupported = context.context(match kind {
            0 => ContextExpr::Swap { input: filter },
            1 => ContextExpr::BothFromRight { input: filter, certificate: EntryCertificateId(0) },
            2 => ContextExpr::WithoutLeftFilter { input: filter },
            3 => ContextExpr::SuffixRightPops { input: IDENTITY, weight },
            _ => ContextExpr::PrefixLeft { input: filter, weight },
        }).unwrap();
        let root = context.context(ContextExpr::Replay { lower: filter, upper: unsupported }).unwrap();
        let relation = context.relation(task_pair(task), root).unwrap();
        assert_eq!(session.candidate_context_execute(task, Some(relation)), Err(exhausted()));
        assert_eq!(state(&session).post_check_context(relation), root);
        assert!(!session.effect_bounds[receiver as usize].exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(view)));
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
    }
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
        // Payload-free operations are executable while the exact replay context stays attached.
        assert_eq!(session.candidate_context_execute(replay_task, Some(child)), Ok(false));
        assert_eq!(state(session).post_check_context(child), retained);
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
fn expression_ascription_parenthesized_pairs_share_child_computation_and_keep_occurrences() {
    let mut session = session_with_source("my answer = (1 as int) as int");
    let owner = empty_bundle_owner(&session);
    let source = session.batch.hir.local_source(&owner).unwrap().unwrap();
    let child = source.expressions().iter().find(|expr| matches!(expr.form,
        yu_hir::shadow::LocalSourceForm::Integer(_))).unwrap();
    let child_positions = session.batch.occurrence_component_positions[&child.occurrence];
    let actions = session.batch.candidate_source.schedules[&owner].clone();
    let pairs: Vec<_> = actions.iter().filter_map(|action| match action {
        candidate_source::Action::Ascription { annotation, endpoint, computation_effect, occurrence, level, scope } =>
            Some((annotation, *endpoint, *computation_effect, occurrence, *level, scope)),
        _ => None,
    }).collect();
    assert_eq!(pairs.len(), 2);
    assert_ne!(pairs[0].0.position, pairs[1].0.position);
    assert_ne!(pairs[0].3, pairs[1].3);
    let child_row = session.live_components[child_positions.value].ordinal;
    for (annotation, endpoint, effect, occurrence, level, scope) in pairs {
        assert!(matches!(endpoint, shadow_apply::CandidateEndpoint::Component(value) if value == child_positions.value));
        assert_eq!(effect, child_positions.effect);
        let occurrence_positions = session.batch.occurrence_component_positions[occurrence];
        assert_eq!(occurrence_positions.value, child_positions.value);
        assert_eq!(occurrence_positions.effect, child_positions.effect);
        session.candidate_expression_ascription(annotation, endpoint, occurrence, level, effect, scope).unwrap();
        for slot in [45, 46] {
            let origin = state(&session).origins.iter().find(|origin|
                origin.occurrence == ConstraintOccurrenceId::new(occurrence.clone(), slot)).unwrap();
            let TypedPairKey::Value(pair) = state(&session).relations[origin.relation.0 as usize].key.pair else { panic!("value pair"); };
            if slot == 45 {
                assert_eq!(pair.lower, ValueEndpointKey::ValueRow(child_row));
            } else {
                assert_eq!(pair.upper, ValueEndpointKey::ValueRow(child_row));
            }
        }
    }
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn expression_ascription_binding_annotation_keeps_separate_source_bundles() {
    for (text, local) in [
        ("my answer:[] int -> int = 1 as ([] int -> int)", false),
        ("my answer = { my local:[] int -> int = 1 as ([] int -> int); 1 }", true),
    ] {
        let mut session = session_with_source(text);
        let owner = empty_bundle_owner(&session);
        let actions = session.batch.candidate_source.schedules[&owner].clone();
        let ascription = actions.iter().find_map(|action| match action {
            candidate_source::Action::Ascription { occurrence, .. } => Some(occurrence.clone()), _ => None,
        }).unwrap();
        let binding = actions.iter().find_map(|action| match action {
            candidate_source::Action::Annotation { occurrence, .. } if !local => Some(occurrence.clone()),
            candidate_source::Action::LocalAnnotation { occurrence, .. } if local => Some(occurrence.clone()), _ => None,
        }).unwrap();
        assert_eq!(ascription, binding);
        session.execute_candidate_source_root(&owner).unwrap();
        let context = state(&session);
        assert_eq!(context.bundles.len(), 2);
        for (slots, anchor) in [([40, 41], 41), ([45, 46], 46)] {
            let bundle = context.bundles.iter().position(|bundle|
                bundle.occurrence == ConstraintOccurrenceId::new(binding.clone(), anchor)).unwrap();
            for slot in slots {
                let origins: Vec<_> = context.origins.iter().filter(|origin|
                    origin.occurrence == ConstraintOccurrenceId::new(binding.clone(), slot)).collect();
                assert_eq!(origins.len(), 1);
                assert!(context.relation_bundles(origins[0].relation)
                    .any(|id| id == AttachmentBundleId(bundle)));
            }
        }
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    }
}

#[test]
fn expression_ascription_binding_annotation_keeps_separate_computation_effect_origins() {
    for text in [
        "my answer:[] int = 1 as [] int",
        "my answer = { my local:[] int = 1 as [] int; local }",
    ] {
        let mut session = session_with_source(text);
        let owner = empty_bundle_owner(&session);
        let occurrence = session.batch.candidate_source.schedules[&owner].iter().find_map(|action| match action {
            candidate_source::Action::Ascription { occurrence, .. } => Some(occurrence.clone()), _ => None,
        }).unwrap();
        session.execute_candidate_source_root(&owner).unwrap();
        let context = state(&session);
        for slot in [42, 47] {
            let origins: Vec<_> = context.origins.iter().filter(|origin|
                origin.occurrence == ConstraintOccurrenceId::new(occurrence.clone(), slot)).collect();
            assert_eq!(origins.len(), 1);
            assert!(matches!(context.relations[origins[0].relation.0 as usize].key.pair, TypedPairKey::Effect { .. }));
        }
    }
}

#[test]
fn expression_ascription_parameter_pair_preserves_parameter_endpoint() {
    let mut session = session_with_source("my answer x = x as int");
    let owner = empty_bundle_owner(&session);
    let action = session.batch.candidate_source.schedules[&owner].iter().find(|action|
        matches!(action, candidate_source::Action::Ascription { .. })).unwrap().clone();
    let candidate_source::Action::Ascription { annotation, endpoint, computation_effect, occurrence, level, scope } = action else { unreachable!() };
    assert!(matches!(endpoint, shadow_apply::CandidateEndpoint::Parameter(_)));
    session.candidate_expression_ascription(&annotation, endpoint, &occurrence, level, computation_effect, &scope).unwrap();
    session.execute_candidate_source_root(&owner).unwrap();
    assert!(session.errors.is_empty());
}

#[test]
fn expression_ascription_concrete_occurrences_keep_distinct_attachment_identity() {
    let mut session = session_with_source("act E\nmy answer = (1 as [E] int) as [E] int");
    let owner = empty_bundle_owner(&session);
    let actions = session.batch.candidate_source.schedules[&owner].clone();
    let positions: Vec<_> = actions.iter().filter_map(|action| match action {
        candidate_source::Action::Ascription { annotation, .. } => annotation.ty.effects.as_ref().map(|row| row.position.clone()),
        _ => None,
    }).collect();
    assert_eq!(positions.len(), 2);
    assert_ne!(positions[0], positions[1]);
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    let weights: Vec<_> = positions.iter().map(|position| context.weights.iter().enumerate()
        .find(|(_, weight)| &weight.position == position && !weight.allowed.is_empty()).unwrap()).collect();
    assert_ne!(weights[0].0, weights[1].0);
    assert_eq!(weights[0].1.allowed, weights[1].1.allowed);
    assert!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.contributions.is_empty());
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn expression_ascription_local_scopes_isolate_named_values_and_effect_attachments() {
    let mut session = session_with_source("act E\nmy answer = { my first = 1 as 'a; my second = 1 as 'a; my third = 1 as [E] int; my fourth = 1 as [E] int; fourth }");
    let owner = empty_bundle_owner(&session);
    let actions = session.batch.candidate_source.schedules[&owner].clone();
    let scopes: Vec<_> = actions.iter().filter_map(|action| match action {
        candidate_source::Action::Ascription { scope, .. } => Some(scope.clone()),
        _ => None,
    }).collect();
    assert_eq!(scopes.len(), 4);
    assert!(scopes.iter().all(|scope| matches!(scope, candidate_effect::AnnotationScope::Local(_))));
    assert_ne!(scopes[0], scopes[1]);
    assert_ne!(scopes[2], scopes[3]);
    for action in &actions {
        if let candidate_source::Action::Ascription { annotation, endpoint, computation_effect, occurrence, level, scope } = action {
            session.candidate_expression_ascription(annotation, *endpoint, occurrence, *level, *computation_effect, scope).unwrap();
        }
    }
    let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
    let rows: Vec<_> = scopes[..2].iter().map(|scope| algebra.annotation_values[&(scope.clone(), Box::<str>::from("'a"))]).collect();
    assert_ne!(rows[0], rows[1]);
    let views: Vec<_> = algebra.views.iter().filter(|view| !view.allowed.is_empty()).collect();
    assert_eq!(views.len(), 2);
    assert!(views.iter().all(|view| view.tail.is_none()));
    assert_ne!(views[0].position, views[1].position);
    let weights: Vec<_> = state(&session).weights.iter().enumerate().filter(|(_, weight)| !weight.allowed.is_empty()).collect();
    assert_eq!(weights.len(), 2);
    assert_eq!(state(&session).attachment_source(candidate_context::LocalWeightId(weights[0].0 as u32)).unwrap().lexical_scope, scopes[2]);
    assert_eq!(state(&session).attachment_source(candidate_context::LocalWeightId(weights[1].0 as u32)).unwrap().lexical_scope, scopes[3]);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn expression_ascription_local_formal_shares_its_named_annotation_row() {
    let mut session = session_with_source("my answer = { my local (x:'a) = x as 'a; local }");
    let owner = empty_bundle_owner(&session);
    let actions = session.batch.candidate_source.schedules[&owner].clone();
    let formal_scope = actions.iter().find_map(|action| match action {
        candidate_source::Action::FormalAnnotation { scope, .. } => Some(scope.clone()), _ => None,
    }).unwrap();
    let expression_scope = actions.iter().find_map(|action| match action {
        candidate_source::Action::Ascription { scope, .. } => Some(scope.clone()), _ => None,
    }).unwrap();
    assert_eq!(formal_scope, expression_scope);
    assert!(matches!(formal_scope, candidate_effect::AnnotationScope::Local(_)));
    session.execute_candidate_source_root(&owner).unwrap();
    let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
    assert_eq!(algebra.annotation_values.len(), 1);
    assert!(algebra.annotation_values.contains_key(&(formal_scope, Box::<str>::from("'a"))));
}

#[test]
fn expression_ascription_call_preserves_original_formal_name_and_registration() {
    for text in ["my answer cb = cb 1", "my answer cb = (cb as (int -> int)) 1"] {
        let mut session = session_with_source(text);
        let owner = empty_bundle_owner(&session);
        session.execute_candidate_source_root(&owner).unwrap();
        let input = &session.batch.candidate_calls.calls[0];
        let name = &session.batch.candidate_calls.names[input.formal_name.unwrap()];
        let registration = &session.batch.candidate_calls.formals[name.registration];
        let source = session.batch.hir.local_source(&owner).unwrap().unwrap();
        let lexical_name = &source.expressions()[name.expression];
        assert!(matches!(&lexical_name.form, yu_hir::shadow::LocalSourceForm::Name {
            resolution: yu_hir::shadow::LocalSourceResolution::Parameter(parameter), ..
        } if parameter == &registration.parameter));
        let call = candidate_call::observe(&session.batch.hir, &session.store, &session.batch.candidate_calls, 0).unwrap();
        assert_eq!(call.formal_registration().unwrap().id, registration.parameter);
        assert_eq!(call.lexical_formal_use().unwrap().occurrence, lexical_name.occurrence);
        assert_ne!(input.checking.occurrence(), &lexical_name.occurrence);
        for expression in source.expressions().iter().filter(|expression| matches!(expression.form,
            yu_hir::shadow::LocalSourceForm::Ascription { .. })) {
            assert_ne!(expression.occurrence, lexical_name.occurrence);
            assert_ne!(&expression.occurrence, input.checking.occurrence());
        }
    }
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

fn synthetic_transport(context: &State, parent: RelationId, child: RelationId, use_origin: usize) -> Dependency {
    fn key(context: &State, relation: RelationId) -> BoundKey {
        match context.relations[relation.0 as usize].key.pair {
            TypedPairKey::Effect { lower, upper } => BoundKey(ExtrusionEndpoint::Effect(lower), Polarity::Negative, ExtrusionEndpoint::Effect(upper)),
            TypedPairKey::Value(pair) => BoundKey(ExtrusionEndpoint::Value(pair.lower), Polarity::Negative, ExtrusionEndpoint::Value(pair.upper)),
        }
    }
    Dependency::Transport { parent, child, use_origin, witness: Some(TransportWitness {
        from: key(context, parent), to: key(context, child),
        reason: if use_origin == 0 { TransportReason::EqualityCanonicalization } else { TransportReason::FreshUse },
    }) }
}

#[test]
fn indexed_bundle_provenance_closes_cycles_and_isolates_fresh_transports() {
    let (mut context, template) = indexed_bundle_fixture();
    let rows: Vec<_> = (0..5).map(|row| indexed_relation(&mut context, row)).collect();
    context.dependency(Dependency::Derived { parent: rows[0], child: rows[1] }).unwrap();
    context.dependency(synthetic_transport(&context, rows[1], rows[2], 0)).unwrap();
    context.dependency(synthetic_transport(&context, rows[2], rows[3], 1)).unwrap();
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
        context.dependency(synthetic_transport(&context, rows[2], rows[4], 0)).unwrap();
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
    context.dependency(synthetic_transport(&context, rows[2], rows[4], 0)).unwrap();
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
            context.dependency(synthetic_transport(&context, parent, child, 0)).unwrap();
            context.bundle_link(parent, second).unwrap();
        }
        let before = context.bundle_visits;
        context.dependency(Dependency::Derived { parent: root, child }).unwrap();
        let edge_visits = context.bundle_visits - before;
        let before = context.bundle_visits;
        context.bundle_link(root, second).unwrap();
        let incidence_visits = context.bundle_visits - before;
        let before = context.bundle_visits;
        context.dependency(synthetic_transport(&context, child, late, 0)).unwrap();
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

#[test]
fn fresh_use_captures_context_only_views_and_preserves_shared_payloads() {
    let mut session = session_with_source("act E\nmy answer:[E] int = 1");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let original = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.iter()
        .position(|view| view.source_weight.is_some() && !view.allowed.is_empty()).unwrap() as u32;
    let tail = session.fresh_effect_at_level(2).unwrap();
    let view = session.candidate_copy_effect_view(original, Some(tail)).unwrap();
    let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].source_weight.unwrap();
    let row = session.fresh_value_at_level(2).unwrap();
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let key = BoundKey(value(row), Polarity::Positive, lower);
    let (occurrence, cause) = cause(&session, 0);
    session.candidate_restore_bound(value(row), Polarity::Positive, lower, &occurrence, &cause).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let prefix = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
    let shared = context.context(ContextExpr::Replay { lower: prefix, upper: prefix }).unwrap();
    let root = context.context(ContextExpr::Swap { input: shared }).unwrap();
    let parent = context.relation(bound_pair(key), shared).unwrap();
    context.attach(key, parent).unwrap();
    let second = context.relation(bound_pair(key), root).unwrap();
    context.attach(key, second).unwrap();
    let bundle = context.retain_bundle(AttachmentBundle { occurrence: occurrence.clone(), sets: Vec::new() }, false).unwrap();
    context.bundle_link(parent, bundle).unwrap();
    let graph = session.capture_candidate_graph(row, 0).unwrap();
    assert_eq!(graph.context_views.len(), 1);
    assert_eq!(graph.context_views[0].0, weight);
    assert!(graph.nodes.iter().all(|node| !matches!(node, candidate_scheme::Node::EffectOperand { .. })));
    assert!(graph.rows.iter().any(|row| row.key == candidate_scheme::RowKey::Effect(tail) && row.local));
    // This fixture keeps the captured graph outside the route. Release its
    // capture charge before starting an independent transaction, whose rollback
    // resets route scratch to zero.
    session.candidate_graph.as_mut().unwrap().scratch_bytes -= graph.bytes().unwrap();
    let template_bundles = state(&session).relation_bundles(parent).collect::<Vec<_>>();
    let before = state(&session).checkpoint();
    let before_views = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len();
    let before_rows = (session.value_levels.len(), session.effect_levels.len());
    let before_scratch = session.candidate_graph.as_ref().unwrap().scratch_bytes;
    let failed: Result<(), SolveAvailabilityError> = session.with_route_transaction(|session| {
        session.freshen_candidate_graph(&graph, 3, &occurrence, &cause)?;
        Err(exhausted())
    });
    assert!(failed.is_err());
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len(), before_views);
    assert_eq!((session.value_levels.len(), session.effect_levels.len()), before_rows);
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, before_scratch);
    let mut copied_weights = Vec::new();
    for _ in 0..2 {
        let before_views = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.len();
        let entry_scratch = session.candidate_graph.as_ref().unwrap().scratch_bytes;
        session.with_route_transaction(|session| {
            session.freshen_candidate_graph(&graph, 3, &occurrence, &cause)?;
            Ok(())
        }).unwrap();
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, entry_scratch);
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        assert_eq!(algebra.views.len(), before_views + 1);
        let copied_view = algebra.views.last().unwrap();
        assert_ne!(copied_view.tail, Some(tail));
        assert_eq!(copied_view.allowed, algebra.views[view as usize].allowed);
        let copied_weight = copied_view.source_weight.unwrap();
        assert_ne!(copied_weight, weight);
        copied_weights.push(copied_weight);
        let context = &algebra.context;
        let child = context.dependencies.iter().rev().find_map(|dependency| match dependency {
            Dependency::Transport { parent: p, child, use_origin, .. } if *p == parent && *use_origin != 0 => Some(*child),
            _ => None,
        }).unwrap();
        let renamed = context.relations[child.0 as usize].key.context;
        let ContextExpr::Replay { lower, upper } = context.contexts[renamed.0 as usize - 1] else { panic!("replay root") };
        assert_eq!(lower, upper);
        assert_eq!(context.contexts[lower.0 as usize - 1], ContextExpr::PrefixLeft { weight: copied_weight, input: IDENTITY });
        assert_eq!(context.relation_bundles(child).count(), 1);
        assert_ne!(context.relation_bundles(child).next().unwrap(), bundle);
        assert_eq!(context.relation_bundles(parent).collect::<Vec<_>>(), template_bundles);
    }
    assert_ne!(copied_weights[0], copied_weights[1]);
}

#[test]
fn fresh_use_keeps_filter_discharge_and_rejects_unowned_certificates() {
    let mut session = session_with_source("act E\nmy answer:[E] int = 1");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let weight = state(&session).weights.iter().position(|weight| !weight.allowed.is_empty()).map(|id| LocalWeightId(id as u32)).unwrap();
    let row = session.fresh_value_at_level(2).unwrap();
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let key = BoundKey(value(row), Polarity::Positive, lower);
    let (occurrence, cause) = cause(&session, 0);
    session.candidate_restore_bound(value(row), Polarity::Positive, lower, &occurrence, &cause).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let prefix = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
    let parent = context.relation(bound_pair(key), prefix).unwrap();
    context.attach(key, parent).unwrap();
    assert_eq!(context.relation_context(parent).unwrap(), prefix);
    // This fixture marks consumption explicitly; merely attaching an unchecked
    // filter to a Value bound supplies no authority to erase it.
    context.discharged.insert(parent);
    context.discharge_log.push(parent);
    assert_eq!(context.relation_context(parent).unwrap(), IDENTITY);
    let graph = session.capture_candidate_graph(row, 0).unwrap();
    assert!(graph.context_views.is_empty());
    session.with_route_transaction(|session| session.freshen_candidate_graph(&graph, 3, &occurrence, &cause).map(|_| ())).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let both = context.context(ContextExpr::BothFromRight { input: IDENTITY, certificate: EntryCertificateId(17) }).unwrap();
    let parent = context.relation(bound_pair(key), both).unwrap();
    context.attach(key, parent).unwrap();
    let before = context.checkpoint();
    let scratch = session.candidate_graph.as_ref().unwrap().scratch_bytes;
    assert!(session.capture_candidate_graph(row, 0).is_err());
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, scratch);
}

#[test]
fn fresh_rename_ledger_counts_map_and_traversal_together_on_failure_and_retry() {
    let mut context = detached_rename_state();
    let leaf = context.context(ContextExpr::PrefixLeft { weight: LocalWeightId(0), input: IDENTITY }).unwrap();
    let mut root = leaf;
    for _ in 0..128 {
        root = context.context(ContextExpr::Replay { lower: root, upper: leaf }).unwrap();
    }
    let unsupported = context.context(ContextExpr::BothFromRight { input: root, certificate: EntryCertificateId(17) }).unwrap();
    let weights = HashMap::from([(LocalWeightId(0), LocalWeightId(1))]);
    let checkpoint = context.checkpoint();
    let entry = 19;
    let mut scratch = entry;
    let mut peak = entry;
    let mut remap = HashMap::new();
    assert!(context.rename_fresh_contexts(&[unsupported], &weights, &mut remap, &mut scratch, &mut peak).is_err());
    assert_eq!(context.checkpoint(), checkpoint);
    assert!(remap.is_empty());
    let retained_map = remap.capacity() * std::mem::size_of::<(ContextId, ContextId)>();
    assert_eq!(scratch, entry + retained_map);
    // Verified nodes and the map coexist at their largest capacities before
    // the unsupported certificate aborts this postorder walk.
    assert!(peak >= scratch + 130 * std::mem::size_of::<ContextId>());
    context.rename_fresh_contexts(&[root], &weights, &mut remap, &mut scratch, &mut peak).unwrap();
    assert_eq!(remap.len(), 130);
    let retained_map = remap.capacity() * std::mem::size_of::<(ContextId, ContextId)>();
    assert_eq!(scratch, entry + retained_map);
    assert!(peak >= scratch + remap.len() * std::mem::size_of::<ContextId>());
    drop(remap);
    scratch -= retained_map;
    assert_eq!(scratch, entry);
}


#[test]
fn inferred_entry_origin_distinguishes_written_function_interface() {
    let mut session = session_with_source("my apply (f:int -> int) = f 1");
    let action = session.batch.candidate_source.schedules.values()
        .flat_map(|actions| actions.iter())
        .find(|action| matches!(action, candidate_source::Action::FormalAnnotation { .. }))
        .unwrap().clone();
    let candidate_source::Action::FormalAnnotation { annotation, parameter, occurrence, scope } = action else { unreachable!() };
    session.with_route_transaction(|session|
        session.candidate_formal_annotation(&annotation, parameter, &occurrence, &scope)
    ).unwrap();
    assert!(state(&session).inferred_entries.is_empty(), "written Function ports grant no inferred-entry origin");
    let recipe = session.batch.lambda_recipes[0].clone();
    session.with_route_transaction(|session| session.admit_lambda_fact(&recipe)).unwrap();
    let origins = &state(&session).inferred_entries;
    assert_eq!(origins.len(), 1);
    let origin = &origins[0];
    assert_eq!(origin.lambda, recipe.occurrence);
    assert_eq!(origin.occurrence, ConstraintOccurrenceId::new(recipe.occurrence.clone(), 3));
    assert_eq!(origin.cause, CauseId::for_occurrence(origin.occurrence.clone()));
    assert_ne!(origin.entry, origin.returned);
    let bindings: Vec<_> = state(&session).origins.iter()
        .filter(|binding| binding.inferred_entry == Some(origin.id)).collect();
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].occurrence, origin.occurrence);
    assert_eq!(state(&session).relations[bindings[0].relation.0 as usize].key.pair,
        TypedPairKey::Effect { lower: origin.entry, upper: origin.returned });
    assert!(state(&session).origins.iter().filter(|binding| binding.occurrence.local_slot() == 4)
        .all(|binding| binding.inferred_entry.is_none()));
    let edge = session.store.provenance().iter()
        .find(|edge| edge.cause() == &origin.cause).unwrap();
    let fact = session.store.facts().iter().find(|fact| fact.id() == edge.fact()).unwrap();
    assert_eq!(session.effect_endpoint(fact.lower(), Polarity::Positive), origin.entry);
    assert_eq!(session.effect_endpoint(fact.upper(), Polarity::Negative), origin.returned);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn inferred_entry_origin_unrelated_slot_three_uses_no_handle() {
    let mut session = session_with_source("my ignore x = ()\nmy literal = 1");
    let recipe = session.batch.lambda_recipes[0].clone();
    session
        .with_route_transaction(|session| session.admit_lambda_fact(&recipe))
        .unwrap();
    let index = session
        .batch
        .occurrences()
        .iter()
        .position(|occurrence| {
            occurrence.id.local_slot() == 3 && occurrence.id.occurrence() != &recipe.occurrence
        })
        .expect("unrelated literal slot-three constraint");
    let occurrence = session.batch.occurrences()[index].id.clone();
    let before = state(&session).origins.len();
    session
        .with_route_transaction(|session| session.admit_collected_fact(index))
        .unwrap();
    let bindings = &state(&session).origins[before..];
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].occurrence, occurrence);
    assert!(bindings[0].inferred_entry.is_none());
    assert_eq!(state(&session).inferred_entries.len(), 1);
    assert_eq!(
        state(&session).bytes().unwrap(),
        state(&session).enumerated_bytes()
    );
}

#[test]
fn inferred_entry_origin_route_rollback_restores_and_retry_retains_once() {
    let mut session = session_with_source("my ignore x = ()");
    let recipe = session.batch.lambda_recipes[0].clone();
    let before = state(&session).checkpoint();
    let mut attempted = None;
    assert_eq!(session.with_route_transaction(|session| {
        session.admit_lambda_fact(&recipe)?;
        attempted = Some(state(session).inferred_entries.last().unwrap().clone());
        assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
        Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
    }), Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(state(&session).checkpoint(), before);
    assert!(state(&session).inferred_entries.is_empty());
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(|session| session.admit_lambda_fact(&recipe)).unwrap();
    assert_eq!(state(&session).inferred_entries.as_slice(), &[attempted.unwrap()]);
    let origin = &state(&session).inferred_entries[0];
    let bindings: Vec<_> = state(&session)
        .origins
        .iter()
        .filter(|binding| binding.inferred_entry == Some(origin.id))
        .collect();
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].occurrence, origin.occurrence);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}


#[test]
fn function_port_context_uses_exact_post_check_parent_and_child_local_order() {
    let mut session = session();
    let effect = session.batch.hir.source_effect_declarations()[0].id.clone();
    let view = session.candidate_effect_view(empty_bundle_owner(&session), effect.declaration.clone(), vec![effect], None).unwrap();
    let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize].closed_weight.unwrap();
    let parent_task = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
    });
    let effect_task = LiveConstraintTask::Effect(EffectEndpointKey::BottomPositive, EffectEndpointKey::Allowance(view));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let first_context = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
    let second_context = context.context(ContextExpr::WithoutLeftFilter { input: first_context }).unwrap();
    let first = context.relation(task_pair(parent_task), first_context).unwrap();
    let second = context.relation(task_pair(parent_task), second_context).unwrap();
    let before = state(&session).checkpoint();
    let mut attempts = Vec::new();
    for rollback in [true, false] {
        let result = session.with_route_transaction(|session| {
            let mut children = Vec::new();
            for (parent, inherited) in [(first, first_context), (second, second_context)] {
                let algebra = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
                algebra.processing = Some(task_pair(parent_task));
                algebra.context.processing = Some(parent);
                for field in [FunctionField::Argument, FunctionField::ArgumentEffect, FunctionField::ResultEffect, FunctionField::Result] {
                    let argument = matches!(field, FunctionField::Argument | FunctionField::ArgumentEffect);
                    let operation = if argument { FunctionPortOperation::Swap } else { FunctionPortOperation::Preserve };
                    for child_task in [parent_task, effect_task] {
                        let child = session.candidate_function_port_admit(child_task, field)?.unwrap();
                        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                        let expected = if argument { context.context(ContextExpr::Swap { input: inherited })? } else { inherited };
                        let expected = if matches!(child_task, LiveConstraintTask::Effect(..)) {
                            context.context(ContextExpr::PrefixLeft { weight, input: expected })?
                        } else { expected };
                        assert_eq!(context.relations[child.0 as usize].key.context, expected);
                        assert!(context.dependency_keys.contains(&Dependency::Derived { child, parent }));
                        assert!(context.dependency_keys.contains(&Dependency::FunctionPort { child, parent, field, operation }));
                        children.push(child);
                        if parent == first && !argument && child_task == effect_task {
                            // Result ports preserve the parent's zero-word filter;
                            // the local allowance checks it and discharges both prefixes.
                            assert_eq!(session.candidate_context_execute(child_task, Some(child)), Ok(true));
                            let context = state(session);
                            assert_eq!(context.relations[child.0 as usize].key.context, expected);
                            assert!(context.discharged.contains(&child));
                            assert!(context.discharge_log.contains(&child));
                            assert_eq!(context.post_check_context(child), IDENTITY);
                            assert!(!context.discharge_residuals.contains_key(&child));
                            assert!(!context.discharged.contains(&parent));
                        } else {
                            assert_eq!(session.candidate_context_execute(child_task, Some(child)), Err(exhausted()));
                        }
                    }
                }
            }
            assert!(children[..8].iter().zip(&children[8..]).all(|(first, second)| first != second));
            if rollback { attempts = children; Err(exhausted()) } else { assert_eq!(children, attempts); Ok(()) }
        });
        if rollback {
            assert_eq!(result, Err(exhausted()));
            assert_eq!(state(&session).checkpoint(), before);
        } else { result.unwrap(); }
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn function_port_context_simplifies_only_post_check_identity_and_keeps_incidence() {
    let mut session = session();
    let task = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
    });
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let nonidentity = context.context(ContextExpr::WithoutLeftFilter { input: IDENTITY }).unwrap();
    let parent = context.relation(task_pair(task), nonidentity).unwrap();
    context.discharged.insert(parent);
    context.processing = Some(parent);
    let nodes = state(&session).contexts.len();
    for field in [FunctionField::Argument, FunctionField::ArgumentEffect, FunctionField::ResultEffect, FunctionField::Result] {
        let child = session.candidate_function_port_admit(task, field).unwrap().unwrap();
        let operation = if matches!(field, FunctionField::Argument | FunctionField::ArgumentEffect) {
            FunctionPortOperation::Swap
        } else { FunctionPortOperation::Preserve };
        assert_eq!(state(&session).relations[child.0 as usize].key.context, IDENTITY);
        assert!(state(&session).dependency_keys.contains(&Dependency::FunctionPort { child, parent, field, operation }));
    }
    assert_eq!(state(&session).contexts.len(), nodes);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn function_port_identity_incidence_changes_without_new_relations_or_intrusion_generation() {
    let mut session = session();
    let parent_task = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
    });
    let child_task = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::UnitPositive, upper: ValueEndpointKey::TopNegative,
    });
    let algebra = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
    let parent = algebra.context.relation(task_pair(parent_task), IDENTITY).unwrap();
    let child = algebra.context.relation(task_pair(child_task), IDENTITY).unwrap();
    assert_ne!(parent, child);
    // Production Function dispatch retains Derived before FunctionPort. Its
    // existing relation and diagnostic edge must not hide new typed incidence.
    algebra.context.dependency(Dependency::Derived { parent, child }).unwrap();
    algebra.processing = Some(task_pair(parent_task));
    algebra.context.processing = Some(parent);
    let before = state(&session).checkpoint();
    let generation = session.candidate_graph.as_ref().unwrap().intrusion.generation;
    let port = Dependency::FunctionPort {
        parent, child, field: FunctionField::Argument, operation: FunctionPortOperation::Swap,
    };
    let roots = [parent];
    {
        let input = state(&session).retained_input(&roots, &[], &[]).unwrap();
        assert_eq!(input.evidence.relations().count(), 2);
        assert_eq!(input.evidence.dependencies().count(), 1);
        let InputCompleteness::Incomplete(gaps) = &input.completeness else {
            panic!("borrowed construction evidence cannot certify readiness");
        };
        assert!(!gaps.contains(&InputGap::InertOperation));
    }
    for rollback in [true, false] {
        let result = session.with_route_transaction(|session| {
            assert_eq!(session.candidate_function_port_admit(child_task, FunctionField::Argument)?, Some(child));
            let context = state(session);
            assert_eq!(context.relations.len(), before.relations);
            assert_eq!(context.contexts.len(), before.contexts);
            assert_eq!(context.edge_log.len(), before.edges);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.generation, generation);
            assert_eq!(context.dependencies.len(), before.dependencies + 1);
            assert_eq!(context.dependencies.last(), Some(&port));
            assert!(context.dependency_keys.contains(&port));
            let input = context.retained_input(&roots, &[], &[])?;
            assert_eq!(input.evidence.relations().count(), 2);
            assert_eq!(input.evidence.dependencies().count(), 2);
            let InputCompleteness::Incomplete(gaps) = &input.completeness else {
                panic!("Function-port incidence remains incomplete construction evidence");
            };
            assert!(gaps.contains(&InputGap::InertOperation));
            drop(input);
            if rollback { return Err(exhausted()); }
            let after = state(session).checkpoint();
            assert_eq!(session.candidate_function_port_admit(child_task, FunctionField::Argument)?, Some(child));
            assert_eq!(state(session).checkpoint(), after, "duplicate admission retains the port once");
            Ok(())
        });
        if rollback {
            assert_eq!(result, Err(exhausted()));
            assert_eq!(state(&session).checkpoint(), before);
            assert!(!state(&session).dependency_keys.contains(&port));
            assert_eq!(state(&session).dependencies, vec![Dependency::Derived { parent, child }]);
            assert!(state(&session).edge_keys.contains(&(parent, child)));
        } else { result.unwrap(); }
        assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.generation, generation);
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn function_port_incidence_preserves_exact_relations_and_route_retry() {
    let mut session = session_with_source("my answer x:int -> int = x");
    let owner = empty_bundle_owner(&session);
    let before = state(&session).checkpoint();
    let mut attempted = Vec::new();
    assert_eq!(
        session.with_route_transaction(|session| {
            session.execute_candidate_source_root(&owner)?;
            attempted = state(session)
                .dependencies
                .iter()
                .copied()
                .filter(|dependency| matches!(dependency, Dependency::FunctionPort { .. }))
                .collect();
            assert!(!attempted.is_empty());
            assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
            Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
        }),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(state(&session).checkpoint(), before);
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    let retained: Vec<_> = context
        .dependencies
        .iter()
        .copied()
        .filter(|dependency| matches!(dependency, Dependency::FunctionPort { .. }))
        .collect();
    assert_eq!(retained, attempted);
    for ports in retained.chunks_exact(4) {
        // Front insertion reverses construction order; execution order is the
        // established Argument, ArgumentEffect, ResultEffect, Result order.
        let mut parent_id = None;
        for (dependency, field, operation) in [
            (
                ports[0],
                FunctionField::Result,
                FunctionPortOperation::Preserve,
            ),
            (
                ports[1],
                FunctionField::ResultEffect,
                FunctionPortOperation::Preserve,
            ),
            (
                ports[2],
                FunctionField::ArgumentEffect,
                FunctionPortOperation::Swap,
            ),
            (
                ports[3],
                FunctionField::Argument,
                FunctionPortOperation::Swap,
            ),
        ] {
            let Dependency::FunctionPort {
                child,
                parent,
                field: actual_field,
                operation: actual_operation,
            } = dependency
            else {
                unreachable!()
            };
            assert_eq!((actual_field, actual_operation), (field, operation));
            assert_eq!(*parent_id.get_or_insert(parent), parent);
            assert!(
                context
                    .dependency_keys
                    .contains(&Dependency::Derived { child, parent })
            );
            let TypedPairKey::Value(pair) = context.relations[parent.0 as usize].key.pair else {
                unreachable!()
            };
            let lower =
                InferenceSession::positive_function_children(&session.store, pair.lower).unwrap();
            let upper =
                InferenceSession::negative_function_children(&session.store, pair.upper).unwrap();
            let expected = match field {
                FunctionField::Argument => TypedPairKey::Value(CanonicalValuePairKey {
                    lower: session.value_endpoint(upper.0, Polarity::Positive),
                    upper: session.value_endpoint(lower.0, Polarity::Negative),
                }),
                FunctionField::ArgumentEffect => TypedPairKey::Effect {
                    lower: session.effect_endpoint(upper.1, Polarity::Positive),
                    upper: session.effect_endpoint(lower.1, Polarity::Negative),
                },
                FunctionField::ResultEffect => TypedPairKey::Effect {
                    lower: session.effect_endpoint(lower.2, Polarity::Positive),
                    upper: session.effect_endpoint(upper.2, Polarity::Negative),
                },
                FunctionField::Result => TypedPairKey::Value(CanonicalValuePairKey {
                    lower: session.value_endpoint(lower.3, Polarity::Positive),
                    upper: session.value_endpoint(upper.3, Polarity::Negative),
                }),
            };
            let admitted = context.relations[child.0 as usize].key;
            assert_eq!(admitted.pair, session.candidate_context_pair(expected));
            assert_eq!(admitted.context, IDENTITY);
        }
    }
    assert_eq!(retained.len() % 4, 0);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn function_port_incidence_keeps_written_argument_filter_child_local() {
    let mut session = session_with_source("act io\nmy bridge (consume:([io] int) -> ()) = consume");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    assert!(context.dependencies.iter().any(|dependency| matches!(
        dependency,
        Dependency::FunctionPort {
            field: FunctionField::ArgumentEffect,
            operation: FunctionPortOperation::Swap,
            ..
        }
    )));
    for dependency in &context.dependencies {
        if let Dependency::FunctionPort { child, .. } = *dependency {
            assert_eq!(context.relations[child.0 as usize].key.context, IDENTITY);
        }
    }
    assert!(
        context
            .contexts
            .iter()
            .any(|expr| matches!(expr, ContextExpr::PrefixLeft { .. }))
    );
    assert!(!context.contexts.iter().any(|expr| matches!(
        expr,
        ContextExpr::Swap { .. } | ContextExpr::BothFromRight { .. }
    )));
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn retained_input_closes_both_directions_and_preserves_ports_replay_and_sharing() {
    let mut context = State::default();
    let parent = context.relation(task_pair(task(0, 1)), IDENTITY).unwrap();
    let child = context.relation(task_pair(task(2, 3)), IDENTITY).unwrap();
    for field in [FunctionField::Argument, FunctionField::ArgumentEffect, FunctionField::ResultEffect, FunctionField::Result] {
        let operation = match field {
            FunctionField::Argument | FunctionField::ArgumentEffect => FunctionPortOperation::Swap,
            _ => FunctionPortOperation::Preserve,
        };
        context.dependency(Dependency::FunctionPort { parent, child, field, operation }).unwrap();
    }
    let shared = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let distinct = context.context(ContextExpr::WithoutLeftFilter { input: shared }).unwrap();
    let replay = context.context(ContextExpr::Replay { lower: shared, upper: distinct }).unwrap();
    let downstream = context.relation(task_pair(task(4, 5)), replay).unwrap();
    let lower_input = BoundKey(value(2), Polarity::Negative, value(3));
    let upper_input = BoundKey(value(3), Polarity::Negative, value(4));
    context.attach(lower_input, child).unwrap();
    context.attach(upper_input, parent).unwrap();
    context.dependency(Dependency::Replay { child: downstream, lower: child, upper: parent, lower_input, upper_input }).unwrap();
    let roots = [child];
    let input = context.retained_input(&roots, &[], &[]).unwrap();
    assert_eq!(input.roots, roots);
    assert_eq!(input.evidence.relations().count(), 3);
    assert_eq!(input.evidence.dependencies().count(), 5);
    assert_eq!(input.evidence.contexts().count(), 3);
    assert!(input.evidence.dependencies().any(|d| *d == Dependency::Replay { child: downstream, lower: child, upper: parent, lower_input, upper_input }));
    assert!(input.evidence.contexts().any(|(id, expression)| id == replay && *expression == ContextExpr::Replay { lower: shared, upper: distinct }));
    let InputCompleteness::Incomplete(gaps) = &input.completeness else { panic!("inert input cannot certify readiness"); };
    assert!(gaps.contains(&InputGap::InertOperation));
    assert!(gaps.contains(&InputGap::ProducerReadinessUnavailable));
    assert!(gaps.contains(&InputGap::DependentObservationsUnavailable));
    assert_eq!(input.owned_bytes().unwrap(), input.evidence.relations.capacity() + input.evidence.contexts.capacity()
        + input.evidence.weights.capacity() + input.evidence.selected_views.capacity() + gaps.capacity() * std::mem::size_of::<InputGap>());
}

#[test]
fn retained_input_transport_reasons_and_missing_evidence_survive_rollback_retry() {
    let mut context = State::default();
    let parent = context.relation(task_pair(task(0, 1)), IDENTITY).unwrap();
    let child = context.relation(task_pair(task(2, 1)), IDENTITY).unwrap();
    let from = BoundKey(value(0), Polarity::Negative, value(1));
    let to = BoundKey(value(2), Polarity::Negative, value(1));
    let parents = [candidate_intrusion::Parent { copy: candidate_scheme::RowKey::Value(0),
        parent: candidate_scheme::RowKey::Value(2), polarity: Polarity::Positive, target: 0 }];
    context.attach(from, parent).unwrap();
    context.attach(to, child).unwrap();
    let checkpoint = context.checkpoint();
    for _ in 0..2 {
        for reason in [TransportReason::Extrusion { operation: value(0), polarity: Polarity::Positive, target_level: 0 },
            TransportReason::ParentCopy { parent_index: 0 }, TransportReason::EqualityCanonicalization, TransportReason::FreshUse] {
            context.dependency(Dependency::Transport { parent, child, use_origin: 1,
                witness: Some(TransportWitness { from, to, reason }) }).unwrap();
        }
        context.dependency(Dependency::Transport { parent, child, use_origin: 2, witness: None }).unwrap();
        let roots = [parent];
        let input = context.retained_input(&roots, &[], &parents).unwrap();
        assert_eq!(input.evidence.dependencies().count(), 5);
        assert_eq!(input.evidence.parents[0].copy, candidate_scheme::RowKey::Value(0));
        assert!(context.edges.is_empty(), "transport evidence creates no solver edge");
        let InputCompleteness::Incomplete(gaps) = &input.completeness else { panic!("missing witness must stay incomplete"); };
        assert!(gaps.contains(&InputGap::MissingTransportWitness));
        assert!(!gaps.contains(&InputGap::MissingReference));
        assert!(!gaps.contains(&InputGap::InconsistentReference));
        drop(input);
        context.rollback(checkpoint);
        assert_eq!(context.checkpoint(), checkpoint);
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
    }
    let roots = [RelationId(u32::MAX)];
    let input = context.retained_input(&roots, &[], &parents).unwrap();
    let InputCompleteness::Incomplete(gaps) = input.completeness else { panic!("missing root cannot be complete"); };
    assert!(gaps.contains(&InputGap::MissingReference));
}

fn retained_view_fixture() -> (State, Vec<candidate_effect::View>) {
    let mut session = session_with_source("act E:\n    our emit: () -> int\n\nmy answer:[E] int = E::emit()");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let original = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views.iter()
        .find(|view| !view.allowed.is_empty()).unwrap();
    let mut context = State::default();
    let weight = context.source_weight(0, &original.owner, &original.position, &original.allowed, None).unwrap();
    let view = candidate_effect::View { closed_weight: Some(weight), source_weight: None,
        provenance: candidate_effect::ViewOrigin::Annotation, owner: original.owner.clone(),
        position: original.position.clone(), allowed: original.allowed.clone(), tail: None };
    (context, vec![view])
}

#[test]
fn retained_input_support_root_collects_view_and_registered_obligations_before_expansion() {
    let (mut context, views) = retained_view_fixture();
    let root = context.relation(TypedPairKey::Effect { lower: EffectEndpointKey::Support(0), upper: EffectEndpointKey::EffectRow(0) }, IDENTITY).unwrap();
    let registered = context.relation(TypedPairKey::Effect { lower: EffectEndpointKey::EffectRow(1), upper: EffectEndpointKey::Allowance(0) }, IDENTITY).unwrap();
    context.attach(BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(1)), Polarity::Negative,
        ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(0))), registered).unwrap();
    let downstream = context.relation(task_pair(task(2, 3)), IDENTITY).unwrap();
    context.dependency(Dependency::Derived { parent: registered, child: downstream }).unwrap();
    let roots = [root];
    let input = context.retained_input(&roots, &views, &[]).unwrap();
    assert_eq!(input.evidence.filter_views().count(), 1);
    assert_eq!(input.evidence.weights().count(), 1);
    assert!(input.evidence.includes(registered));
    assert!(input.evidence.includes(downstream));
    assert_eq!(input.evidence.inferred_entries().count(), 0);
    assert_eq!(input.evidence.bundles().count(), 0);
    let InputCompleteness::Incomplete(gaps) = input.completeness else { panic!("readiness unavailable"); };
    assert!(!gaps.contains(&InputGap::MissingReference));
}

#[test]
fn retained_input_missing_support_view_and_out_of_range_member_remain_incomplete() {
    let (mut context, views) = retained_view_fixture();
    for (lower, expected) in [(EffectEndpointKey::Support(u32::MAX), InputGap::MissingReference),
        (EffectEndpointKey::AnnotationMember(0, views[0].allowed.len() as u32), InputGap::InconsistentReference)] {
        let root = context.relation(TypedPairKey::Effect { lower, upper: EffectEndpointKey::EffectRow(0) }, IDENTITY).unwrap();
        let roots = [root];
        let input = context.retained_input(&roots, &views, &[]).unwrap();
        let InputCompleteness::Incomplete(gaps) = input.completeness else { panic!("invalid operand cannot be complete"); };
        assert!(gaps.contains(&expected));
    }
}

#[test]
fn retained_input_rejects_missing_bound_keys_and_mismatched_transport_parent_incidence() {
    let mut context = State::default();
    let parent = context.relation(task_pair(task(0, 1)), IDENTITY).unwrap();
    let other = context.relation(task_pair(task(4, 1)), IDENTITY).unwrap();
    let child = context.relation(task_pair(task(2, 1)), IDENTITY).unwrap();
    let from = BoundKey(value(0), Polarity::Negative, value(1));
    let to = BoundKey(value(2), Polarity::Negative, value(1));
    context.attach(from, parent).unwrap();
    context.attach(to, child).unwrap();
    let checkpoint = context.checkpoint();
    for (recorded_parent, source, expected) in [(parent, BoundKey(value(99), Polarity::Negative, value(1)), InputGap::MissingReference),
        (other, from, InputGap::InconsistentReference)] {
        context.dependency(Dependency::Transport { parent: recorded_parent, child, use_origin: 1,
            witness: Some(TransportWitness { from: source, to, reason: TransportReason::FreshUse }) }).unwrap();
        let roots = [child];
        let input = context.retained_input(&roots, &[], &[]).unwrap();
        let InputCompleteness::Incomplete(gaps) = input.completeness else { panic!("invalid transport cannot be complete"); };
        assert!(gaps.contains(&expected));
        context.rollback(checkpoint);
    }
    context.dependency(Dependency::Transport { parent, child, use_origin: 0,
        witness: Some(TransportWitness { from, to, reason: TransportReason::ParentCopy { parent_index: 0 } }) }).unwrap();
    let parents = [candidate_intrusion::Parent { copy: candidate_scheme::RowKey::Value(99),
        parent: candidate_scheme::RowKey::Value(2), polarity: Polarity::Positive, target: 0 }];
    let roots = [child];
    let input = context.retained_input(&roots, &[], &parents).unwrap();
    let InputCompleteness::Incomplete(gaps) = input.completeness else { panic!("unknown original-row correspondence cannot be complete"); };
    assert!(gaps.contains(&InputGap::TransportAuthenticationUnavailable));
    assert!(context.edges.is_empty());
}


#[test]
fn queued_relation_equality_transport_retains_context_ancestry_and_retry() {
    for effect in [false, true] {
      for context_case in 0..4 {
        let mut session = session();
        let (occurrence, cause) = cause(&session, 0);
        let parent = if effect {
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(session.fresh_effect_at_level(2).unwrap()))
        } else { value(session.fresh_value_at_level(2).unwrap()) };
        if !effect {
            session.candidate_restore_bound(parent, Polarity::Negative, ExtrusionEndpoint::Value(ValueEndpointKey::UnitNegative), &occurrence, &cause).unwrap();
        }
        let copy = session.candidate_extrude(parent, Polarity::Positive, 0).unwrap();
        let raw = match copy {
            ExtrusionEndpoint::Value(upper) => LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::IntPositive, upper }),
            ExtrusionEndpoint::Effect(upper) => LiveConstraintTask::Effect(match parent { ExtrusionEndpoint::Effect(lower) => lower, _ => unreachable!() }, upper),
        };
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let residual = if context_case == 0 { IDENTITY } else { context.context(ContextExpr::Swap { input: IDENTITY }).unwrap() };
        let retained = if context_case == 3 { context.context(ContextExpr::Replay { lower: residual, upper: residual }).unwrap() } else { residual };
        let original = context.relation(task_pair(raw), retained).unwrap();
        if context_case >= 2 {
            context.discharged.insert(original);
            context.discharge_log.push(original);
            if context_case == 3 { context.discharge_residuals.insert(original, residual); }
        }
        let expected = context.post_check_context(original);
        let original_key = state(&session).relations[original.0 as usize].key;
        assert_eq!(session.candidate_context_transport_task(raw, Some(original)).unwrap(), Some(original));
        let before = state(&session).checkpoint();
        let mut first = None;
        for rollback in [true, false] {
            let result = session.with_route_transaction(|session| {
                session.candidate_restore_bound(copy, Polarity::Negative, parent, &occurrence, &cause)?;
                session.settle_candidate_intrusion(None)?;
                assert_eq!(session.canonical_extrusion(copy), parent);
                let child = session.candidate_context_transport_task(raw, Some(original))?.unwrap();
                assert_ne!(child, original);
                assert_eq!(state(session).relations[original.0 as usize].key, original_key);
                assert_eq!(state(session).relations[child.0 as usize].key.context, expected);
                assert!(state(session).dependency_keys.contains(&Dependency::Derived { parent: original, child }));
                session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(child);
                assert_eq!(session.candidate_context_execute(raw, Some(original))?, false);
                assert_eq!(state(session).processing, Some(child));
                if effect {
                    assert_eq!(session.candidate_context_transport_task(raw, Some(child))?, Some(child));
                } else {
                    session.constrain_live_item(TypedWorkItem { task: raw, relation: Some(original) }, &occurrence, &cause)?;
                    let canonical = session.candidate_context_pair(task_pair(raw));
                    assert_eq!(state(session).relations[child.0 as usize].key.pair, canonical);
                    assert!(session.typed_pairs.contains_key(&task_pair(raw)), "raw diagnostic memo remains retained");
                    assert!(session.errors.iter().any(|error| error.occurrence == occurrence && error.cause == cause));
                    assert!(session.candidate_graph.as_ref().unwrap().intrusion.completed.contains_key(&child), "canonical continuation completes the transported relation");
                }
                if rollback { first = Some(child); Err(exhausted()) }
                else { assert_eq!(first, Some(child)); Ok(()) }
            });
            if rollback { assert_eq!(result, Err(exhausted())); assert_eq!(state(&session).checkpoint(), before); }
            else { result.unwrap(); }
        }
      }
    }
}

#[test]
fn local_annotation_bridge_queued_endpoints_follow_parent_copy_equality() {
    let mut session = session_with_source("act E\nmy left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int): ((int -> [E, 't] int) -> ['x] int) -> [E, 'x] int = { my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb }; bridge }");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
}
