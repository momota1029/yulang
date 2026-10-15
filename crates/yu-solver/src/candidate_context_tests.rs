use super::*;
use yu_hir::shadow::lower_module_with_local_source;

// Qualify real row copies with an actual source call occurrence, independently
// of the type bounds used by these transport fixtures.
fn source_extrude(session: &mut InferenceSession, parent: ExtrusionEndpoint, polarity: Polarity) -> ExtrusionEndpoint {
    let checking = session.batch.candidate_source.references.checking.keys().next().unwrap().clone();
    let task = match parent {
        ExtrusionEndpoint::Value(row) => LiveConstraintTask::Value(CanonicalValuePairKey { lower: row, upper: row }),
        ExtrusionEndpoint::Effect(row) => LiveConstraintTask::Effect(row, row),
    };
    let relation = session.candidate_context_seed(task, &checking, None).unwrap().unwrap();
    let previous = session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing.replace(relation);
    let copy = session.candidate_extrude(parent, polarity, 0).unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous;
    copy
}

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

#[test]
fn omitted_formal_structural_incidence_survives_source_capture_without_effect_authority() {
    let mut early = session_with_source("my relay cb = cb");
    let owner = empty_bundle_owner(&early);
    early.execute_candidate_source_root(&owner).unwrap();
    let origin = state(&early).origins.iter().find(|origin| origin.formal.is_some()).unwrap();
    let construction = origin.formal.as_ref().unwrap();
    assert_eq!(state(&early).origins.iter().filter(|other| other.occurrence == origin.occurrence).count(), 1,
        "owning Lambda admission seeds exactly one origin");
    assert_eq!(construction.source.lambda, *origin.occurrence.occurrence());
    assert_eq!(construction.source.owner, SourceRootId::Definition(owner.clone()));
    assert!(early.batch.candidate_source.omitted_formals.contains_key(&construction.source.lambda));
    let ValueEndpointKey::ValueRow(domain) = construction.domain else { panic!("omitted formal stays an unknown row"); };
    let (original_child, _, _, _) = InferenceSession::positive_function_children(&early.store, construction.function).unwrap();
    assert_eq!(original_child, construction.domain_child);
    let TermView::LiveVariable(view) = early.store.term_view(original_child).unwrap() else { panic!("raw constructed child is the original formal"); };
    assert_eq!(view.ordinal(), domain);
    assert_eq!(view.kind(), ComponentKind::Value);
    assert_eq!(view.polarity(), Polarity::Negative);
    let entry_occurrence = ConstraintOccurrenceId::new(construction.source.lambda.clone(), 3);
    let entry_origins: Vec<_> = state(&early).origins.iter().filter(|other| other.occurrence == entry_occurrence).collect();
    assert_eq!(entry_origins.len(), 1);
    assert!(entry_origins[0].inferred_entry.is_some(), "single seeding preserves the independent inferred-entry fact");
    assert!(early.bounds[domain as usize].exact_non_variable_lowers.is_empty());
    assert!(early.bounds[domain as usize].exact_non_variable_uppers.is_empty());
    assert!(matches!(&construction.source.scope, candidate_effect::AnnotationScope::Definition(scope) if *scope == owner));
    let local_source = early.batch.hir.local_source(&owner).unwrap().unwrap();
    let parameter = local_source.expressions().iter().find_map(|expression| {
        if expression.occurrence == construction.source.lambda {
            if let yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. } = &expression.form { return Some(parameter); }
        }
        None
    }).unwrap();
    assert!(parameter.annotation.is_none());
    assert_eq!(parameter.id, construction.source.formal);
    assert_eq!(parameter.source, construction.source.position);
    assert_eq!(state(&early).relations[origin.relation.0 as usize].key.context, IDENTITY);

    let mut session = session_with_source("my outer = { my relay cb = cb; my identity x = x; my first = relay identity; relay identity }");
    let owner = empty_bundle_owner(&session);
    session.execute_candidate_source_root(&owner).unwrap();
    let arguments: Vec<_> = state(&session).dependencies.iter().filter_map(|dependency| {
        if let Dependency::FunctionPort { child, field: FunctionField::Argument, .. } = *dependency { Some(child) } else { None }
    }).collect();
    let incidence = arguments.iter().find_map(|&argument| session.candidate_formal_argument_incidence(argument))
        .expect("source local capture/fresh use authenticates its Argument child");
    assert_eq!(incidence.construction.source.owner, SourceRootId::Definition(owner.clone()));
    assert_ne!(incidence.source_relation, incidence.transport_relation);
    let handoff = incidence.name_handoff.expect("local use retains the source Name handoff");
    let link = incidence.name_link.expect("handoff retains the Name publication input");
    assert!(state(&session).dependencies.iter().any(|dependency| matches!(*dependency,
        Dependency::Replay { child, lower, upper, .. }
            if child == handoff && lower == incidence.transport_relation && upper == link)));
    assert!(state(&session).dependencies.iter().any(|dependency| matches!(*dependency,
        Dependency::Replay { child, lower, .. } if child == incidence.comparison
            && state(&session).dependencies.contains(&Dependency::Derived { child: lower, parent: handoff }))));
    let TypedPairKey::Value(comparison) = state(&session).relations[incidence.comparison.0 as usize].key.pair else { unreachable!() };
    let (fresh_child, _, _, _) = InferenceSession::positive_function_children(&session.store, comparison.lower).unwrap();
    assert_eq!(session.value_endpoint(fresh_child, Polarity::Negative), session.canonical_value(incidence.domain),
        "authentic Argument incidence uses the reconstructed child under current equality");
    assert_eq!(state(&session).relations[incidence.argument.0 as usize].key.context, IDENTITY);
    let pair = state(&session).relations[incidence.argument.0 as usize].key.pair;
    let lambda = incidence.construction.source.lambda.clone();
    // Equal endpoints admitted as a separate source relation do not acquire
    // the actual comparison's FunctionPort/Replay/FreshUse derivation.
    let unrelated = session.candidate_context_seed(task_pair_to_task(pair), &ConstraintOccurrenceId::new(lambda, 99), None).unwrap().unwrap();
    assert!(session.candidate_formal_argument_incidence(unrelated).is_none());
}
#[test]
fn omitted_formal_source_domains_correlate_with_retained_extrusion_pairs() {
    let mut session = session_with_source("my outer cb = { my inner x = cb x; inner }");
    let owner = empty_bundle_owner(&session);
    let initial_levels = session.value_levels.clone();
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    let formals: Vec<_> = context.origins.iter().filter_map(|origin| {
        let construction = origin.formal.as_ref()?;
        let ValueEndpointKey::ValueRow(domain) = construction.domain else { panic!("raw omitted domain"); };
        let recipe = session.batch.lambda_recipes.iter()
            .find(|recipe| recipe.occurrence == construction.source.lambda).unwrap();
        assert_eq!(domain, session.parameter_live_base + recipe.parameter_position as u32);
        assert_eq!(construction.source.lambda, *origin.occurrence.occurrence());
        let local = session.batch.hir.local_source_for(&construction.source.owner).unwrap().unwrap();
        let parameter = local.expressions().iter().find_map(|expression| {
            if expression.occurrence != construction.source.lambda { return None; }
            match &expression.form {
                yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. } => Some(parameter),
                _ => None,
            }
        }).unwrap();
        assert!(parameter.annotation.is_none());
        assert_eq!(parameter.id, construction.source.formal);
        assert_eq!(parameter.source, construction.source.position);
        let (child, _, _, _) = InferenceSession::positive_function_children(&session.store, construction.function).unwrap();
        assert_eq!(child, construction.domain_child);
        let TermView::LiveVariable(view) = session.store.term_view(child).unwrap() else { panic!("raw formal child"); };
        assert_eq!(view.ordinal(), domain);
        assert_eq!(view.kind(), ComponentKind::Value);
        assert_eq!(view.polarity(), Polarity::Negative);
        eprintln!("formal lambda={:?} parameter={:?} domain={domain} initial_level={} retained_level={} source_relation={:?}",
            construction.source.lambda, parameter.id, initial_levels[domain as usize], session.value_levels[domain as usize], origin.relation);
        Some((construction, domain))
    }).collect();
    assert!(!formals.is_empty());
    let parents: Vec<_> = session.candidate_graph.as_ref().unwrap().intrusion.parents.iter()
        .filter_map(|parent| match (parent.parent, parent.copy) {
            (candidate_scheme::RowKey::Value(raw_parent), candidate_scheme::RowKey::Value(raw_copy)) =>
                Some((parent, raw_parent, raw_copy)),
            _ => None,
        }).collect();
    assert!(!parents.is_empty());
    // Only raw same-session constructor identities establish these links.
    // None leaves the missing correspondence unknown; it does not reject the
    // source or establish callback protection, and equal representatives do
    // not supply a formal identity. Levels here are snapshots, not copy-time
    // parent levels (which the retained Parent does not record).
    for (parent, raw_parent, raw_copy) in &parents {
        assert_ne!(raw_parent, raw_copy);
        assert!((*raw_parent as usize) < session.value_levels.len());
        assert!((*raw_copy as usize) < session.value_levels.len());
        let parent_formals: Vec<_> = formals.iter().filter(|(_, domain)| domain == raw_parent)
            .map(|(construction, _)| &construction.source.formal).collect();
        let copy_formals: Vec<_> = formals.iter().filter(|(_, domain)| domain == raw_copy)
            .map(|(construction, _)| &construction.source.formal).collect();
        eprintln!("copy parent={raw_parent} copy={raw_copy} polarity={:?} target={} occurrence={} comparison={:?} sources={:?} parent_formals={parent_formals:?} copy_formals={copy_formals:?}",
            parent.polarity, parent.target, parent.occurrence, parent.comparison, parent.sources);
    }
    let argument_dependency_count = context.dependencies.iter().filter(|dependency| matches!(dependency,
        Dependency::FunctionPort { field: FunctionField::Argument, .. })).count();
    eprintln!("retained_function_argument_dependencies={argument_dependency_count}");
    for dependency in &context.dependencies {
        let Dependency::FunctionPort { child, parent: comparison, field: FunctionField::Argument, .. } = *dependency else { continue; };
        let pair = context.relations[child.0 as usize].key.pair;
        let incidence = session.candidate_formal_argument_incidence(child);
        let formal = incidence.as_ref().map(|incidence| &incidence.construction.source.formal);
        if let Some(incidence) = &incidence {
            assert_eq!(incidence.argument, child);
            assert!(context.dependencies.iter().any(|dependency| matches!(*dependency,
                Dependency::FunctionPort { child: argument, parent, field: FunctionField::Argument, operation: FunctionPortOperation::Swap }
                    if argument == incidence.argument && parent == incidence.comparison)));
            assert!(formals.iter().any(|(construction, _)| std::ptr::eq(*construction, incidence.construction)));
        }
        // Parent.comparison retains a TypedPairKey, while the consumer has a
        // RelationId. Equal pair keys can belong to distinct contextual/source
        // relations: these candidate matches authenticate neither a unique
        // comparison operation nor a FunctionPort consumer. That correspondence
        // remains missing; zero retained Argument dependencies is not source rejection.
        let comparison_pair = context.relations[comparison.0 as usize].key.pair;
        let candidate_occurrences_by_pair_key: Vec<_> = parents.iter().filter(|(parent, _, _)| parent.comparison == Some(comparison_pair))
            .map(|(parent, _, _)| parent.occurrence).collect();
        let incidence_comparison = incidence.as_ref().map(|incidence| incidence.comparison);
        eprintln!("argument={child:?} pair={pair:?} comparison={comparison:?} formal={formal:?} incidence_comparison={incidence_comparison:?} candidate_occurrences_by_pair_key={candidate_occurrences_by_pair_key:?}");
    }
}

#[test]
fn omitted_formal_receiving_call_records_authenticated_argument_dispatch() {
    use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};
    const SOURCE: &str = "my root = { my outer cb = { my inner x = cb x; inner }; my identity z = z; outer identity }";
    let mut session = session_with_source(SOURCE);
    let owner = empty_bundle_owner(&session);
    let local = session.batch.hir.local_source(&owner).unwrap().unwrap();
    let expressions = local.expressions();
    // Binder, initializer, Lambda and parameter identities come from HIR;
    // their spelling selects only the requested fixture position.
    let mut selected = Vec::new();
    for (binder, formal) in [("outer", "cb"), ("inner", "x"), ("identity", "z")] {
        let binding = local.bindings().iter().find(|binding| binding.spelling.as_ref() == binder).unwrap();
        let lambda = &expressions[binding.initializer.ordinal() as usize];
        let LocalSourceForm::Lambda { parameter, .. } = &lambda.form else { panic!("fixture initializer Lambda"); };
        assert_eq!(parameter.spelling.as_ref(), formal);
        assert!(parameter.annotation.is_none());
        selected.push((binder, formal, binding.id.clone(), lambda.occurrence.clone(), parameter.id.clone(), parameter.source.clone()));
    }
    let mut selected_calls = Vec::new();
    for (index, expression) in expressions.iter().enumerate() {
        let LocalSourceForm::Apply { callee, argument, .. } = &expression.form else { continue; };
        let LocalSourceForm::Name { spelling: callee_name, resolution: callee_resolution } = &expressions[callee.ordinal() as usize].form else { panic!("fixture callee Name"); };
        let LocalSourceForm::Name { spelling: argument_name, resolution: argument_resolution } = &expressions[argument.ordinal() as usize].form else { panic!("fixture argument Name"); };
        let receiving = match (callee_resolution, argument_resolution) {
            (LocalSourceResolution::Local(callee_id), LocalSourceResolution::Local(argument_id)) => {
                assert_eq!(callee_id, &selected[0].2);
                assert_eq!(argument_id, &selected[2].2);
                assert_eq!((callee_name.as_ref(), argument_name.as_ref()), ("outer", "identity"));
                true
            }
            (LocalSourceResolution::Parameter(callee_id), LocalSourceResolution::Parameter(argument_id)) => {
                assert_eq!(callee_id, &selected[0].4);
                assert_eq!(argument_id, &selected[1].4);
                assert_eq!((callee_name.as_ref(), argument_name.as_ref()), ("cb", "x"));
                false
            }
            _ => panic!("fixture lexical Apply resolution"),
        };
        let input = session.batch.candidate_calls.calls.iter().find(|input| input.owner.definition_root() == Some(&owner) && input.expression == index).unwrap();
        assert_eq!(input.checking.occurrence(), &expression.occurrence);
        assert_eq!(input.callee, *callee);
        assert_eq!(input.argument, *argument);
        assert_eq!(session.batch.candidate_recipes[input.recipe].occurrence, expression.occurrence);
        selected_calls.push((receiving, input.checking.clone(), input.recipe));
    }
    assert_eq!(selected_calls.len(), 2, "exact two source Apply constructors");
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    for (binder, formal, _, lambda, parameter, position) in &selected {
        let origin = context.origins.iter().find(|origin| origin.formal.as_ref().is_some_and(|construction| construction.source.lambda == *lambda)).unwrap();
        let construction = origin.formal.as_ref().unwrap();
        assert_eq!(construction.source.owner, SourceRootId::Definition(owner.clone()));
        assert_eq!(&construction.source.formal, parameter);
        assert_eq!(&construction.source.position, position);
        assert_eq!(origin.occurrence.occurrence(), lambda);
        let recipe = session.batch.lambda_recipes.iter().find(|recipe| recipe.occurrence == *lambda).unwrap();
        assert_eq!(construction.domain, ValueEndpointKey::ValueRow(session.parameter_live_base + recipe.parameter_position as u32));
        let (domain, _, _, _) = InferenceSession::positive_function_children(&session.store, construction.function).unwrap();
        assert_eq!(domain, construction.domain_child);
        eprintln!("constructor {binder}/{formal}: source_relation={:?} construction={construction:?} domain_term={:?}", origin.relation, session.store.term_view(domain).unwrap());
    }
    for (receiving, checking, recipe) in &selected_calls {
        let input = session.batch.candidate_calls.calls.iter().find(|input| input.recipe == *recipe).unwrap();
        let native = input.native.as_ref().expect("executed source Apply retains native interface");
        eprintln!("source_apply receiving={receiving} checking={checking:?} native={native:?} demand_view={:?}", session.store.term_view(native.demand).unwrap());
        for origin in context.origins.iter().filter(|origin| origin.occurrence == *checking) {
            eprintln!("source_apply_relation receiving={receiving} relation={:?} key={:?}", origin.relation, context.relations[origin.relation.0 as usize].key);
        }
    }
    let receiving_checking = &selected_calls.iter().find(|call| call.0).unwrap().1;
    let cb_checking = &selected_calls.iter().find(|call| !call.0).unwrap().1;
    let cb_origins: Vec<_> = context.origins.iter().filter(|origin| origin.occurrence == *cb_checking).collect();
    for origin in &cb_origins {
        eprintln!("authenticated_cb_apply_origin relation={:?} checking={:?} key={:?}",
            origin.relation, origin.occurrence, context.relations[origin.relation.0 as usize].key);
    }
    // Enumerate the complete retained relation table, including every context.
    // Exact pair/source identity is a discriminator, never a canonical-row join.
    let mut unique_cb_copies = Vec::new();
    for (index, parent) in session.candidate_graph.as_ref().unwrap().intrusion.parents.iter().enumerate() {
        let candidates: Vec<_> = context.relations.iter().enumerate().filter(|(_, relation)|
            Some(relation.key.pair) == parent.comparison && relation.key.sources == parent.sources)
            .map(|(ordinal, relation)| (RelationId(u32::try_from(ordinal).unwrap()), relation.key)).collect();
        eprintln!("copy_relation_candidates parent_index={index} occurrence={} pair={:?} sources={:?} candidates={candidates:?}",
            parent.occurrence, parent.comparison, parent.sources);
        if candidates.len() != 1 {
            eprintln!("copy_relation_obstruction parent_index={index}: exact pair/source matched {} relations; no relation-to-copy inference", candidates.len());
            continue;
        }
        let (relation, key) = candidates[0];
        if cb_origins.len() != 1 || relation != cb_origins[0].relation {
            eprintln!("copy_relation_obstruction parent_index={index}: singleton {relation:?} is not the unique authenticated cb x source relation; source_origin_count={}", cb_origins.len());
            continue;
        }
        // Static processing alignment is documented in the leased note. The
        // retained source origin and full key supply this session's exact join.
        assert_eq!(Some(key.pair), parent.comparison);
        assert_eq!(key.sources, parent.sources);
        unique_cb_copies.push((index, relation));
        eprintln!("unique_cb_copy_relation parent_index={index} relation={relation:?} key={key:?} raw_parent={:?} raw_copy={:?}; no direct Function field path is retained", parent.parent, parent.copy);
    }
    let mut source_relations_with_consumers = Vec::new();
    let mut unique_cb_source_relations = Vec::new();
    for &(_, relation) in &unique_cb_copies {
        if !unique_cb_source_relations.contains(&relation) {
            unique_cb_source_relations.push(relation);
        }
    }
    let mut authenticated_receiving = 0;
    for dependency in &context.dependencies {
        let Dependency::FunctionPort { child, parent, field: FunctionField::Argument, operation } = *dependency else { continue; };
        assert_eq!(operation, FunctionPortOperation::Swap);
        let TypedPairKey::Value(pair) = context.relations[parent.0 as usize].key.pair else { panic!("Function comparison Value pair"); };
        let lower = InferenceSession::positive_function_children(&session.store, pair.lower).unwrap();
        let upper = InferenceSession::negative_function_children(&session.store, pair.upper).unwrap();
        let ValueEndpointKey::PositiveFunction(lower_term) = pair.lower else { unreachable!() };
        let ValueEndpointKey::NegativeFunction(upper_term) = pair.upper else { unreachable!() };
        eprintln!("paired_function_terms lower={lower_term:?} view={:?} upper={upper_term:?} view={:?}",
            session.store.term_view(lower_term).unwrap(), session.store.term_view(upper_term).unwrap());
        let incidence = session.candidate_formal_argument_incidence(child);
        if let Some(incidence) = &incidence {
            for edge in &context.dependencies {
                if matches!(*edge, Dependency::Transport { child, .. } if child == incidence.transport_relation) {
                    eprintln!("constructor_transport {edge:?}");
                }
            }
        }
        eprintln!("argument child={child:?} parent={parent:?} parent_key={:?} child_key={:?} lower={:?} upper={:?} lower_domain={:?} upper_argument={:?} incidence={incidence:?}",
            context.relations[parent.0 as usize].key, context.relations[child.0 as usize].key, pair.lower, pair.upper,
            session.store.term_view(lower.0).unwrap(), session.store.term_view(upper.0).unwrap());
        for replay in &context.dependencies {
            let Dependency::Replay { child: comparison, lower, upper, lower_input, upper_input } = *replay else { continue; };
            if comparison != parent { continue; }
            assert_eq!(context.relations[lower.0 as usize].key.pair, bound_pair(lower_input));
            assert_eq!(context.relations[upper.0 as usize].key.pair, bound_pair(upper_input));
            eprintln!("comparison_replay child={comparison:?} lower_relation={lower:?} upper_relation={upper:?} lower_input={lower_input:?} upper_input={upper_input:?}");
            // Follow only explicitly retained one-parent derivations/transport
            // of the upper bound. Pair equality and multi-input Replay ancestry
            // cannot identify which source supplied this negative demand.
            let mut pending = vec![upper];
            let mut seen = Vec::new();
            while let Some(relation) = pending.pop() {
                if seen.contains(&relation) { continue; }
                seen.push(relation);
                for edge in &context.dependencies {
                    let antecedent = match *edge {
                        Dependency::Derived { child, parent } if child == relation => Some(parent),
                        Dependency::Transport { child, parent, .. } if child == relation => Some(parent),
                        _ => None,
                    };
                    if let Some(antecedent) = antecedent {
                        eprintln!("upper_bound_ancestry {edge:?}");
                        pending.push(antecedent);
                    }
                }
            }
            let receiving_upper = context.origins.iter().any(|origin| seen.contains(&origin.relation) && origin.occurrence == *receiving_checking);
            for &source in &unique_cb_source_relations {
                if seen.contains(&source) {
                    source_relations_with_consumers.push(source);
                    let matching_copy_parents: Vec<_> = unique_cb_copies.iter()
                        .filter_map(|&(index, copy_source)| (copy_source == source).then_some(index))
                        .collect();
                    eprintln!("cb_source_relation_consumer source_relation={source:?} matching_copy_initiator_parents={matching_copy_parents:?} replay={replay:?} argument_dependency={dependency:?} upper_ancestry={seen:?}; source-to-copy initiation and source-to-consumer ancestry share a source relation, with no retained per-copy field path");
                    // Inspect only actual retained upper-ancestry transports.
                    // Decode raw term identities: endpoint translators canonicalize
                    // rows and would erase precisely the distinction under study.
                    let raw_row = |term, polarity, kind| {
                        match session.store.term_view(term).unwrap() {
                            TermView::LiveVariable(view) if view.kind() == kind && view.polarity() == polarity => {
                                Some(match kind {
                                    ComponentKind::Value => candidate_scheme::RowKey::Value(view.ordinal()),
                                    ComponentKind::Effect => candidate_scheme::RowKey::Effect(view.ordinal()),
                                })
                            }
                            TermView::Component(component) if component.kind() == kind => {
                                let ordinal = session.component_endpoint(term).ordinal;
                                Some(match kind {
                                    ComponentKind::Value => candidate_scheme::RowKey::Value(ordinal),
                                    ComponentKind::Effect => candidate_scheme::RowKey::Effect(ordinal),
                                })
                            }
                            _ => None,
                        }
                    };
                    // Query the existing root-output index using the authenticated
                    // source pair and the actual final FreshUse input, never IDs.
                    let source_key = context.relations[source.0 as usize].key;
                    let root_witnesses: Vec<_> = context.dependencies.iter().filter_map(|edge| {
                        let Dependency::Transport { child, parent: antecedent, witness: Some(witness), .. } = *edge else { return None; };
                        (child == upper && witness.to == upper_input && seen.contains(&antecedent)
                            && matches!(witness.reason, TransportReason::FreshUse)
                            && context.dependencies.iter().any(|edge| matches!(*edge,
                                Dependency::Derived { child, parent } if child == antecedent && parent == source)))
                            .then_some((edge, witness))
                    }).collect();
                    if root_witnesses.len() != 1 {
                        eprintln!("root_output_obstruction source={source:?}: exact consumer FreshUse with direct source Derived ancestry has {} witnesses", root_witnesses.len());
                    } else {
                        let (edge, witness) = root_witnesses[0];
                        let intrusion = &session.candidate_graph.as_ref().unwrap().intrusion;
                        let groups = intrusion.observed_output_groups(source_key.pair, witness.from.2);
                        eprintln!("root_output_groups source={source:?} key={source_key:?} edge={edge:?} groups={groups:?}; output membership does not authenticate rewrite-enqueue activation");
                        if groups.len() != 1 {
                            eprintln!("root_output_obstruction source={source:?}: exact output index has {} groups", groups.len());
                        } else {
                            let (group_id, occurrence, start, end, _) = groups[0];
                            let census_matches = matching_copy_parents.len() == 4 && end.checked_sub(start) == Some(4)
                                && intrusion.parents.get(start..end).is_some_and(|parents| parents.iter().enumerate().all(|(offset, parent)|
                                    matching_copy_parents.contains(&(start + offset)) && parent.occurrence == occurrence
                                        && parent.comparison == Some(source_key.pair) && parent.sources == source_key.sources));
                            eprintln!("root_output_group_census group={group_id} occurrence={occurrence} span={start}..{end} exact_four_parent_census={census_matches}");
                            if !census_matches {
                                eprintln!("root_output_obstruction: unique group does not equal the exact four source/pair census Parents");
                            } else {
                                let ports = |endpoint| match endpoint {
                                    ValueEndpointKey::PositiveFunction(_) => InferenceSession::positive_function_children(&session.store, endpoint),
                                    ValueEndpointKey::NegativeFunction(_) => InferenceSession::negative_function_children(&session.store, endpoint),
                                    _ => None,
                                };
                                let original = match source_key.pair { TypedPairKey::Value(pair) => ports(pair.upper), _ => None };
                                let root = match witness.from.2 { ExtrusionEndpoint::Value(endpoint) => ports(endpoint), _ => None };
                                let consumer = match witness.to.2 { ExtrusionEndpoint::Value(endpoint) => ports(endpoint), _ => None };
                                if let (Some(original), Some(root), Some(consumer)) = (original, root, consumer) {
                                    let polarity = witness.from.1;
                                    let opposite = match polarity { Polarity::Positive => Polarity::Negative, Polarity::Negative => Polarity::Positive };
                                    let fields = [
                                        (FunctionField::Argument, original.0, root.0, consumer.0, opposite, ComponentKind::Value),
                                        (FunctionField::ArgumentEffect, original.1, root.1, consumer.1, opposite, ComponentKind::Effect),
                                        (FunctionField::ResultEffect, original.2, root.2, consumer.2, polarity, ComponentKind::Effect),
                                        (FunctionField::Result, original.3, root.3, consumer.3, polarity, ComponentKind::Value),
                                    ];
                                    eprintln!("root_output_raw_fields original={original:?} root={root:?} consumer={consumer:?} fields={fields:?} exact_consumer_relation={upper:?} exact_consumer_input={upper_input:?}");
                                    if witness.to.1 != polarity {
                                        eprintln!("root_output_obstruction: FreshUse changes bound polarity");
                                    } else {
                                        let mut complete = true;
                                        for index in start..end {
                                            let copy = &intrusion.parents[index];
                                            let matches: Vec<_> = fields.iter().filter(|&&(_, before, copied, _, field_polarity, kind)|
                                                copy.polarity == field_polarity && raw_row(before, field_polarity, kind) == Some(copy.parent)
                                                    && raw_row(copied, field_polarity, kind) == Some(copy.copy)).collect();
                                            eprintln!("root_output_parent_fields parent_index={index} raw_parent={:?} raw_copy={:?} polarity={:?} candidates={matches:?}; same-position FreshUse terms belong to the exact consumer BoundKey", copy.parent, copy.copy, copy.polarity);
                                            if matches.len() != 1 {
                                                complete = false;
                                                eprintln!("root_output_obstruction parent_index={index}: {} direct raw field candidates; selected descendants and shared fields remain unresolved", matches.len());
                                                break;
                                            }
                                            let &&(field, _, _, output, field_polarity, kind) = matches.first().unwrap();
                                            let consumer_row = raw_row(output, field_polarity, kind);
                                            let shared_consumer_fields: Vec<_> = fields.iter().filter_map(|&(candidate, _, _, term, sign, candidate_kind)|
                                                (sign == field_polarity && candidate_kind == kind && consumer_row.is_some()
                                                    && raw_row(term, sign, candidate_kind) == consumer_row).then_some(candidate)).collect();
                                            eprintln!("root_output_fresh_field field={field:?} raw_consumer_row={consumer_row:?} shared_consumer_fields={shared_consumer_fields:?} exact_consumer_relation={upper:?} exact_consumer_input={upper_input:?}");
                                            if consumer_row.is_none() || shared_consumer_fields.len() != 1 {
                                                complete = false;
                                                eprintln!("root_output_obstruction parent_index={index}: same-position FreshUse raw consumer field is missing or shared");
                                                break;
                                            }
                                        }
                                        eprintln!("root_output_field_observation complete={complete}; bounded raw field correspondence only, no rewrite-enqueue activation or profile/protection claim");
                                    }
                                } else {
                                    eprintln!("root_output_obstruction: source upper, exact indexed root output, or exact consumer input is not a decodable Function");
                                }
                            }
                        }
                    }
                    let mut function_witnesses = 0;
                    for edge in &context.dependencies {
                        let Dependency::Transport { child: transported, parent: antecedent,
                            witness: Some(witness), .. } = *edge else { continue; };
                        if !seen.contains(&transported) || !seen.contains(&antecedent) { continue; }
                        let TransportReason::Extrusion { .. } = witness.reason else { continue; };
                        let polarity = witness.from.1;
                        if witness.to.1 != polarity { continue; }
                        let (ExtrusionEndpoint::Value(from), ExtrusionEndpoint::Value(to)) =
                            (witness.from.2, witness.to.2) else { continue; };
                        let ports = |endpoint| match endpoint {
                            ValueEndpointKey::PositiveFunction(_) => InferenceSession::positive_function_children(&session.store, endpoint),
                            ValueEndpointKey::NegativeFunction(_) => InferenceSession::negative_function_children(&session.store, endpoint),
                            _ => None,
                        };
                        let (Some(before), Some(after)) = (ports(from), ports(to)) else { continue; };
                        function_witnesses += 1;
                        let opposite = match polarity { Polarity::Positive => Polarity::Negative, Polarity::Negative => Polarity::Positive };
                        let fields = [
                            (FunctionField::Argument, before.0, after.0, opposite, ComponentKind::Value),
                            (FunctionField::ArgumentEffect, before.1, after.1, opposite, ComponentKind::Effect),
                            (FunctionField::ResultEffect, before.2, after.2, polarity, ComponentKind::Effect),
                            (FunctionField::Result, before.3, after.3, polarity, ComponentKind::Value),
                        ];
                        // Exact BoundKey identity authenticates the final upper
                        // input. Matching Function endpoints alone does not.
                        let exact_consumer_input = transported == upper && witness.to == upper_input;
                        eprintln!("cb_function_transport edge={edge:?} from_ports={before:?} to_ports={after:?} exact_consumer_input={exact_consumer_input}; inspect all fields, no endpoint-only output attribution");
                        for &index in &matching_copy_parents {
                            let copy = &session.candidate_graph.as_ref().unwrap().intrusion.parents[index];
                            let matches: Vec<_> = fields.iter().filter_map(|&(field, original, output, field_polarity, kind)| {
                                (copy.polarity == field_polarity && raw_row(original, field_polarity, kind) == Some(copy.parent)
                                    && raw_row(output, field_polarity, kind) == Some(copy.copy))
                                    .then_some(field)
                            }).collect();
                            eprintln!("cb_raw_copy_field_candidates parent_index={index} raw_parent={:?} raw_copy={:?} polarity={:?} fields={matches:?} exact_consumer_input={exact_consumer_input}; empty candidates do not identify selected-bound descendants; repeated/shared candidates remain ambiguous",
                                copy.parent, copy.copy, copy.polarity);
                        }
                    }
                    eprintln!("cb_copy_field_frontier source_relation={source:?} upper_ancestry={seen:?} eligible_extrusion_function_witnesses={function_witnesses}; runtime_obstruction=no qualifying Extrusion Function TransportWitness on authenticated consumer ancestry, so no per-copy field candidate or exact consumer-input flag was evaluated; static retention frontier: Work::Function child-key/output association versus Work::Bound selected descendant; this static seam is not established as the first consumer-path break");
                }
            }
            let outer_constructor = incidence.as_ref().is_some_and(|incidence| incidence.comparison == parent && incidence.construction.source.lambda == selected[0].3);
            if receiving_upper && outer_constructor {
                authenticated_receiving += 1;
                eprintln!("authenticated_receiving_argument child={child:?} comparison={parent:?} upper_ancestry={seen:?}");
            } else {
                eprintln!("unattributed_argument child={child:?} receiving_upper={receiving_upper} outer_constructor={outer_constructor} upper_ancestry={seen:?}; earlier extrusion is outside the bounded incidence reader");
            }
        }
    }
    for &relation in &unique_cb_source_relations {
        if !source_relations_with_consumers.contains(&relation) {
            let matching_copy_parents: Vec<_> = unique_cb_copies.iter()
                .filter_map(|&(index, copy_source)| (copy_source == relation).then_some(index))
                .collect();
            eprintln!("copy_consumer_obstruction relation={relation:?} matching_copy_initiator_parents={matching_copy_parents:?}: no immediate Argument-parent Replay upper input has explicit Derived/Transport ancestry to this source relation");
        }
    }
    for parent in &session.candidate_graph.as_ref().unwrap().intrusion.parents {
        eprintln!("extrusion_parent raw_parent={:?} raw_copy={:?} polarity={:?} target={} occurrence={} pair_only={:?} sources={:?}; no retained contextual RelationId or direct Function field path",
            parent.parent, parent.copy, parent.polarity, parent.target, parent.occurrence, parent.comparison, parent.sources);
    }
    eprintln!("authenticated_receiving_argument_chains={authenticated_receiving}; absence is an attribution obstruction, not lost protection; later cb-demand comparisons require their own authenticated ancestry");
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
        let mut session = session_with_source("act E\nmy seed x = seed x");
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
        let copy = source_extrude(&mut session, parent, Polarity::Negative);
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
            session.constrain_live_item(TypedWorkItem { task, relation: Some(relation), replay_ack: None }, &occurrence, &cause)?;
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
            TypedWorkItem { task, relation: Some(relation), replay_ack: None },
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
            session.constrain_live_item(TypedWorkItem { task, relation: Some(root), replay_ack: None }, &occurrence, &cause)?;
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
        session.constrain_live_item(TypedWorkItem { task, relation: Some(relation), replay_ack: None }, &occurrence, &cause)?;
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
        session.enqueue_item(TypedWorkItem { task: replay_task, relation: Some(child), replay_ack: None }, false).unwrap();
        assert_eq!(session.typed_worklist.pop_front(), Some(TypedWorkItem { task: replay_task, relation: Some(child), replay_ack: None }));
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
        let mut session = session_with_source("act E\nmy seed x = seed x");
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
        let copy = source_extrude(&mut session, parent, Polarity::Positive);
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
fn replay_queue_preflight_failure_preserves_transfer_cursor_before_retry() {
    for direct_drain in [false, true] {
        for after_reserve in [false, true] {
            let mut session = session();
            let (occurrence, cause) = cause(&session, 0);
            let owner = session.fresh_value_at_level(1).unwrap();
            let lower = session.fresh_value_at_level(1).unwrap();
            let upper = session.fresh_value_at_level(1).unwrap();
            let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
            let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
            let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            for key in [lower_input, upper_input] {
                let relation = context.relation(bound_pair(key), IDENTITY).unwrap();
                context.attach(key, relation).unwrap();
            }
            let operation = session.with_route_transaction(|session|
                session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)).unwrap();
            let checkpoint = state(&session).checkpoint();
            assert_eq!(session.with_route_transaction(|session| {
                if after_reserve { inject_next_f5b_post_reserve_failure(F5bCapacityLane::TypedWorklist); }
                else { inject_next_f5b_reserve_failure(F5bCapacityLane::TypedWorklist); }
                let provenance = direct_drain.then_some((&occurrence, &cause));
                let result = session.candidate_context_consume_replay_child(operation, provenance);
                assert_eq!(result, Err(exhausted()));
                let retained = &state(session).replay_operations[&operation];
                assert_eq!((retained.queued, retained.consumed, retained.retired), (0, 0, false));
                assert!(session.typed_worklist.is_empty());
                result.map(|_| ())
            }), Err(exhausted()));
            assert_eq!(state(&session).checkpoint(), checkpoint);
            session.with_route_transaction(|session| {
                let provenance = direct_drain.then_some((&occurrence, &cause));
                assert!(session.candidate_context_consume_replay_child(operation, provenance)?);
                if !direct_drain {
                    let item = session.typed_worklist.pop_front().unwrap();
                    session.constrain_live_item(item, &occurrence, &cause)?;
                }
                let retained = &state(session).replay_operations[&operation];
                assert_eq!((retained.queued, retained.consumed, retained.retired), (1, 1, true));
                Ok(())
            }).unwrap();
            assert!(!state(&session).replay_operations.contains_key(&operation));
            assert_eq!(state(&session).replay_child_bytes, 0);
            assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
        }
    }
}

#[test]
fn replay_completion_undo_failure_samples_transient_ack_buffer_before_drop() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    for key in [lower_input, upper_input] {
        let relation = context.relation(bound_pair(key), IDENTITY).unwrap();
        context.attach(key, relation).unwrap();
    }
    let operation = session.with_route_transaction(|session|
        session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)).unwrap();
    let checkpoint = state(&session).checkpoint();
    let mut event_total = 0;
    assert_eq!(session.with_route_transaction(|session| {
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.fail_replay_completion_undo_reserve = true;
        let result = session.candidate_context_consume_replay_child(operation, Some((&occurrence, &cause)));
        assert_eq!(result, Err(exhausted()));
        let context = state(session);
        let (event_context_bytes, ack_bytes) = context.failed_replay_completion_bytes.unwrap();
        assert!(ack_bytes > 0, "the fresh drain buffer grew before the injected failure");
        assert!(context.typed_drains.is_empty());
        assert_eq!(context.enumerated_bytes() + ack_bytes, event_context_bytes);
        let retained = &context.replay_operations[&operation];
        assert_eq!((retained.queued, retained.consumed, retained.retired), (1, 0, false));
        assert_eq!(session.typed_worklist.front().unwrap().replay_ack,
            Some(ReplayChildAck { operation, index: 0 }));
        event_total = session.resource_ledger.inference_session_retained_bytes;
        assert!(session.resource_ledger.inference_session_peak_bytes >= event_total);
        session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        assert_eq!(session.resource_ledger.inference_session_retained_bytes + ack_bytes, event_total,
            "the event sample includes exactly the subsequently dropped acknowledgement buffer");
        result.map(|_| ())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), checkpoint);
    let retained = &state(&session).replay_operations[&operation];
    assert_eq!((retained.queued, retained.consumed, retained.retired), (0, 0, false));
    assert!(state(&session).typed_drains.is_empty());
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
    assert!(session.resource_ledger.inference_session_retained_bytes < event_total);
    assert!(session.resource_ledger.inference_session_peak_bytes >= event_total);
    session.with_route_transaction(|session| {
        assert!(session.candidate_context_consume_replay_child(operation, Some((&occurrence, &cause)))?);
        let retained = &state(session).replay_operations[&operation];
        assert_eq!((retained.queued, retained.consumed, retained.retired), (1, 1, true));
        Ok(())
    }).unwrap();
    assert!(!state(&session).replay_operations.contains_key(&operation));
}

#[test]
fn operation_retirement_frontier_ignores_historical_capacity_and_untouched_pending_operations() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let restoration_owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    for key in [lower_input, upper_input] {
        let relation = context.relation(bound_pair(key), IDENTITY).unwrap();
        context.attach(key, relation).unwrap();
    }
    let persistent = session.with_route_transaction(|session|
        session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)).unwrap();
    session.with_route_transaction(|session| {
        let mut replays = Vec::new();
        let mut restorations = Vec::new();
        for _ in 0..64 {
            replays.push(session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)?);
            restorations.push(session.candidate_begin_bound_restoration(value(restoration_owner), Polarity::Positive,
                value(lower), &occurrence, &cause, BoundAdmissionCause::OwnerEmission { processing: None })?);
        }
        for replay in replays { session.candidate_context_drive_replay(replay, Some((&occurrence, &cause)))?; }
        for restoration in restorations { session.candidate_drive_bound_restoration(restoration)?; }
        Ok(())
    }).unwrap();
    assert_eq!(state(&session).replay_operations.len(), 1);
    assert!(state(&session).restorations.is_empty());
    assert!(state(&session).replay_operations.capacity() >= 64);
    assert!(state(&session).restorations.capacity() >= 64);
    let visits = state(&session).operation_frontier_visits;
    session.with_route_transaction(|_| Ok(())).unwrap();
    assert_eq!(state(&session).operation_frontier_visits, visits);
    assert_eq!(state(&session).replay_operations[&persistent].consumed, 0);
    assert_eq!(session.with_route_transaction(|_| Err::<(), _>(exhausted())), Err(exhausted()));
    assert_eq!(state(&session).operation_frontier_visits, visits);
    assert!(state(&session).replay_operations.contains_key(&persistent));
    session.with_route_transaction(|session|
        session.candidate_context_drive_replay(persistent, Some((&occurrence, &cause)))).unwrap();
    assert!(state(&session).replay_operations.is_empty());
    assert_eq!(state(&session).replay_child_bytes, 0);
    let visits = state(&session).operation_frontier_visits;
    session.with_route_transaction(|_| Ok(())).unwrap();
    assert_eq!(session.with_route_transaction(|_| Err::<(), _>(exhausted())), Err(exhausted()));
    assert_eq!(state(&session).operation_frontier_visits, visits);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    eprintln!("retirement frontier structural observation: replay_capacity={}, restoration_capacity={}, following_empty_route_visits=0",
        state(&session).replay_operations.capacity(), state(&session).restorations.capacity());
}

#[test]
fn restoration_previous_replay_pointer_controls_reclamation_and_rollback_bytes() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    session.candidate_insert_bound(value(owner), Polarity::Negative, value(upper)).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let (restoration, replay) = session.with_route_transaction(|session| {
        let restoration = session.candidate_begin_bound_restoration(value(owner), Polarity::Positive, value(lower),
            &occurrence, &cause, BoundAdmissionCause::OwnerEmission { processing: None })?;
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.prepare_restoration_update(restoration, true)?;
        let replay = session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)?;
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.set_restoration_replay(restoration, replay);
        session.candidate_context_drive_replay(replay, Some((&occurrence, &cause)))?;
        Ok((restoration, replay))
    }).unwrap();
    assert!(state(&session).replay_operations[&replay].retired);
    assert_eq!(state(&session).restorations[&restoration].replay, Some(replay));
    let child_bytes = state(&session).replay_child_bytes;
    assert!(child_bytes > 0);
    let checkpoint = state(&session).checkpoint();
    let advance = |session: &mut InferenceSession| {
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        context.prepare_restoration_update(restoration, true)?;
        context.advance_restoration(restoration, true);
        Ok(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        advance(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), checkpoint);
    assert_eq!(state(&session).restorations[&restoration].replay, Some(replay));
    assert!(state(&session).replay_operations[&replay].retired);
    assert_eq!(state(&session).replay_child_bytes, child_bytes);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(advance).unwrap();
    assert!(!state(&session).replay_operations.contains_key(&replay));
    assert!(state(&session).restorations.contains_key(&restoration));
    assert_eq!(state(&session).replay_child_bytes, 0);
    session.with_route_transaction(|session| session.candidate_drive_bound_restoration(restoration)).unwrap();
    assert!(state(&session).restorations.is_empty());
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn queued_replay_child_waits_for_successful_typed_drain_and_rolls_back_both_cursors() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    for key in [lower_input, upper_input] {
        let relation = context.relation(bound_pair(key), IDENTITY).unwrap();
        context.attach(key, relation).unwrap();
    }
    let operation = session.with_route_transaction(|session|
        session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), false)).unwrap();
    let checkpoint = state(&session).checkpoint();
    let child = state(&session).replay_operation_next(operation).unwrap().unwrap().relation;
    let queue_and_drain = |session: &mut InferenceSession| {
        assert!(session.candidate_context_consume_replay_child(operation, None)?);
        let retained = &state(session).replay_operations[&operation];
        assert_eq!((retained.queued, retained.consumed, retained.retired), (1, 0, false));
        let queued_checkpoint = state(session).checkpoint();
        assert!(!session.candidate_context_consume_replay_child(operation, None)?);
        assert_eq!(state(session).checkpoint(), queued_checkpoint);
        let item = session.typed_worklist.pop_front().unwrap();
        assert_eq!(item.relation, child);
        assert_eq!(item.replay_ack, Some(ReplayChildAck { operation, index: 0 }));
        session.constrain_live_item(item, &occurrence, &cause)?;
        let retained = &state(session).replay_operations[&operation];
        assert_eq!((retained.queued, retained.consumed, retained.retired), (1, 1, true));
        Ok(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        queue_and_drain(session)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), checkpoint);
    let retained = &state(&session).replay_operations[&operation];
    assert_eq!((retained.queued, retained.consumed, retained.retired), (0, 0, false));
    assert_eq!(state(&session).replay_operation_next(operation).unwrap().unwrap().relation, child);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(queue_and_drain).unwrap();
    assert!(!state(&session).replay_operations.contains_key(&operation));
    assert_eq!(state(&session).replay_child_bytes, 0);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn retained_replay_capacity_tracks_batch_sum_and_releases_it_at_transaction_boundaries() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    for key in [lower_input, upper_input] {
        let relation = context.relation(bound_pair(key), IDENTITY).unwrap();
        context.attach(key, relation).unwrap();
    }
    for count in [8, 1] {
        session.with_route_transaction(|session| {
            let mut operations = Vec::new();
            for _ in 0..count {
                operations.push(session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)?);
            }
            let expected = operations.iter().map(|id| state(session).replay_operations[id].children.capacity()
                * std::mem::size_of::<RelationId>()).sum::<usize>();
            assert_eq!(state(session).replay_child_bytes, expected);
            for operation in operations { session.candidate_context_drive_replay(operation, Some((&occurrence, &cause)))?; }
            assert_eq!(state(session).replay_child_bytes, expected, "completed batches stay owned until commit");
            assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
            eprintln!("retained replay structural observation: operations={count}, child_capacity_bytes={}, undo_capacity_bytes={}",
                state(session).replay_child_bytes, state(session).replay_operation_undo.capacity() * std::mem::size_of::<ReplayOperationUndo>());
            Ok(())
        }).unwrap();
        assert_eq!(state(&session).replay_child_bytes, 0);
        assert!(state(&session).replay_operations.is_empty());
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn retained_restoration_retries_saved_opposites_without_reemitting_accepted_bound() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let uppers = [session.fresh_value_at_level(1).unwrap(), session.fresh_value_at_level(1).unwrap()];
    for upper in uppers {
        session.candidate_insert_bound(value(owner), Polarity::Negative, value(upper)).unwrap();
    }
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(uppers[0]));
    let (restoration, replay) = session.with_route_transaction(|session| {
        let restoration = session.candidate_begin_bound_restoration(value(owner), Polarity::Positive, value(lower),
            &occurrence, &cause, BoundAdmissionCause::OwnerEmission { processing: None })?;
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let swap = context.context(ContextExpr::Swap { input: IDENTITY })?;
        for key in [lower_input, upper_input] {
            let relation = context.relation(bound_pair(key), swap)?;
            context.attach(key, relation)?;
        }
        context.prepare_restoration_update(restoration, true)?;
        let replay = session.candidate_context_begin_replay(lower_input, upper_input, task(lower, uppers[0]), true)?;
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.set_restoration_replay(restoration, replay);
        session.candidate_context_consume_replay_child(replay, Some((&occurrence, &cause)))?;
        Ok((restoration, replay))
    }).unwrap();
    assert_eq!(state(&session).restorations[&restoration].opposite_count, 2);
    assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
    assert_eq!(state(&session).replay_operations[&replay].consumed, 1);
    let checkpoint = state(&session).checkpoint();
    let emission = state(&session).restorations[&restoration].emission;
    let original_emission = state(&session).evidence.emissions[emission.0];
    let original_admission = state(&session).evidence.admissions[original_emission.admission.0];
    let original_admission_count = |context: &State| context.evidence.admissions.iter().filter(|admission|
        admission.bound == original_admission.bound && admission.relation == original_admission.relation
            && admission.origin == original_admission.origin
            && admission.cause == (BoundAdmissionCause::OwnerEmission { processing: None })).count();
    let accepted_admissions = original_admission_count(state(&session));
    let emissions = state(&session).evidence.emissions.len();
    let pending = state(&session).replay_operation_next(replay).unwrap().unwrap().relation;
    assert_eq!(session.with_route_transaction(|session| {
        assert_eq!(session.candidate_drive_bound_restoration(restoration)?, emission);
        assert!(state(session).restorations[&restoration].retired);
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), checkpoint);
    assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
    assert_eq!(state(&session).restorations[&restoration].replay, Some(replay));
    assert_eq!(state(&session).replay_operation_next(replay).unwrap().unwrap().relation, pending);
    assert_eq!(state(&session).evidence.emissions.len(), emissions);
    session.with_route_transaction(|session| {
        assert_eq!(session.candidate_drive_bound_restoration(restoration)?, emission);
        assert_eq!(state(session).restorations[&restoration].next_opposite, 2);
        // Draining children can emit derived bounds. The accepted restoration
        // keeps its original emission and never repeats its owner admission.
        let retained = state(session).evidence.emissions[emission.0];
        assert_eq!((retained.admission, retained.bound, retained.physical),
            (original_emission.admission, original_emission.bound, original_emission.physical));
        let admission = state(session).evidence.admissions[retained.admission.0];
        assert_eq!((admission.bound, admission.relation, admission.origin, admission.cause),
            (original_admission.bound, original_admission.relation, original_admission.origin, original_admission.cause));
        assert_eq!(original_admission_count(state(session)), accepted_admissions);
        Ok(())
    }).unwrap();
    assert!(state(&session).restorations.is_empty());
    assert!(state(&session).replay_operations.is_empty());
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn retained_replay_commits_pending_children_and_restores_consumption_on_retry() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let swap = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let mut fibers = Vec::new();
    for key in [lower_input, upper_input] {
        for retained in [IDENTITY, swap] {
            let relation = context.relation(bound_pair(key), retained).unwrap();
            context.attach(key, relation).unwrap();
            fibers.push(relation);
        }
    }
    let operation = session.with_route_transaction(|session| {
        let id = session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true)?;
        let children = &state(session).replay_operations[&id].children;
        assert_eq!(children.len(), 4);
        for (&child, (lower, upper)) in children.iter().zip([
            (fibers[1], fibers[3]), (fibers[1], fibers[2]),
            (fibers[0], fibers[3]), (fibers[0], fibers[2]),
        ]) {
            assert!(state(session).dependency_keys.contains(&Dependency::Replay { child, lower, upper, lower_input, upper_input }));
        }
        session.candidate_context_consume_replay_child(id, Some((&occurrence, &cause)))?;
        Ok(id)
    }).unwrap();
    let context = state(&session);
    let retained = &context.replay_operations[&operation];
    assert_eq!(retained.consumed, 1);
    assert!(!retained.retired);
    assert_eq!(retained.heads, context.replay_heads[&(lower_input, upper_input)]);
    assert_eq!(retained.prior, (None, None));
    assert!(retained.incoming_use);
    assert_eq!(retained.inputs, (lower_input, upper_input));
    assert!(context.replay_operation_undo.is_empty());
    let pending = context.replay_operation_next(operation).unwrap().unwrap().relation;
    let generation = context.checkpoint();
    let children = context.replay_operations[&operation].children.clone();
    for _ in 0..3 {
        assert_eq!(state(&session).replay_operation_next(operation).unwrap().unwrap().relation, pending);
        assert_eq!(state(&session).checkpoint(), generation);
    }
    assert_eq!(session.with_route_transaction(|session| {
        session.candidate_context_consume_replay_child(operation, Some((&occurrence, &cause)))?;
        assert_eq!(state(session).replay_operations[&operation].consumed, 2);
        session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), generation);
    assert_eq!(state(&session).replay_operation_next(operation).unwrap().unwrap().relation, pending);
    assert_eq!(state(&session).replay_operations[&operation].children, children);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(|session| {
        session.candidate_context_drive_replay(operation, Some((&occurrence, &cause)))?;
        assert_eq!(state(session).replay_operations[&operation].consumed, 4);
        assert!(state(session).replay_operations[&operation].retired);
        Ok(())
    }).unwrap();
    assert!(!state(&session).replay_operations.contains_key(&operation));
    assert!(state(&session).replay_operation_undo.is_empty());
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
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
            session.enqueue_item(TypedWorkItem { task: replay_task, relation: Some(replay[0]), replay_ack: None }, false)?;
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
            session.enqueue_item(TypedWorkItem { task: replay_task, relation: Some(replay[0]), replay_ack: None }, false)?;
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
        assert_eq!(set.owner, SourceRootId::Definition(owner.clone()));
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
        + graph.bound_evidence.capacity() * std::mem::size_of::<EvidenceSnapshot>()
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
                retained_extrusion_rewrite: None,
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
    let lifecycle_generation = state(&session).lifecycle_generation;
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
        let mut route_checkpoint = None;
        let result = session.with_route_transaction(|session| {
            route_checkpoint = Some(RouteCheckpoint::capture(session));
            assert_eq!(session.candidate_function_port_admit(child_task, FunctionField::Argument)?, Some(child));
            let context = state(session);
            assert_eq!(context.lifecycle_generation, lifecycle_generation + 1);
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
            assert_eq!(state(session).lifecycle_generation, lifecycle_generation + 1, "exact duplicate does not advance lifecycle generation");
            Ok(())
        });
        if rollback {
            assert_eq!(result, Err(exhausted()));
            route_checkpoint.unwrap().assert_restored(&session);
            assert_eq!(state(&session).checkpoint(), before);
            assert_eq!(state(&session).lifecycle_generation, lifecycle_generation, "route failure restores the prior lifecycle generation");
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
        parent: candidate_scheme::RowKey::Value(2), polarity: Polarity::Positive, target: 0, sources: None, comparison: None, occurrence: 0 }];
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
        parent: candidate_scheme::RowKey::Value(2), polarity: Polarity::Positive, target: 0, sources: None, comparison: None, occurrence: 0 }];
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
        let mut session = session_with_source("act E\nmy seed x = seed x");
        let (occurrence, cause) = cause(&session, 0);
        let parent = if effect {
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(session.fresh_effect_at_level(2).unwrap()))
        } else { value(session.fresh_value_at_level(2).unwrap()) };
        if !effect {
            session.candidate_restore_bound(parent, Polarity::Negative, ExtrusionEndpoint::Value(ValueEndpointKey::UnitNegative), &occurrence, &cause).unwrap();
        }
        let copy = source_extrude(&mut session, parent, Polarity::Positive);
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
                    session.constrain_live_item(TypedWorkItem { task: raw, relation: Some(original), replay_ack: None }, &occurrence, &cause)?;
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

#[test]
fn support_retention_duplicate_admissions_emissions_and_sampling_preserve_semantic_dedup() {
    let mut session = session();
    let owner = value(session.fresh_value_at_level(1).unwrap());
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let bound = BoundKey(owner, Polarity::Positive, lower);
    let cause = BoundAdmissionCause::OwnerEmission { processing: None };
    let first = session.candidate_insert_bound_with_evidence(owner, Polarity::Positive, lower, true, cause).unwrap();
    let semantic = (state(&session).relations.len(), state(&session).bound_keys.len(), state(&session).dependencies.len());
    let second = session.candidate_insert_bound_with_evidence(owner, Polarity::Positive, lower, true, cause).unwrap();
    assert_ne!(first, second);
    assert_eq!(semantic, (state(&session).relations.len(), state(&session).bound_keys.len(), state(&session).dependencies.len()));
    while state(&session).evidence.admissions.len() < state(&session).evidence.admissions.capacity() {
        session.candidate_bound_origin(bound, None).unwrap();
    }
    let before_len = state(&session).evidence.admissions.len();
    let before = state(&session).evidence.counters;
    let sampled_before = session.resource_ledger.inference_session_retained_bytes;
    let bytes = state(&session).evidence.bytes().unwrap();
    session.candidate_bound_origin(bound, None).unwrap();
    let evidence = &state(&session).evidence;
    assert_eq!(evidence.admissions.len(), before_len + 1);
    assert_eq!(evidence.emissions.len(), 2);
    assert_eq!(evidence.emissions[0].physical.index, 0);
    assert_eq!(evidence.emissions[1].physical.index, 1);
    assert_eq!(evidence.counters.admission_samples, before.admission_samples + 1);
    assert_eq!(evidence.counters.duplicate_admissions, before.duplicate_admissions + 1);
    assert!(evidence.bytes().unwrap() > bytes);
    assert!(session.resource_ledger.inference_session_retained_bytes >= sampled_before + evidence.bytes().unwrap() - bytes);
    assert_eq!(session.candidate_bound_origin_count(bound), 1);
    assert!(evidence.admissions.iter().all(|admission| admission.coverage.contains(CoverageGap::OrdinarySeedAuthenticationUnavailable)));
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn support_retention_frozen_transitive_snapshots_and_delta_rollback() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 84);
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let a = BoundKey(value(session.fresh_value_at_level(2).unwrap()), Polarity::Positive, lower);
    let b = BoundKey(value(session.fresh_value_at_level(2).unwrap()), Polarity::Positive, lower);
    let c_row = session.fresh_value_at_level(2).unwrap();
    let c = BoundKey(value(c_row), Polarity::Positive, lower);
    let first_emission = session.candidate_insert_bound_with_evidence(a.0, a.1, a.2, true, BoundAdmissionCause::OwnerEmission { processing: None }).unwrap();
    let relation = state(&session).bound_relations(a).next().unwrap();
    let snapshot = state(&session).evidence.snapshot(a, Some(relation));
    let source = session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.import_evidence(snapshot).unwrap();
    let middle_emission = session.candidate_insert_bound_with_evidence(b.0, b.1, b.2, true,
        BoundAdmissionCause::BoundTransport { antecedent: source, through: TransportReason::EqualityCanonicalization }).unwrap();
    let b_relation = state(&session).bound_relations(b).next().unwrap();
    let frozen_b = state(&session).evidence.snapshot(b, Some(b_relation));
    let middle_source = session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.import_evidence(frozen_b).unwrap();
    let mapped = session.candidate_context_fresh_transport(b_relation, c, 1, IDENTITY, b).unwrap();
    session.candidate_insert_bound_with_evidence(c.0, c.1, c.2, true,
        BoundAdmissionCause::FreshUse { antecedent: middle_source, use_origin: 1, source_bound: b, mapped_relation: Some(mapped) }).unwrap();
    let graph = session.capture_candidate_graph(c_row, 0).unwrap();
    session.candidate_graph.as_mut().unwrap().scratch_bytes -= graph.bytes().unwrap();
    for key in [a, b] { session.candidate_insert_bound(key.0, key.1, key.2).unwrap(); }
    assert_eq!(state(&session).evidence.snapshots[source.0], snapshot);
    assert_eq!(state(&session).evidence.snapshots[middle_source.0], frozen_b);
    assert_eq!(snapshot.emission_head, Some(first_emission));
    assert_eq!(frozen_b.emission_head, Some(middle_emission));
    assert_eq!(state(&session).evidence.emissions[first_emission.0].previous_on_group, None);
    assert_eq!(state(&session).evidence.emissions[middle_emission.0].previous_on_group, None);
    let before = state(&session).checkpoint();
    assert_eq!(session.with_route_transaction(|session| {
        session.freshen_candidate_graph(&graph, 3, &occurrence, &cause)?;
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    session.with_route_transaction(|session| session.freshen_candidate_graph(&graph, 3, &occurrence, &cause).map(|_| ())).unwrap();
    assert_eq!(state(&session).evidence.snapshots[source.0], snapshot);
    assert_eq!(state(&session).evidence.snapshots[middle_source.0], frozen_b);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn support_retention_capture_fresh_use_imports_and_route_failure_retry() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 81);
    let root = session.fresh_value_at_level(2).unwrap();
    let shared = session.fresh_value_at_level(0).unwrap();
    let effect = session.fresh_effect_at_level(2).unwrap();
    session.candidate_insert_bound(value(root), Polarity::Positive, value(shared)).unwrap();
    let argument = session.batch.collected_leaf_term(Leaf::IntNegative);
    let result = session.batch.collected_leaf_term(Leaf::IntPositive);
    let argument_effect = session.live_effect_term(Polarity::Negative, effect).unwrap();
    let result_effect = session.live_effect_term(Polarity::Positive, effect).unwrap();
    let function = session.positive_function_term(argument, argument_effect, result_effect, result).unwrap();
    let endpoint = session.value_endpoint(function, Polarity::Positive);
    session.candidate_insert_bound(value(root), Polarity::Positive, ExtrusionEndpoint::Value(endpoint)).unwrap();
    session.candidate_insert_bound(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(effect)), Polarity::Positive,
        ExtrusionEndpoint::Effect(EffectEndpointKey::BottomPositive)).unwrap();
    let graph = session.capture_candidate_graph(root, 0).unwrap();
    assert!(!graph.bounds.is_empty());
    assert!(graph.bound_evidence.len() <= graph.bounds.len());
    assert!(graph.bounds.iter().all(|bound| bound.evidence.0 < graph.bound_evidence.len()));
    session.candidate_graph.as_mut().unwrap().scratch_bytes -= graph.bytes().unwrap();
    let before = state(&session).checkpoint();
    let row_lengths = (session.bounds.len(), session.effect_bounds.len());
    let failed: Result<(), SolveAvailabilityError> = session.with_route_transaction(|session| {
        session.freshen_candidate_graph(&graph, 3, &occurrence, &cause)?;
        Err(exhausted())
    });
    assert_eq!(failed, Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), before);
    assert_eq!((session.bounds.len(), session.effect_bounds.len()), row_lengths);
    for _ in 0..2 {
        session.with_route_transaction(|session| session.freshen_candidate_graph(&graph, 3, &occurrence, &cause).map(|_| ())).unwrap();
    }
    let evidence = &state(&session).evidence;
    let uses = evidence.admissions[before.evidence.admissions..].iter().filter_map(|admission| match admission.cause {
        BoundAdmissionCause::FreshUse { antecedent, use_origin, mapped_relation, .. } => {
            assert!(antecedent.0 < evidence.snapshots.len());
            assert!(admission.coverage.contains(CoverageGap::ReplayUseAntecedentsNotRetained));
            assert!(mapped_relation.is_some());
            Some(use_origin)
        }
        _ => None,
    }).collect::<HashSet<_>>();
    assert_eq!(uses.len(), 2);
    assert!(session.candidate_graph.as_ref().unwrap().capture_evidence_peak_capacity >= graph.bound_evidence.len());
    assert!(session.candidate_graph.as_ref().unwrap().import_evidence_peak_capacity >= graph.bound_evidence.len());
    assert!(evidence.emissions[before.evidence.emissions..].iter().any(|emission| emission.physical.lane == BoundLane::EffectLowerAtom));
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn support_retention_shared_and_fanout_replay_recipes_stay_canonical() {
    for (anchors, k, uses) in [(1, 4, 8), (4, 2, 4)] {
        let mut session = session();
        let (occurrence, cause) = cause(&session, 82);
        let mut owners = Vec::new();
        for _ in 0..anchors {
            let owner = value(session.fresh_value_at_level(0).unwrap());
            let mut lowers = Vec::new();
            for _ in 0..k {
                let lower = value(session.fresh_value_at_level(0).unwrap());
                let upper = value(session.fresh_value_at_level(0).unwrap());
                session.candidate_insert_bound(owner, Polarity::Positive, lower).unwrap();
                session.candidate_insert_bound(owner, Polarity::Negative, upper).unwrap();
                lowers.push(lower);
            }
            owners.push((owner, lowers));
        }
        // Actual restore owners execute incoming-use replay on shared identities.
        for _ in 0..uses {
            for (owner, lowers) in &owners {
                for &lower in lowers {
                    session.candidate_restore_bound(*owner, Polarity::Positive, lower, &occurrence, &cause).unwrap();
                }
            }
        }
        let context = state(&session);
        let dependencies = context.dependencies.iter().filter(|dependency| matches!(dependency, Dependency::Replay { .. })).count();
        assert_eq!(context.evidence.recipes.len(), dependencies);
        assert!(context.evidence.recipes.iter().all(|recipe| recipe.coverage.contains(CoverageGap::ReplayUseAntecedentsNotRetained)));
        let recipe_count = context.evidence.recipes.len();
        let visits = context.evidence.counters.replay_visits;
        let semantic = (context.relations.len(), context.dependencies.len(), context.bound_keys.len());
        for (owner, lowers) in &owners {
            for &lower in lowers { session.candidate_restore_bound(*owner, Polarity::Positive, lower, &occurrence, &cause).unwrap(); }
        }
        let context = state(&session);
        assert_eq!(context.evidence.recipes.len(), recipe_count);
        assert_eq!((context.relations.len(), context.dependencies.len(), context.bound_keys.len()), semantic);
        assert!(context.evidence.counters.replay_visits > visits);
        assert!(context.evidence.counters.recipe_hits > 0);
        assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
        eprintln!("support retention anchors={anchors} K=L={k} U={uses}: D={dependencies}, fibers={}, products={}, hits={}, admissions={}, emissions={}, bytes={}",
            context.bound_keys.len(), context.evidence.counters.replay_visits, context.evidence.counters.recipe_hits,
            context.evidence.admissions.len(), context.evidence.emissions.len(), context.evidence.bytes().unwrap());
    }
    let mut source = session_with_source("my answer = 1 as int");
    let owner = empty_bundle_owner(&source);
    source.execute_candidate_source_root(&owner).unwrap();
    assert!(source.errors.is_empty());
}

#[test]
fn support_retention_charged_failure_locations_rollback_no_ids_escape_and_retry() {
    for point in [EvidenceFailurePoint::Admission, EvidenceFailurePoint::Emission,
        EvidenceFailurePoint::ImportReserve, EvidenceFailurePoint::ImportedSnapshot, EvidenceFailurePoint::Transport,
        EvidenceFailurePoint::Recipe, EvidenceFailurePoint::CaptureScratch] {
        let mut session = session();
        let (occurrence, cause) = cause(&session, 83);
        let root = session.fresh_value_at_level(2).unwrap();
        let destination = session.fresh_value_at_level(2).unwrap();
        let lower = value(session.fresh_value_at_level(0).unwrap());
        let upper = value(session.fresh_value_at_level(0).unwrap());
        session.candidate_insert_bound(value(root), Polarity::Positive, lower).unwrap();
        session.candidate_insert_bound(value(root), Polarity::Negative, upper).unwrap();
        let graph = session.capture_candidate_graph(root, 0).unwrap();
        session.candidate_graph.as_mut().unwrap().scratch_bytes -= graph.bytes().unwrap();
        assert!(graph.bound_evidence.len() > 1);
        let before = state(&session).checkpoint();
        let route_before = (session.bounds.len(), session.effect_bounds.len(), session.candidate_graph.as_ref().unwrap().routes.len());
        let row_before = (session.bounds[root as usize].direct_lower_rows.len(), session.bounds[root as usize].direct_upper_rows.len(),
            session.bounds[root as usize].exact_non_variable_lowers.len(), session.bounds[root as usize].has_int_positive_lower);
        let peak = session.resource_ledger.inference_session_peak_bytes;
        session.candidate_graph.as_mut().unwrap().evidence_failure = Some(point);
        let execute = |session: &mut InferenceSession| -> Result<(), SolveAvailabilityError> {
            match point {
                EvidenceFailurePoint::Admission | EvidenceFailurePoint::Emission => session.candidate_insert_bound(value(root), Polarity::Positive,
                    ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive)),
                EvidenceFailurePoint::ImportReserve | EvidenceFailurePoint::ImportedSnapshot => session.freshen_candidate_graph(&graph, 3, &occurrence, &cause).map(|_| ()),
                EvidenceFailurePoint::Transport => session.candidate_transfer_bound_origins(
                    BoundKey(value(root), Polarity::Positive, lower), BoundKey(value(destination), Polarity::Positive, lower),
                    TransportReason::ParentCopy { parent_index: 0 }),
                EvidenceFailurePoint::Recipe => session.candidate_restore_bound(value(root), Polarity::Positive, lower, &occurrence, &cause),
                EvidenceFailurePoint::CaptureScratch => session.capture_candidate_graph(root, 0).map(|_| ()),
            }
        };
        assert_eq!(session.with_route_transaction(execute), Err(exhausted()), "failure at {point:?}");
        assert_eq!(session.candidate_graph.as_ref().unwrap().failed_evidence_point, Some(point));
        assert_eq!(state(&session).checkpoint(), before, "rollback at {point:?}");
        assert_eq!((session.bounds.len(), session.effect_bounds.len(), session.candidate_graph.as_ref().unwrap().routes.len()), route_before);
        if point == EvidenceFailurePoint::ImportedSnapshot {
            assert_eq!(session.candidate_graph.as_ref().unwrap().failed_import_count, Some(1));
            let (scratch, total, sampled) = session.candidate_graph.as_ref().unwrap().import_failure_sample.unwrap();
            assert!(sampled && scratch > 0);
            assert!(session.resource_ledger.inference_session_peak_bytes >= total);
        }
        assert_eq!((session.bounds[root as usize].direct_lower_rows.len(), session.bounds[root as usize].direct_upper_rows.len(),
            session.bounds[root as usize].exact_non_variable_lowers.len(), session.bounds[root as usize].has_int_positive_lower), row_before);
        assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        assert!(session.resource_ledger.inference_session_peak_bytes >= peak);
        if matches!(point, EvidenceFailurePoint::ImportReserve | EvidenceFailurePoint::CaptureScratch) {
            let (_, charged_scratch, charged_total) = session.candidate_graph.as_ref().unwrap().failed_evidence_sample.unwrap();
            if point == EvidenceFailurePoint::CaptureScratch { assert!(charged_scratch > 0); }
            assert!(charged_total >= charged_scratch + state(&session).bytes().unwrap());
            assert!(session.resource_ledger.inference_session_peak_bytes >= charged_total);
            if point == EvidenceFailurePoint::ImportReserve {
                let (scratch, total, sampled) = session.candidate_graph.as_ref().unwrap().import_failure_sample.unwrap();
                assert!(sampled);
                assert_eq!(session.candidate_graph.as_ref().unwrap().failed_import_count, Some(0));
                assert_eq!(session.candidate_graph.as_ref().unwrap().import_evidence_peak_capacity, 0);
                assert!(scratch >= charged_scratch);
                assert!(session.resource_ledger.inference_session_peak_bytes >= total);
            }
        }
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
        session.with_route_transaction(execute).unwrap();
        let evidence = &state(&session).evidence;
        assert!(evidence.admissions.iter().all(|admission| match admission.cause {
            BoundAdmissionCause::FreshUse { antecedent, .. } | BoundAdmissionCause::BoundTransport { antecedent, .. } => antecedent.0 < evidence.snapshots.len(),
            _ => true,
        }));
        assert!(evidence.emissions.iter().all(|emission| emission.admission.0 < evidence.admissions.len()));
        if matches!(point, EvidenceFailurePoint::Admission | EvidenceFailurePoint::Emission | EvidenceFailurePoint::ImportedSnapshot | EvidenceFailurePoint::Transport | EvidenceFailurePoint::Recipe) {
            assert!(evidence.failed_attempts > 0 || point == EvidenceFailurePoint::ImportedSnapshot);
        }
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn support_retention_actual_extrusion_freezes_exact_fiber_heads_and_rolls_back() {
    let mut session = session();
    let parent = value(session.fresh_value_at_level(2).unwrap());
    let lower = ExtrusionEndpoint::Value(ValueEndpointKey::IntPositive);
    let from = BoundKey(parent, Polarity::Positive, lower);
    let emission = session.candidate_insert_bound_with_evidence(parent, Polarity::Positive, lower, true,
        BoundAdmissionCause::OwnerEmission { processing: None }).unwrap();
    let source_relation = state(&session).bound_relations(from).next().unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let operation = context.context(ContextExpr::Swap { input: IDENTITY }).unwrap();
    let second_relation = context.relation(bound_pair(from), operation).unwrap();
    context.attach(from, second_relation).unwrap();
    context.processing = Some(second_relation);
    let second_emission = session.candidate_insert_bound_with_evidence(parent, Polarity::Positive, lower, true,
        BoundAdmissionCause::OwnerEmission { processing: Some(second_relation) }).unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = None;
    let parents = [source_relation, second_relation];
    let frozen: Vec<_> = parents.iter().map(|&parent| state(&session).evidence.snapshot(from, Some(parent))).collect();
    assert_ne!(frozen[0], frozen[1]);
    assert_eq!(frozen[0].emission_head, Some(emission));
    assert_eq!(frozen[1].emission_head, Some(second_emission));
    let before = state(&session).checkpoint();
    for rollback in [true, false] {
        let result = session.with_route_transaction(|session| {
            let copy = session.candidate_extrude(parent, Polarity::Positive, 0)?;
            let transforms: Vec<_> = state(session).evidence.transforms.iter().filter(|transform| transform.from == from && transform.to.0 == copy).copied().collect();
            assert_eq!(transforms.len(), 2);
            assert_ne!(transforms[0].antecedent, transforms[1].antecedent);
            assert_ne!(transforms[0].child_relation, transforms[1].child_relation);
            for (index, &source_relation) in parents.iter().enumerate() {
                let transform = *transforms.iter().find(|transform| transform.source_relation == source_relation).unwrap();
                assert_eq!(state(session).evidence.snapshots[transform.antecedent.0], frozen[index]);
                assert_eq!(transform.coverage, frozen[index].coverage);
                assert!(state(session).dependency_keys.contains(&Dependency::Transport { child: transform.child_relation,
                    parent: source_relation, use_origin: 0, witness: Some(TransportWitness { from, to: transform.to, reason: transform.reason }) }));
                let count = state(session).evidence.transforms.len();
                let semantic = (state(session).relations.len(), state(session).dependencies.len(), state(session).bound_keys.len());
                session.candidate_context_transport_witness_with_evidence(source_relation, transform.to, 0,
                    TransportWitness { from, to: transform.to, reason: transform.reason })?;
                assert_eq!(state(session).evidence.transforms.len(), count);
                assert_eq!((state(session).relations.len(), state(session).dependencies.len(), state(session).bound_keys.len()), semantic);
                assert!(state(session).evidence.counters.transform_hits > 0);
                session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(source_relation);
                session.candidate_insert_bound(parent, Polarity::Positive, lower)?;
                session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = None;
                assert_eq!(state(session).evidence.snapshots[transform.antecedent.0], frozen[index]);
                assert_ne!(state(session).evidence.snapshot(from, Some(source_relation)).emission_head, frozen[index].emission_head);
            }
            assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
            if rollback { Err(exhausted()) } else { Ok(()) }
        });
        if rollback { assert_eq!(result, Err(exhausted())); assert_eq!(state(&session).checkpoint(), before); }
        else { result.unwrap(); }
    }
}

#[test]
fn support_retention_identity_function_named_ports_rollback_retry() {
    let mut session = session_with_source("my answer x:int -> int = x");
    let owner = empty_bundle_owner(&session);
    let before = state(&session).checkpoint();
    let mut attempted = Vec::new();
    for rollback in [true, false] {
        let result = session.with_route_transaction(|session| {
            session.execute_candidate_source_root(&owner)?;
            let context = state(session);
            let ports: Vec<_> = context.dependencies.iter().filter_map(|dependency| {
                if let Dependency::FunctionPort { child, parent, field, operation } = *dependency {
                    Some((child, parent, field, operation))
                } else { None }
            }).collect();
            for (field, operation) in [
                (FunctionField::Argument, FunctionPortOperation::Swap),
                (FunctionField::ArgumentEffect, FunctionPortOperation::Swap),
                (FunctionField::ResultEffect, FunctionPortOperation::Preserve),
                (FunctionField::Result, FunctionPortOperation::Preserve),
            ] {
                assert!(ports.iter().any(|port| (port.2, port.3) == (field, operation)), "missing named port {field:?}");
            }
            assert!(!context.evidence.admissions.is_empty());
            assert!(context.evidence.emissions.iter().all(|emission| emission.admission.0 < context.evidence.admissions.len()));
            if rollback { attempted = ports; Err(exhausted()) }
            else { assert_eq!(ports, attempted); Ok(()) }
        });
        if rollback {
            assert_eq!(result, Err(exhausted()));
            assert_eq!(state(&session).checkpoint(), before);
            assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        } else { result.unwrap(); }
    }
}

#[test]
fn owned_function_dispatch_retains_admitted_child_until_enqueue_and_rolls_back() {
    let mut session = session();
    let (occurrence, cause) = cause(&session, 0);
    let value_task = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
    });
    let value_pair = task_pair(value_task);
    let effect_pair = TypedPairKey::Effect {
        lower: EffectEndpointKey::BottomPositive, upper: EffectEndpointKey::EmptyNegative,
    };
    let children = [
        (FunctionField::Argument, value_pair),
        (FunctionField::ArgumentEffect, effect_pair),
        (FunctionField::ResultEffect, effect_pair),
        (FunctionField::Result, value_pair),
    ];
    let before = state(&session).checkpoint();
    let run = |session: &mut InferenceSession, fail: bool| -> Result<(), SolveAvailabilityError> {
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let parent = context.relation(value_pair, IDENTITY)?;
        context.processing = Some(parent);
        let index = context.begin_typed_drain(value_task, &occurrence, &cause, None, Some(parent))?;
        context.typed_drains[index].current = Some(TypedWorkItem { task: value_task, relation: Some(parent), replay_ack: None });
        context.typed_drains[index].function = Some(FunctionDispatch { children, next: 0, pending: None });
        context.typed_drains[index].stage = TypedDrainStage::FunctionAdmission;
        let mut admitted = Vec::new();
        for next in 0..children.len() {
            assert!(session.candidate_step_function_dispatch(index)?);
            let frame = &state(session).typed_drains[index];
            let dispatch = frame.function.as_ref().unwrap();
            assert_eq!(dispatch.next, next, "admission alone cannot advance the port cursor");
            assert_eq!(frame.stage, TypedDrainStage::FunctionEnqueue);
            assert_eq!(frame.current.unwrap().relation, Some(parent));
            assert_eq!((&frame.occurrence, &frame.cause), (&occurrence, &cause));
            let pending = dispatch.pending.unwrap();
            let relation = pending.relation.unwrap();
            let (field, pair) = children[children.len() - 1 - next];
            assert_eq!(task_pair(pending.task), pair);
            assert!(state(session).dependency_keys.contains(&Dependency::FunctionPort {
                parent, child: relation, field,
                operation: if matches!(field, FunctionField::Argument | FunctionField::ArgumentEffect) {
                    FunctionPortOperation::Swap
                } else { FunctionPortOperation::Preserve },
            }));
            assert_eq!(session.typed_worklist.len(), next);
            assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
            if fail { return Err(exhausted()); }
            admitted.push(pending);
            assert!(session.candidate_step_function_dispatch(index)?);
            let dispatch = state(session).typed_drains[index].function.as_ref().unwrap();
            assert_eq!(dispatch.next, next + 1);
            assert!(dispatch.pending.is_none());
            assert_eq!(session.typed_worklist.front(), Some(&pending));
        }
        assert!(!session.candidate_step_function_dispatch(index)?);
        assert_eq!(session.typed_worklist.iter().copied().collect::<Vec<_>>(), admitted.into_iter().rev().collect::<Vec<_>>());
        // This test exercises a private step seam, not a completed typed drain.
        // Discard the whole synthetic route after inspecting its ownership.
        Err(exhausted())
    };
    for fail in [true, false] {
        assert_eq!(session.with_route_transaction(|session| run(session, fail)), Err(exhausted()));
        assert_eq!(state(&session).checkpoint(), before);
        assert!(state(&session).typed_drains.is_empty());
        assert!(session.typed_worklist.is_empty());
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn source_local_annotation_wait_retains_construction_and_restores_prior_frame_on_failure() {
    use crate::candidate_source::{CandidateRun, Schedule, Stage, Support, Wait};
    let mut session = session_with_source("my outer = { my local:int = 1; local }");
    let root = session.batch.definitions[0].root.clone();
    let position = session.batch.candidate_source.schedules[&root].iter()
        .position(|action| matches!(action, crate::candidate_source::Action::LocalAnnotation { .. })).unwrap();
    session.begin_candidate_source(Schedule::Root(0)).unwrap();
    while session.candidate_graph.as_ref().unwrap().source.unwrap().next < position {
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    }
    assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    let frame = session.candidate_graph.as_ref().unwrap().source.unwrap();
    let Stage::PublishLocal { slot, exposed, .. } = frame.stage else { panic!("constructed annotation must await publication"); };
    assert_eq!(frame.next, position, "construction does not consume the publication action");
    assert!(session.candidate_graph.as_ref().unwrap().locals[slot].is_none());
    let bounds_len = session.bounds.len();
    let facts_len = session.store.facts.len();
    let wait = Wait { generation: 7, dependency: position };
    assert_eq!(session.drive_candidate_source(Support { wait: Some(wait) }).unwrap(), CandidateRun::Suspended(wait));
    let waiting = session.candidate_graph.as_ref().unwrap().source.unwrap();
    let counters = session.execution_counters.clone();
    let samples = session.resource_boundary_samples;
    for _ in 0..3 {
        assert_eq!(session.drive_candidate_source(Support { wait: Some(wait) }).unwrap(), CandidateRun::Suspended(wait));
        assert_eq!(session.candidate_graph.as_ref().unwrap().source, Some(waiting));
        assert_eq!(session.resource_boundary_samples, samples, "unchanged wait does no work or sampling");
    }
    assert_eq!(session.execution_counters, counters);
    let mut checkpoint = None;
    assert_eq!(session.with_route_transaction(|session| {
        checkpoint = Some(RouteCheckpoint::capture(session));
        assert_eq!(session.step_candidate_source(Support::READY)?, CandidateRun::Complete(false));
        assert!(session.candidate_graph.as_ref().unwrap().locals[slot].is_some());
        assert_eq!(session.candidate_graph.as_ref().unwrap().source.unwrap().next, position + 1);
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    checkpoint.unwrap().assert_restored(&session);
    assert_eq!(session.candidate_graph.as_ref().unwrap().source, Some(waiting), "rollback restores a frame present before the checkpoint, including its wait and constructed root");
    assert!(session.candidate_graph.as_ref().unwrap().locals[slot].is_none());
    session.with_route_transaction(|session| {
        assert_eq!(session.step_candidate_source(Support::READY)?, CandidateRun::Complete(false));
        Ok(())
    }).unwrap();
    let scheme = session.candidate_graph.as_ref().unwrap().locals[slot].as_ref().unwrap();
    assert_eq!(ValueEndpointKey::ValueRow(scheme.root), session.value_endpoint(exposed, Polarity::Positive));
    assert_eq!(session.bounds.len(), bounds_len, "publication does not reconstruct the exposed root");
    assert_eq!(session.store.facts.len(), facts_len, "publication does not repeat annotation links");
    assert_eq!(session.drive_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(()));
    assert!(session.candidate_graph.as_ref().unwrap().source.is_none());
}

#[test]
fn source_cursor_wait_after_completed_local_use_does_not_freshen_it_again() {
    use crate::candidate_source::{Action, CandidateRun, Schedule, Support, Wait};
    let text = "my outer = { my id x = x; my first = id 1; id 2 }";
    let mut session = session_with_source(text);
    let root = session.batch.definitions[0].root.clone();
    let first_use = session.batch.candidate_source.schedules[&root].iter()
        .position(|action| matches!(action, Action::Local { .. })).unwrap();
    session.begin_candidate_source(Schedule::Root(0)).unwrap();
    while session.candidate_graph.as_ref().unwrap().source.unwrap().next <= first_use {
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    }
    assert_eq!(session.candidate_graph.as_ref().unwrap().local_routes.len(), 1);
    let next_use = state(&session).checkpoint();
    let facts_len = session.store.facts.len();
    let wait = Wait { generation: 11, dependency: first_use + 1 };
    for _ in 0..3 {
        assert_eq!(session.drive_candidate_source(Support { wait: Some(wait) }).unwrap(), CandidateRun::Suspended(wait));
        assert_eq!(state(&session).checkpoint(), next_use, "waiting preserves the completed per-use identities");
        assert_eq!(session.store.facts.len(), facts_len);
        assert_eq!(session.candidate_graph.as_ref().unwrap().local_routes.len(), 1);
    }
    assert_eq!(session.drive_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(()));
    assert_eq!(session.candidate_graph.as_ref().unwrap().local_routes.len(), 2, "only the remaining source occurrence freshens");
    let mut uninterrupted = session_with_source(text);
    let root = uninterrupted.batch.definitions[0].root.clone();
    uninterrupted.execute_candidate_source_root(&root).unwrap();
    assert_eq!(session.candidate_graph.as_ref().unwrap().local_routes.len(), uninterrupted.candidate_graph.as_ref().unwrap().local_routes.len());
    assert_eq!(session.store.facts.len(), uninterrupted.store.facts.len());
    assert_eq!(session.errors, uninterrupted.errors);
}

#[test]
fn function_port_lifecycle_generation_exhaustion_precedes_mutation_and_duplicates_remain_inert() {
    let mut context = State::default();
    assert!(context.bytes().unwrap() >= std::mem::size_of::<u64>(), "the fixed lifecycle owner is included in retained bytes");
    let parent_pair = task_pair(LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
    }));
    let child_pair = task_pair(LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::UnitPositive, upper: ValueEndpointKey::TopNegative,
    }));
    let parent = context.relation(parent_pair, IDENTITY).unwrap();
    let child = context.relation(child_pair, IDENTITY).unwrap();
    context.dependency(Dependency::Derived { parent, child }).unwrap();
    assert_eq!(context.lifecycle_generation, 0, "Derived admission is outside this first producer hook");
    let port = Dependency::FunctionPort { parent, child, field: FunctionField::Argument, operation: FunctionPortOperation::Swap };
    context.lifecycle_generation = u64::MAX;
    let before = context.checkpoint();
    let bytes = context.bytes().unwrap();
    assert_eq!(context.dependency(port), Err(exhausted()));
    assert_eq!(context.checkpoint(), before);
    assert_eq!(context.bytes().unwrap(), bytes, "generation exhaustion precedes even dependency reservation");
    assert!(!context.dependency_keys.contains(&port));
    context.lifecycle_generation = 0;
    context.dependency(port).unwrap();
    assert_eq!(context.lifecycle_generation, 1);
    context.lifecycle_generation = u64::MAX;
    let duplicate = context.checkpoint();
    context.dependency(port).unwrap();
    assert_eq!(context.checkpoint(), duplicate, "a duplicate does not require another generation");
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn function_port_lifecycle_identity_source_completes_without_certificate_or_suspension() {
    let mut session = session_with_source("my answer x:int -> int = x");
    let owner = empty_bundle_owner(&session);
    let before = state(&session).lifecycle_generation;
    session.execute_candidate_source_root(&owner).unwrap();
    let context = state(&session);
    let mut ports = 0;
    for dependency in &context.dependencies {
        if let Dependency::FunctionPort { parent, child, .. } = dependency {
            ports += 1;
            assert_eq!(context.relations[parent.0 as usize].key.context, IDENTITY);
            assert_eq!(context.relations[child.0 as usize].key.context, IDENTITY);
        }
    }
    assert!(ports > 0, "ordinary identity source exercises the real producer hook");
    assert_eq!(context.lifecycle_generation, before + ports);
    assert!(context.typed_drains.is_empty());
    assert!(session.candidate_graph.as_ref().unwrap().source.is_none(), "generation changes alone do not suspend ordinary source");
    assert!(session.errors.is_empty());
    let roots: Vec<_> = context.dependencies.iter().filter_map(|dependency| match dependency {
        Dependency::FunctionPort { parent, .. } => Some(*parent), _ => None,
    }).collect();
    let input = context.retained_input(&roots, &[], &[]).unwrap();
    let InputCompleteness::Incomplete(gaps) = &input.completeness else { panic!("generation alone cannot mint a certificate"); };
    assert!(gaps.contains(&InputGap::ProducerReadinessUnavailable));
    assert!(gaps.contains(&InputGap::FilterObligationsUnavailable));
    assert!(gaps.contains(&InputGap::DependentObservationsUnavailable));
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

fn retained_source_publication() -> (InferenceSession, RelationId, RelationId) {
    use crate::candidate_source::{CandidateRun, Schedule, Stage, Support};
    let mut session = session_with_source("my outer = { my local:int = 1; local }");
    let root = session.batch.definitions[0].root.clone();
    let position = session.batch.candidate_source.schedules[&root].iter()
        .position(|action| matches!(action, crate::candidate_source::Action::LocalAnnotation { .. })).unwrap();
    session.begin_candidate_source(Schedule::Root(0)).unwrap();
    while session.candidate_graph.as_ref().unwrap().source.unwrap().next < position {
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    }
    assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    assert!(matches!(session.candidate_graph.as_ref().unwrap().source.unwrap().stage, Stage::PublishLocal { .. }));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    let parent = context.relation(TypedPairKey::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::TopNegative,
    }), IDENTITY).unwrap();
    let child = context.relation(TypedPairKey::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::UnitPositive, upper: ValueEndpointKey::TopNegative,
    }), IDENTITY).unwrap();
    context.dependency(Dependency::Derived { parent, child }).unwrap();
    (session, parent, child)
}

#[test]
fn exact_source_support_endpoint_invalidation_withholds_constructed_publication_and_ready_is_inert() {
    use crate::candidate_source::{CandidateRun, Stage, Support, Wait};
    for watch_child in [false, true] {
        let (mut session, parent, child) = retained_source_publication();
        let id = session.supply_synthetic_source_support(&[if watch_child { child } else { parent }]).unwrap();
        let original = session.candidate_graph.as_ref().unwrap().source.unwrap();
        let Stage::PublishLocal { slot, exposed, .. } = original.stage else { unreachable!() };
        let before = state(&session).checkpoint();
        let equality = session.candidate_graph.as_ref().unwrap().intrusion.generation;
        let port = Dependency::FunctionPort { parent, child, field: FunctionField::Argument, operation: FunctionPortOperation::Swap };
        session.with_route_transaction(|session| {
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.dependency(port)?;
            assert_eq!(state(session).relations.len(), before.relations);
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.generation, equality);
            let wait = state(session).source_support_wait(id)?.unwrap();
            assert_eq!(session.step_candidate_source(Support::READY)?, CandidateRun::Suspended(wait));
            Ok(())
        }).unwrap();
        let waiting = session.candidate_graph.as_ref().unwrap().source.unwrap();
        let wait = waiting.wait.unwrap();
        assert_eq!(waiting.stage, original.stage);
        assert_eq!(waiting.next, original.next);
        assert!(session.candidate_graph.as_ref().unwrap().locals[slot].is_none());
        let samples = session.resource_boundary_samples;
        let facts = session.store.facts.len();
        for support in [Support::READY, Support { wait: Some(Wait { generation: u64::MAX, dependency: usize::MAX }) }, Support::READY] {
            assert_eq!(session.drive_candidate_source(support).unwrap(), CandidateRun::Suspended(wait));
            assert_eq!(session.candidate_graph.as_ref().unwrap().source, Some(waiting));
            assert_eq!(session.resource_boundary_samples, samples);
        }
        let snapshot = state(&session).checkpoint();
        session.with_route_transaction(|session| {
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.dependency(port)?;
            assert_eq!(state(session).checkpoint(), snapshot, "exact duplicate is inert");
            Ok(())
        }).unwrap();
        assert_eq!(session.with_route_transaction(|session| {
            session.supply_synthetic_source_support(&[parent, child])?;
            assert_eq!(session.step_candidate_source(Support::READY)?, CandidateRun::Complete(false));
            assert!(session.candidate_graph.as_ref().unwrap().locals[slot].is_some());
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        assert_eq!(session.candidate_graph.as_ref().unwrap().source, Some(waiting));
        assert!(session.candidate_graph.as_ref().unwrap().locals[slot].is_none());
        assert_eq!(state(&session).source_support_wait(id).unwrap(), Some(wait));
        session.supply_synthetic_source_support(&[parent, child]).unwrap();
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
        let scheme = session.candidate_graph.as_ref().unwrap().locals[slot].as_ref().unwrap();
        assert_eq!(ValueEndpointKey::ValueRow(scheme.root), session.value_endpoint(exposed, Polarity::Positive));
        assert_eq!(session.store.facts.len(), facts, "supported replacement publishes the retained construction once");
        assert!(session.candidate_graph.as_ref().unwrap().source.unwrap().registration.is_none());
        assert_eq!(session.drive_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(()));
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn exact_source_support_unrelated_incidence_and_duplicate_do_not_invalidate() {
    let mut context = State::default();
    let mut ids = Vec::new();
    for lower in [ValueEndpointKey::IntPositive, ValueEndpointKey::UnitPositive, ValueEndpointKey::BottomPositive] {
        ids.push(context.relation(TypedPairKey::Value(CanonicalValuePairKey { lower, upper: ValueEndpointKey::TopNegative }), IDENTITY).unwrap());
    }
    let port = Dependency::FunctionPort { parent: ids[1], child: ids[2], field: FunctionField::Argument, operation: FunctionPortOperation::Swap };
    context.dependency(port).unwrap();
    let watched_duplicate = context.synthetic_source_support(&[ids[1]]).unwrap();
    let unrelated = context.synthetic_source_support(&[ids[0]]).unwrap();
    let before = context.checkpoint();
    context.dependency(port).unwrap();
    assert_eq!(context.checkpoint(), before);
    assert_eq!(context.source_support_wait(watched_duplicate).unwrap(), None);
    context.dependency(Dependency::FunctionPort { parent: ids[1], child: ids[2], field: FunctionField::Result, operation: FunctionPortOperation::Preserve }).unwrap();
    assert!(context.source_support_wait(watched_duplicate).unwrap().is_some());
    assert_eq!(context.source_support_wait(unrelated).unwrap(), None);
    assert_eq!(context.bytes().unwrap(), context.enumerated_bytes());
}

#[test]
fn exact_source_support_registration_and_dependency_failures_restore_frame_and_validity() {
    use crate::candidate_source::{CandidateRun, Support};
    let (mut session, parent, child) = retained_source_publication();
    let id = session.supply_synthetic_source_support(&[parent]).unwrap();
    let frame = session.candidate_graph.as_ref().unwrap().source;
    let before = state(&session).checkpoint();
    let port = Dependency::FunctionPort { parent, child, field: FunctionField::Argument, operation: FunctionPortOperation::Swap };
    for failure in [SourceSupportFailure::Registration, SourceSupportFailure::DependencyPublication, SourceSupportFailure::AfterInvalidation] {
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.source_support_failure = Some(failure);
        let mut checkpoint = None;
        assert_eq!(session.with_route_transaction(|session| {
            checkpoint = Some(RouteCheckpoint::capture(session));
            if failure == SourceSupportFailure::Registration { session.supply_synthetic_source_support(&[child])?; }
            else { session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.dependency(port)?; }
            Ok(())
        }), Err(exhausted()));
        checkpoint.unwrap().assert_restored(&session);
        assert_eq!(state(&session).checkpoint(), before);
        assert_eq!(session.candidate_graph.as_ref().unwrap().source, frame);
        assert_eq!(state(&session).source_support_wait(id).unwrap(), None);
        assert!(!state(&session).dependency_keys.contains(&port));
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
    let mut stale = None;
    assert_eq!(session.with_route_transaction(|session| {
        stale = Some(session.supply_synthetic_source_support(&[child])?);
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.dependency(port)?;
        assert!(matches!(session.step_candidate_source(Support::READY)?, CandidateRun::Suspended(_)));
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(session.candidate_graph.as_ref().unwrap().source, frame);
    assert_eq!(state(&session).source_support_wait(id).unwrap(), None);
    assert_eq!(state(&session).source_support_wait(stale.unwrap()), Err(exhausted()));
    let replacement = session.supply_synthetic_source_support(&[parent]).unwrap();
    assert_ne!(Some(replacement), stale, "rolled-back IDs are never recycled");
    assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    assert_eq!(session.drive_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(()));
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

fn terminal_drain_fixture(session: &mut InferenceSession, empty: bool) -> (usize, ReplayOperationId, ReplayOperationId) {
    let (occurrence, cause) = cause(session, 0);
    let owner = session.fresh_value_at_level(1).unwrap();
    let lower = session.fresh_value_at_level(1).unwrap();
    let upper = session.fresh_value_at_level(1).unwrap();
    session.candidate_insert_bound(value(owner), Polarity::Negative, value(upper)).unwrap();
    let restoration = session.candidate_begin_bound_restoration(value(owner), Polarity::Positive, value(lower),
        &occurrence, &cause, BoundAdmissionCause::OwnerEmission { processing: None }).unwrap();
    let lower_input = BoundKey(value(owner), Polarity::Positive, value(lower));
    let upper_input = BoundKey(value(owner), Polarity::Negative, value(upper));
    let replay = session.candidate_context_begin_replay(lower_input, upper_input, task(lower, upper), true).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    // Terminal-only fixture: preserve two exact ordered occurrences of the
    // generated child without invoking diagnostic or constraint dispatch again.
    if empty {
        let operation = context.replay_operations.get_mut(&replay).unwrap();
        context.replay_child_bytes -= operation.children.capacity() * std::mem::size_of::<RelationId>();
        operation.children = Vec::new();
    } else {
        let operation = context.replay_operations.get_mut(&replay).unwrap();
        let relation = operation.children[0];
        let old_capacity = operation.children.capacity();
        operation.children.push(relation);
        context.replay_child_bytes += (operation.children.capacity() - old_capacity) * std::mem::size_of::<RelationId>();
        operation.queued = operation.children.len();
    }
    context.set_restoration_replay(restoration, replay);
    let index = context.begin_typed_drain(task(lower, upper), &occurrence, &cause,
        Some(task_pair(task(lower, upper))), context.replay_operations[&replay].children.first().copied()).unwrap();
    let frame = &mut context.typed_drains[index];
    frame.stage = TypedDrainStage::Acknowledgements;
    frame.transitions = 19;
    frame.replay_acks = (0..context.replay_operations[&replay].children.len())
        .map(|index| ReplayChildAck { operation: replay, index }).collect();
    // Warm only journal storage, so exact retained-byte equality after rollback
    // is independent of the allocator's first capacity growth.
    context.typed_drain_undo.try_reserve(1).unwrap();
    context.replay_operation_undo.try_reserve(8).unwrap();
    context.restoration_undo.try_reserve(4).unwrap();
    (index, restoration, replay)
}

#[test]
fn typed_drain_terminal_partial_ack_failure_resume_and_exact_rollback() {
    let mut session = session();
    let (index, restoration, replay) = terminal_drain_fixture(&mut session, false);
    session.with_route_transaction(|session| {
        assert_eq!(session.candidate_step_typed_drain_terminal(index)?, None);
        Ok(())
    }).unwrap();
    assert_eq!(state(&session).typed_drains[index].completed_acks, 1);
    assert_eq!(state(&session).typed_drains[index].prepared_acks, 1, "commit releases the remaining children's preflight ownership");
    assert!(!state(&session).typed_drains[index].terminal_prepared);
    let original_frame = state(&session).typed_drains[index].clone();
    let original_capacity = state(&session).typed_drains[index].replay_acks.capacity();
    let original_replay = state(&session).replay_operations[&replay].clone();
    let original_restoration = state(&session).restorations[&restoration].clone();
    let checkpoint = state(&session).checkpoint();
    let bytes = state(&session).bytes().unwrap();
    let errors = session.errors.clone();
    let processing = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.processing;
    assert_eq!(session.with_route_transaction(|session| {
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.fail_replay_completion_undo_reserve = true;
        assert_eq!(session.candidate_step_typed_drain_terminal(index), Err(exhausted()));
        assert_eq!(state(session).typed_drains[index], original_frame);
        assert_eq!(state(session).replay_operations[&replay], original_replay);
        assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), checkpoint);
    assert_eq!(state(&session).typed_drains[index], original_frame);
    assert_eq!(state(&session).typed_drains[index].replay_acks.capacity(), original_capacity);
    assert_eq!(state(&session).bytes().unwrap(), bytes);
    assert_eq!(session.with_route_transaction(|session| {
        assert_eq!(session.candidate_step_typed_drain_terminal(index)?, None);
        assert_eq!(state(session).typed_drains[index].stage, TypedDrainStage::ReturnReady);
        assert_eq!(state(session).typed_drains[index].completed_acks, 2);
        assert_eq!(state(session).replay_operations[&replay].consumed, 2);
        assert_eq!(session.candidate_step_typed_drain_terminal(index)?, Some(19));
        assert!(state(session).typed_drains.is_empty());
        assert_eq!(state(session).bytes()?, state(session).enumerated_bytes());
        Err::<(), _>(exhausted())
    }), Err(exhausted()));
    assert_eq!(state(&session).checkpoint(), checkpoint);
    assert_eq!(state(&session).typed_drains[index], original_frame);
    assert_eq!(state(&session).typed_drains[index].replay_acks.capacity(), original_capacity);
    assert_eq!(state(&session).replay_operations[&replay], original_replay);
    assert_eq!(state(&session).restorations[&restoration], original_restoration);
    assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.processing, processing);
    assert_eq!(state(&session).bytes().unwrap(), bytes);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    session.with_route_transaction(|session| {
        assert_eq!(session.candidate_finish_typed_drain(index)?, 19);
        Ok(())
    }).unwrap();
    assert!(state(&session).typed_drains.is_empty());
    assert_eq!(state(&session).replay_operations[&replay].consumed, 2);
    assert_eq!(session.errors, errors, "terminal resume never repeats successful diagnostics");
    session.candidate_drive_bound_restoration(restoration).unwrap();
    assert!(!state(&session).replay_operations.contains_key(&replay));
    assert!(!state(&session).restorations.contains_key(&restoration));
}

#[test]
fn typed_drain_terminal_final_child_handoff_and_empty_batch_keep_parent_handle_usable() {
    for transactional in [false, true] { for empty in [false, true] {
        let mut session = session();
        let (index, restoration, replay) = terminal_drain_fixture(&mut session, empty);
        let run = |session: &mut InferenceSession| -> Result<(), SolveAvailabilityError> {
            if empty {
                // Empty replay completion has the same parent handoff boundary.
                assert!(!session.candidate_context_consume_replay_child(replay, None)?);
            }
            assert_eq!(session.candidate_finish_typed_drain(index)?, 19);
            let context = state(session);
            assert_eq!(context.restorations[&restoration].replay, Some(replay));
            assert!(context.replay_operations[&replay].retired);
            assert_eq!(context.replay_operations[&replay].consumed, context.replay_operations[&replay].children.len());
            assert_eq!(context.bytes()?, context.enumerated_bytes());
            // Resuming the waiting parent observes the completed handle and
            // advances the physical product exactly once before reclaiming it.
            session.candidate_drive_bound_restoration(restoration)?;
            assert!(!state(session).restorations.contains_key(&restoration) || transactional);
            Ok(())
        };
        if transactional {
            let checkpoint = state(&session).checkpoint();
            let original_frame = state(&session).typed_drains[index].clone();
            let original_replay = state(&session).replay_operations[&replay].clone();
            let original_restoration = state(&session).restorations[&restoration].clone();
            let bytes = state(&session).bytes().unwrap();
            assert_eq!(session.with_route_transaction(|session| {
                run(session)?;
                Err::<(), _>(exhausted())
            }), Err(exhausted()));
            assert_eq!(state(&session).checkpoint(), checkpoint);
            assert_eq!(state(&session).typed_drains[index], original_frame);
            assert_eq!(state(&session).replay_operations[&replay], original_replay);
            assert_eq!(state(&session).restorations[&restoration], original_restoration);
            assert_eq!(state(&session).bytes().unwrap(), bytes);
            assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
            session.with_route_transaction(run).unwrap();
        } else { run(&mut session).unwrap(); }
        assert!(!state(&session).replay_operations.contains_key(&replay));
        assert!(!state(&session).restorations.contains_key(&restoration));
        assert!(state(&session).typed_drains.is_empty());
        assert_eq!(state(&session).replay_child_bytes, 0);
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    } }
}

#[test]
fn typed_drain_terminal_cold_undo_samples_active_and_rollback_peak_before_cleanup() {
    for fail_preflight in [false, true] {
        let mut session = session();
        let (index, restoration, replay) = terminal_drain_fixture(&mut session, false);
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        // This witness intentionally starts with cold terminal journal storage.
        context.typed_drain_undo = Vec::new();
        context.replay_operation_undo = Vec::new();
        let original_frame = context.typed_drains[index].clone();
        let original_replay = context.replay_operations[&replay].clone();
        let original_restoration = context.restorations[&restoration].clone();
        let mut sampled_peak = 0;
        assert_eq!(session.with_route_transaction(|session| {
            let attempts = session.incoming_route_sample_attempts;
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.fail_replay_completion_undo_reserve = fail_preflight;
            let result = session.candidate_step_typed_drain_terminal(index);
            assert_eq!(result, if fail_preflight { Err(exhausted()) } else { Ok(None) });
            assert!(session.incoming_route_sample_attempts > attempts);
            let context = state(session);
            assert_eq!(context.typed_drain_undo.len(), 1);
            assert!(context.typed_drain_undo.capacity() > 0);
            let active_ack_bytes = context.typed_drains[index].replay_acks.capacity() * std::mem::size_of::<ReplayChildAck>();
            let undo_ack_bytes = context.typed_drain_undo[0].frame.replay_acks.capacity() * std::mem::size_of::<ReplayChildAck>();
            assert!(active_ack_bytes > 0 && undo_ack_bytes > 0);
            assert_eq!(context.bytes()?, context.enumerated_bytes());
            sampled_peak = session.resource_ledger.inference_session_retained_bytes;
            assert!(session.resource_ledger.inference_session_peak_bytes >= sampled_peak);
            if fail_preflight {
                assert!(context.replay_operation_undo.is_empty());
                assert_eq!(context.typed_drains[index], original_frame);
            } else {
                assert_eq!(context.replay_operation_undo.len(), 1, "direct terminal preflight retains one applicable completion undo");
                // Model the existing pre-pop owner for the remaining child:
                // reserve once, then hand its prepared cursor to terminal.
                let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let ack = context.typed_drains[index].replay_acks[1];
                context.prepare_replay_child_completion(ack, true)?;
                context.typed_drains[index].prepared_acks = 2;
                context.fail_replay_completion_undo_reserve = true;
                let attempts = session.incoming_route_sample_attempts;
                assert_eq!(session.candidate_step_typed_drain_terminal(index)?, None);
                assert_eq!(session.incoming_route_sample_attempts, attempts, "unchanged acknowledgement storage needs no full sample");
                assert!(state(session).fail_replay_completion_undo_reserve, "prepared completion has no second fallible reservation");
                assert_eq!(state(session).replay_operation_undo.len(), 2, "each child has one applicable preflight");
                sampled_peak = session.resource_ledger.inference_session_retained_bytes;
                let event_context_bytes = state(session).bytes()?;
                assert_eq!(session.candidate_step_typed_drain_terminal(index)?, Some(19));
                assert_eq!(session.incoming_route_sample_attempts, attempts, "ReturnReady removal reuses the sampled peak");
                assert_eq!(state(session).bytes()? + active_ack_bytes, event_context_bytes);
                // The terminal sampler ran before pop. A subsequent sample
                // drops exactly the active acknowledgement allocation.
                assert_eq!(session.resource_ledger.inference_session_retained_bytes, sampled_peak);
                session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
                assert_eq!(session.resource_ledger.inference_session_retained_bytes + active_ack_bytes, sampled_peak);
            }
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        assert_eq!(state(&session).typed_drains[index], original_frame);
        assert_eq!(state(&session).replay_operations[&replay], original_replay);
        assert_eq!(state(&session).restorations[&restoration], original_restoration);
        assert!(state(&session).typed_drain_undo.is_empty());
        assert!(state(&session).replay_operation_undo.is_empty());
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
        session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
        assert!(session.resource_ledger.inference_session_retained_bytes < sampled_peak);
        assert!(session.resource_ledger.inference_session_peak_bytes >= sampled_peak);
    }
}

#[test]
fn parsed_local_use_retains_one_fresh_parent_across_committed_pause_and_failed_resume() {
    use crate::candidate_scheme::LocalScriptStep::{Complete, DriveOne, FailOne, Idle};
    use crate::candidate_source::{Action, CandidateRun, Schedule, Support};
    fn assert_same_term(left_session: &InferenceSession, left: Term, right_session: &InferenceSession, right: Term) {
        // Validate each handle in its owning arena before ignoring its brand.
        let left_view = left_session.store.term_view(left).unwrap();
        let right_view = right_session.store.term_view(right).unwrap();
        assert_eq!(left.test_index(), right.test_index());
        match (left_view, right_view) {
            (TermView::Leaf(left), TermView::Leaf(right)) => assert_eq!(left, right),
            (TermView::Component(left), TermView::Component(right)) => match (left, right) {
                (ComponentId::Occurrence { occurrence: left, kind: left_kind },
                    ComponentId::Occurrence { occurrence: right, kind: right_kind }) => {
                    assert_eq!(left.ordinal(), right.ordinal());
                    assert_eq!(left_kind, right_kind);
                }
                (ComponentId::DefinitionValue { root: left },
                    ComponentId::DefinitionValue { root: right }) => {
                    let left_position = left_session.batch.definitions.iter()
                        .position(|definition| &definition.root == left)
                        .expect("left definition component belongs to its session");
                    let right_position = right_session.batch.definitions.iter()
                        .position(|definition| &definition.root == right)
                        .expect("right definition component belongs to its session");
                    assert_eq!(left_position, right_position);
                }
                (left, right) => panic!("different component variants: {left:?} and {right:?}"),
            },
            (TermView::LiveVariable(left), TermView::LiveVariable(right)) => {
                assert_eq!(left.kind(), right.kind());
                assert_eq!(left.polarity(), right.polarity());
                assert_eq!(left.ordinal(), right.ordinal());
            }
            (TermView::PositiveBottom, TermView::PositiveBottom)
            | (TermView::NegativeTop, TermView::NegativeTop)
            | (TermView::NegativeBottom, TermView::NegativeBottom) => {}
            (TermView::PositiveFunction {
                argument: la, argument_effect: lae, result_effect: lre, result: lr,
            }, TermView::PositiveFunction {
                argument: ra, argument_effect: rae, result_effect: rre, result: rr,
            })
            | (TermView::NegativeFunction {
                argument: la, argument_effect: lae, result_effect: lre, result: lr,
            }, TermView::NegativeFunction {
                argument: ra, argument_effect: rae, result_effect: rre, result: rr,
            }) => {
                for (left, right) in [(la, ra), (lae, rae), (lre, rre), (lr, rr)] {
                    assert_same_term(left_session, left, right_session, right);
                }
            }
            (left, right) => panic!("different term variants: {left:?} and {right:?}"),
        }
    }
    let text = "my outer = { my local:int = 1; local }";
    let mut session = session_with_source(text);
    let root = session.batch.definitions[0].root.clone();
    let local_position = session.batch.candidate_source.schedules[&root].iter()
        .position(|action| matches!(action, Action::Local { .. })).unwrap();
    session.begin_candidate_source(Schedule::Root(0)).unwrap();
    while session.candidate_graph.as_ref().unwrap().source.unwrap().next < local_position {
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    }
    // Conditional enclosed test driver: no external incidence mutation, no
    // authenticated support, and no production Suspended outcome. Each drive
    // returns through the real route transaction and commits its retained parent.
    let observations = session.candidate_test_local_script(&[
        DriveOne, Idle, Idle, FailOne, DriveOne, FailOne, Complete,
    ]).unwrap();
    let paused = &observations[0];
    assert_eq!(paused.source_next, local_position);
    assert_eq!(paused.routes, 0, "unfinished Local does not publish a route");
    assert!(paused.cursor.unwrap().restoration.is_some());
    assert_eq!(paused.cursor.unwrap().next_bound, 0);
    assert!(paused.use_origin.is_some());
    assert_eq!(&observations[1], paused, "unchanged private pause performs no work");
    assert_eq!(&observations[2], paused);
    assert_eq!(&observations[3], paused, "failure restores the pre-existing parent and accepted handle");
    assert_eq!(observations[4].use_origin, paused.use_origin, "resume preserves the original fresh use");
    assert_eq!(observations[5], observations[4], "later owner-step failure restores the same cursor and accounting");
    let completed = &observations[6];
    assert_eq!(completed.source_next, local_position + 1);
    assert_eq!(completed.routes, 1);
    assert_eq!(completed.cursor, None);
    assert_eq!(completed.typed_drains, 0);
    assert_eq!(state(&session).uses, paused.use_origin.unwrap(), "one begin_use for this parsed Local");
    assert_eq!(session.drive_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(()));
    let mut uninterrupted = session_with_source(text);
    let root = uninterrupted.batch.definitions[0].root.clone();
    uninterrupted.execute_candidate_source_root(&root).unwrap();
    // Separate parsed-source sessions have distinct arena brands. Compare the
    // ordered facts and owned endpoint structures, without claiming provenance parity.
    assert_eq!(session.store.facts.len(), uninterrupted.store.facts.len());
    for (left, right) in session.store.facts.iter().zip(&uninterrupted.store.facts) {
        assert_eq!(left.id(), right.id());
        assert_same_term(&session, left.lower(), &uninterrupted, right.lower());
        assert_same_term(&session, left.upper(), &uninterrupted, right.upper());
    }
    assert_eq!(session.errors, uninterrupted.errors);
    assert_eq!(state(&session).uses, state(&uninterrupted).uses);
    assert_eq!(state(&session).evidence.emissions.len(), state(&uninterrupted).evidence.emissions.len(), "accepted bound emission is not repeated");
}

#[test]
fn internal_restoration_owner_steps_keep_multiple_live_products_and_return_ownership() {
    // Internal adapter control only. This seeded row state is not source
    // readiness or §7 evidence. One exclusive borrow encloses all committed
    // pauses/resumes; incidence is constructed before the first pause.
    fn run(session: &mut InferenceSession) {
        let (occurrence, cause) = cause(session, 0);
        let owner = session.fresh_value_at_level(1).unwrap();
        let lower = session.fresh_value_at_level(1).unwrap();
        let first = session.fresh_value_at_level(1).unwrap();
        let second = session.fresh_value_at_level(1).unwrap();
        session.candidate_insert_bound(value(owner), Polarity::Negative, value(first)).unwrap();
        session.candidate_insert_bound(value(owner), Polarity::Negative, value(second)).unwrap();
        session.candidate_insert_bound(value(owner), Polarity::Negative,
            ExtrusionEndpoint::Value(ValueEndpointKey::IntNegative)).unwrap();
        let restoration = session.with_route_transaction(|session| {
            session.candidate_begin_bound_restoration(value(owner), Polarity::Positive, value(lower),
                &occurrence, &cause, BoundAdmissionCause::OwnerEmission { processing: None })
        }).unwrap();
        let emission = state(session).restorations[&restoration].emission;
        assert_eq!(state(session).restorations[&restoration].opposite_count, 3);
        assert_eq!(state(session).restorations[&restoration].next_opposite, 0);
        for index in 0..3 {
            session.with_route_transaction(|session| {
                assert_eq!(session.candidate_step_bound_restoration(restoration)?, None);
                Ok(())
            }).unwrap();
            let before = state(session).restorations[&restoration].clone();
            let replay = before.replay.unwrap();
            let upper = [ValueEndpointKey::ValueRow(first), ValueEndpointKey::ValueRow(second), ValueEndpointKey::IntNegative][index];
            assert_eq!(state(session).replay_operations[&replay].task,
                LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(lower), upper }),
                "saved index reads direct entries before the live exact lane");
            assert_eq!(before.next_opposite, index);
            assert!(state(session).replay_operations.contains_key(&replay));
            let checkpoint = state(session).checkpoint();
            let facts = session.store.facts.clone();
            let errors = session.errors.clone();
            assert_eq!(session.with_route_transaction(|session| {
                assert_eq!(session.candidate_step_bound_restoration(restoration)?, None);
                Err::<(), _>(exhausted())
            }), Err(exhausted()));
            assert_eq!(state(session).checkpoint(), checkpoint);
            assert_eq!(state(session).restorations[&restoration], before);
            assert!(state(session).replay_operations.contains_key(&replay), "rollback retains the parent's exact child handle");
            assert_eq!(session.store.facts, facts);
            assert_eq!(session.errors, errors);
            session.with_route_transaction(|session| {
                assert_eq!(session.candidate_step_bound_restoration(restoration)?, None);
                assert!(state(session).typed_drains.is_empty(), "typed completion and diagnostics precede parent advancement");
                assert_eq!(state(session).restorations[&restoration].next_opposite, index + 1);
                assert_eq!(state(session).restorations[&restoration].replay, None);
                Ok(())
            }).unwrap();
            assert!(!state(session).replay_operations.contains_key(&replay), "parent consumption releases the completed child");
        }
        session.with_route_transaction(|session| {
            assert_eq!(session.candidate_step_bound_restoration(restoration)?, Some(emission));
            Ok(())
        }).unwrap();
        assert!(!state(session).restorations.contains_key(&restoration));
    }
    run(&mut session());
}

#[test]
fn retained_nonterminal_prefix_failure_precedes_pop_and_restores_repeated_operation_undo() {
    for successful_preparations in [1, 2] {
        let mut session = session();
        let (index, restoration, replay) = terminal_drain_fixture(&mut session, false);
        let (queued_frame, _, queued_replay) = terminal_drain_fixture(&mut session, false);
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        assert_eq!(queued_frame, index + 1);
        context.typed_drains.pop();
        let queued_operation = &context.replay_operations[&queued_replay];
        let queued_item = TypedWorkItem { task: queued_operation.task,
            relation: Some(queued_operation.children[0]),
            replay_ack: Some(ReplayChildAck { operation: queued_replay, index: 0 }) };
        context.typed_drains[index].stage = TypedDrainStage::Transport;
        session.typed_worklist.push_back(queued_item);
        let frame = state(&session).typed_drains[index].clone();
        let ack_capacity = frame.replay_acks.capacity();
        let replay_before = state(&session).replay_operations[&replay].clone();
        let queued_before = state(&session).replay_operations[&queued_replay].clone();
        let restoration_before = state(&session).restorations[&restoration].clone();
        let queue = session.typed_worklist.clone();
        let capacity = session.typed_worklist.capacity();
        assert_eq!(session.resume_typed_drain_route(index, |session, index| {
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.fail_replay_completion_after = Some(successful_preparations);
            assert_eq!(session.step_typed_drain(index), Err(exhausted()));
            assert_eq!(state(session).typed_drains[index].prepared_acks, successful_preparations);
            assert_eq!(session.typed_worklist, queue, "preflight failure occurs before queue ownership transfer");
            let journal = session.route_journal.as_ref().unwrap();
            assert_eq!(journal.checked_retained_bytes()?, journal.checked_independent_retained_bytes()?);
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        assert_eq!(state(&session).typed_drains[index], frame);
        assert_eq!(state(&session).typed_drains[index].replay_acks.capacity(), ack_capacity);
        assert_eq!(state(&session).replay_operations[&replay], replay_before);
        assert_eq!(state(&session).replay_operations[&queued_replay], queued_before);
        assert_eq!(state(&session).restorations[&restoration], restoration_before);
        assert_eq!(session.typed_worklist, queue);
        assert_eq!(session.typed_worklist.capacity(), capacity);
        assert_eq!(session.resume_typed_drain_route(index, |session, index| {
            assert_eq!(session.step_typed_drain(index)?, DrainStep::More);
            assert!(session.typed_worklist.is_empty());
            let frame = &state(session).typed_drains[index];
            assert_eq!(frame.prepared_acks, 3);
            assert_eq!(frame.current, Some(queued_item));
            assert_eq!(state(session).restorations[&restoration], restoration_before,
                "an unfinished typed step cannot advance its restoration parent");
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        assert_eq!(state(&session).typed_drains[index], frame);
        assert_eq!(session.typed_worklist, queue);
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
    }
}

#[test]
fn direct_function_steps_prepare_full_retained_prefix_before_admission_or_enqueue() {
    for pending in [false, true] {
        let mut session = session();
        let (index, _, replay) = terminal_drain_fixture(&mut session, false);
        let relation = state(&session).replay_operations[&replay].children[0];
        let task = state(&session).replay_operations[&replay].task;
        let value_pair = task_pair(task);
        let effect_pair = TypedPairKey::Effect { lower: EffectEndpointKey::BottomPositive, upper: EffectEndpointKey::EmptyNegative };
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        context.processing = Some(relation);
        let frame = &mut context.typed_drains[index];
        frame.current = Some(TypedWorkItem { task, relation: Some(relation), replay_ack: None });
        frame.stage = if pending { TypedDrainStage::FunctionEnqueue } else { TypedDrainStage::FunctionAdmission };
        frame.function = Some(FunctionDispatch {
            children: [(FunctionField::Argument, value_pair), (FunctionField::ArgumentEffect, effect_pair),
                (FunctionField::ResultEffect, effect_pair), (FunctionField::Result, value_pair)], next: 0,
            pending: pending.then_some(TypedWorkItem { task, relation: Some(relation), replay_ack: None }),
        });
        let frame = state(&session).typed_drains[index].clone();
        let before = state(&session).checkpoint();
        assert_eq!(session.resume_typed_drain_route(index, |session, index| {
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.fail_replay_completion_after = Some(1);
            assert_eq!(session.candidate_step_function_dispatch(index), Err(exhausted()));
            assert_eq!(state(session).typed_drains[index].function, frame.function);
            assert!(session.typed_worklist.is_empty());
            Err::<(), _>(exhausted())
        }), Err(exhausted()));
        assert_eq!(state(&session).checkpoint(), before);
        assert_eq!(state(&session).typed_drains[index], frame);
    }
}

fn retained_replay_parent_fixture(empty: bool) -> (InferenceSession, ReplayOperationId, ReplayOperationId) {
    let mut session = session();
    let (index, restoration, replay) = terminal_drain_fixture(&mut session, empty);
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    assert_eq!(index, 0);
    context.typed_drains.pop().unwrap();
    context.replay_operations.get_mut(&replay).unwrap().queued = 0;
    (session, restoration, replay)
}

fn retained_parent_step(session: &mut InferenceSession, restoration: ReplayOperationId, fail: bool) -> Result<Option<BoundEmissionId>, SolveAvailabilityError> {
    session.begin_route_transaction_for(RoutePurpose::RetainedResume)?;
    session.finish_route_transaction(|session| {
        let result = session.candidate_step_bound_restoration_child(restoration, true)?;
        if fail { return Err(exhausted()); }
        Ok(result)
    })
}

#[test]
fn retained_replay_parent_commits_more_and_ready_before_exact_once_delivery() {
    // Synthetic ordered-occurrence fixture, not lifecycle/source readiness.
    let (mut session, restoration, replay) = retained_replay_parent_fixture(false);
    let emission = state(&session).restorations[&restoration].emission;
    let children = state(&session).replay_operations[&replay].children.clone();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], children[1], "occurrence identity cannot be relation equality");
    for index in 0..2 {
        assert_eq!(retained_parent_step(&mut session, restoration, false).unwrap(), None);
        let ack = ReplayChildAck { operation: replay, index };
        assert!(matches!(state(&session).replay_operations[&replay].waiting_child,
            ReplayChildWait::Running { ack: actual, drain_index: 0 } if actual == ack));
        assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
        assert_eq!(session.candidate_context_consume_replay_child(replay, None), Err(exhausted()),
            "queue transfer cannot release an unfinished provenance child");
        loop {
            let ack_capacity = state(&session).typed_drains[0].replay_acks.capacity();
            let before = state(&session).typed_drains[0].clone();
            let replay_before = state(&session).replay_operations[&replay].clone();
            let restoration_before = state(&session).restorations[&restoration].clone();
            let queue = session.typed_worklist.clone();
            let delta = session.diagnostic_delta.clone();
            let capacities = (session.typed_worklist.capacity(), session.diagnostic_delta.capacity(),
                session.diagnostic_delta_indices.capacity(), ack_capacity);
            assert_eq!(retained_parent_step(&mut session, restoration, true), Err(exhausted()));
            assert_eq!(state(&session).typed_drains[0], before);
            assert_eq!(state(&session).typed_drains[0].replay_acks.capacity(), capacities.3);
            assert_eq!(state(&session).replay_operations[&replay], replay_before);
            assert_eq!(state(&session).restorations[&restoration], restoration_before);
            assert_eq!(session.typed_worklist, queue);
            assert_eq!(session.diagnostic_delta, delta);
            assert_eq!((session.typed_worklist.capacity(), session.diagnostic_delta.capacity(),
                session.diagnostic_delta_indices.capacity()), (capacities.0, capacities.1, capacities.2));
            assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
            assert_eq!(retained_parent_step(&mut session, restoration, false).unwrap(), None);
            assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
            if let ReplayChildWait::Ready { ack: actual, drain_index, completion } =
                state(&session).replay_operations[&replay].waiting_child {
                assert_eq!(actual, ack);
                assert_eq!(drain_index, 0);
                assert_eq!(completion.transitions, before.transitions);
                assert!(state(&session).typed_drains.is_empty());
                break;
            }
        }
        let ready = state(&session).replay_operations[&replay].clone();
        assert_eq!(ready.consumed, index + 1);
        assert_eq!(ready.queued, index + 1);
        assert_eq!(ready.retired, index == 1);
        assert_eq!(session.candidate_context_consume_replay_child(replay, None), Err(exhausted()),
            "retirement and acknowledgement cannot bypass Ready");
        assert_eq!(retained_parent_step(&mut session, restoration, true), Err(exhausted()));
        assert_eq!(state(&session).replay_operations[&replay], ready);
        assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
        assert_eq!(retained_parent_step(&mut session, restoration, false).unwrap(), None);
        if index == 0 {
            let operation = &state(&session).replay_operations[&replay];
            assert_eq!(operation.waiting_child, ReplayChildWait::Idle);
            assert_eq!(operation.consumed, 1, "receipt delivery never acknowledges again");
            assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
        }
    }
    assert_eq!(state(&session).restorations[&restoration].next_opposite, 1);
    assert_eq!(state(&session).restorations[&restoration].replay, None);
    assert!(!state(&session).replay_operations.contains_key(&replay));
    let before = state(&session).restorations[&restoration].clone();
    assert_eq!(retained_parent_step(&mut session, restoration, true), Err(exhausted()));
    assert_eq!(state(&session).restorations[&restoration], before);
    assert_eq!(retained_parent_step(&mut session, restoration, false).unwrap(), Some(emission));
    assert!(!state(&session).restorations.contains_key(&restoration));
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn retained_replay_parent_empty_batch_has_no_fabricated_drain_receipt() {
    let (mut session, restoration, replay) = retained_replay_parent_fixture(true);
    let before = state(&session).replay_operations[&replay].clone();
    let emission = state(&session).restorations[&restoration].emission;
    assert_eq!(retained_parent_step(&mut session, restoration, true), Err(exhausted()));
    assert_eq!(state(&session).replay_operations[&replay], before);
    assert!(state(&session).typed_drains.is_empty());
    assert_eq!(retained_parent_step(&mut session, restoration, false).unwrap(), None);
    assert!(!state(&session).replay_operations.contains_key(&replay));
    assert!(state(&session).typed_drains.is_empty());
    assert_eq!(state(&session).restorations[&restoration].next_opposite, 1);
    assert_eq!(retained_parent_step(&mut session, restoration, false).unwrap(), Some(emission));
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}

#[test]
fn parsed_local_retained_child_steps_restore_parent_cursor_after_failure() {
    use crate::candidate_scheme::LocalScriptStep::DriveOne;
    use crate::candidate_source::{Action, CandidateRun, Schedule, Support};
    let mut session = session_with_source("my outer = { my local:int = 1; local }");
    let root = session.batch.definitions[0].root.clone();
    let position = session.batch.candidate_source.schedules[&root].iter()
        .position(|action| matches!(action, Action::Local { .. })).unwrap();
    session.begin_candidate_source(Schedule::Root(0)).unwrap();
    while session.candidate_graph.as_ref().unwrap().source.unwrap().next < position {
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    }
    session.candidate_test_local_script(&[DriveOne]).unwrap();
    let uses = state(&session).uses;
    let emissions = state(&session).evidence.emissions.len();
    loop {
        let frame = &session.candidate_graph.as_ref().unwrap().local_use[0];
        let cursor = frame.cursor;
        let restoration = cursor.restoration.unwrap();
        let operation = state(&session).restorations[&restoration].clone();
        let replay = operation.replay.map(|id| (id, state(&session).replay_operations[&id].clone()));
        let drains = state(&session).typed_drains.clone();
        let queue = session.typed_worklist.clone();
        assert_eq!(session.candidate_test_retained_local_step(true), Err(exhausted()));
        assert_eq!(session.candidate_graph.as_ref().unwrap().local_use[0].cursor, cursor);
        assert_eq!(state(&session).restorations[&restoration], operation);
        if let Some((id, replay)) = replay { assert_eq!(state(&session).replay_operations[&id], replay); }
        assert_eq!(state(&session).typed_drains, drains);
        assert_eq!(session.typed_worklist, queue);
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
        session.candidate_test_retained_local_step(false).unwrap();
        assert_eq!(state(&session).uses, uses);
        assert_eq!(state(&session).evidence.emissions.len(), emissions);
        let next = session.candidate_graph.as_ref().unwrap().local_use[0].cursor;
        if next.restoration.is_none() {
            assert_eq!(next.next_bound, cursor.next_bound + 1);
            assert!(state(&session).typed_drains.is_empty());
            break;
        }
        assert_eq!(next.next_bound, cursor.next_bound);
    }
}

#[test]
fn parsed_literal_local_retains_nonempty_child_until_exact_once_receipt_delivery() {
    use crate::candidate_scheme::LocalScriptStep::DriveOne;
    use crate::candidate_source::{Action, CandidateRun, Schedule, Support};
    // Authentic parsed replay execution; not the lifecycle regression of §7.
    let mut session = session_with_source("my outer = { my local = 1; local }");
    let root = session.batch.definitions[0].root.clone();
    let position = session.batch.candidate_source.schedules[&root].iter()
        .position(|action| matches!(action, Action::Local { .. })).unwrap();
    session.begin_candidate_source(Schedule::Root(0)).unwrap();
    while session.candidate_graph.as_ref().unwrap().source.unwrap().next < position {
        assert_eq!(session.step_candidate_source(Support::READY).unwrap(), CandidateRun::Complete(false));
    }
    let observations = session.candidate_test_local_script(&[DriveOne]).unwrap();
    let use_origin = observations[0].use_origin.unwrap();
    let uses = state(&session).uses;
    let first = observations[0].restoration.as_ref().unwrap();
    let owner = first.owner;
    let first_emission = first.emission;
    assert_eq!(first.polarity, Polarity::Positive);
    assert_eq!(first.opposite_count, 0);
    session.candidate_test_retained_local_step(false).unwrap();
    let cursor = session.candidate_graph.as_ref().unwrap().local_use[0].cursor;
    assert_eq!(cursor.next_bound, 1);
    assert_eq!(cursor.restoration, None);
    session.candidate_test_retained_local_step(false).unwrap();
    let cursor = session.candidate_graph.as_ref().unwrap().local_use[0].cursor;
    assert_eq!(cursor.next_bound, 1);
    let restoration = cursor.restoration.unwrap();
    let bound = state(&session).restorations[&restoration].clone();
    assert_eq!(bound.owner, owner);
    assert_eq!(bound.polarity, Polarity::Negative);
    assert_eq!(bound.opposite_count, 1);
    assert_ne!(bound.emission, first_emission);
    let emissions = state(&session).evidence.emissions.len();
    session.candidate_test_retained_local_step(false).unwrap();
    let replay = state(&session).restorations[&restoration].replay.unwrap();
    let generated = &state(&session).replay_operations[&replay];
    assert!(generated.incoming_use);
    assert!(generated.heads.0.is_some() && generated.heads.1.is_some());
    assert_eq!(generated.prior, (None, None));
    assert!(!generated.children.is_empty(), "native source replay must generate a child");
    let children = generated.children.clone();
    for index in 0..children.len() {
        let ack = ReplayChildAck { operation: replay, index };
        session.candidate_test_retained_local_step(false).unwrap();
        assert!(matches!(state(&session).replay_operations[&replay].waiting_child,
            ReplayChildWait::Running { ack: actual, drain_index: 0 } if actual == ack));
        let mut ready_reached = false;
        for _ in 0..64 {
            let checkpoint = state(&session).checkpoint();
            let operation = state(&session).restorations[&restoration].clone();
            let replay_before = state(&session).replay_operations[&replay].clone();
            let drains = state(&session).typed_drains.clone();
            let queue = session.typed_worklist.clone();
            let delta = session.diagnostic_delta.clone();
            let indices = session.diagnostic_delta_indices.clone();
            let capacities = (session.typed_worklist.capacity(), session.diagnostic_delta.capacity(),
                session.diagnostic_delta_indices.capacity(), state(&session).typed_drains[0].replay_acks.capacity());
            assert_eq!(session.candidate_test_retained_local_step(true), Err(exhausted()));
            assert_eq!(state(&session).checkpoint(), checkpoint);
            assert_eq!(session.candidate_graph.as_ref().unwrap().local_use[0].cursor, cursor);
            assert_eq!(state(&session).restorations[&restoration], operation);
            assert_eq!(state(&session).replay_operations[&replay], replay_before);
            assert_eq!(state(&session).typed_drains, drains);
            assert_eq!(session.typed_worklist, queue);
            assert_eq!(session.diagnostic_delta, delta);
            assert_eq!(session.diagnostic_delta_indices, indices);
            assert_eq!((session.typed_worklist.capacity(), session.diagnostic_delta.capacity(),
                session.diagnostic_delta_indices.capacity(), state(&session).typed_drains[0].replay_acks.capacity()), capacities);
            assert_eq!(state(&session).uses, uses);
            assert_eq!(state(&session).evidence.emissions.len(), emissions);
            assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
            session.candidate_test_retained_local_step(false).unwrap();
            assert_eq!(session.candidate_graph.as_ref().unwrap().local_use[0].cursor, cursor);
            assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
            assert_eq!(state(&session).restorations[&restoration].emission, bound.emission);
            assert_eq!(state(&session).uses, uses);
            assert_eq!(state(&session).evidence.emissions.len(), emissions);
            if let ReplayChildWait::Ready { ack: actual, drain_index, .. } =
                state(&session).replay_operations[&replay].waiting_child {
                assert_eq!(actual, ack);
                assert_eq!(drain_index, 0);
                assert!(state(&session).typed_drains.is_empty());
                ready_reached = true;
                break;
            }
        }
        assert!(ready_reached, "retained child did not reach Ready: {:?}",
            state(&session).replay_operations[&replay].waiting_child);
        let ready = state(&session).replay_operations[&replay].clone();
        assert_eq!(ready.children, children);
        assert_eq!(ready.queued, index + 1);
        assert_eq!(ready.consumed, index + 1);
        assert_eq!(ready.retired, index + 1 == children.len());
        assert_eq!(session.candidate_context_consume_replay_child(replay, None), Err(exhausted()));
        let ready_checkpoint = state(&session).checkpoint();
        let ready_restoration = state(&session).restorations[&restoration].clone();
        let ready_drains = state(&session).typed_drains.clone();
        let ready_queue = session.typed_worklist.clone();
        let ready_delta = session.diagnostic_delta.clone();
        let ready_indices = session.diagnostic_delta_indices.clone();
        let ready_capacities = (session.typed_worklist.capacity(), session.diagnostic_delta.capacity(),
            session.diagnostic_delta_indices.capacity(), state(&session).bytes().unwrap());
        assert_eq!(session.candidate_test_retained_local_step(true), Err(exhausted()));
        assert_eq!(state(&session).replay_operations[&replay], ready);
        assert_eq!(state(&session).checkpoint(), ready_checkpoint);
        assert_eq!(state(&session).restorations[&restoration], ready_restoration);
        assert_eq!(state(&session).typed_drains, ready_drains);
        assert_eq!(session.typed_worklist, ready_queue);
        assert_eq!(session.diagnostic_delta, ready_delta);
        assert_eq!(session.diagnostic_delta_indices, ready_indices);
        assert_eq!((session.typed_worklist.capacity(), session.diagnostic_delta.capacity(),
            session.diagnostic_delta_indices.capacity(), state(&session).bytes().unwrap()), ready_capacities);
        assert_eq!(session.candidate_graph.as_ref().unwrap().local_use[0].cursor, cursor);
        assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
        session.candidate_test_retained_local_step(false).unwrap();
        assert_eq!(session.candidate_graph.as_ref().unwrap().local_use[0].cursor, cursor);
        if index + 1 < children.len() {
            let delivered = &state(&session).replay_operations[&replay];
            assert_eq!(delivered.waiting_child, ReplayChildWait::Idle);
            assert_eq!(delivered.consumed, index + 1, "delivery cannot acknowledge twice");
            assert_eq!(state(&session).restorations[&restoration].next_opposite, 0);
        }
    }
    assert!(!state(&session).replay_operations.contains_key(&replay));
    assert_eq!(state(&session).restorations[&restoration].next_opposite, 1);
    assert_eq!(state(&session).restorations[&restoration].replay, None);
    assert_eq!(state(&session).restorations[&restoration].emission, bound.emission);
    session.candidate_test_retained_local_step(false).unwrap();
    let completed = session.candidate_graph.as_ref().unwrap().local_use[0].cursor;
    assert_eq!(completed.next_bound, 2);
    assert_eq!(completed.restoration, None);
    assert!(!state(&session).restorations.contains_key(&restoration));
    let observations = session.candidate_test_local_script(&[crate::candidate_scheme::LocalScriptStep::Idle]).unwrap();
    assert_eq!(observations[0].use_origin, Some(use_origin));
    assert_eq!(state(&session).uses, uses);
    assert_eq!(state(&session).evidence.emissions.len(), emissions);
    assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
}


#[test]
fn private_failed_candidate_census_restores_current_bytes_and_preserves_peak() {
    for retained in [false, true] {
        let (mut session, restoration, _) = retained_replay_parent_fixture(false);
        let checkpoint = state(&session).checkpoint();
        let restoration_before = state(&session).restorations[&restoration].clone();
        let rows = session.bounds.len();
        session.begin_route_transaction_for(if retained { RoutePurpose::RetainedResume } else { RoutePurpose::Fresh }).unwrap();
        let mut event_peak = 0;
        let mut samples = 0;
        let operation = |session: &mut InferenceSession| {
            session.fresh_value_at_level(1)?;
            session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            event_peak = session.execution_counters.inference_session_peak_bytes;
            samples = session.resource_boundary_samples;
            Err::<(), _>(exhausted())
        };
        let result = if retained { session.finish_route_transaction(operation) }
            else { session.finish_route_transaction_with_candidate_accounting(operation, true) };
        assert_eq!(result, Err(exhausted()));
        assert_eq!(session.bounds.len(), rows);
        assert_eq!(state(&session).checkpoint(), checkpoint);
        assert_eq!(state(&session).restorations[&restoration], restoration_before);
        assert_eq!(state(&session).bytes().unwrap(), state(&session).enumerated_bytes());
        assert_eq!(session.resource_boundary_samples, samples + 1);
        assert!(session.execution_counters.inference_session_peak_bytes >= event_peak);
        let current = (session.execution_counters.semantic_arena_retained_bytes,
            session.execution_counters.inference_session_retained_bytes);
        assert_eq!(current, (session.resource_ledger.semantic_arena_retained_bytes,
            session.resource_ledger.inference_session_retained_bytes));
        session.sample_f4_resources(ResourceBoundary::IncomingRoute).unwrap();
        assert_eq!(current, (session.execution_counters.semantic_arena_retained_bytes,
            session.execution_counters.inference_session_retained_bytes), "rollback boundary agrees with the restored owner census");
    }
}

#[test]
fn private_failed_candidate_census_overflow_publishes_no_partial_sample() {
    for retained in [false, true] {
        let (mut session, restoration, _) = retained_replay_parent_fixture(false);
        let checkpoint = state(&session).checkpoint();
        let restoration_before = state(&session).restorations[&restoration].clone();
        session.begin_route_transaction_for(if retained { RoutePurpose::RetainedResume } else { RoutePurpose::Fresh }).unwrap();
        let ledger = session.resource_ledger.clone();
        let counters = session.execution_counters.clone();
        let samples = session.resource_boundary_samples;
        let attempts = session.incoming_route_sample_attempts;
        let operation = |session: &mut InferenceSession| {
            // This probe becomes active only after setup, at the final census.
            session.sample_fixed_capacity_probe = Some(SampleFixedCapacityProbe::RouteJournal);
            Err::<(), _>(SolveAvailabilityError::ReceiptMismatch)
        };
        let result = if retained { session.finish_route_transaction(operation) }
            else { session.finish_route_transaction_with_candidate_accounting(operation, true) };
        assert_eq!(result, Err(exhausted()));
        assert_eq!(session.incoming_route_sample_attempts, attempts + 1);
        assert_eq!(session.resource_boundary_samples, samples);
        assert_eq!(session.resource_ledger, ledger);
        assert_eq!(session.execution_counters, counters);
        assert_eq!(state(&session).checkpoint(), checkpoint);
        assert_eq!(state(&session).restorations[&restoration], restoration_before);
        assert!(session.route_journal.is_none());
        // Accounting exhaustion is terminal: discard this private session.
    }
}

#[test]
fn delayed_replay_uses_stored_demand_source_association() {
    let text = "my loop x = loop x\nmy id x = x\nmy client x = id x";
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)), Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let mut session = session_with_source(text);
    assert_eq!(session.batch.hir.items().len(), 3);
    assert_eq!(session.batch.candidate_source.references.events.len(), 2);
    let events: Vec<_> = session.batch.candidate_source.references.checking.iter().map(|(checking, &event)|
        (checking.clone(), session.batch.candidate_source.references.qualifies(event))).collect();
    let qualified = events.iter().find(|(_, yes)| *yes).unwrap().0.clone();
    let unrelated = events.iter().find(|(_, yes)| !*yes).unwrap().0.clone();
    let owner = value(session.fresh_value_at_level(0).unwrap());
    let demand = value(session.fresh_value_at_level(2).unwrap());
    let actual = value(session.fresh_value_at_level(0).unwrap());
    let upper = BoundKey(owner, Polarity::Negative, demand);
    let lower = BoundKey(owner, Polarity::Positive, actual);
    let relation = session.candidate_context_seed(task_pair_to_task(bound_pair(upper)), &qualified, None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.attach(upper, relation).unwrap();
    let unrelated_relation = session.candidate_context_seed(task_pair_to_task(bound_pair(lower)), &unrelated, None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.attach(lower, unrelated_relation).unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(unrelated_relation);
    let replay_task = match (actual, demand) { (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => LiveConstraintTask::Value(CanonicalValuePairKey { lower, upper }), _ => unreachable!() };
    session.candidate_context_replay(lower, upper, replay_task, |session, children| {
        assert_eq!(children.len(), 1);
        let child = children[0];
        let sources = state(session).relations[child.0 as usize].key.sources.unwrap();
        let events = state(session).source_events(sources);
        assert_eq!(events.len(), 2, "replay retains both complete authentic source events");
        assert!(events.iter().any(|&event| session.batch.candidate_source.references.qualifies(event)));
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(child);
        let copy = session.candidate_extrude(demand, Polarity::Negative, 0)?;
        session.settle_candidate_intrusion(None)?;
        assert_eq!(session.canonical_extrusion(copy), session.canonical_extrusion(demand));
        Ok(())
    }).unwrap();
}

fn task_pair_to_task(pair: TypedPairKey) -> LiveConstraintTask {
    match pair { TypedPairKey::Value(pair) => LiveConstraintTask::Value(pair), TypedPairKey::Effect { lower, upper } => LiveConstraintTask::Effect(lower, upper) }
}

// Provisional finite native-operation observer. This does not assert H2 closure,
// source Catch reachability, H1/U, or production correctness.
#[test]
fn observe_structural_value_extrusion_current_and_late_allowance_pairs() {
    fn drain(session: &mut InferenceSession, task: LiveConstraintTask, slot: u8) -> Vec<LiveConstraintTask> {
        let (occurrence, cause) = cause(session, slot);
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let previous_processing = algebra.processing;
        let previous_relation = algebra.context.processing;
        let index = session.start_typed_drain(TypedWorkItem { task, relation: None, replay_ack: None },
            &occurrence, &cause, None, None).unwrap();
        let mut queued_effects = Vec::new();
        for _ in 0..256 {
            for item in &session.typed_worklist {
                if matches!(item.task, LiveConstraintTask::Effect(..)) && !queued_effects.contains(&item.task) {
                    queued_effects.push(item.task);
                }
            }
            if let DrainStep::Complete(_) = session.step_typed_drain(index).unwrap() {
                assert!(session.typed_worklist.is_empty());
                assert!(state(session).typed_drains.is_empty());
                session.candidate_processing(previous_processing);
                session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous_relation;
                return queued_effects;
            }
        }
        panic!("bounded observer exceeded 256 drain steps");
    }

    let mut session = session_with_source("act E\nact F\nmy seed x = x");
    let owner = empty_bundle_owner(&session);
    let declarations = session.batch.hir.source_effect_declarations();
    let allowed = declarations.iter().find(|d| d.spelling.as_ref() == "E").unwrap().id.clone();
    let unmatched = declarations.iter().find(|d| d.spelling.as_ref() == "F").unwrap().id.clone();
    let tail = session.fresh_effect_at_level(2).unwrap();
    let source = session.fresh_effect_at_level(2).unwrap();
    let symbolic = session.fresh_effect_at_level(1).unwrap();
    let views: Vec<_> = (0..2).map(|_| session.candidate_effect_view(owner.clone(),
        allowed.declaration.clone(), vec![allowed.clone()], Some(tail)).unwrap()).collect();
    assert_ne!(views[0], views[1]);
    let (occurrence, cause) = cause(&session, 0);
    // Level 1 < level 2 selects a positive lower on source; it is symbolic and
    // already present when both distinct cuts are admitted by their live owner.
    session.constrain_live(LiveConstraintTask::Effect(EffectEndpointKey::EffectRow(symbolic),
        EffectEndpointKey::EffectRow(source)), &occurrence, &cause).unwrap();
    for &view in &views {
        session.constrain_live(LiveConstraintTask::Effect(EffectEndpointKey::EffectRow(source),
            EffectEndpointKey::Allowance(view)), &occurrence, &cause).unwrap();
    }
    assert!(session.effect_bounds[source as usize].direct_lower_rows.contains(&symbolic));
    let original_lower = BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(source)),
        Polarity::Positive, ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(symbolic)));
    let original_cuts: Vec<_> = views.iter().map(|&view| BoundKey(original_lower.0,
        Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view)))).collect();
    for &bound in original_cuts.iter().chain(std::iter::once(&original_lower)) {
        assert!(state(&session).bound_relations(bound).next().is_some());
    }

    // Same structural result-effect port as the existing mixed-Allowance
    // fixture, but lib.rs Value dispatch owns the call to candidate_extrude.
    let effect = session.live_effect_term(Polarity::Positive, tail).unwrap();
    let function = session.positive_function_term(
        session.batch.collected_leaf_term(Leaf::IntNegative),
        session.batch.collected_leaf_term(Leaf::EmptyEffectNegative), effect,
        session.batch.collected_leaf_term(Leaf::IntPositive)).unwrap();
    let receiver = session.fresh_value_at_level(1).unwrap();
    let structural = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::PositiveFunction(function), upper: ValueEndpointKey::ValueRow(receiver),
    });
    let transform_start = state(&session).evidence.transforms.len();
    let queued_current = drain(&mut session, structural, 1);
    let copied_function = session.bounds[receiver as usize].exact_non_variable_lowers.iter().find_map(|endpoint|
        match endpoint { ValueEndpointKey::PositiveFunction(term) => Some(*term), _ => None }).unwrap();
    assert_ne!(function, copied_function);
    let (_, _, effect, _) = InferenceSession::positive_function_children(&session.store,
        ValueEndpointKey::PositiveFunction(copied_function)).unwrap();
    let EffectEndpointKey::EffectRow(copied_tail) = session.effect_endpoint(effect, Polarity::Positive)
        else { panic!("structural copy retains effect-row result port") };
    assert_ne!(tail, copied_tail);
    let mut copied_cuts = Vec::new();
    for &original in &original_cuts {
        // Only positive tail incidence reconstructs these negative cuts here:
        // Work::IncomingAllowance, not selected negative Work::Bound traversal.
        let transforms: Vec<_> = state(&session).evidence.transforms[transform_start..].iter()
            .filter(|t| t.from == original && matches!(t.reason, TransportReason::Extrusion { .. })).copied().collect();
        assert_eq!(transforms.len(), 1);
        let transform = transforms[0];
        let BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copy_source)), Polarity::Negative,
            ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(copy_view))) = transform.to else { panic!("copied cut") };
        assert_ne!(copy_source, source);
        assert!(!views.contains(&copy_view));
        assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[copy_view as usize].tail, Some(copied_tail));
        assert!(state(&session).dependency_keys.contains(&Dependency::Transport { child: transform.child_relation,
            parent: transform.source_relation, use_origin: 0, witness: Some(TransportWitness {
                from: original, to: transform.to, reason: transform.reason }) }));
        assert!(session.effect_bounds[copy_source as usize].exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(copy_view)));
        copied_cuts.push(transform.to);
    }
    assert_eq!(copied_cuts[0].0, copied_cuts[1].0);
    assert_ne!(copied_cuts[0].2, copied_cuts[1].2);
    let copied_lower = BoundKey(copied_cuts[0].0, Polarity::Positive, original_lower.2);
    // This positive selected lower is Work::Bound's separate transport route.
    assert!(state(&session).evidence.transforms[transform_start..].iter().any(|t|
        t.from == original_lower && t.to == copied_lower));
    for &bound in copied_cuts.iter().chain(std::iter::once(&copied_lower)) {
        assert!(state(&session).bound_relations(bound).next().is_some());
        eprintln!("current_cut transported_bound={bound:?} origin_count={}", session.candidate_bound_origin_count(bound));
    }
    let current_replays: Vec<_> = state(&session).dependencies.iter().filter(|dependency|
        matches!(dependency, Dependency::Replay { lower_input, upper_input, .. }
            if *lower_input == copied_lower && copied_cuts.contains(upper_input))).copied().collect();
    eprintln!("current_cut original_lower={original_lower:?} original_cuts={original_cuts:?} copied_lower={copied_lower:?} copied_cuts={copied_cuts:?} replay_dependencies={current_replays:?} queued_effects={queued_current:?}");

    let late = session.candidate_effect_contribution(unmatched.clone(), unmatched.declaration.clone()).unwrap();
    let ExtrusionEndpoint::Effect(copy_source) = copied_cuts[0].0 else { unreachable!() };
    let dependency_start = state(&session).dependencies.len();
    let queued_late = drain(&mut session, LiveConstraintTask::Effect(late, copy_source), 2);
    let late_lower = BoundKey(copied_cuts[0].0, Polarity::Positive, ExtrusionEndpoint::Effect(late));
    for &cut in &copied_cuts {
        assert!(state(&session).dependencies[dependency_start..].iter().any(|dependency|
            matches!(dependency, Dependency::Replay { lower_input, upper_input, .. }
                if *lower_input == late_lower && *upper_input == cut)));
    }
    assert!(session.effect_bounds[copied_tail as usize].exact_non_variable_lowers.contains(&late));
    eprintln!("current_cut late_lower={late_lower:?} replay_dependencies={:?} queued_effects={queued_late:?} drained_tail_lowers={:?}",
        &state(&session).dependencies[dependency_start..], session.effect_bounds[copied_tail as usize].exact_non_variable_lowers);
    assert!(session.errors.is_empty());
}


#[test]
fn structural_value_extrusion_replays_initialized_allowance_fibers() {
    fn drain(session: &mut InferenceSession, task: LiveConstraintTask, slot: u8) -> Vec<LiveConstraintTask> {
        let (occurrence, cause) = cause(session, slot);
        let algebra = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let previous_processing = algebra.processing;
        let previous_relation = algebra.context.processing;
        let index = session.start_typed_drain(TypedWorkItem { task, relation: None, replay_ack: None },
            &occurrence, &cause, None, None).unwrap();
        let mut queued_effects = Vec::new();
        for _ in 0..256 {
            for item in &session.typed_worklist {
                if matches!(item.task, LiveConstraintTask::Effect(..)) && !queued_effects.contains(&item.task) {
                    queued_effects.push(item.task);
                }
            }
            if let DrainStep::Complete(_) = session.step_typed_drain(index).unwrap() {
                assert!(session.typed_worklist.is_empty());
                assert!(state(session).typed_drains.is_empty());
                session.candidate_processing(previous_processing);
                session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous_relation;
                return queued_effects;
            }
        }
        panic!("bounded observer exceeded 256 drain steps");
    }

    for symbolic_level in [1, 2] {
        let mut session = session_with_source("act E\nact F\nmy seed x = x\nmy client x = seed x");
        let owner = empty_bundle_owner(&session);
        let declarations = session.batch.hir.source_effect_declarations();
        let allowed = declarations.iter().find(|d| d.spelling.as_ref() == "E").unwrap().id.clone();
        let unmatched = declarations.iter().find(|d| d.spelling.as_ref() == "F").unwrap().id.clone();
        let tail = session.fresh_effect_at_level(2).unwrap();
        let source = session.fresh_effect_at_level(2).unwrap();
        let symbolic = session.fresh_effect_at_level(symbolic_level).unwrap();
        let views: Vec<_> = (0..2).map(|_| session.candidate_effect_view(owner.clone(),
            allowed.declaration.clone(), vec![allowed.clone()], Some(tail)).unwrap()).collect();
        assert_ne!(views[0], views[1]);
        let (occurrence, cause) = cause(&session, 0);
        // Pin the selected symbolic lower at its actual bound owner. Equal-level
        // rows would otherwise select the opposite storage direction at admission.
        let original_lower = BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(source)),
            Polarity::Positive, ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(symbolic)));
        let checking = session.batch.candidate_source.references.checking.keys().next().unwrap().clone();
        let relation = session.candidate_context_seed(task_pair_to_task(bound_pair(original_lower)),
            &checking, None).unwrap().unwrap();
        let closed = session.candidate_effect_view(owner.clone(), allowed.declaration.clone(),
            vec![allowed.clone()], None).unwrap();
        let weight = session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[closed as usize]
            .closed_weight.unwrap();
        let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let seeded = context.relations[relation.0 as usize].key;
        assert!(seeded.sources.is_some());
        let nonidentity = context.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }).unwrap();
        let relation = context.relation_with_sources(seeded.pair, nonidentity, seeded.sources).unwrap();
        context.processing = Some(relation);
        session.candidate_restore_bound(original_lower.0, original_lower.1, original_lower.2,
            &occurrence, &cause).unwrap();
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = None;
        for &view in &views {
            session.constrain_live(LiveConstraintTask::Effect(EffectEndpointKey::EffectRow(source),
                EffectEndpointKey::Allowance(view)), &occurrence, &cause).unwrap();
        }
        assert!(session.effect_bounds[source as usize].direct_lower_rows.contains(&symbolic));
        let original_cuts: Vec<_> = views.iter().map(|&view| BoundKey(original_lower.0,
            Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(view)))).collect();
        for &bound in original_cuts.iter().chain(std::iter::once(&original_lower)) {
            assert!(state(&session).bound_relations(bound).next().is_some());
        }

        // Same structural result-effect port as the existing mixed-Allowance
        // fixture, but lib.rs Value dispatch owns the call to candidate_extrude.
        let effect = session.live_effect_term(Polarity::Positive, tail).unwrap();
        let function = session.positive_function_term(
            session.batch.collected_leaf_term(Leaf::IntNegative),
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative), effect,
            session.batch.collected_leaf_term(Leaf::IntPositive)).unwrap();
        let receiver = session.fresh_value_at_level(1).unwrap();
        let structural = LiveConstraintTask::Value(CanonicalValuePairKey {
            lower: ValueEndpointKey::PositiveFunction(function), upper: ValueEndpointKey::ValueRow(receiver),
        });
        let transform_start = state(&session).evidence.transforms.len();
        let queued_current = drain(&mut session, structural, 1);
        let copied_function = session.bounds[receiver as usize].exact_non_variable_lowers.iter().find_map(|endpoint|
            match endpoint { ValueEndpointKey::PositiveFunction(term) => Some(*term), _ => None }).unwrap();
        assert_ne!(function, copied_function);
        let (_, _, effect, _) = InferenceSession::positive_function_children(&session.store,
            ValueEndpointKey::PositiveFunction(copied_function)).unwrap();
        let EffectEndpointKey::EffectRow(copied_tail) = session.effect_endpoint(effect, Polarity::Positive)
            else { panic!("structural copy retains effect-row result port") };
        assert_ne!(tail, copied_tail);
        let mut copied_cuts = Vec::new();
        for &original in &original_cuts {
            // Only positive tail incidence reconstructs these negative cuts here:
            // Work::IncomingAllowance, not selected negative Work::Bound traversal.
            let transforms: Vec<_> = state(&session).evidence.transforms[transform_start..].iter()
                .filter(|t| t.from == original && matches!(t.reason, TransportReason::Extrusion { .. })).copied().collect();
            assert_eq!(transforms.len(), 1);
            let transform = transforms[0];
            let BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(copy_source)), Polarity::Negative,
                ExtrusionEndpoint::Effect(EffectEndpointKey::Allowance(copy_view))) = transform.to else { panic!("copied cut") };
            assert_ne!(copy_source, source);
            assert!(!views.contains(&copy_view));
            assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[copy_view as usize].tail, Some(copied_tail));
            assert!(state(&session).dependency_keys.contains(&Dependency::Transport { child: transform.child_relation,
                parent: transform.source_relation, use_origin: 0, witness: Some(TransportWitness {
                    from: original, to: transform.to, reason: transform.reason }) }));
            assert!(session.effect_bounds[copy_source as usize].exact_non_variable_uppers.contains(&EffectEndpointKey::Allowance(copy_view)));
            copied_cuts.push(transform.to);
        }
        assert_eq!(copied_cuts[0].0, copied_cuts[1].0);
        assert_ne!(copied_cuts[0].2, copied_cuts[1].2);
        // Work::Bound transports the reused row at level 1 and a fresh positive
        // copy at level 2, independently of IncomingAllowance's negative cuts.
        let lower_transforms: Vec<_> = state(&session).evidence.transforms[transform_start..].iter()
            .filter(|t| t.from == original_lower && t.to.0 == copied_cuts[0].0).copied().collect();
        assert_eq!(lower_transforms.len(), 1);
        let copied_lower = lower_transforms[0].to;
        for transform in state(&session).evidence.transforms[transform_start..].iter()
            .filter(|t| t.from == original_lower || original_cuts.contains(&t.from)) {
            let context = state(&session);
            let source = context.relations[transform.source_relation.0 as usize].key;
            let child = context.relations[transform.child_relation.0 as usize].key;
            assert_eq!(source.pair, bound_pair(transform.from));
            assert_eq!(child.pair, bound_pair(transform.to));
            assert_eq!(source.context, child.context);
            assert_eq!(source.sources, child.sources);
        }
        assert_eq!(copied_lower.1, Polarity::Positive);
        assert_eq!(copied_lower.2 == original_lower.2, symbolic_level == 1);
        for &bound in copied_cuts.iter().chain(std::iter::once(&copied_lower)) {
            assert!(state(&session).bound_relations(bound).next().is_some());
            assert!(session.candidate_bound_origin_count(bound) > 0);
        }
        let current_replays: Vec<_> = state(&session).dependencies.iter().filter(|dependency|
            matches!(dependency, Dependency::Replay { lower_input, upper_input, .. }
                if *lower_input == copied_lower && copied_cuts.contains(upper_input))).copied().collect();
        for &cut in &copied_cuts {
            let replays: Vec<_> = current_replays.iter().filter(|dependency|
                matches!(dependency, Dependency::Replay { lower, upper_input, .. }
                    if *upper_input == cut && *lower == lower_transforms[0].child_relation)).collect();
            assert!(!replays.is_empty(), "each initialized lineage receives the existing symbolic lower");
            for &&dependency in &replays {
                let Dependency::Replay { child, lower, upper, lower_input, upper_input } = dependency else { unreachable!() };
                let context = state(&session);
                assert_eq!(lower_input, copied_lower);
                assert_eq!(upper_input, cut);
                assert!(context.bound_relations(copied_lower).any(|r| r == lower));
                assert!(context.bound_relations(cut).any(|r| r == upper));
                let lower_key = context.relations[lower.0 as usize].key;
                let upper_key = context.relations[upper.0 as usize].key;
                let child_key = context.relations[child.0 as usize].key;
                assert_eq!(lower_key.context, nonidentity);
                assert_eq!(lower_key.sources, seeded.sources);
                assert_eq!(lower_key.pair, bound_pair(copied_lower));
                assert_eq!(upper_key.pair, bound_pair(cut));
                let (ExtrusionEndpoint::Effect(lower_endpoint), ExtrusionEndpoint::Effect(upper_endpoint)) =
                    (copied_lower.2, cut.2) else { unreachable!() };
                assert_eq!(child_key.pair, TypedPairKey::Effect { lower: lower_endpoint, upper: upper_endpoint });
                if lower_key.context == IDENTITY && upper_key.context == IDENTITY {
                    assert_eq!(child_key.context, IDENTITY);
                } else {
                    assert_eq!(context.contexts[child_key.context.0 as usize - 1],
                        ContextExpr::Replay { lower: lower_key.context, upper: upper_key.context });
                }
                for parent in [lower_key, upper_key] {
                    if let Some(sources) = parent.sources {
                        let child_sources = child_key.sources.expect("replay retains source identities");
                        for source in context.source_events(sources) {
                            assert!(context.source_events(child_sources).contains(source));
                        }
                    }
                }
                assert!(queued_current.contains(&LiveConstraintTask::Effect(lower_endpoint, upper_endpoint)));
            }
        }
        assert!(state(&session).replay_operations.is_empty());

        let late = session.candidate_effect_contribution(unmatched.clone(), unmatched.declaration.clone()).unwrap();
        let ExtrusionEndpoint::Effect(copy_source) = copied_cuts[0].0 else { unreachable!() };
        let dependency_start = state(&session).dependencies.len();
        let queued_late = drain(&mut session, LiveConstraintTask::Effect(late, copy_source), 2);
        let late_lower = BoundKey(copied_cuts[0].0, Polarity::Positive, ExtrusionEndpoint::Effect(late));
        for &cut in &copied_cuts {
            assert!(state(&session).dependencies[dependency_start..].iter().any(|dependency|
                matches!(dependency, Dependency::Replay { lower_input, upper_input, .. }
                    if *lower_input == late_lower && *upper_input == cut)));
        }
        assert!(session.effect_bounds[copied_tail as usize].exact_non_variable_lowers.contains(&late));
        for cut in &copied_cuts {
            let ExtrusionEndpoint::Effect(upper) = cut.2 else { unreachable!() };
            assert!(queued_late.contains(&LiveConstraintTask::Effect(late, upper)));
        }
        assert!(state(&session).replay_operations.is_empty());
        assert!(session.errors.is_empty());
    }
}

#[test]
fn structural_bound_scoped_payload_keeps_typed_owners_and_authentic_copied_demands() {
    let text: Arc<yu_syntax::SourceText> = Arc::from(
        "act signal:\n    our ping: () -> int\n\nmy g h x = h x\nmy callback i = signal::ping()\nmy first = g callback 0\nmy second = g callback 1",
    );
    let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    let hir = Arc::new(lower_module_with_local_source(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("typed-bound", "source.yu"))),
        &parsed, yu_hir::SemanticImports::empty(),
    ).unwrap());
    let mut session = InferenceSession::try_new_candidate(
        ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
    ).unwrap();
    session.execute().unwrap();
    let lower = session.fresh_effect_at_level(1).unwrap();
    let upper = session.fresh_effect_at_level(1).unwrap();
    let effect_pair = TypedPairKey::Effect {
        lower: EffectEndpointKey::EffectRow(lower), upper: EffectEndpointKey::EffectRow(upper),
    };
    let bound = BoundKey(ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(lower)),
        Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(upper)));
    let (parent, parent_pair, copied) = state(&session).observed_relations().find_map(|(index, pair, flow)| {
        let demand = flow.demand?;
        if demand.use_instance == 0 { return None; }
        if !matches!(pair, TypedPairKey::Value(CanonicalValuePairKey {
            upper: ValueEndpointKey::NegativeFunction(root), .. }) if *root == demand.root) { return None; }
        Some((RelationId(index as u32), *pair, flow))
    }).expect("actual authenticated copied demand");
    let demand = copied.demand.unwrap();
    let original = &session.batch.candidate_calls.calls[demand.original_call];
    assert!(original.introduction.is_some());
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    assert_eq!(context.bound_scoped_payload(parent, parent_pair).unwrap(), copied,
        "original Call, use instance, mapped root, scope and input stay jointly retained");
    assert_eq!(context.bound_scoped_payload(parent, effect_pair).unwrap(), ScopedFlow::default());
    assert_eq!(context.bound_scoped_payload_for(parent, parent_pair, BoundConstructionPurpose::ExtrusionLink).unwrap(), ScopedFlow::default(),
        "explicit structural Value copy purpose does not propagate the original demand to a sibling row");
    context.processing = Some(parent);
    let sources = context.relations[parent.0 as usize].key.sources;
    let inherited = context.post_check_context(parent);
    let child = session.candidate_context_bound(bound, parent_pair).unwrap();
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    assert_eq!(context.scoped_flow(child).unwrap(), ScopedFlow::default());
    assert_eq!(context.relations[child.0 as usize].key.sources, sources);
    assert_eq!(context.relations[child.0 as usize].key.context, inherited);
    assert!(context.dependency_keys.contains(&Dependency::Derived { child, parent }));
    assert!(context.bound_keys.iter().any(|(key, relation, _)| *key == bound && *relation == child));
    let transform = context.intern_scope(candidate_scope::ScopeTransformer::protect_body(demand.output_scope, demand.input).unwrap()).unwrap();
    let effect_flow = ScopedFlow { transformer: transform, demand: None };
    let effect_parent = context.relation_with_scoped(effect_pair, IDENTITY, None, effect_flow).unwrap();
    assert_eq!(context.bound_scoped_payload(effect_parent, effect_pair).unwrap(), effect_flow);
    assert_eq!(context.bound_scoped_payload_for(effect_parent, effect_pair, BoundConstructionPurpose::ExtrusionLink).unwrap(), effect_flow);
    assert_eq!(context.bound_scoped_payload(effect_parent, parent_pair), Err(SolveAvailabilityError::ReceiptMismatch));
    let plain_effect = context.relation_with_scoped(effect_pair, IDENTITY, None, ScopedFlow::default()).unwrap();
    context.scoped_enabled = false;
    assert_eq!(context.bound_scoped_payload(plain_effect, parent_pair).unwrap(), ScopedFlow::default(),
        "ordinary mode retains its existing unqualified structural behavior");
    assert_eq!(context.bound_scoped_payload(effect_parent, parent_pair), Err(SolveAvailabilityError::ReceiptMismatch));
    context.scoped_enabled = true;
    assert_eq!(context.relation_with_scoped(effect_pair, IDENTITY, None, copied), Err(SolveAvailabilityError::ReceiptMismatch));
    assert_eq!(context.relation_with_scoped(parent_pair, IDENTITY, None, effect_flow), Err(SolveAvailabilityError::ReceiptMismatch));
    // The structural rule must not replace genuine Function-port projection.
    for (field, expected) in [
        (FunctionField::ArgumentEffect, candidate_scope::ScopeTransformer::stamp_input(demand.input).unwrap()),
        (FunctionField::ResultEffect, candidate_scope::ScopeTransformer::protect_body(demand.output_scope, demand.input).unwrap()),
    ] {
        let child = session.candidate_function_port_admit(
            LiveConstraintTask::Effect(EffectEndpointKey::EffectRow(lower), EffectEndpointKey::EffectRow(upper)), field,
        ).unwrap().unwrap();
        let context = state(&session);
        let flow = context.scoped_flow(child).unwrap();
        assert!(flow.demand.is_none());
        assert_eq!(context.scope_transformer(flow.transformer).unwrap(), &expected);
    }
}

#[test]
fn whole_value_rewrite_transports_only_the_authentic_upper_demand_root() {
    let text: Arc<yu_syntax::SourceText> = Arc::from("my g h = h 0");
    let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    let hir = Arc::new(lower_module_with_local_source(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("whole-rewrite", "source.yu"))),
        &parsed, yu_hir::SemanticImports::empty(),
    ).unwrap());
    let mut session = InferenceSession::try_new_candidate(
        ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
    ).unwrap();
    session.execute().unwrap();
    let (parent, original, original_flow) = state(&session).observed_relations().find_map(|(index, pair, flow)| {
        let demand = flow.demand?;
        let TypedPairKey::Value(pair) = *pair else { return None; };
        (pair.upper == ValueEndpointKey::NegativeFunction(demand.root)).then_some((RelationId(index as u32), pair, flow))
    }).unwrap();
    {
        let algebra = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra;
        algebra.processing = Some(TypedPairKey::Value(original));
        algebra.context.processing = Some(parent);
    }
    let ExtrusionEndpoint::Value(copied_upper) = session.candidate_extrude(
        ExtrusionEndpoint::Value(original.upper), Polarity::Negative, 0,
    ).unwrap() else { panic!("Value extrusion"); };
    assert_ne!(copied_upper, original.upper);
    let rewritten = CanonicalValuePairKey { upper: copied_upper, ..original };
    let child = session.candidate_context_value_rewrite(original, rewritten).unwrap().unwrap();
    let context = state(&session);
    let mut expected = original_flow;
    let ValueEndpointKey::NegativeFunction(root) = copied_upper else { panic!("copied upper Function"); };
    expected.demand.as_mut().unwrap().root = root;
    assert_eq!(context.scoped_flow(child).unwrap(), expected);
    assert_eq!(context.relations[child.0 as usize].key.sources, context.relations[parent.0 as usize].key.sources);
    assert!(context.dependency_keys.contains(&Dependency::Derived { child, parent }));
    let ExtrusionEndpoint::Value(copied_lower) = session.candidate_extrude(
        ExtrusionEndpoint::Value(original.lower), Polarity::Positive, 0,
    ).unwrap() else { panic!("Value extrusion"); };
    let lower_only = CanonicalValuePairKey { lower: copied_lower, ..original };
    let lower_child = session.candidate_context_value_rewrite(original, lower_only).unwrap().unwrap();
    assert_eq!(state(&session).scoped_flow(lower_child).unwrap(), original_flow);
    let wrong_original = CanonicalValuePairKey { lower: ValueEndpointKey::IntPositive, ..original };
    assert_eq!(session.candidate_context_value_rewrite(wrong_original, rewritten), Err(SolveAvailabilityError::ReceiptMismatch));
    let context = &mut session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
    context.processing = Some(child);
    let bad = CanonicalValuePairKey { lower: rewritten.lower, upper: original.upper };
    let malformed = context.relation_with_scoped(TypedPairKey::Value(bad), IDENTITY, None, expected).unwrap();
    context.processing = Some(malformed);
    assert_eq!(session.candidate_function_port_admit(
        LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::IntNegative }),
        FunctionField::Result,
    ), Err(SolveAvailabilityError::ReceiptMismatch));
}

#[test]
fn grouped_helper_actual_copied_h_ports_retain_protection_without_default_bypass() {
    let text: Arc<yu_syntax::SourceText> = Arc::from(
        "act signal:\n    our ping: () -> int\n\nmy invoke cb = cb 0\nmy g h = catch ({ my step i = h i; my direct = signal::ping(); invoke step }) { signal::ping(), _ -> 1, v -> v }\nmy callback_first i = signal::ping()\nmy callback_second i = signal::ping()\nmy first = catch g callback_first { signal::ping(), _ -> 2, v -> v }\nmy second = catch g callback_second { signal::ping(), _ -> 3, v -> v }",
    );
    let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    assert!(parsed.structural_recoveries().is_empty());
    let hir = Arc::new(lower_module_with_local_source(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("actual-helper-ports", "source.yu"))),
        &parsed, yu_hir::SemanticImports::empty(),
    ).unwrap());
    let mut session = InferenceSession::try_new_candidate(
        ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
    ).unwrap();
    session.execute().unwrap();
    let owner = session.batch.hir.items().iter().find_map(|item| match item {
        yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "g" => Some(binding.definition_root()),
        _ => None,
    }).unwrap();
    let source = session.batch.hir.local_source(owner).unwrap().unwrap();
    let calls: Vec<_> = session.batch.candidate_calls.calls.iter().enumerate().filter_map(|(index, call)| {
        if call.owner.definition_root() != Some(owner) { return None; }
        let name = session.batch.candidate_calls.names.get(call.formal_name?)?;
        let registration = &session.batch.candidate_calls.formals[name.registration];
        let yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. } = &source.expressions()[registration.lambda].form else { return None; };
        (parameter.spelling.as_ref() == "h").then_some((index, call))
    }).collect();
    assert_eq!(calls.len(), 1);
    let (original_call, call) = calls[0];
    assert!(call.introduction.is_some());
    let original_scope = session.batch.candidate_source.computation_scopes[call.checking.occurrence()];
    let context = state(&session);
    let comparisons: Vec<_> = context.observed_relations().filter_map(|(index, pair, flow)| {
        let demand = flow.demand?;
        if demand.original_call != original_call || demand.use_instance == 0 { return None; }
        let TypedPairKey::Value(pair @ CanonicalValuePairKey {
            lower: ValueEndpointKey::PositiveFunction(_), upper: ValueEndpointKey::NegativeFunction(root),
        }) = *pair else { return None; };
        assert_eq!(root, demand.root, "the actual comparison must retain its mapped demand root");
        Some((RelationId(index as u32), pair, demand))
    }).collect();
    let mut uses = HashSet::new();
    for (parent, pair, demand) in comparisons {
        uses.insert(demand.use_instance);
        assert_ne!(demand.output_scope, original_scope);
        assert_ne!(demand.input, candidate_scope::InputRouteId(original_call as u32));
        assert_eq!(context.scope_inventory.scope_origins[demand.output_scope.0 as usize], original_scope);
        assert_eq!(context.scope_inventory.input_origins[demand.input.0 as usize], candidate_scope::InputRouteId(original_call as u32));
        let key = context.relations[parent.0 as usize].key;
        for (index, relation) in context.relations.iter().enumerate() {
            if relation.key.pair == key.pair && relation.key.sources == key.sources {
                assert!(context.scoped_flow(RelationId(index as u32)).unwrap().demand.is_some(),
                    "actual helper comparison {parent:?} has an unqualified same-pair/source bypass at relation {index}");
            }
        }
        let (_, lower_ae, lower_re, _) = InferenceSession::positive_function_children(&session.store, pair.lower).unwrap();
        let (_, upper_ae, upper_re, _) = InferenceSession::negative_function_children(&session.store, pair.upper).unwrap();
        for (field, operation, expected, lower, upper) in [
            (FunctionField::ArgumentEffect, FunctionPortOperation::Swap,
                candidate_scope::ScopeTransformer::stamp_input(demand.input).unwrap(), upper_ae, lower_ae),
            (FunctionField::ResultEffect, FunctionPortOperation::Preserve,
                candidate_scope::ScopeTransformer::protect_body(demand.output_scope, demand.input).unwrap(), lower_re, upper_re),
        ] {
            let children: Vec<_> = context.dependency_keys.iter().filter_map(|dependency| match dependency {
                Dependency::FunctionPort { child, parent: owner, field: actual_field, operation: actual_operation }
                    if *owner == parent && *actual_field == field => {
                        assert_eq!(*actual_operation, operation);
                        Some(*child)
                    }
                _ => None,
            }).collect();
            assert!(!children.is_empty(), "actual helper comparison must project {field:?}");
            let expected_pair = session.candidate_context_pair(TypedPairKey::Effect {
                lower: session.effect_endpoint(lower, Polarity::Positive),
                upper: session.effect_endpoint(upper, Polarity::Negative),
            });
            for child in children {
                assert_eq!(context.relations[child.0 as usize].key.pair, expected_pair);
                let flow = context.scoped_flow(child).unwrap();
                assert!(flow.demand.is_none());
                assert_eq!(context.scope_transformer(flow.transformer).unwrap(), &expected);
            }
        }
        assert!(context.scope_observations.iter().any(|observation| {
            context.evaluate_observation(observation.relation).unwrap().1.protections.contains(&demand.output_scope)
        }), "this actual copied h protection must reach a real source contribution");
    }
    assert!(uses.len() >= 2, "both real helper calls must yield authenticated copied Function comparisons");
}

// Bounded construction census, not an Inc/same-z or selected-provider theorem.
mod native_selected_use_census {
    use super::*;
    use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution};

    const CAPTURED: &str = "act signal:\n    our ping: () -> int\nact write:\n    our put: () -> int\nmy receive (f: () -> 'a) = { my g = f(); g() }\nmy outer (thunk:[write] int) = {\n    my captured (u:()) = thunk;\n    my direct (u:()) = signal::ping();\n    my factory_captured (u:()) = captured;\n    my factory_direct (u:()) = direct;\n    catch receive factory_captured { signal::ping(), _ -> 1, v -> v }\n}\nmy answer = outer (signal::ping())\n";

    fn facts<'a>(session: &'a InferenceSession, occurrence: &HirOccurrenceId, slot: u8) -> Vec<&'a SemanticFact> {
        session.store.provenance().iter().filter(|edge| {
            edge.cause().occurrence().occurrence() == occurrence
                && edge.cause().occurrence().local_slot() == slot
        }).map(|edge| session.store.facts().iter().find(|fact| fact.id() == edge.fact()).unwrap()).collect()
    }
    fn canonical_bound(session: &InferenceSession, bound: BoundKey) -> BoundKey {
        let endpoint = |value| match value {
            ExtrusionEndpoint::Value(value) => ExtrusionEndpoint::Value(session.canonical_value(value)),
            ExtrusionEndpoint::Effect(effect) => ExtrusionEndpoint::Effect(session.canonical_effect(effect)),
        };
        BoundKey(endpoint(bound.0), bound.1, endpoint(bound.2))
    }
    fn mapped_bound(session: &InferenceSession, graph: &candidate_scheme::Graph,
        snapshot: &candidate_scheme::LocalUseSnapshot, bound: &candidate_scheme::Bound) -> BoundKey {
        let endpoint = |index: usize, polarity: Polarity| match bound.kind {
            ComponentKind::Value => ExtrusionEndpoint::Value(session.value_endpoint(snapshot.terms[index].unwrap(), polarity)),
            ComponentKind::Effect => ExtrusionEndpoint::Effect(snapshot.effect_operands.get(&index).copied()
                .unwrap_or_else(|| session.effect_endpoint(snapshot.terms[index].unwrap(), polarity))),
        };
        assert_eq!(snapshot.terms.len(), graph.nodes.len());
        let lower = endpoint(bound.lower, Polarity::Positive);
        let upper = endpoint(bound.upper, Polarity::Negative);
        if bound.side == Polarity::Positive { BoundKey(upper, bound.side, lower) }
        else { BoundKey(lower, bound.side, upper) }
    }
    fn parents(context: &State) -> HashMap<RelationId, Vec<(RelationId, &'static str)>> {
        let mut parents: HashMap<_, Vec<_>> = HashMap::new();
        for dependency in &context.dependencies {
            let (child, inputs): (_, Vec<_>) = match *dependency {
                Dependency::Derived { child, parent } => (child, vec![(parent, "Derived")]),
                Dependency::FunctionPort { child, parent, .. } => (child, vec![(parent, "FunctionPort")]),
                Dependency::Transport { child, parent, .. } => (child, vec![(parent, "Transport")]),
                Dependency::Replay { child, lower, upper, .. } =>
                    (child, vec![(lower, "Replay.lower"), (upper, "Replay.upper")]),
            };
            for (parent, role) in inputs {
                assert!((parent.0 as usize) < context.relations.len());
                parents.entry(child).or_default().push((parent, role));
            }
        }
        parents
    }
    fn ancestry(start: RelationId, parents: &HashMap<RelationId, Vec<(RelationId, &'static str)>>) -> HashSet<RelationId> {
        let mut seen = HashSet::new();
        let mut work = vec![start];
        while let Some(relation) = work.pop() {
            if !seen.insert(relation) { continue; }
            for &(parent, _) in parents.get(&relation).into_iter().flatten() { work.push(parent); }
        }
        seen
    }

    #[test]
    fn native_selected_use_census_retains_actual_local_maps_and_source_anchors() {
        for selected in ["factory_captured", "factory_direct"] {
            let text = CAPTURED.replace("receive factory_captured", &format!("receive {selected}"));
            let source: Arc<yu_syntax::SourceText> = Arc::from(text.as_str());
            let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
                Arc::new(yu_syntax::SyntaxEnvironment::empty()));
            assert!(parsed.syntax_diagnostics().unwrap().is_empty());
            let hir = Arc::new(lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("selected-use-census", selected))),
                &parsed, yu_hir::SemanticImports::empty()).unwrap());
            let root = |name: &str| hir.items().iter().find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root()),
                _ => None,
            }).unwrap();
            let outer = hir.local_source(root("outer")).unwrap().unwrap();
            let receive = hir.local_source(root("receive")).unwrap().unwrap();
            let local = |source: &yu_hir::LocalSource, name: &str| source.bindings().iter()
                .find(|binding| binding.spelling.as_ref() == name).unwrap().id.clone();
            let selected_id = local(outer, selected);
            let provider_id = local(outer, if selected == "factory_captured" { "captured" } else { "direct" });
            let g_id = local(receive, "g");
            let mut requested = HashSet::new();
            for item in hir.items() {
                let HirItem::Binding(binding) = item else { continue; };
                if let Some(source) = hir.local_source(binding.definition_root()).unwrap() {
                    for expression in source.expressions() {
                        if matches!(&expression.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Local(_), .. }) {
                            requested.insert(expression.occurrence.clone());
                        }
                    }
                }
            }
            let mut session = InferenceSession::try_new_candidate(
                ConstraintBatch::collect_candidate_mode_scoped(hir.clone(), true, true, false).unwrap()).unwrap();
            session.candidate_graph.as_mut().unwrap().local_use_census = Some(candidate_scheme::LocalUseCensus {
                requested, snapshots: Vec::new(), module_uses: Vec::new(),
            });
            session.execute().unwrap();
            assert!(!state(&session).scoped_enabled);
            let context = state(&session);
            let graph_state = session.candidate_graph.as_ref().unwrap();
            let snapshots = &graph_state.local_use_census.as_ref().unwrap().snapshots;
            assert!(!snapshots.is_empty());
            let mut selected_routes = 0;
            let mut provider_routes = 0;
            let mut g_routes = 0;
            let mut restored = 0;
            for snapshot in snapshots {
                let route = &graph_state.local_routes[snapshot.route];
                assert_eq!(route.slot, snapshot.slot);
                assert_eq!(route.occurrence, snapshot.occurrence);
                let source = hir.local_source(route.local.definition_root().unwrap()).unwrap().unwrap();
                let expression = source.expressions().iter().find(|expression| expression.occurrence == route.occurrence).unwrap();
                assert!(matches!(&expression.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &route.local));
                assert_eq!(hir.occurrence_source_key(&route.occurrence).unwrap(), Some(&expression.source));
                assert_eq!(route.graph.live_root, graph_state.locals[route.slot].as_ref().unwrap().root);
                assert_eq!(snapshot.restored_bounds, route.graph.bounds.len());
                assert_eq!(snapshot.evidence_remap.len(), route.graph.bound_evidence.len());
                let fresh_root = snapshot.terms[route.graph.root].unwrap();
                let target = session.batch.component_term_at(snapshot.target_component);
                assert!(facts(&session, &route.occurrence, 0).iter().any(|fact| fact.lower() == fresh_root && fact.upper() == target), "actual FreshUse publication");
                for (index, bound) in route.graph.bounds.iter().enumerate() {
                    let antecedent = snapshot.evidence_remap[bound.evidence.0];
                    assert_eq!(context.evidence.snapshots[antecedent.0], route.graph.bound_evidence[bound.evidence.0]);
                    let mapped = mapped_bound(&session, &route.graph, snapshot, bound);
                    let admissions: Vec<_> = context.evidence.admissions.iter().enumerate().filter(|(_, admission)| {
                        matches!(admission.cause, BoundAdmissionCause::FreshUse { antecedent: actual, use_origin, source_bound, .. }
                            if actual == antecedent && use_origin == snapshot.context_use && source_bound == bound.source_bound)
                    }).collect();
                    assert!(!admissions.is_empty(), "bound {index} has actual FreshUse restoration evidence");
                    assert!(admissions.iter().any(|(_, admission)| canonical_bound(&session, admission.bound) == canonical_bound(&session, mapped)));
                    for (admission_index, admission) in admissions {
                        assert!(context.evidence.emissions.iter().any(|emission| emission.admission.0 == admission_index));
                        if let BoundAdmissionCause::FreshUse { mapped_relation: Some(child), .. } = admission.cause {
                            let parent = bound.relation.unwrap();
                            assert!(context.dependency_keys.iter().any(|dependency| matches!(dependency,
                                Dependency::Transport { child: actual, parent: original, use_origin, witness: Some(witness) }
                                if *actual == child && *original == parent && *use_origin == snapshot.context_use
                                    && witness.reason == TransportReason::FreshUse && witness.from == bound.source_bound
                                    && canonical_bound(&session, witness.to) == canonical_bound(&session, mapped))));
                            assert!(snapshot.context_remap.values().any(|mapped| *mapped == context.relations[child.0 as usize].key.context));
                        }
                    }
                    restored += 1;
                }
                selected_routes += usize::from(route.local == selected_id);
                provider_routes += usize::from(route.local == provider_id);
                g_routes += usize::from(route.local == g_id);
                eprintln!("PRESENT {selected} local route={} use={} occurrence={:?} root={fresh_root:?} target={target:?} restored={}", snapshot.route, snapshot.context_use, snapshot.occurrence, snapshot.restored_bounds);
            }
            assert!(selected_routes > 0 && provider_routes > 0 && g_routes > 0);
            let outer_registration = session.batch.candidate_calls.formals.iter().find(|formal|
                formal.owner.definition_root() == Some(root("outer")) && formal.role == candidate_call::FormalRole::Computation).unwrap();
            let entry = outer_registration.entry_effect.unwrap();
            let lambda = &outer.expressions()[outer_registration.lambda];
            let function = facts(&session, &lambda.occurrence, 2).into_iter().find_map(|fact|
                InferenceSession::positive_function_children(&session.store, session.value_endpoint(fact.lower(), Polarity::Positive))).unwrap();
            assert_eq!(session.effect_endpoint(function.1, Polarity::Negative), session.canonical_effect(EffectEndpointKey::EffectRow(entry)));
            let thunk = outer.expressions().iter().find(|expression| matches!(&expression.form,
                LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(id), .. } if id == &outer_registration.parameter)).unwrap();
            for slot in [1, 2] {
                assert!(!facts(&session, &thunk.occurrence, slot).is_empty());
                assert!(context.origins.iter().any(|origin| origin.occurrence == ConstraintOccurrenceId::new(thunk.occurrence.clone(), slot)));
            }
            let operation = outer.expressions().iter().find(|expression| matches!(&expression.form,
                LocalSourceForm::Operation { resolution: yu_hir::SourceOperationResolution::Resolved(_) })).unwrap();
            assert!(!facts(&session, &operation.occurrence, 42).is_empty());
            assert_eq!(hir.occurrence_source_key(&operation.occurrence).unwrap(), Some(&operation.source));
            let calls: Vec<_> = session.batch.candidate_calls.calls.iter().filter(|call| call.owner.definition_root() == Some(root("receive"))).collect();
            assert_eq!(calls.len(), 2);
            let first = calls.iter().find(|call| matches!(&receive.expression(&call.callee).unwrap().form,
                LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(_), .. })).unwrap();
            let second = calls.iter().find(|call| matches!(&receive.expression(&call.callee).unwrap().form,
                LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &g_id)).unwrap();
            for call in [*first, *second] {
                let native = call.native.unwrap();
                let demand = InferenceSession::negative_function_children(&session.store, session.value_endpoint(native.demand, Polarity::Negative)).unwrap();
                assert_eq!(demand.3, native.result);
                assert_eq!(demand.2, native.invocation_effect);
                assert_eq!(session.value_endpoint(native.result, Polarity::Negative), session.canonical_value(ValueEndpointKey::ValueRow(session.live_components[call.result].ordinal)));
                assert_eq!(hir.occurrence_source_key(call.checking.occurrence()).unwrap(), Some(&receive.expressions()[call.expression].source));
                eprintln!("PRESENT {selected} call={:?} result={:?} invocation={:?} application={:?}", call.checking, native.result, native.invocation_effect, native.application_effect);
            }
            let first_result = session.value_endpoint(first.native.unwrap().result, Polarity::Negative);
            let scheme = graph_state.locals.iter().flatten().find(|scheme| scheme.id == g_id).unwrap();
            assert_eq!(session.canonical_value(ValueEndpointKey::ValueRow(scheme.root)), first_result);
            let parents = parents(context);
            let first_origins: HashSet<_> = context.origins.iter().filter(|origin| origin.occurrence == first.checking).map(|origin| origin.relation).collect();
            let second_origins: HashSet<_> = context.origins.iter().filter(|origin| origin.occurrence == second.checking).map(|origin| origin.relation).collect();
            assert!(!first_origins.is_empty() && !second_origins.is_empty());
            let mut projected = [0usize; 2];
            for dependency in &context.dependencies {
                let Dependency::FunctionPort { child, parent, field, .. } = *dependency else { continue; };
                if !matches!(field, FunctionField::Result | FunctionField::ResultEffect) { continue; }
                let lineage = ancestry(parent, &parents);
                for (index, origins) in [&first_origins, &second_origins].iter().enumerate() {
                    if !lineage.is_disjoint(origins) {
                        let parent_key = context.relations[parent.0 as usize].key;
                        let TypedPairKey::Value(pair) = parent_key.pair else { panic!("Function parent"); };
                        let lower = InferenceSession::positive_function_children(&session.store, pair.lower).unwrap();
                        let upper = InferenceSession::negative_function_children(&session.store, pair.upper).unwrap();
                        let expected = if field == FunctionField::Result {
                            TypedPairKey::Value(CanonicalValuePairKey { lower: session.value_endpoint(lower.3, Polarity::Positive), upper: session.value_endpoint(upper.3, Polarity::Negative) })
                        } else { TypedPairKey::Effect { lower: session.effect_endpoint(lower.2, Polarity::Positive), upper: session.effect_endpoint(upper.2, Polarity::Negative) } };
                        assert_eq!(session.candidate_context_pair(context.relations[child.0 as usize].key.pair), session.candidate_context_pair(expected));
                        projected[index] += 1;
                    }
                }
            }
            eprintln!("PRESENT {selected} entry_raw={entry} entry_rep={:?} outward={:?} mapped_restorations={restored} call_projection_counts={projected:?} directed_dependencies={}", session.canonical_effect(EffectEndpointKey::EffectRow(entry)), session.effect_endpoint(function.2, Polarity::Positive), context.dependencies.len());
            eprintln!("NEXT UNINSPECTED {selected}: selected module-use -> first f() dispatch use-instance/provider association; retained local maps authenticate each constructor but no cross-call provider association census is claimed. Both provider declarations and both ordered Replay inputs remain retained.");
        }
    }

    fn bound_endpoints(bound: BoundKey) -> (ExtrusionEndpoint, ExtrusionEndpoint) {
        if bound.1 == Polarity::Positive { (bound.2, bound.0) } else { (bound.0, bound.2) }
    }
    fn module_function_images(session: &InferenceSession, route: &candidate_scheme::FreshRoute,
        use_origin: usize, original: ValueEndpointKey) -> Vec<(RelationId, ValueEndpointKey)> {
        let context = state(session);
        let mut images = Vec::new();
        for bound in &route.graph.bounds {
            let Some(parent) = bound.relation else { continue; };
            let (lower, upper) = bound_endpoints(bound.source_bound);
            let side = if lower == ExtrusionEndpoint::Value(original) { Some(true) }
                else if upper == ExtrusionEndpoint::Value(original) { Some(false) } else { None };
            let Some(lower_side) = side else { continue; };
            for dependency in &context.dependencies {
                let Dependency::Transport { child, parent: actual_parent, use_origin: actual_use,
                    witness: Some(witness) } = *dependency else { continue; };
                if actual_parent != parent || actual_use != use_origin || witness.from != bound.source_bound
                    || witness.reason != TransportReason::FreshUse { continue; }
                assert_eq!(context.relations[child.0 as usize].key.sources,
                    context.relations[parent.0 as usize].key.sources);
                assert_eq!(session.candidate_context_pair(context.relations[child.0 as usize].key.pair),
                    session.candidate_context_pair(bound_pair(witness.to)));
                let (lower, upper) = bound_endpoints(witness.to);
                let ExtrusionEndpoint::Value(image) = (if lower_side { lower } else { upper })
                    else { panic!("Value Function image"); };
                images.push((child, image));
            }
        }
        images
    }

    #[test]
    fn native_module_use_origin_census_joins_actual_transport_instances() {
        for selected in ["factory_captured", "factory_direct"] {
            let text = CAPTURED.replace("receive factory_captured", &format!("receive {selected}"));
            let source: Arc<yu_syntax::SourceText> = Arc::from(text.as_str());
            let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
                Arc::new(yu_syntax::SyntaxEnvironment::empty()));
            assert!(parsed.syntax_diagnostics().unwrap().is_empty());
            let hir = Arc::new(lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("module-use-census", selected))),
                &parsed, yu_hir::SemanticImports::empty()).unwrap());
            let binding = |name: &str| hir.items().iter().find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding), _ => None,
            }).unwrap();
            let outer = hir.local_source(binding("outer").definition_root()).unwrap().unwrap();
            let receive = hir.local_source(binding("receive").definition_root()).unwrap().unwrap();
            let answer = hir.local_source(binding("answer").definition_root()).unwrap().unwrap();
            let selected_local = outer.bindings().iter().find(|local| local.spelling.as_ref() == selected).unwrap();
            let g = receive.bindings().iter().find(|local| local.spelling.as_ref() == "g").unwrap();
            let module_name = |source: &yu_hir::LocalSource, id: &yu_hir::DefId| source.expressions().iter()
                .find(|expression| matches!(&expression.form,
                    LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(actual), .. } if actual == id))
                .unwrap().occurrence.clone();
            let receive_name = module_name(outer, binding("receive").id());
            let outer_name = module_name(answer, binding("outer").id());
            let mut requested = HashSet::from([receive_name.clone(), outer_name.clone()]);
            for source in [outer, receive] {
                for expression in source.expressions() {
                    if matches!(&expression.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Local(_), .. }) {
                        requested.insert(expression.occurrence.clone());
                    }
                }
            }
            let mut session = InferenceSession::try_new_candidate(
                ConstraintBatch::collect_candidate_mode_scoped(hir.clone(), true, true, false).unwrap()).unwrap();
            session.candidate_graph.as_mut().unwrap().local_use_census = Some(candidate_scheme::LocalUseCensus {
                requested, snapshots: Vec::new(), module_uses: Vec::new(),
            });
            session.execute().unwrap();
            let context = state(&session);
            assert!(!context.scoped_enabled);
            let graph = session.candidate_graph.as_ref().unwrap();
            let census = graph.local_use_census.as_ref().unwrap();
            let parents = parents(context);
            let first = session.batch.candidate_calls.calls.iter().find(|call|
                call.owner.definition_root() == Some(binding("receive").definition_root())
                    && matches!(&receive.expression(&call.callee).unwrap().form,
                        LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(_), .. })).unwrap();
            let second = session.batch.candidate_calls.calls.iter().find(|call|
                call.owner.definition_root() == Some(binding("receive").definition_root())
                    && matches!(&receive.expression(&call.callee).unwrap().form,
                        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &g.id)).unwrap();
            assert_eq!(g.initializer.ordinal() as usize, first.expression);
            let selected_snapshot = census.snapshots.iter().find(|snapshot|
                graph.local_routes[snapshot.route].local == selected_local.id).unwrap();
            let selected_publication: HashSet<_> = context.origins.iter().filter(|origin|
                origin.occurrence == ConstraintOccurrenceId::new(selected_snapshot.occurrence.clone(), 0))
                .map(|origin| origin.relation).collect();
            assert!(!selected_publication.is_empty());
            let g_name = &receive.expression(&second.callee).unwrap().occurrence;
            let g_snapshot = census.snapshots.iter().find(|snapshot| &snapshot.occurrence == g_name).unwrap();
            let g_route = &graph.local_routes[g_snapshot.route];
            assert_eq!(g_route.local, g.id);
            assert_eq!(g_route.graph.live_root, graph.locals[g_route.slot].as_ref().unwrap().root);
            assert!(facts(&session, g_name, 0).iter().any(|fact|
                fact.lower() == g_snapshot.terms[g_route.graph.root].unwrap()
                    && fact.upper() == session.batch.component_term_at(g_snapshot.target_component)));
            let outer_registration = session.batch.candidate_calls.formals.iter().find(|formal|
                formal.owner.definition_root() == Some(binding("outer").definition_root())
                    && formal.role == candidate_call::FormalRole::Computation).unwrap();
            let entry = outer_registration.entry_effect.unwrap();
            let lambda = &outer.expressions()[outer_registration.lambda];
            let original_outer_function = facts(&session, &lambda.occurrence, 2).into_iter().find_map(|fact| {
                let endpoint = session.value_endpoint(fact.lower(), Polarity::Positive);
                InferenceSession::positive_function_children(&session.store, endpoint).map(|_| endpoint)
            }).unwrap();
            let mut first_unavailable = None;
            for (name, original_functions) in [
                (&receive_name, vec![session.value_endpoint(first.native.unwrap().demand, Polarity::Negative),
                    session.value_endpoint(second.native.unwrap().demand, Polarity::Negative)]),
                (&outer_name, vec![original_outer_function]),
            ] {
                let routes: Vec<_> = graph.routes.iter().filter(|route| route.use_id.occurrence() == name).collect();
                assert!(!routes.is_empty(), "actual module definition route");
                let origins: Vec<_> = census.module_uses.iter().filter(|(occurrence, _)| occurrence == name).collect();
                assert!(!origins.is_empty(), "actual module FreshUse constructor origin");
                for route in routes {
                    let uses: Vec<_> = session.batch.definition_uses().iter().filter(|use_record|
                        use_record.id() == &route.use_id).collect();
                    assert_eq!(uses.len(), 1);
                    let record = uses[0];
                    let publication: Vec<_> = session.routed_uses.iter().filter(|published|
                        published.use_id == route.use_id).collect();
                    assert_eq!(publication.len(), 1);
                    let fact_id = publication[0].fact.expect("structured module root link");
                    let fact = session.store.facts().iter().find(|fact| fact.id() == fact_id).unwrap();
                    assert!(session.store.provenance().iter().any(|edge| edge.fact() == fact_id
                        && edge.cause().occurrence() == &ConstraintOccurrenceId::new(name.clone(), 0)));
                    assert_eq!(fact.upper(), session.batch.component_term_at(record.use_value_component));
                    let source = if name == &receive_name { outer } else { answer };
                    let expression = source.expressions().iter().find(|expression| &expression.occurrence == name).unwrap();
                    assert_eq!(hir.occurrence_source_key(name).unwrap(), Some(&expression.source));
                    for (_, use_origin) in &origins {
                        let use_origin = *use_origin;
                        let mut bound_transports = 0;
                        for bound in &route.graph.bounds {
                            let Some(parent) = bound.relation else { continue; };
                            for dependency in &context.dependencies {
                                if let Dependency::Transport { child, parent: original, use_origin: actual,
                                    witness: Some(witness) } = *dependency {
                                    if original == parent && actual == use_origin && witness.from == bound.source_bound {
                                        assert_eq!(witness.reason, TransportReason::FreshUse);
                                        assert_eq!(context.relations[child.0 as usize].key.sources,
                                            context.relations[parent.0 as usize].key.sources);
                                        assert_eq!(session.candidate_context_pair(context.relations[child.0 as usize].key.pair),
                                            session.candidate_context_pair(bound_pair(witness.to)));
                                        bound_transports += 1;
                                    }
                                }
                            }
                        }
                        eprintln!("PRESENT {selected} module={name:?} DefinitionUse={:?} Fact={fact_id:?} actual_context_use={use_origin} captured_transports={bound_transports}", route.use_id);
                        for (function_index, &original) in original_functions.iter().enumerate() {
                            let images = module_function_images(&session, route, use_origin, original);
                            if images.is_empty() {
                                let shared_rows = route.graph.rows.iter().zip(&route.rows).filter(|(source, image)| source.key == **image).count();
                                eprintln!("UNAVAILABLE {selected} exact Function image module={name:?} operand={original:?}; shared-row anchors={shared_rows} (no source-field association inferred from canonical equality)");
                                first_unavailable.get_or_insert("original Function operand -> same-module-use copied Function/shared field anchor");
                            }
                            for (transport, image) in images {
                                match original {
                                    ValueEndpointKey::PositiveFunction(_) => {
                                        let original = InferenceSession::positive_function_children(&session.store, original).unwrap();
                                        let mapped = InferenceSession::positive_function_children(&session.store, image).unwrap();
                                        assert_eq!(session.effect_endpoint(original.1, Polarity::Negative), session.canonical_effect(EffectEndpointKey::EffectRow(entry)));
                                        eprintln!("PRESENT {selected} actual_outer_AE Transport={transport:?} original_term={:?} mapped_term={:?} mapped_endpoint={:?}", original.1, mapped.1, session.effect_endpoint(mapped.1, Polarity::Negative));
                                    }
                                    ValueEndpointKey::NegativeFunction(_) => {
                                        let mut dispatches = 0;
                                        let mut selected_dispatches = 0;
                                        let mut result_children = 0;
                                        let mut effect_children = 0;
                                        for (index, relation) in context.relations.iter().enumerate() {
                                            let TypedPairKey::Value(pair @ CanonicalValuePairKey {
                                                lower: ValueEndpointKey::PositiveFunction(_), upper,
                                            }) = relation.key.pair else { continue; };
                                            if upper != image { continue; }
                                            let parent = RelationId(index as u32);
                                            let lineage = ancestry(parent, &parents);
                                            if !lineage.contains(&transport) { continue; }
                                            dispatches += 1;
                                            selected_dispatches += usize::from(!lineage.is_disjoint(&selected_publication));
                                            let lower = InferenceSession::positive_function_children(&session.store, pair.lower).unwrap();
                                            let upper = InferenceSession::negative_function_children(&session.store, pair.upper).unwrap();
                                            for dependency in &context.dependencies {
                                                let Dependency::FunctionPort { child, parent: actual, field, .. } = *dependency else { continue; };
                                                if actual != parent { continue; }
                                                let expected = match field {
                                                    FunctionField::Result => { result_children += 1;
                                                        TypedPairKey::Value(CanonicalValuePairKey { lower: session.value_endpoint(lower.3, Polarity::Positive), upper: session.value_endpoint(upper.3, Polarity::Negative) }) }
                                                    FunctionField::ResultEffect => { effect_children += 1;
                                                        TypedPairKey::Effect { lower: session.effect_endpoint(lower.2, Polarity::Positive), upper: session.effect_endpoint(upper.2, Polarity::Negative) } }
                                                    _ => continue,
                                                };
                                                assert_eq!(session.candidate_context_pair(context.relations[child.0 as usize].key.pair), session.candidate_context_pair(expected));
                                            }
                                        }
                                        eprintln!("PRESENT {selected} same_module_use={use_origin} original_call={function_index} Function_image={image:?} via={transport:?} dispatch_candidates={dispatches} selected_publication_ancestry={selected_dispatches} Result={result_children} ResultEffect={effect_children}");
                                        if selected_dispatches == 0 {
                                            first_unavailable.get_or_insert("selected factory publication -> same-module-use Function dispatch directed retained ancestry");
                                        }
                                    }
                                    _ => unreachable!(),
                                }
                            }
                        }
                    }
                }
            }
            eprintln!("PRESENT {selected} original g initializer=first f() expression; local Name publication context_use={} actual mapped root retained", g_snapshot.context_use);
            match first_unavailable {
                Some(seam) => eprintln!("FIRST UNAVAILABLE {selected}: {seam}; bounded association search only, not erasure or source Inc"),
                None => eprintln!("NEXT UNINSPECTED {selected}: compose both same-return packet inlets and event/view/receipt interpretation; candidate sets are not a uniqueness theorem"),
            }
        }
    }

}
