//! Actual candidate extrusion/intrusion evidence, separate from injective transport models.
use super::*;
use crate::candidate_scheme::RowKey;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};

fn hir(text: &str) -> Arc<HirModule> {
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "healthy source fixture: {text}");
    Arc::new(lower_module_with_local_source(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("intrusion", "source.yu"))),
        &parsed, yu_hir::SemanticImports::empty()).unwrap())
}
fn session() -> InferenceSession {
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir("my seed x = seed x"), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    session
}
fn cause(session: &InferenceSession) -> (ConstraintOccurrenceId, CauseId) {
    let HirItem::Binding(binding) = &session.batch.hir.items()[0] else { panic!("source binding") };
    let occurrence = ConstraintOccurrenceId::new(binding.value().occurrence().clone(), 0);
    let cause = CauseId::for_occurrence(occurrence.clone());
    (occurrence, cause)
}
fn row(session: &mut InferenceSession, effect: bool, level: u32) -> RowKey {
    if effect { RowKey::Effect(session.fresh_effect_at_level(level).unwrap()) }
    else { RowKey::Value(session.fresh_value_at_level(level).unwrap()) }
}
fn extrude(session: &mut InferenceSession, parent: RowKey, polarity: Polarity) -> RowKey {
    let checking = session.batch.candidate_source.references.checking.keys().next().unwrap().clone();
    let task = match parent {
        RowKey::Value(row) => LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(row), upper: ValueEndpointKey::ValueRow(row) }),
        RowKey::Effect(row) => LiveConstraintTask::Effect(EffectEndpointKey::EffectRow(row), EffectEndpointKey::EffectRow(row)),
    };
    let relation = session.candidate_context_seed(task, &checking, None).unwrap().unwrap();
    let previous = session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing.replace(relation);
    let copy = session.candidate_extrude(row_endpoint(parent), polarity, 0).unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = previous;
    let copy = match copy {
        ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(i)) => RowKey::Value(i),
        ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(i)) => RowKey::Effect(i),
        _ => panic!("extrusion returns a real row copy"),
    };
    assert_ne!(copy, parent);
    let recorded = session.candidate_graph.as_ref().unwrap().intrusion.parents.last().unwrap();
    assert_eq!(recorded.copy, copy);
    assert_eq!(recorded.parent, parent);
    assert_eq!(recorded.polarity, polarity);
    assert_eq!(recorded.target, 0);
    copy
}
fn close_cycle(session: &mut InferenceSession, _parent: RowKey, _copy: RowKey, _polarity: Polarity) {
    // The source fixture's actual self-reference qualifies the retained event.
    // No reverse type bound is needed to establish a source Value SCC.
    session.settle_candidate_intrusion(None).unwrap();
}

#[test]
fn real_extrusion_parent_copy_scc_equates_both_kinds_and_polarities() {
    for effect in [false, true] {
        for polarity in [Polarity::Positive, Polarity::Negative] {
            let mut session = session();
            let parent = row(&mut session, effect, 2);
            let copy = extrude(&mut session, parent, polarity);
            match copy { RowKey::Value(i) => session.value_metadata[i as usize].non_generic = true,
                RowKey::Effect(i) => session.effect_metadata[i as usize].non_generic = true }
            close_cycle(&mut session, parent, copy, polarity);
            let state = &session.candidate_graph.as_ref().unwrap().intrusion;
            assert_eq!(state.rep(copy), parent);
            assert_eq!(state.rep(parent), parent);
            assert!(state.generation > 0);
            match parent {
                RowKey::Value(i) => { assert_eq!(session.value_levels[i as usize], 0); assert!(session.value_metadata[i as usize].non_generic); }
                RowKey::Effect(i) => { assert_eq!(session.effect_levels[i as usize], 0); assert!(session.effect_metadata[i as usize].non_generic); }
            }
            assert!(session.typed_worklist.is_empty());
        }
    }
}

#[test]
fn real_extrusion_between_distinct_source_components_keeps_parent_copy_distinct() {
    for effect in [false, true] {
        for polarity in [Polarity::Positive, Polarity::Negative] {
            let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir("my id x = x\nmy client x = id x"), true, true).unwrap()).unwrap();
            session.start_candidate_graph().unwrap();
            assert_eq!(session.batch.hir.items().len(), 2);
            assert_eq!(session.batch.candidate_source.references.events.len(), 1);
            let parent = row(&mut session, effect, 2);
            let copy = extrude(&mut session, parent, polarity);
            session.settle_candidate_intrusion(None).unwrap();
            let state = &session.candidate_graph.as_ref().unwrap().intrusion;
            assert_ne!(state.rep(copy), state.rep(parent));
            assert_eq!(state.generation, 0);
            assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
        }
    }
}

#[test]
fn merged_identity_accepts_later_bounds_and_failed_transaction_restores_it() {
    let mut session = session();
    let parent = row(&mut session, false, 2);
    let parent_index = match parent { RowKey::Value(i) => i as usize, _ => unreachable!() };
    session.candidate_insert_bound(row_endpoint(parent), Polarity::Negative,
        ExtrusionEndpoint::Value(ValueEndpointKey::TopNegative)).unwrap();
    let values_before = session.bounds.len();
    let (occurrence, cause) = cause(&session);
    let result: Result<(), SolveAvailabilityError> = session.with_route_transaction(|session| {
        let copy = extrude(session, parent, Polarity::Positive);
        if let RowKey::Value(i) = copy { session.value_metadata[i as usize].non_generic = true; }
        close_cycle(session, parent, copy, Polarity::Positive);
        let copy_index = match copy { RowKey::Value(i) => i, _ => unreachable!() };
        session.constrain_live_value(CanonicalValuePairKey {
            lower: ValueEndpointKey::IntPositive, upper: ValueEndpointKey::ValueRow(copy_index),
        }, &occurrence, &cause)?;
        assert!(session.bounds[parent_index].exact_non_variable_lowers.contains(&ValueEndpointKey::IntPositive));
        assert_eq!(session.canonical_value(ValueEndpointKey::ValueRow(copy_index)), ValueEndpointKey::ValueRow(parent_index as u32));
        Err(SolveAvailabilityError::IdentityExhausted)
    });
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.bounds.len(), values_before);
    assert_eq!(session.value_levels[parent_index], 2);
    assert!(session.bounds[parent_index].exact_non_variable_lowers.is_empty());
    assert_eq!(session.bounds[parent_index].exact_non_variable_uppers, vec![ValueEndpointKey::TopNegative]);
    assert!(session.bounds[parent_index].direct_lower_rows.is_empty());
    assert!(session.bounds[parent_index].direct_upper_rows.is_empty());
    assert!(!session.value_metadata[parent_index].non_generic);
    let state = &session.candidate_graph.as_ref().unwrap().intrusion;
    assert!(state.parents.is_empty());
    assert_eq!(state.generation, 0);
    assert_eq!(state.rep(parent), parent);
    assert_eq!(session.candidate_graph.as_ref().unwrap().scratch_bytes, 0);
}

#[test]
fn natural_recursive_definitions_use_open_roots_and_keep_real_function_bounds() {
    for text in ["my recur x = recur x", "my left x = right x\nmy right y = left y"] {
        let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir(text), true, true).unwrap()).unwrap();
        assert!(!session.batch.scc_plan().components_in_dependency_first_order().all(|component|
            session.batch.scc_plan().internal_uses(component).unwrap().is_empty()));
        session.start_candidate_graph().unwrap();
        let solved = session.run_candidate().unwrap();
        assert!(solved.data.errors.is_empty());
        let state = solved.data.candidate_graph.as_ref().unwrap();
        assert!(state.intrusion.active_roots.is_empty());
        assert!(state.intrusion.active_uses.is_empty());
        for graph in state.graphs.iter().flatten() {
            assert!(graph.nodes.iter().any(|node| matches!(node, crate::candidate_scheme::Node::Function { polarity: Polarity::Positive, .. })));
            assert!(graph.nodes.iter().any(|node| matches!(node, crate::candidate_scheme::Node::Function { polarity: Polarity::Negative, .. })));
            assert!(graph.rows.iter().any(|row| row.key.kind() == ComponentKind::Effect));
        }
    }
}

#[test]
fn natural_local_capture_keeps_live_late_integer_bounds_and_shared_older_images() {
    let hir = hir("my succ x = 1\nmy apply g = { my relay x = g x; my before = relay 1; relay 1 }\nmy answer = apply succ");
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    let solved = session.run_candidate().unwrap();
    assert!(solved.data.errors.is_empty());
    let state = solved.data.candidate_graph.as_ref().unwrap();
    assert!(!state.intrusion.parents.is_empty(), "captured younger coordinates underwent actual extrusion");
    let answer = solved.data.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "answer" => Some(binding.definition_root()), _ => None,
    }).unwrap();
    let apply = solved.data.hir.items().iter().find_map(|item| match item {
        HirItem::Binding(binding) if binding.name().spelling() == "apply" => Some(binding.definition_root()), _ => None,
    }).unwrap();
    let source = hir.local_source(apply).unwrap().unwrap();
    let occurrences: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) } if spelling.as_ref() == "relay"))
        .map(|expression| &expression.occurrence).collect();
    assert_eq!(occurrences.len(), 2);
    let routes: Vec<_> = occurrences.iter().map(|occurrence| state.local_routes.iter().find(|route| &route.occurrence == *occurrence).unwrap()).collect();
    assert!(routes[0].graph.rows.iter().enumerate().any(|(a, source)| !source.local
        && routes[1].graph.rows.iter().enumerate().any(|(b, other)| !other.local
            && state.intrusion.rep(source.key) == state.intrusion.rep(other.key)
            && state.intrusion.rep(routes[0].rows[a]) == state.intrusion.rep(source.key)
            && state.intrusion.rep(routes[1].rows[b]) == state.intrusion.rep(other.key))),
        "the same older captured anchor remains its original image across uses");
    assert!(routes[0].graph.rows.iter().enumerate().any(|(a, source)| source.local
        && routes[1].graph.rows.iter().enumerate().any(|(b, other)| other.local
            && state.intrusion.rep(source.key) == state.intrusion.rep(other.key)
            && state.intrusion.rep(routes[0].rows[a]) != state.intrusion.rep(routes[1].rows[b]))),
        "eligible local coordinates have independent fresh images alongside shared captures");
    let position = solved.data.root_scheme_positions[answer];
    let graph = state.graphs[position].as_ref().unwrap();
    let same_node = |a: usize, b: usize| a == b || match (graph.nodes[a], graph.nodes[b]) {
        (crate::candidate_scheme::Node::Row { row: a, .. }, crate::candidate_scheme::Node::Row { row: b, .. }) =>
            state.intrusion.rep(graph.rows[a].key) == state.intrusion.rep(graph.rows[b].key),
        _ => false,
    };
    let mut pending: Vec<_> = graph.nodes.iter().enumerate().filter_map(|(index, node)|
        matches!(node, crate::candidate_scheme::Node::Leaf(crate::candidate_scheme::Atom::IntPositive)).then_some(index)).collect();
    let mut seen = Vec::new();
    let mut integer_reaches_answer = false;
    while let Some(node) = pending.pop() {
        if same_node(node, graph.root) { integer_reaches_answer = true; break; }
        if seen.iter().copied().any(|old| same_node(old, node)) { continue; }
        seen.push(node);
        for bound in graph.bounds.iter().filter(|bound| bound.kind == ComponentKind::Value) {
            if same_node(bound.lower, node) { pending.push(bound.upper); }
        }
    }
    assert!(integer_reaches_answer, "an actual integer value bound reaches the answer root");
}

#[test]
fn relation_completion_generation_rollback_and_supported_retry() {
    for effect in [false, true] {
        let mut session = session();
        let parent = row(&mut session, effect, 2);
        let task = match parent {
            RowKey::Value(row) => LiveConstraintTask::Value(CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(row), upper: ValueEndpointKey::ValueRow(row),
            }),
            RowKey::Effect(row) => LiveConstraintTask::Effect(
                EffectEndpointKey::EffectRow(row), EffectEndpointKey::EffectRow(row)),
        };
        let pair = candidate_context::task_pair(task);
        let relation = session.candidate_context_admit(task).unwrap().unwrap();
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
        let (occurrence, cause) = cause(&session);
        session.constrain_live_item(TypedWorkItem { task, relation: Some(relation), replay_ack: None }, &occurrence, &cause).unwrap();
        let before = session.candidate_graph.as_ref().unwrap().intrusion.completed.clone();
        let result: Result<(), SolveAvailabilityError> = session.with_route_transaction(|session| {
            let copy = extrude(session, parent, Polarity::Positive);
            close_cycle(session, parent, copy, Polarity::Positive);
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
            assert!(!session.pair_is_current(pair), "SCC representative changes invalidate completion");
            session.mark_candidate_pair(pair)?;
            assert!(session.pair_is_current(pair));
            Err(SolveAvailabilityError::IdentityExhausted)
        });
        assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
        let state = &session.candidate_graph.as_ref().unwrap().intrusion;
        assert_eq!(state.generation, 0);
        assert_eq!(state.completed, before, "rollback restores old entries and removes new ones");
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
        assert!(session.pair_is_current(pair));
        let copy = extrude(&mut session, parent, Polarity::Positive);
        close_cycle(&mut session, parent, copy, Polarity::Positive);
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
        assert!(!session.pair_is_current(pair));
        session.mark_candidate_pair(pair).unwrap();
        assert!(session.pair_is_current(pair));
    }
}

#[test]
fn raw_alias_diagnostic_admission_cannot_complete_invalidated_canonical_relation() {
    let mut session = session();
    let parent = row(&mut session, false, 2);
    let RowKey::Value(parent_row) = parent else { unreachable!() };
    let canonical = CanonicalValuePairKey {
        lower: ValueEndpointKey::ValueRow(parent_row), upper: ValueEndpointKey::TopNegative,
    };
    let (occurrence, cause) = cause(&session);
    session.constrain_live_value(canonical, &occurrence, &cause).unwrap();
    let relation = session.candidate_context_admit(LiveConstraintTask::Value(canonical)).unwrap().unwrap();
    let copy = extrude(&mut session, parent, Polarity::Positive);
    close_cycle(&mut session, parent, copy, Polarity::Positive);
    let RowKey::Value(copy_row) = copy else { unreachable!() };
    let raw = CanonicalValuePairKey {
        lower: ValueEndpointKey::ValueRow(copy_row), upper: ValueEndpointKey::TopNegative,
    };
    let intrusion = &session.candidate_graph.as_ref().unwrap().intrusion;
    assert!(session.typed_pairs.contains_key(&TypedPairKey::Value(canonical)));
    assert_ne!(intrusion.completed.get(&relation), Some(&intrusion.generation));
    let before = intrusion.completed.clone();
    let run = |session: &mut InferenceSession| {
        let admissions = session.execution_counters.constraint_pair_admissions;
        session.constrain_live_value(raw, &occurrence, &cause)?;
        assert_eq!(session.execution_counters.constraint_pair_admissions - admissions, 2,
            "raw diagnostic admission must leave canonical semantic replay pending");
        let intrusion = &session.candidate_graph.as_ref().unwrap().intrusion;
        assert_eq!(intrusion.completed.get(&relation), Some(&intrusion.generation));
        assert!(session.typed_pairs.contains_key(&TypedPairKey::Value(raw)));
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| {
        run(session)?;
        Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
    }), Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.completed, before);
    assert!(!session.typed_pairs.contains_key(&TypedPairKey::Value(raw)));
    run(&mut session).unwrap();
}

#[test]
fn source_less_type_cycle_does_not_qualify_intrusion() {
    for effect in [false, true] {
        for polarity in [Polarity::Positive, Polarity::Negative] {
            let mut session = session();
            let parent = row(&mut session, effect, 2);
            let copy = session.candidate_extrude(row_endpoint(parent), polarity, 0).unwrap();
            let (occurrence, cause) = cause(&session);
            session.candidate_restore_bound(copy, polarity, row_endpoint(parent), &occurrence, &cause).unwrap();
            session.settle_candidate_intrusion(None).unwrap();
            assert_ne!(session.canonical_extrusion(copy), session.canonical_extrusion(row_endpoint(parent)));
            assert!(session.candidate_graph.as_ref().unwrap().intrusion.parents.iter().all(|parent| parent.sources.is_none()));
        }
    }
}

#[test]
fn nested_definition_source_owns_real_call_demand_extrusion() {
    let module = hir("my loop x = { my helper y = loop y; helper x }");
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(module, true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    let references = session.batch.candidate_source.references.clone();
    assert_eq!(references.events.len(), 2);
    let a = references.events[0]; let b = references.events[1];
    assert_ne!(a.origin, b.origin, "nested initializer has its own source Value root");
    assert_eq!(a.origin, b.receiver);
    assert_eq!(b.origin, a.receiver);
    assert!(references.qualifies(0) && references.qualifies(1));
    let solved = session.run_candidate().unwrap();
    assert!(solved.data.errors.is_empty());
    let state = &solved.data.candidate_graph.as_ref().unwrap().intrusion;
    assert!(!state.parents.is_empty(), "native call-demand propagation actually extrudes younger coordinates");
    assert!(state.parents.iter().any(|parent| parent.sources.is_some_and(|sources|
        state.effect_algebra.context.source_events(sources).iter().any(|&event| references.qualifies(event)))));
    for parent in &state.parents {
        if parent.sources.is_some_and(|sources| state.effect_algebra.context.source_events(sources).iter().any(|&event| references.qualifies(event))) {
            assert_eq!(state.rep(parent.copy), state.rep(parent.parent));
        }
    }
}

#[test]
fn transparent_callee_keeps_original_resolved_source_binder() {
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir("my loop x = (loop) x"), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    let references = &session.batch.candidate_source.references;
    assert_eq!(references.events.len(), 1);
    assert_eq!(references.events[0].origin, references.events[0].receiver);
    assert!(references.qualifies(0));
    assert!(session.run_candidate().unwrap().data.errors.is_empty());
}

#[test]
fn queued_occurrences_keep_distinct_associations_for_the_same_native_pair() {
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir(
        "my loop x = loop x\nmy id x = x\nmy client x = id x"), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    assert_eq!(session.batch.hir.items().len(), 3);
    assert_eq!(session.batch.candidate_source.references.events.len(), 2);
    let mut occurrences: Vec<_> = session.batch.candidate_source.references.checking.iter()
        .map(|(checking, &event)| (checking.clone(), event)).collect();
    occurrences.sort_by_key(|(_, event)| *event);
    let (qualified, unqualified) = occurrences.iter().partition::<Vec<_>, _>(|(_, event)| session.batch.candidate_source.references.qualifies(*event));
    assert_eq!(qualified.len(), 1); assert_eq!(unqualified.len(), 1);
    let parent = row(&mut session, false, 2);
    let RowKey::Value(parent_row) = parent else { unreachable!() };
    let task = LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(parent_row), upper: ValueEndpointKey::TopNegative });
    let nonrecursive = session.candidate_context_seed(task, &unqualified[0].0, None).unwrap().unwrap();
    let recursive = session.candidate_context_seed(task, &qualified[0].0, None).unwrap().unwrap();
    assert_ne!(nonrecursive, recursive, "pair/context sharing must preserve separate source incidence");
    for relation in [nonrecursive, recursive] { session.enqueue_item(TypedWorkItem { task, relation: Some(relation), replay_ack: None }, false).unwrap(); }
    let mut copies = Vec::new();
    while let Some(item) = session.pop_worklist().unwrap() {
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = item.relation;
        copies.push(session.candidate_extrude(row_endpoint(parent), Polarity::Positive, 0).unwrap());
    }
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = None;
    session.settle_candidate_intrusion(None).unwrap();
    assert_ne!(session.canonical_extrusion(copies[0]), row_endpoint(parent));
    assert_eq!(session.canonical_extrusion(copies[1]), row_endpoint(parent));
}

#[test]
fn shared_transformed_comparison_retains_later_authentic_source_cause() {
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir(
        "my loop x = loop x\nmy id x = x\nmy client x = id x"), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    assert_eq!(session.batch.hir.items().len(), 3);
    assert_eq!(session.batch.candidate_source.references.events.len(), 2);
    let events: Vec<_> = session.batch.candidate_source.references.checking.iter().map(|(checking, &event)|
        (checking.clone(), session.batch.candidate_source.references.qualifies(event))).collect();
    let nonrecursive = events.iter().find(|(_, yes)| !*yes).unwrap().0.clone();
    let recursive = events.iter().find(|(_, yes)| *yes).unwrap().0.clone();
    let parent = row(&mut session, false, 2);
    let RowKey::Value(parent_row) = parent else { unreachable!() };
    let task = LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(parent_row), upper: ValueEndpointKey::TopNegative });
    let pair = candidate_context::task_pair(task);
    let first = session.candidate_context_seed(task, &nonrecursive, None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(first);
    session.candidate_processing(Some(pair));
    let copy = session.candidate_extrude(row_endpoint(parent), Polarity::Positive, 0).unwrap();
    session.settle_candidate_intrusion(None).unwrap();
    assert_ne!(session.canonical_extrusion(copy), row_endpoint(parent));
    let rows = session.bounds.len();
    let original_occurrence = session.candidate_graph.as_ref().unwrap().intrusion.parents[0].occurrence;
    let second = session.candidate_context_seed(task, &recursive, None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(second);
    let ExtrusionEndpoint::Value(copy_row) = copy else { unreachable!() };
    session.recapture_candidate_extrusion(pair, CanonicalValuePairKey { lower: copy_row, upper: ValueEndpointKey::TopNegative }).unwrap();
    session.settle_candidate_intrusion(None).unwrap();
    assert_eq!(session.bounds.len(), rows, "authentic memo reuse retains the existing transformed graph");
    assert_eq!(session.canonical_extrusion(copy), row_endpoint(parent));
    let state = &session.candidate_graph.as_ref().unwrap().intrusion;
    assert!(state.parents.iter().all(|parent| parent.occurrence == original_occurrence));
    assert_eq!(state.reuses.len(), 1);
    assert_ne!(state.reuses[0].occurrence, original_occurrence);
    assert_ne!(state.parents[0].sources, Some(state.reuses[0].sources));
    assert!(state.parents[0].sources.is_some_and(|sources| state.effect_algebra.context.source_events(sources).iter()
        .all(|&event| !session.batch.candidate_source.references.qualifies(event))));
}

#[test]
fn nested_apply_fragments_have_bounded_linear_storage() {
    let mut previous = None;
    for depth in [8, 16, 32, 64] {
        let text = format!("my loop x = loop{}", "(0)".repeat(depth));
        let batch = ConstraintBatch::collect_candidate_mode(hir(&text), true, true).unwrap();
        let graph = &batch.candidate_source.references;
        assert_eq!(graph.events.len(), depth);
        assert_eq!(graph.checking.len(), depth);
        // Exactly the first callee resolves to the recursive binder. Later
        // receivers are distinct Apply Values; containment adds no reverse edge.
        assert_eq!(graph.events.iter().filter(|event| event.origin == event.receiver).count(), 1);
        assert_eq!((0..depth).filter(|&event| graph.qualifies(event)).count(), 1);
        if let Some(bytes) = previous { assert!(graph.bytes() <= bytes * 3, "doubling source depth stays linear"); }
        previous = Some(graph.bytes());
    }
}

fn reuse_group_fixture(pairs: usize, events: usize, original_qualified: bool)
    -> (InferenceSession, TypedPairKey, CanonicalValuePairKey, Vec<ConstraintOccurrenceId>)
{
    let mut text = String::from("my id x = x\nmy client x = id x");
    for event in 0..events { text.push_str(&format!("\nmy loop{event} x = loop{event} x")); }
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir(&text), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    let references = &session.batch.candidate_source.references;
    let nonrecursive = references.checking.iter().find(|(_, event)| !references.qualifies(**event)).unwrap().0.clone();
    let mut qualified: Vec<_> = references.checking.iter().filter(|(_, event)| references.qualifies(**event))
        .map(|(checking, &event)| (event, checking.clone())).collect();
    qualified.sort_by_key(|(event, _)| *event);
    let qualified: Vec<_> = qualified.into_iter().map(|(_, checking)| checking).collect();
    let first = row(&mut session, false, 2);
    let RowKey::Value(first_row) = first else { unreachable!() };
    let task = LiveConstraintTask::Value(CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(first_row), upper: ValueEndpointKey::TopNegative });
    let pair = candidate_context::task_pair(task);
    let checking = if original_qualified { &qualified[0] } else { &nonrecursive };
    let relation = session.candidate_context_seed(task, checking, None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
    session.candidate_processing(Some(pair));
    let occurrence = session.begin_candidate_extrusion().unwrap();
    let mut output = None;
    for index in 0..pairs {
        let parent = if index == 0 { first } else { row(&mut session, index % 2 == 1, 2) };
        let copy = row(&mut session, index % 2 == 1, 0);
        session.retain_extrusion_parent(row_endpoint(copy), row_endpoint(parent),
            if index % 2 == 0 { Polarity::Positive } else { Polarity::Negative }, 0, occurrence).unwrap();
        if index == 0 { output = Some(row_endpoint(copy)); }
    }
    let output = output.unwrap();
    session.finish_candidate_extrusion(occurrence, 0, output).unwrap();
    let ExtrusionEndpoint::Value(output) = output else { unreachable!() };
    (session, pair, CanonicalValuePairKey { lower: output, upper: ValueEndpointKey::TopNegative }, qualified)
}

#[test]
fn qualified_reuses_enqueue_each_original_pair_only_once() {
    const T: usize = 12;
    const K: usize = 8;
    for original_qualified in [false, true] {
        let (mut session, pair, output, qualified) = reuse_group_fixture(T, K, original_qualified);
        for checking in &qualified {
            let relation = session.candidate_context_seed(LiveConstraintTask::Value(match pair { TypedPairKey::Value(pair) => pair, _ => unreachable!() }), checking, None).unwrap().unwrap();
            session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
            session.recapture_candidate_extrusion(pair, output).unwrap();
            session.settle_candidate_intrusion(None).unwrap();
            let state = &session.candidate_graph.as_ref().unwrap().intrusion;
            assert_eq!(state.pending.len(), T);
            assert_eq!(state.pending_cursor, T);
            assert_eq!(state.generation, T as u64);
            assert!(state.parents.iter().all(|parent| state.rep(parent.copy) == state.rep(parent.parent)));
        }
        let state = &session.candidate_graph.as_ref().unwrap().intrusion;
        assert_eq!(state.reuses.len(), K - usize::from(original_qualified));
        let mut occurrences: Vec<_> = state.reuses.iter().map(|reuse| reuse.occurrence).collect();
        occurrences.sort_unstable(); occurrences.dedup();
        assert_eq!(occurrences.len(), state.reuses.len());
    }
}

#[test]
fn rollback_restores_preexisting_group_activation_and_pending_cursor_for_retry() {
    let (mut session, pair, output, qualified) = reuse_group_fixture(4, 2, false);
    let task = LiveConstraintTask::Value(match pair { TypedPairKey::Value(pair) => pair, _ => unreachable!() });
    let relation = session.candidate_context_seed(task, &qualified[0], None).unwrap().unwrap();
    let activate = |session: &mut InferenceSession| {
        session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(relation);
        session.recapture_candidate_extrusion(pair, output)?;
        session.settle_candidate_intrusion(None)?;
        let state = &session.candidate_graph.as_ref().unwrap().intrusion;
        assert!(state.groups[0].activated);
        assert_eq!(state.pending_cursor, 4);
        assert!(state.parents.iter().all(|parent| state.rep(parent.copy) == state.rep(parent.parent)));
        Ok::<_, SolveAvailabilityError>(())
    };
    assert_eq!(session.with_route_transaction(|session| { activate(session)?; Err::<(), _>(SolveAvailabilityError::IdentityExhausted) }),
        Err(SolveAvailabilityError::IdentityExhausted));
    let state = &session.candidate_graph.as_ref().unwrap().intrusion;
    assert!(!state.groups[0].activated);
    assert!(state.pending.is_empty());
    assert_eq!(state.pending_cursor, 0);
    assert!(state.activations.is_empty());
    assert!(state.reuses.is_empty());
    assert_eq!(state.generation, 0);
    assert!(state.parents.iter().all(|parent| state.rep(parent.copy) != state.rep(parent.parent)));
    session.with_route_transaction(activate).unwrap();
}

#[test]
fn repeated_source_argument_keeps_original_bound_relations_with_ordinary_diagnostics() {
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir(
        "my apply (f: 'a -> int) (x: int) = { my first = f x; f x }"), true, true).unwrap()).unwrap();
    session.start_candidate_graph().unwrap();
    session.execute().unwrap();
    assert!(session.errors.is_empty());
    let context = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
    let mut witnessed = false;
    for (&memo_key, memo) in &session.typed_pairs {
        let TypedPairKey::Value(pair) = memo_key else { continue; };
        let (ValueEndpointKey::ValueRow(lower), ValueEndpointKey::ValueRow(upper)) = (pair.lower, pair.upper) else { continue; };
        let TypedPairMemo::Value { children, .. } = memo else { continue; };
        if !children.iter().any(|edge| edge.child.lower == ValueEndpointKey::IntPositive && edge.child.upper == pair.upper) { continue; }
        let mut arguments: Vec<_> = context.observed_dependencies().filter_map(|dependency| match dependency {
            candidate_context::Dependency::FunctionPort { child, field: FunctionField::Argument, .. }
                if context.observed_pair(*child).unwrap() == memo_key => Some(*child),
            _ => None,
        }).collect();
        arguments.sort_by_key(|relation| relation.0);
        arguments.dedup();
        if arguments.len() < 2 { continue; }
        assert_eq!(session.value_levels[lower as usize], session.value_levels[upper as usize]);
        let bound = crate::candidate_effect::BoundKey(
            ExtrusionEndpoint::Value(pair.lower), Polarity::Negative, ExtrusionEndpoint::Value(pair.upper));
        for relation in &arguments {
            assert!(context.bound_relations(bound).any(|attached| attached == *relation),
                "each authentic call's original argument relation owns its bound association");
        }
        witnessed = true;
    }
    assert!(witnessed, "two authentic calls revisit a row pair with an ordinary Int replay child and no extrusion replacement");
}

#[test]
fn retained_whole_value_extrusion_reuses_exactly_one_child_and_survives_memo_lifecycle() {
    let fixture = || {
        let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir(
            "my loop x = loop x\nmy id x = x\nmy client x = id x"), true, true).unwrap()).unwrap();
        session.start_candidate_graph().unwrap();
        let references = &session.batch.candidate_source.references;
        let nonrecursive = references.checking.iter().find(|(_, event)| !references.qualifies(**event)).unwrap().0.clone();
        let recursive = references.checking.iter().find(|(_, event)| references.qualifies(**event)).unwrap().0.clone();
        let checking = [nonrecursive, recursive];
        let owner = session.fresh_value_at_level(0).unwrap();
        let parent = session.fresh_value_at_level(2).unwrap();
        let argument = session.live_value_term(Polarity::Positive, parent).unwrap();
        let function = session.negative_function_term(argument,
            session.batch.collected_leaf_term(Leaf::EffectBottomPositive),
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session.batch.collected_leaf_term(Leaf::IntNegative)).unwrap();
        let pair = CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(owner), upper: session.value_endpoint(function, Polarity::Negative) };
        let key = TypedPairKey::Value(pair);
        let task = LiveConstraintTask::Value(pair);
        let first = session.candidate_context_seed(task, &checking[0], None).unwrap().unwrap();
        let item = TypedWorkItem { task, relation: Some(first), replay_ack: None };
        (session, pair, key, item, checking)
    };
    let (mut session, pair, key, item, checking) = fixture();
    let task = item.task;
    let first = item.relation.unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(first);
    session.candidate_processing(Some(key));
    // A failed route must remove a newly published replacement and its copy graph.
    let before_rows = session.bounds.len();
    let result = session.with_route_transaction(|session| {
        session.dispatch_live_item(item, None, false, &mut 0)?;
        assert!(matches!(session.typed_pairs.get(&key), Some(TypedPairMemo::Value { retained_extrusion_rewrite: Some(_), .. })));
        Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
    });
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert!(!session.typed_pairs.contains_key(&key));
    assert_eq!(session.bounds.len(), before_rows);
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(first);
    session.candidate_processing(Some(key));
    session.dispatch_live_item(item, None, false, &mut 0).unwrap();
    let rewritten = match session.typed_pairs[&key] {
        TypedPairMemo::Value { retained_extrusion_rewrite: Some(rewritten), .. } => rewritten,
        _ => panic!("the actual extrusion producer retains its final rewritten pair"),
    };
    assert_ne!(rewritten, pair);
    assert_eq!(session.pop_worklist().unwrap().unwrap().task, LiveConstraintTask::Value(rewritten));
    assert!(session.pop_worklist().unwrap().is_none());
    // An additional diagnostic consequence cannot become another replacement.
    let ordinary = CanonicalValuePairKey { lower: ValueEndpointKey::IntPositive, upper: pair.upper };
    session.record_diagnostic_edge(pair, ordinary, None).unwrap();
    let rows = session.bounds.len();
    let parents = session.candidate_graph.as_ref().unwrap().intrusion.parents.len();
    assert!(parents > 0);
    let second = session.candidate_context_seed(task, &checking[1], None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(second);
    session.dispatch_live_item(TypedWorkItem { relation: Some(second), ..item }, None, false, &mut 0).unwrap();
    assert_eq!(session.pop_worklist().unwrap().unwrap().task, LiveConstraintTask::Value(rewritten));
    assert!(session.pop_worklist().unwrap().is_none(), "mixed diagnostics do not enqueue more rewrite children");
    assert_eq!(session.bounds.len(), rows, "reuse allocates no new copied rows");
    assert_eq!(session.candidate_graph.as_ref().unwrap().intrusion.parents.len(), parents);
    session.settle_candidate_intrusion(None).unwrap();
    assert!(session.candidate_graph.as_ref().unwrap().intrusion.generation > 0);
    assert!(matches!(session.typed_pairs[&key], TypedPairMemo::Value { retained_extrusion_rewrite: Some(retained), .. } if retained == rewritten),
        "intrusion invalidation retains the original copied graph replacement");
    assert_eq!(session.retain_candidate_value_rewrite(pair, ordinary), Err(SolveAvailabilityError::IdentityExhausted));
    // Selection inspection above deliberately owns popped work without draining
    // it. Exercise old-memo rollback in a separate, fully drained solver route.
    let (mut session, pair, key, item, checking) = fixture();
    let task = item.task;
    let occurrence = checking[0].clone();
    let cause = CauseId::for_occurrence(occurrence.clone());
    session.constrain_live_item(item, &occurrence, &cause).unwrap();
    let rewritten = match session.typed_pairs[&key] {
        TypedPairMemo::Value { retained_extrusion_rewrite: Some(rewritten), .. } => rewritten,
        _ => panic!("the completed producer retains its actual extrusion replacement"),
    };
    let second = session.candidate_context_seed(task, &checking[1], None).unwrap().unwrap();
    let occurrence = checking[1].clone();
    let cause = CauseId::for_occurrence(occurrence.clone());
    session.constrain_live_item(TypedWorkItem { relation: Some(second), ..item }, &occurrence, &cause).unwrap();
    assert!(session.typed_worklist.is_empty());
    assert!(session.diagnostic_delta.is_empty());
    let memo = session.typed_pairs[&key].clone();
    let result = session.with_route_transaction(|session| {
        session.candidate_reopen_root(pair)?;
        session.record_typed_pair_admission(key, TypedPairMemo::Value {
            children: DiagnosticChildren::new(), direct_witness: None,
            completion: DiagnosticCompletion::Pending, retained_extrusion_rewrite: None,
        })?;
        assert!(matches!(session.typed_pairs[&key], TypedPairMemo::Value { retained_extrusion_rewrite: Some(retained), .. } if retained == rewritten));
        Err::<(), _>(SolveAvailabilityError::IdentityExhausted)
    });
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.typed_pairs[&key], memo, "journal reconstruction preserves the retained rewrite and diagnostic edges");
}
