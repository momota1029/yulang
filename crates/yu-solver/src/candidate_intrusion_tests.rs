//! Actual candidate extrusion/intrusion evidence, separate from injective transport models.
use super::*;
use crate::candidate_scheme::RowKey;
use yu_hir::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};

fn hir(text: &str) -> Arc<HirModule> {
    let source: Arc<yu_syntax::SourceText> = Arc::from(text);
    let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    Arc::new(lower_module_with_local_source(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("intrusion", "source.yu"))),
        &parsed, yu_hir::SemanticImports::empty()).unwrap())
}
fn session() -> InferenceSession {
    let mut session = InferenceSession::try_new(ConstraintBatch::collect_candidate_mode(hir("my seed = 1"), true, true).unwrap()).unwrap();
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
    let copy = session.candidate_extrude(row_endpoint(parent), polarity, 0).unwrap();
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
fn close_cycle(session: &mut InferenceSession, parent: RowKey, copy: RowKey, polarity: Polarity) {
    let (occurrence, cause) = cause(session);
    let opposite = if polarity == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
    // Extrusion installed parent -> copy. This actual bound adds copy -> parent.
    session.candidate_restore_bound(row_endpoint(copy), opposite, row_endpoint(parent), &occurrence, &cause).unwrap();
    match copy {
        RowKey::Value(i) => { session.constrain_live_value(CanonicalValuePairKey {
            lower: ValueEndpointKey::ValueRow(i), upper: ValueEndpointKey::ValueRow(i),
        }, &occurrence, &cause).unwrap(); }
        RowKey::Effect(i) => { session.constrain_live_effect(EffectEndpointKey::EffectRow(i), EffectEndpointKey::EffectRow(i), &occurrence, &cause).unwrap(); }
    }
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
fn real_extrusion_without_reverse_dependency_keeps_parent_copy_distinct() {
    for effect in [false, true] {
        for polarity in [Polarity::Positive, Polarity::Negative] {
            let mut session = session();
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
    for text in ["my recur x = recur x", "my left x = right x; my right y = left y"] {
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
    let hir = hir("my succ x = 1; my apply g = { my relay x = g x; my before = relay 1; relay 1 }; my answer = apply succ");
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
