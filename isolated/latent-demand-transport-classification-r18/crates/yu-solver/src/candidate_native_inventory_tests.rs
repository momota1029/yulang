//! Read-only native inventory adapter and adversarial correspondence checks.
//! Physical/provenance readback is not a semantic solution or native-Ok theorem.
use super::*;
use crate::candidate_scheme::RowKey;

#[derive(Clone, Debug, Eq, PartialEq)]
struct PhysicalEntry {
    slot: PhysicalBoundSlot,
    raw: BoundKey,
    canonical: BoundKey,
    comparison: TypedPairKey,
    emissions: Vec<BoundEmissionId>,
}

/// Borrow actual producer slices, including missing relations and coverage gaps.
#[allow(dead_code, reason = "complete evidence surface exceeds the discriminating fixture")]
struct Provenance<'a> {
    admissions: &'a [BoundAdmission],
    emissions: &'a [BoundEmission],
    snapshots: &'a [EvidenceSnapshot],
    transforms: &'a [FiberTransform],
    recipes: &'a [ReplayRecipe],
    reverse: &'a [EvidenceReverseEdge],
    relations: &'a [Relation],
    origins: &'a [Origin],
    source_completions: &'a [SourceDrainReceipt],
    contexts: &'a [ContextExpr],
    bound_fibers: &'a [(BoundKey, RelationId, Option<usize>)],
    replays: Vec<(ReplayOperationId, &'a ReplayOperation)>,
    restorations: Vec<(ReplayOperationId, &'a BoundRestoration)>,
}

#[allow(dead_code, reason = "retain row metadata even when the fixture does not consume it")]
#[derive(Debug)]
struct RowEntry {
    raw: RowKey,
    representative: RowKey,
    level: u32,
    non_generic: bool,
}

#[allow(dead_code, reason = "export all original and reuse identities without qualification filtering")]
struct Inventory<'a> {
    physical: Vec<PhysicalEntry>,
    rows: Vec<RowEntry>,
    terms: Vec<(Term, Option<TermView<'a>>)>,
    dependencies: Vec<Dependency>,
    provenance: Provenance<'a>,
    parents: &'a [candidate_intrusion::Parent],
    groups: Vec<(usize, usize, usize, usize, bool)>,
    reuses: Vec<(usize, usize, usize, usize)>,
    source_sets: &'a [Vec<usize>],
    qualified_events: Vec<bool>,
    pending: (usize, usize),
    generation: u64,
    effect_views: &'a [candidate_effect::View],
    effect_contributions: &'a [candidate_effect::Contribution],
    effect_capture: &'a [candidate_effect::CaptureIncidence],
    source_graph: &'a candidate_value_graph::Graph,
    module_uses: &'a [candidate_scheme::FreshRoute],
    local_uses: &'a [candidate_scheme::LocalFreshRoute],
    operator_uses: &'a [candidate_scheme::OperatorFreshUse],
    member_uses: &'a [candidate_scheme::MemberFreshUse],
}

fn context(session: &InferenceSession) -> &State {
    &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context
}
fn row_endpoint(key: RowKey) -> ExtrusionEndpoint {
    match key {
        RowKey::Value(row) => ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(row)),
        RowKey::Effect(row) => ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
    }
}
fn comparison(BoundKey(owner, side, item): BoundKey) -> TypedPairKey {
    let (lower, upper) = if side == Polarity::Positive { (item, owner) } else { (owner, item) };
    match (lower, upper) {
        (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) =>
            TypedPairKey::Value(CanonicalValuePairKey { lower, upper }),
        (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) =>
            TypedPairKey::Effect { lower, upper },
        _ => unreachable!("physical vectors are kind separated"),
    }
}

/// Independent addressed lookup: do not canonicalize physical storage.
fn physical_read(session: &InferenceSession, slot: PhysicalBoundSlot) -> Option<BoundKey> {
    use BoundLane::*;
    let (side, item) = match (slot.owner, slot.lane) {
        (RowKey::Value(row), ValueLowerRow) => (Polarity::Positive,
            ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(*session.bounds.get(row as usize)?.direct_lower_rows.get(slot.index)?))),
        (RowKey::Value(row), ValueUpperRow) => (Polarity::Negative,
            ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(*session.bounds.get(row as usize)?.direct_upper_rows.get(slot.index)?))),
        (RowKey::Value(row), ValueLowerAtom) => (Polarity::Positive,
            ExtrusionEndpoint::Value(*session.bounds.get(row as usize)?.exact_non_variable_lowers.get(slot.index)?)),
        (RowKey::Value(row), ValueUpperAtom) => (Polarity::Negative,
            ExtrusionEndpoint::Value(*session.bounds.get(row as usize)?.exact_non_variable_uppers.get(slot.index)?)),
        (RowKey::Effect(row), EffectLowerRow) => (Polarity::Positive,
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(*session.effect_bounds.get(row as usize)?.direct_lower_rows.get(slot.index)?))),
        (RowKey::Effect(row), EffectUpperRow) => (Polarity::Negative,
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(*session.effect_bounds.get(row as usize)?.direct_upper_rows.get(slot.index)?))),
        (RowKey::Effect(row), EffectLowerAtom) => (Polarity::Positive,
            ExtrusionEndpoint::Effect(*session.effect_bounds.get(row as usize)?.exact_non_variable_lowers.get(slot.index)?)),
        (RowKey::Effect(row), EffectUpperAtom) => (Polarity::Negative,
            ExtrusionEndpoint::Effect(*session.effect_bounds.get(row as usize)?.exact_non_variable_uppers.get(slot.index)?)),
        _ => return None,
    };
    Some(BoundKey(row_endpoint(slot.owner), side, item))
}

fn endpoint_term(endpoint: ExtrusionEndpoint) -> Option<Term> {
    match endpoint {
        ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(t) | ValueEndpointKey::NegativeFunction(t)
            | ValueEndpointKey::PositiveTuple(t, _) | ValueEndpointKey::NegativeTuple(t, _)
            | ValueEndpointKey::PositiveRecord(t) | ValueEndpointKey::NegativeRecord(t)
            | ValueEndpointKey::PositiveVariant(t) | ValueEndpointKey::NegativeVariant(t)) => Some(t),
        _ => None,
    }
}

fn inventory(session: &InferenceSession) -> Inventory<'_> {
    use BoundLane::*;
    let state = context(session);
    let intrusion = &session.candidate_graph.as_ref().unwrap().intrusion;
    let mut emissions = HashMap::<PhysicalBoundSlot, Vec<BoundEmissionId>>::new();
    for (id, emission) in state.evidence.emissions.iter().enumerate() {
        emissions.entry(emission.physical).or_default().push(BoundEmissionId(id));
    }
    let mut physical = Vec::new();
    let mut rows = Vec::new();
    let mut append = |owner, lane, side, items: Vec<ExtrusionEndpoint>| {
        for (index, item) in items.into_iter().enumerate() {
            let slot = PhysicalBoundSlot { owner, lane, index };
            let raw = BoundKey(row_endpoint(owner), side, item);
            let canonical = BoundKey(session.canonical_extrusion(raw.0), side, session.canonical_extrusion(item));
            physical.push(PhysicalEntry { slot, raw, canonical, comparison: comparison(canonical),
                emissions: emissions.remove(&slot).unwrap_or_default() });
        }
    };
    for (index, row) in session.bounds.iter().enumerate() {
        let owner = RowKey::Value(u32::try_from(index).unwrap());
        rows.push(RowEntry { raw: owner, representative: intrusion.rep(owner),
            level: session.value_levels[index], non_generic: session.value_metadata[index].non_generic });
        append(owner, ValueLowerRow, Polarity::Positive, row.direct_lower_rows.iter().map(|&r| row_endpoint(RowKey::Value(r))).collect());
        append(owner, ValueUpperRow, Polarity::Negative, row.direct_upper_rows.iter().map(|&r| row_endpoint(RowKey::Value(r))).collect());
        append(owner, ValueLowerAtom, Polarity::Positive, row.exact_non_variable_lowers.iter().copied().map(ExtrusionEndpoint::Value).collect());
        append(owner, ValueUpperAtom, Polarity::Negative, row.exact_non_variable_uppers.iter().copied().map(ExtrusionEndpoint::Value).collect());
    }
    for (index, row) in session.effect_bounds.iter().enumerate() {
        let owner = RowKey::Effect(u32::try_from(index).unwrap());
        rows.push(RowEntry { raw: owner, representative: intrusion.rep(owner),
            level: session.effect_levels[index], non_generic: session.effect_metadata[index].non_generic });
        append(owner, EffectLowerRow, Polarity::Positive, row.direct_lower_rows.iter().map(|&r| row_endpoint(RowKey::Effect(r))).collect());
        append(owner, EffectUpperRow, Polarity::Negative, row.direct_upper_rows.iter().map(|&r| row_endpoint(RowKey::Effect(r))).collect());
        append(owner, EffectLowerAtom, Polarity::Positive, row.exact_non_variable_lowers.iter().copied().map(ExtrusionEndpoint::Effect).collect());
        append(owner, EffectUpperAtom, Polarity::Negative, row.exact_non_variable_uppers.iter().copied().map(ExtrusionEndpoint::Effect).collect());
    }
    let mut work: Vec<_> = physical.iter().flat_map(|entry| [entry.raw.0, entry.raw.2]).filter_map(endpoint_term).collect();
    for relation in &state.relations {
        if let TypedPairKey::Value(pair) = relation.key.pair {
            work.extend([pair.lower, pair.upper].into_iter().filter_map(|endpoint|
                endpoint_term(ExtrusionEndpoint::Value(endpoint))));
        }
    }
    let mut seen = HashSet::new();
    let mut terms = Vec::new();
    while let Some(term) = work.pop() {
        if !seen.insert(term) { continue; }
        let view = session.store.term_view(term).ok();
        match &view {
            Some(TermView::PositiveFunction { argument, argument_effect, result_effect, result }
                | TermView::NegativeFunction { argument, argument_effect, result_effect, result }) =>
                work.extend([*argument, *argument_effect, *result_effect, *result]),
            Some(TermView::PositiveTuple { elements } | TermView::NegativeTuple { elements }) => work.extend(elements.iter().copied()),
            Some(TermView::PositiveRecord { fields } | TermView::NegativeRecord { fields }) => work.extend(fields.iter().map(|field| field.value)),
            Some(TermView::PositiveVariant { alternatives } | TermView::NegativeVariant { alternatives }) =>
                work.extend(alternatives.iter().flat_map(|alternative| alternative.payloads.iter().copied())),
            _ => {},
        }
        terms.push((term, view));
    }
    let mut replays: Vec<_> = state.replay_operations.iter().map(|(&id, value)| (id, value)).collect();
    replays.sort_by_key(|(id, _)| id.0);
    let mut restorations: Vec<_> = state.restorations.iter().map(|(&id, value)| (id, value)).collect();
    restorations.sort_by_key(|(id, _)| id.0);
    Inventory { physical, rows, terms, dependencies: state.dependencies.clone(),
        provenance: Provenance { admissions: &state.evidence.admissions, emissions: &state.evidence.emissions,
            snapshots: &state.evidence.snapshots, transforms: &state.evidence.transforms,
            recipes: &state.evidence.recipes, reverse: &state.evidence.reverse,
            relations: &state.relations, origins: &state.origins,
            source_completions: &state.source_drain_completions, contexts: &state.contexts,
            bound_fibers: &state.bound_keys, replays, restorations },
        parents: &intrusion.parents, groups: intrusion.observed_groups().collect(), reuses: intrusion.observed_reuses().collect(),
        source_sets: &state.source_sets,
        qualified_events: (0..session.batch.candidate_source.references.events.len())
            .map(|event| session.batch.candidate_source.references.qualifies(event)).collect(),
        pending: intrusion.observed_pending(), generation: intrusion.generation,
        effect_views: &intrusion.effect_algebra.views, effect_contributions: &intrusion.effect_algebra.contributions,
        effect_capture: &intrusion.effect_algebra.capture_records,
        source_graph: &session.batch.candidate_source.references,
        module_uses: &session.candidate_graph.as_ref().unwrap().routes,
        local_uses: &session.candidate_graph.as_ref().unwrap().local_routes,
        operator_uses: &session.candidate_graph.as_ref().unwrap().operator_uses,
        member_uses: &session.candidate_graph.as_ref().unwrap().member_uses }
}

fn validate(session: &InferenceSession, extracted: &Inventory<'_>) -> Result<(), &'static str> {
    let count = session.bounds.iter().map(|r| r.direct_lower_rows.len() + r.direct_upper_rows.len()
        + r.exact_non_variable_lowers.len() + r.exact_non_variable_uppers.len()).sum::<usize>()
        + session.effect_bounds.iter().map(|r| r.direct_lower_rows.len() + r.direct_upper_rows.len()
        + r.exact_non_variable_lowers.len() + r.exact_non_variable_uppers.len()).sum::<usize>();
    if extracted.physical.len() != count { return Err("missing physical slot"); }
    let mut seen = HashSet::new();
    for entry in &extracted.physical {
        if !seen.insert(entry.slot) { return Err("duplicate physical slot"); }
        if physical_read(session, entry.slot) != Some(entry.raw) { return Err("wrong physical readback"); }
        let canonical = BoundKey(session.canonical_extrusion(entry.raw.0), entry.raw.1, session.canonical_extrusion(entry.raw.2));
        if entry.canonical != canonical || entry.comparison != comparison(canonical) { return Err("wrong oriented canonical comparison"); }
        let expected: Vec<_> = context(session).evidence.emissions.iter().enumerate()
            .filter(|(_, emission)| emission.physical == entry.slot).map(|(id, _)| BoundEmissionId(id)).collect();
        if entry.emissions != expected { return Err("missing emission identity"); }
        for &id in &entry.emissions {
            let emission = &context(session).evidence.emissions[id.0];
            if emission.readback.slot != entry.slot || emission.readback.bound != entry.raw
                || emission.bound != entry.raw || emission.readback.phase != PhysicalReadbackPhase::ConstructorAfterAppend
                || context(session).evidence.admissions.get(emission.admission.0).is_none() {
                return Err("emission is not constructor readback");
            }
        }
    }
    for (term, view) in &extracted.terms {
        if &session.store.term_view(*term).ok() != view { return Err("changed structural port"); }
    }
    // Compare with the real consumer API, preserving its direct-before-exact
    // order and its opposite-side convention, including redirected owners.
    for row in &extracted.rows {
        for polarity in [Polarity::Positive, Polarity::Negative] {
            let opposite = if polarity == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
            let expected: Vec<_> = extracted.physical.iter()
                .filter(|entry| entry.slot.owner == row.representative && entry.raw.1 == opposite)
                .map(|entry| entry.canonical.2).collect();
            let owner = row_endpoint(row.raw);
            if session.candidate_opposite_count(owner, polarity).ok() != Some(expected.len()) {
                return Err("opposite count mismatch");
            }
            for (index, expected) in expected.iter().enumerate() {
                if session.candidate_opposite_bound(owner, polarity, index) != *expected {
                    return Err("opposite order mismatch");
                }
            }
        }
    }
    if extracted.dependencies != context(session).dependencies { return Err("missing retained dependency"); }
    Ok(())
}

fn session() -> InferenceSession {
    let source: Arc<yu_syntax::SourceText> = Arc::from("my seed x = seed x");
    let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
        Arc::new(yu_syntax::SyntaxEnvironment::empty()));
    let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
        yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("native-inventory", "source.yu"))),
        &parsed, yu_hir::SemanticImports::empty()).unwrap());
    InferenceSession::try_new_candidate(ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap()).unwrap()
}

#[test]
fn physical_inventory_preserves_lanes_ports_replays_and_aliases() {
    let mut session = session();
    let v = session.fresh_value_at_level(2).unwrap();
    let w = session.fresh_value_at_level(2).unwrap();
    let e = session.fresh_effect_at_level(2).unwrap();
    let f = session.fresh_effect_at_level(2).unwrap();
    let a = session.fresh_value_at_level(2).unwrap();
    let r = session.fresh_value_at_level(2).unwrap();
    let ae = session.fresh_effect_at_level(2).unwrap();
    let re = session.fresh_effect_at_level(2).unwrap();
    let a = session.live_value_term(Polarity::Negative, a).unwrap();
    let r = session.live_value_term(Polarity::Positive, r).unwrap();
    let ae = session.live_effect_term(Polarity::Negative, ae).unwrap();
    let re = session.live_effect_term(Polarity::Positive, re).unwrap();
    let function = session.positive_function_term(a, ae, re, r).unwrap();
    let owner = row_endpoint(RowKey::Value(v));
    let effect_owner = row_endpoint(RowKey::Effect(e));
    let fun = ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(function));
    let top = ExtrusionEndpoint::Value(ValueEndpointKey::TopNegative);
    for (owner, side, item) in [
        (owner, Polarity::Positive, row_endpoint(RowKey::Value(w))),
        (owner, Polarity::Negative, row_endpoint(RowKey::Value(w))),
        (owner, Polarity::Positive, fun), (owner, Polarity::Negative, top),
        (effect_owner, Polarity::Positive, row_endpoint(RowKey::Effect(f))),
        (effect_owner, Polarity::Negative, row_endpoint(RowKey::Effect(f))),
        (effect_owner, Polarity::Positive, ExtrusionEndpoint::Effect(EffectEndpointKey::BottomPositive)),
        (effect_owner, Polarity::Negative, ExtrusionEndpoint::Effect(EffectEndpointKey::EmptyNegative)),
    ] {
        session.candidate_insert_bound_with_evidence(owner, side, item, false,
            BoundAdmissionCause::OwnerEmission { processing: None }).unwrap();
    }
    session.candidate_replay_bound(owner, Polarity::Positive, fun, None).unwrap();
    {
        let mut exported = inventory(&session);
        assert_eq!(validate(&session, &exported), Ok(()));
        assert_eq!(exported.physical.iter().map(|entry| entry.slot.lane).collect::<HashSet<_>>().len(), 8);
        assert!(!exported.provenance.replays.is_empty());
        let removed = exported.physical.pop().unwrap();
        assert_eq!(validate(&session, &exported), Err("missing physical slot"));
        exported.physical.push(removed);
        let shape = exported.terms.iter_mut().find(|(term, _)| *term == function).unwrap();
        let original = shape.1.clone();
        let Some(TermView::PositiveFunction { argument, argument_effect, result_effect, result }) = original.clone() else { panic!("function readback"); };
        assert_ne!(argument, result); assert_ne!(argument_effect, result_effect);
        shape.1 = Some(TermView::PositiveFunction { argument: result, argument_effect, result_effect, result: argument });
        assert_eq!(validate(&session, &exported), Err("changed structural port"));
        exported.terms.iter_mut().find(|(term, _)| *term == function).unwrap().1 = Some(
            TermView::PositiveFunction { argument, argument_effect: result_effect, result_effect: argument_effect, result });
        assert_eq!(validate(&session, &exported), Err("changed structural port"));
        exported.terms.iter_mut().find(|(term, _)| *term == function).unwrap().1 = original;
        let replay = exported.dependencies.iter().position(|edge| matches!(edge, Dependency::Replay { .. })).unwrap();
        exported.dependencies.remove(replay);
        assert_eq!(validate(&session, &exported), Err("missing retained dependency"));
    }
    // Actual extrusion/qualified merge creates aliases; the test does not write
    // a forest edge or manufacture a source qualification bit.
    let checking = session.batch.candidate_source.references.checking.keys().next().unwrap().clone();
    let task = LiveConstraintTask::Value(CanonicalValuePairKey {
        lower: ValueEndpointKey::ValueRow(v), upper: ValueEndpointKey::ValueRow(v) });
    let seed = session.candidate_context_seed(task, &checking, None).unwrap().unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = Some(seed);
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.processing = Some(task_pair(task));
    session.candidate_extrude(owner, Polarity::Positive, 0).unwrap();
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.processing = None;
    session.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.processing = None;
    session.settle_candidate_intrusion(None).unwrap();
    let exported = inventory(&session);
    assert_eq!(validate(&session, &exported), Ok(()));
    assert!(exported.physical.iter().any(|entry| entry.raw != entry.canonical));
    assert!(exported.rows.iter().any(|row| row.raw != row.representative));
    assert!(exported.dependencies.iter().any(|edge| matches!(edge, Dependency::Transport {
        witness: Some(TransportWitness { reason: TransportReason::ParentCopy { .. }, .. }), .. })));
    eprintln!("NATIVE-INVENTORY slots={} emissions={} terms={} dependencies={} parents={} groups={} reuses={} generation={}",
        exported.physical.len(), exported.provenance.emissions.len(), exported.terms.len(), exported.dependencies.len(),
        exported.parents.len(), exported.groups.len(), exported.reuses.len(), exported.generation);
}
