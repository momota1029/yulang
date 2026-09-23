use super::*;

#[test]
fn f5c_incoming_reported_errors_growth_samples_after_first_union_member_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-reported-errors-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Union(vec![
            F5cPositive::Int,
            F5cPositive::Function {
                argument: Box::new(F5cNegative::Top),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(F5cPositive::Quantified(0)),
            },
        ]),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let scheme = finalized.into_parts().0;
    let view = session
        .finalization
        .as_ref()
        .unwrap()
        .scheme_view(&scheme)
        .unwrap();
    let PositiveValueView::Union(children) = view.positive_value(view.predicate()).unwrap() else {
        panic!("finalized predicate must be a Union");
    };
    assert_eq!(children.len(), 2);
    assert_ne!(children[0], children[1]);
    assert!(matches!(
        view.positive_value(children[0]).unwrap(),
        PositiveValueView::Int
    ));
    assert!(matches!(
        view.positive_value(children[1]).unwrap(),
        PositiveValueView::Function { .. }
    ));
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(scheme);
    let use_row =
        session.live_components[session.batch.definition_uses()[0].use_value_component].ordinal;
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 204);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_value(
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(use_row),
                upper: ValueEndpointKey::IntNegative,
            },
            &occurrence,
            &cause,
        )
        .unwrap();
    assert!(session.errors.is_empty());
    session.errors.try_reserve(1).unwrap();
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .route_journal_spare
        .as_mut()
        .unwrap()
        .reported_error_keys
        .try_reserve(1)
        .unwrap();
    session.reported_errors = Default::default();
    assert_eq!(session.reported_errors.capacity(), 0);
    assert!(session.errors.capacity() > 0);
    assert!(
        session
            .route_journal_spare
            .as_ref()
            .unwrap()
            .reported_error_keys
            .capacity()
            > 0
    );
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let baseline_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let baseline_session = session.resource_ledger.inference_session_retained_bytes;
    let finish_output = session.resource_ledger.finish_output_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ReportedErrors);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    assert_eq!(
        F5C_ROUTE_MANY_PRIVATE_COMPLETIONS.with(|count| count.get()),
        1
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("reported-errors-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "ReportedErrors".into())),
        Some(&1)
    );
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "Errors".into())),
        None
    );
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    let (position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "typed-route" && event.lane == "ReportedErrors")
        .expect("ReportedErrors reserve must have a completed event-time sample");
    assert!(position > 0);
    let previous = &trace.completed_events[position - 1];
    assert!(previous.sample.semantic_retained_bytes > baseline_semantic);
    assert!(previous.sample.session_retained_bytes > baseline_session);
    assert!(
        trace.completed_events[..position]
            .iter()
            .any(|earlier| earlier.owner == "typed-route"
                && earlier.lane == "FreshValueBounds"
                && earlier.old_capacity < earlier.new_capacity)
    );
    assert_eq!(event.old_capacity, 0);
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<(ConstraintOccurrenceId, SolverErrorKind)>())
        .unwrap();
    assert!(delta > 0);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        previous.sample.semantic_retained_bytes
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        previous.sample.session_retained_bytes + delta
    );
    assert_eq!(
        event.sample.semantic_peak_bytes,
        previous.sample.semantic_peak_bytes
    );
    assert_eq!(
        event.sample.session_peak_bytes,
        previous
            .sample
            .session_peak_bytes
            .max(previous.sample.session_retained_bytes + delta + finish_output)
    );
    assert_eq!(session.reported_errors.capacity(), event.new_capacity);
    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("one completed post-rollback sample");
    assert_eq!(post.semantic_peak_bytes, event.sample.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, event.sample.session_peak_bytes);
    let (independent, nested) = independent_post_rollback_value_row_resources(
        &session,
        event.sample.semantic_peak_bytes,
        event.sample.session_peak_bytes,
    );
    assert_eq!(
        post.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(post.nested_bound_bytes, nested.total_bound_bytes());
    assert_eq!(
        post.semantic_peak_bytes,
        independent.semantic_arena_peak_bytes
    );
    assert_eq!(
        post.session_peak_bytes,
        independent.inference_session_peak_bytes
    );
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        post.session_retained_bytes
    );
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    assert!(session.errors.is_empty());
    assert!(session.reported_errors.is_empty());
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.errors.len(), 1);
    assert_eq!(
        session.errors[0].kind,
        SolverErrorKind::IncompatibleValue {
            lower: ValueShape::Function,
            upper: ValueShape::Int
        }
    );
    assert_eq!(session.reported_errors.len(), 1);
    assert_eq!(session.store.facts().len(), 1);
    assert!(matches!(
        session.store.term_view(session.store.facts()[0].lower()),
        Ok(TermView::Leaf(Leaf::IntPositive))
    ));
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_errors_growth_samples_after_first_union_member_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-errors-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Union(vec![
            F5cPositive::Int,
            F5cPositive::Function {
                argument: Box::new(F5cNegative::Top),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(F5cPositive::Quantified(0)),
            },
        ]),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let scheme = finalized.into_parts().0;
    let view = session
        .finalization
        .as_ref()
        .unwrap()
        .scheme_view(&scheme)
        .unwrap();
    let PositiveValueView::Union(children) = view.positive_value(view.predicate()).unwrap() else {
        panic!("finalized predicate must be a Union");
    };
    assert_eq!(children.len(), 2);
    assert_ne!(children[0], children[1]);
    assert!(matches!(
        view.positive_value(children[0]).unwrap(),
        PositiveValueView::Int
    ));
    assert!(matches!(
        view.positive_value(children[1]).unwrap(),
        PositiveValueView::Function { .. }
    ));
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(scheme);
    let use_row =
        session.live_components[session.batch.definition_uses()[0].use_value_component].ordinal;
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 204);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_value(
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(use_row),
                upper: ValueEndpointKey::IntNegative,
            },
            &occurrence,
            &cause,
        )
        .unwrap();
    assert!(session.errors.is_empty());
    session.reported_errors.try_reserve(1).unwrap();
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .route_journal_spare
        .as_mut()
        .unwrap()
        .reported_error_keys
        .try_reserve(1)
        .unwrap();
    session.errors = Vec::new();
    assert_eq!(session.errors.capacity(), 0);
    assert!(session.reported_errors.capacity() > 0);
    assert!(
        session
            .route_journal_spare
            .as_ref()
            .unwrap()
            .reported_error_keys
            .capacity()
            > 0
    );
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let baseline_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let baseline_session = session.resource_ledger.inference_session_retained_bytes;
    let finish_output = session.resource_ledger.finish_output_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::Errors);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    assert_eq!(
        F5C_ROUTE_MANY_PRIVATE_COMPLETIONS.with(|count| count.get()),
        1
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("errors-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "Errors".into())),
        Some(&1)
    );
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    let (position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "typed-route" && event.lane == "Errors")
        .expect("Errors reserve must have a completed event-time sample");
    assert!(position > 0);
    let previous = &trace.completed_events[position - 1];
    assert!(previous.sample.semantic_retained_bytes > baseline_semantic);
    assert!(previous.sample.session_retained_bytes > baseline_session);
    assert!(
        trace.completed_events[..position]
            .iter()
            .any(|earlier| earlier.owner == "typed-route"
                && earlier.lane == "FreshValueBounds"
                && earlier.old_capacity < earlier.new_capacity)
    );
    assert_eq!(event.old_capacity, 0);
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<SolverError>())
        .unwrap();
    assert!(delta > 0);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        previous.sample.semantic_retained_bytes
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        previous.sample.session_retained_bytes + delta
    );
    assert_eq!(
        event.sample.semantic_peak_bytes,
        previous.sample.semantic_peak_bytes
    );
    assert_eq!(
        event.sample.session_peak_bytes,
        previous
            .sample
            .session_peak_bytes
            .max(previous.sample.session_retained_bytes + delta + finish_output)
    );
    assert_eq!(session.errors.capacity(), event.new_capacity);
    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("one completed post-rollback sample");
    assert_eq!(post.semantic_peak_bytes, event.sample.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, event.sample.session_peak_bytes);
    let (independent, nested) = independent_post_rollback_value_row_resources(
        &session,
        event.sample.semantic_peak_bytes,
        event.sample.session_peak_bytes,
    );
    assert_eq!(
        post.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(post.nested_bound_bytes, nested.total_bound_bytes());
    assert_eq!(
        post.semantic_peak_bytes,
        independent.semantic_arena_peak_bytes
    );
    assert_eq!(
        post.session_peak_bytes,
        independent.inference_session_peak_bytes
    );
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        post.session_retained_bytes
    );
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    assert!(session.errors.is_empty());
    assert!(session.reported_errors.is_empty());
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.errors.len(), 1);
    assert_eq!(
        session.errors[0].kind,
        SolverErrorKind::IncompatibleValue {
            lower: ValueShape::Function,
            upper: ValueShape::Int
        }
    );
    assert_eq!(session.reported_errors.len(), 1);
    assert_eq!(session.store.facts().len(), 1);
    assert!(matches!(
        session.store.term_view(session.store.facts()[0].lower()),
        Ok(TermView::Leaf(Leaf::IntPositive))
    ));
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

fn independent_post_rollback_value_row_resources(
    session: &InferenceSession,
    semantic_peak_before: usize,
    session_peak_before: usize,
) -> (IndependentResourceLedger, IndependentNestedCapacityLedger) {
    let mut nested = IndependentNestedCapacityLedger::from_surviving_rows(
        &session.bounds,
        &session.effect_bounds,
    );
    assert_eq!(session.independent_nested_capacities.diagnostic_edges, 0);
    nested.diagnostic_edges = session.independent_nested_capacities.diagnostic_edges;
    let mut ledger = IndependentResourceLedger::default();
    ledger.semantic_arena_peak_bytes = semantic_peak_before;
    ledger.inference_session_peak_bytes = session_peak_before;
    let journal_bytes = session
        .route_journal
        .as_ref()
        .or(session.route_journal_spare.as_ref())
        .map(RouteMutationJournal::checked_independent_retained_bytes)
        .transpose()
        .unwrap()
        .unwrap_or(0);
    ledger
        .record(
            ResourceBoundary::IncomingRoute,
            &session.store,
            None,
            None,
            &session.errors,
            &session.reported_errors,
            &session.cross_kind_components,
            &session.live_components,
            &session.bounds,
            &session.effect_bounds,
            &session.value_levels,
            &session.effect_levels,
            &session.value_metadata,
            &session.effect_metadata,
            &session.extrusion_stack,
            &session.extrusion_value_marks,
            &session.extrusion_effect_marks,
            &session.occurrence_exact_bounds,
            &session.typed_pairs,
            &session.typed_worklist,
            &session.diagnostic_delta,
            &session.diagnostic_delta_indices,
            &session.diagnostic_reverse_offsets,
            &session.diagnostic_reverse_edges,
            &session.diagnostic_reverse_cursors,
            &session.diagnostic_dfs_stack,
            &session.diagnostic_finish_order,
            &session.diagnostic_scc_indices,
            &session.diagnostic_scc_nodes,
            &session.diagnostic_scc_offsets,
            &session.diagnostic_scc_pending_children,
            &session.diagnostic_scc_worklist,
            &session.diagnostic_bucket_heads,
            &session.diagnostic_bucket_tails,
            &session.diagnostic_bucket_candidates,
            &session.diagnostic_node_witnesses,
            &session.routed_uses,
            &session.routed_use_positions,
            &session.schemes,
            &session.drafts,
            &session.instantiation_scratch,
            session.current_closed_retained_bytes,
            session.batch.counters.f2_batch_retained_bytes,
            session.batch.component_term_positions.capacity(),
            session.resource_ledger.finish_output_retained_bytes,
            &nested,
            journal_bytes,
        )
        .unwrap();
    (ledger, nested)
}

#[test]
fn f5c_incoming_diagnostic_delta_indices_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-diagnostic-delta-indices-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Quantified(0),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(finalized.into_parts().0);
    session.typed_pairs.try_reserve(1).unwrap();
    session.diagnostic_delta.try_reserve(1).unwrap();
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .route_journal_spare
        .as_mut()
        .unwrap()
        .typed_pair_keys
        .try_reserve(1)
        .unwrap();
    session.diagnostic_delta_indices = HashMap::new();
    assert_eq!(session.diagnostic_delta_indices.capacity(), 0);
    assert!(session.typed_pairs.capacity() > session.typed_pairs.len());
    assert!(session.diagnostic_delta.capacity() > 0);
    assert!(
        session
            .route_journal_spare
            .as_ref()
            .unwrap()
            .typed_pair_keys
            .capacity()
            > 0
    );
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let baseline_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let baseline_session = session.resource_ledger.inference_session_retained_bytes;
    let finish_output = session.resource_ledger.finish_output_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::DiagnosticDeltaIndices);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("diagnostic-delta-indices-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "DiagnosticDeltaIndices".into())),
        Some(&1)
    );
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    let (position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "typed-route" && event.lane == "DiagnosticDeltaIndices")
        .expect("DiagnosticDeltaIndices changed reserve must have a completed sample");
    assert!(position > 0);
    let previous = &trace.completed_events[position - 1];
    assert!(previous.sample.semantic_retained_bytes > baseline_semantic);
    assert!(previous.sample.session_retained_bytes > baseline_session);
    assert!(trace.completed_events[..position].iter().any(|earlier| {
        earlier.owner == "typed-route"
            && earlier.lane == "FreshValueBounds"
            && earlier.old_capacity < earlier.new_capacity
    }));
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<(CanonicalValuePairKey, usize)>())
        .unwrap();
    assert_eq!(event.old_capacity, 0);
    assert!(delta > 0);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        previous.sample.semantic_retained_bytes + delta
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        previous.sample.session_retained_bytes + delta
    );
    assert_eq!(
        event.sample.semantic_peak_bytes,
        previous
            .sample
            .semantic_peak_bytes
            .max(previous.sample.semantic_retained_bytes + delta)
    );
    assert_eq!(
        event.sample.session_peak_bytes,
        previous
            .sample
            .session_peak_bytes
            .max(previous.sample.session_retained_bytes + delta + finish_output)
    );
    assert_eq!(
        session.diagnostic_delta_indices.capacity(),
        event.new_capacity
    );
    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("one completed post-rollback sample");
    assert_eq!(post.semantic_peak_bytes, event.sample.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, event.sample.session_peak_bytes);
    let (independent, nested) = independent_post_rollback_value_row_resources(
        &session,
        event.sample.semantic_peak_bytes,
        event.sample.session_peak_bytes,
    );
    assert_eq!(
        post.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(post.nested_bound_bytes, nested.total_bound_bytes());
    assert_eq!(
        post.semantic_peak_bytes,
        independent.semantic_arena_peak_bytes
    );
    assert_eq!(
        post.session_peak_bytes,
        independent.inference_session_peak_bytes
    );
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        post.session_retained_bytes
    );
    assert_eq!(
        session.execution_counters.semantic_arena_peak_bytes,
        post.semantic_peak_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_peak_bytes,
        post.session_peak_bytes
    );
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    let fact = &session.store.facts()[0];
    let provenance = &session.store.provenance()[0];
    assert_eq!(provenance.fact(), fact.id());
    assert_eq!(session.store.consumed_receipts.len(), 1);
    assert_eq!(session.routed_uses[0].use_id, route_id);
    assert_eq!(session.routed_uses[0].fact, Some(fact.id()));
    assert!(session.routed_use_positions.contains(&route_id));
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_diagnostic_delta_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-diagnostic-delta-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Quantified(0),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(finalized.into_parts().0);
    session.typed_pairs.try_reserve(1).unwrap();
    session.diagnostic_delta_indices.try_reserve(1).unwrap();
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .route_journal_spare
        .as_mut()
        .unwrap()
        .typed_pair_keys
        .try_reserve(1)
        .unwrap();
    session.diagnostic_delta = Vec::new();
    assert_eq!(session.diagnostic_delta.capacity(), 0);
    assert!(session.typed_pairs.capacity() > session.typed_pairs.len());
    assert!(session.diagnostic_delta_indices.capacity() > 0);
    assert!(
        session
            .route_journal_spare
            .as_ref()
            .unwrap()
            .typed_pair_keys
            .capacity()
            > 0
    );
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let baseline_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let baseline_session = session.resource_ledger.inference_session_retained_bytes;
    let finish_output = session.resource_ledger.finish_output_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::DiagnosticDelta);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("diagnostic-delta-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "DiagnosticDelta".into())),
        Some(&1)
    );
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    let (position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "typed-route" && event.lane == "DiagnosticDelta")
        .expect("DiagnosticDelta changed reserve must have a completed sample");
    assert!(
        position > 0,
        "DiagnosticDelta must follow a sampled capacity event"
    );
    let previous = &trace.completed_events[position - 1];
    let prior_semantic = previous.sample.semantic_retained_bytes;
    let prior_session = previous.sample.session_retained_bytes;
    let prior_semantic_peak = previous.sample.semantic_peak_bytes;
    let prior_session_peak = previous.sample.session_peak_bytes;
    assert!(prior_semantic > baseline_semantic);
    assert!(prior_session > baseline_session);
    assert!(trace.completed_events[..position].iter().any(|earlier| {
        earlier.owner == "typed-route"
            && earlier.lane == "FreshValueBounds"
            && earlier.old_capacity < earlier.new_capacity
    }));
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<CanonicalValuePairKey>())
        .unwrap();
    assert_eq!(event.old_capacity, 0);
    assert!(delta > 0);
    assert_eq!(event.sample.semantic_retained_bytes, prior_semantic + delta);
    assert_eq!(event.sample.session_retained_bytes, prior_session + delta);
    assert_eq!(
        event.sample.semantic_peak_bytes,
        prior_semantic_peak.max(prior_semantic + delta)
    );
    assert_eq!(
        event.sample.session_peak_bytes,
        prior_session_peak.max(prior_session + delta + finish_output)
    );
    assert_eq!(session.diagnostic_delta.capacity(), event.new_capacity);
    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("one completed post-rollback snapshot");
    assert_eq!(post.semantic_peak_bytes, event.sample.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, event.sample.session_peak_bytes);
    let (independent, nested) = independent_post_rollback_value_row_resources(
        &session,
        event.sample.semantic_peak_bytes,
        event.sample.session_peak_bytes,
    );
    assert_eq!(
        post.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(post.nested_bound_bytes, nested.total_bound_bytes());
    assert_eq!(
        post.semantic_peak_bytes,
        independent.semantic_arena_peak_bytes
    );
    assert_eq!(
        post.session_peak_bytes,
        independent.inference_session_peak_bytes
    );
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        post.session_retained_bytes
    );
    assert_eq!(
        session.execution_counters.semantic_arena_peak_bytes,
        post.semantic_peak_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_peak_bytes,
        post.session_peak_bytes
    );
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_value_metadata_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-value-metadata-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Quantified(0),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(finalized.into_parts().0);
    while session.value_metadata.len() < session.value_metadata.capacity() {
        session.fresh_value_at_level(1).unwrap();
    }
    assert_eq!(
        session.value_metadata.len(),
        session.value_metadata.capacity()
    );
    session.bounds.try_reserve(1).unwrap();
    session.value_levels.try_reserve(1).unwrap();
    session.extrusion_value_marks.try_reserve(1).unwrap();
    assert!(session.bounds.len() < session.bounds.capacity());
    assert!(session.value_levels.len() < session.value_levels.capacity());
    assert!(session.extrusion_value_marks.len() < session.extrusion_value_marks.capacity());
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let old_capacity = session.value_metadata.capacity();
    let old_bounds_capacity = session.bounds.capacity();
    let old_levels_capacity = session.value_levels.capacity();
    let old_marks_capacity = session.extrusion_value_marks.capacity();
    let old_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let old_session = session.resource_ledger.inference_session_retained_bytes;
    let old_semantic_peak = session.execution_counters.semantic_arena_peak_bytes;
    let old_session_peak = session.execution_counters.inference_session_peak_bytes;
    let old_nested_bound_bytes = session.independent_nested_capacities.total_bound_bytes();
    let old_finish_output_bytes = session.resource_ledger.finish_output_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ValueMetadata);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("value-metadata-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace.event_lanes,
        [(("typed-route".into(), "ValueMetadata".into()), 1)]
            .into_iter()
            .collect()
    );
    let event = trace
        .completed_event_samples
        .get(&(String::from("typed-route"), String::from("ValueMetadata")))
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("ValueMetadata growth must have one completed event-time sample");
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    let post_rollback = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("post-rollback must have one completed sample");
    let (independent, independent_nested) = independent_post_rollback_value_row_resources(
        &session,
        old_semantic_peak,
        old_session_peak,
    );
    assert_eq!(
        post_rollback.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post_rollback.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(
        post_rollback.nested_bound_bytes,
        independent_nested.total_bound_bytes()
    );
    assert_eq!(
        post_rollback.semantic_peak_bytes,
        independent.semantic_arena_peak_bytes
    );
    assert_eq!(
        post_rollback.session_peak_bytes,
        independent.inference_session_peak_bytes
    );
    assert_eq!(trace.samples, 2);
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    let grown_capacity = session.value_metadata.capacity();
    assert!(grown_capacity > old_capacity);
    assert_eq!(session.bounds.capacity(), old_bounds_capacity);
    assert_eq!(session.value_levels.capacity(), old_levels_capacity);
    assert_eq!(session.extrusion_value_marks.capacity(), old_marks_capacity);
    let delta = (grown_capacity - old_capacity) * std::mem::size_of::<LiveVariableMetadata>();
    assert_eq!(event.semantic_retained_bytes, old_semantic + delta);
    assert_eq!(event.session_retained_bytes, old_session + delta);
    assert_eq!(event.nested_bound_bytes, old_nested_bound_bytes);
    assert_eq!(
        event.semantic_peak_bytes,
        old_semantic_peak.max(old_semantic + delta)
    );
    assert_eq!(
        event.session_peak_bytes,
        old_session_peak.max(old_session + delta + old_finish_output_bytes)
    );
    assert_eq!(post_rollback.nested_bound_bytes, old_nested_bound_bytes);
    assert_eq!(post_rollback.semantic_retained_bytes, old_semantic + delta);
    assert_eq!(post_rollback.session_retained_bytes, old_session + delta);
    assert_eq!(post_rollback.semantic_peak_bytes, event.semantic_peak_bytes);
    assert_eq!(post_rollback.session_peak_bytes, event.session_peak_bytes);
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        old_semantic + delta
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        old_session + delta
    );
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
        session.resource_ledger.inference_session_retained_bytes
    );
    assert_eq!(
        session.execution_counters.semantic_arena_peak_bytes,
        post_rollback.semantic_peak_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_peak_bytes,
        post_rollback.session_peak_bytes
    );
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_extrusion_value_marks_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-extrusion-value-marks-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Quantified(0),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(finalized.into_parts().0);
    while session.extrusion_value_marks.len() < session.extrusion_value_marks.capacity() {
        session.fresh_value_at_level(1).unwrap();
    }
    assert_eq!(
        session.extrusion_value_marks.len(),
        session.extrusion_value_marks.capacity()
    );
    session.bounds.try_reserve(1).unwrap();
    session.value_levels.try_reserve(1).unwrap();
    session.value_metadata.try_reserve(1).unwrap();
    assert!(session.bounds.len() < session.bounds.capacity());
    assert!(session.value_levels.len() < session.value_levels.capacity());
    assert!(session.value_metadata.len() < session.value_metadata.capacity());
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let old_capacity = session.extrusion_value_marks.capacity();
    let old_bounds_capacity = session.bounds.capacity();
    let old_levels_capacity = session.value_levels.capacity();
    let old_metadata_capacity = session.value_metadata.capacity();
    let old_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let old_session = session.resource_ledger.inference_session_retained_bytes;
    let old_semantic_peak = session.execution_counters.semantic_arena_peak_bytes;
    let old_session_peak = session.execution_counters.inference_session_peak_bytes;
    let old_nested_bound_bytes = session.independent_nested_capacities.total_bound_bytes();
    let old_finish_output_bytes = session.resource_ledger.finish_output_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ExtrusionValueMarks);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("extrusion-value-marks-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace.event_lanes,
        [(("typed-route".into(), "ExtrusionValueMarks".into()), 1)]
            .into_iter()
            .collect()
    );
    let event = trace
        .completed_event_samples
        .get(&(
            String::from("typed-route"),
            String::from("ExtrusionValueMarks"),
        ))
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("ExtrusionValueMarks growth must have one completed event-time sample");
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    let post_rollback = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("post-rollback must have one completed sample");
    let (independent, independent_nested) = independent_post_rollback_value_row_resources(
        &session,
        old_semantic_peak,
        old_session_peak,
    );
    assert_eq!(
        post_rollback.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post_rollback.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(
        post_rollback.nested_bound_bytes,
        independent_nested.total_bound_bytes()
    );
    assert_eq!(
        post_rollback.semantic_peak_bytes,
        independent.semantic_arena_peak_bytes
    );
    assert_eq!(
        post_rollback.session_peak_bytes,
        independent.inference_session_peak_bytes
    );
    assert_eq!(trace.samples, 2);
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    let grown_capacity = session.extrusion_value_marks.capacity();
    assert!(grown_capacity > old_capacity);
    assert_eq!(session.bounds.capacity(), old_bounds_capacity);
    assert_eq!(session.value_levels.capacity(), old_levels_capacity);
    assert_eq!(session.value_metadata.capacity(), old_metadata_capacity);
    let delta = (grown_capacity - old_capacity) * std::mem::size_of::<u32>();
    assert_eq!(event.semantic_retained_bytes, old_semantic + delta);
    assert_eq!(event.session_retained_bytes, old_session + delta);
    assert_eq!(event.nested_bound_bytes, old_nested_bound_bytes);
    assert_eq!(
        event.semantic_peak_bytes,
        old_semantic_peak.max(old_semantic + delta)
    );
    assert_eq!(
        event.session_peak_bytes,
        old_session_peak.max(old_session + delta + old_finish_output_bytes)
    );
    assert_eq!(post_rollback.nested_bound_bytes, old_nested_bound_bytes);
    assert_eq!(post_rollback.semantic_retained_bytes, old_semantic + delta);
    assert_eq!(post_rollback.session_retained_bytes, old_session + delta);
    assert_eq!(post_rollback.semantic_peak_bytes, event.semantic_peak_bytes);
    assert_eq!(post_rollback.session_peak_bytes, event.session_peak_bytes);
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        old_semantic + delta
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        old_session + delta
    );
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
        session.resource_ledger.inference_session_retained_bytes
    );
    assert_eq!(
        session.execution_counters.semantic_arena_peak_bytes,
        post_rollback.semantic_peak_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_peak_bytes,
        post_rollback.session_peak_bytes
    );
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_value_levels_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-value-levels-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Quantified(0),
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(finalized.into_parts().0);
    while session.value_levels.len() < session.value_levels.capacity() {
        session.fresh_value_at_level(1).unwrap();
    }
    assert_eq!(session.value_levels.len(), session.value_levels.capacity());
    session.bounds.try_reserve(1).unwrap();
    assert!(session.bounds.len() < session.bounds.capacity());
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let old_capacity = session.value_levels.capacity();
    let old_value_levels_bytes = old_capacity * std::mem::size_of::<u32>();
    let old_semantic = session.resource_ledger.semantic_arena_retained_bytes;
    let old_session = session.resource_ledger.inference_session_retained_bytes;
    let old_semantic_peak = session.execution_counters.semantic_arena_peak_bytes;
    let old_session_peak = session.execution_counters.inference_session_peak_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ValueLevels);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("value-levels-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace.event_lanes,
        [(("typed-route".into(), "ValueLevels".into()), 1)]
            .into_iter()
            .collect()
    );
    let event = trace
        .completed_event_samples
        .get(&(String::from("typed-route"), String::from("ValueLevels")))
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("ValueLevels growth must have one completed event-time sample");
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, 2);
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    let grown_capacity = session.value_levels.capacity();
    assert!(
        grown_capacity > old_capacity,
        "the Q row must grow ValueLevels"
    );
    let delta = (grown_capacity - old_capacity) * std::mem::size_of::<u32>();
    let grown_value_levels_bytes = grown_capacity * std::mem::size_of::<u32>();
    assert_eq!(event.value_levels_bytes, grown_value_levels_bytes);
    assert_eq!(event.value_levels_bytes - old_value_levels_bytes, delta);
    assert_eq!(grown_value_levels_bytes - old_value_levels_bytes, delta);
    assert_eq!(event.semantic_retained_bytes, old_semantic + delta);
    assert_eq!(event.session_retained_bytes, old_session + delta);
    assert!(event.semantic_peak_bytes >= event.semantic_retained_bytes);
    assert!(event.session_peak_bytes >= event.session_retained_bytes);
    assert!(event.semantic_peak_bytes > old_semantic_peak);
    assert!(event.session_peak_bytes > old_session_peak);
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        old_semantic + delta
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        old_session + delta
    );
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
        session.resource_ledger.inference_session_retained_bytes
    );
    assert!(session.execution_counters.semantic_arena_peak_bytes >= event.semantic_peak_bytes);
    assert!(session.execution_counters.inference_session_peak_bytes >= event.session_peak_bytes);
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_value_exact_lower_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-value-exact-lower-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(
        session
            .finalization
            .as_mut()
            .unwrap()
            .finalize_scheme(|finalizer| {
                let predicate = finalizer.positive_int()?;
                finalizer.set_scheme(0, &[], predicate)
            })
            .unwrap()
            .into_parts()
            .0,
    );
    let use_row =
        session.live_components[session.batch.definition_uses()[0].use_value_component].ordinal;
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 206);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_value(
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(use_row),
                upper: ValueEndpointKey::BottomNegative,
            },
            &occurrence,
            &cause,
        )
        .unwrap();
    let before = RouteCheckpoint::capture(&session);
    let old_exact_lower = session.independent_nested_capacities.value_exact_lower;
    let old_semantic_retained = session.resource_ledger.semantic_arena_retained_bytes;
    let old_session_retained = session.resource_ledger.inference_session_retained_bytes;
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ValueExactLower);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("value-exact-lower-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("value".into(), "ValueExactLower".into())),
        Some(&1)
    );
    assert_eq!(trace.named_samples.get("post-rollback"), Some(&1));
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    let surviving = IndependentNestedCapacityLedger::from_surviving_rows(
        &session.bounds,
        &session.effect_bounds,
    );
    let retained_lane_delta = surviving
        .value_exact_lower
        .checked_sub(old_exact_lower)
        .expect("the preexisting exact-lower lane must retain its grown capacity");
    assert!(retained_lane_delta > 0);
    let event_sample = trace
        .completed_event_samples
        .get(&(String::from("value"), String::from("ValueExactLower")))
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("exact-lower event must have one completed aggregate sample");
    assert_eq!(
        event_sample.nested_bound_bytes,
        surviving.total_bound_bytes()
    );
    assert!(
        event_sample.semantic_retained_bytes
            >= old_semantic_retained
                .checked_add(retained_lane_delta)
                .unwrap()
    );
    assert!(
        event_sample.session_retained_bytes
            >= old_session_retained
                .checked_add(retained_lane_delta)
                .unwrap()
    );
    assert!(event_sample.semantic_peak_bytes >= event_sample.semantic_retained_bytes);
    assert!(event_sample.session_peak_bytes >= event_sample.session_retained_bytes);
    assert_eq!(session.independent_nested_capacities, surviving);
    assert_eq!(
        session.independent_nested_capacities.total_bound_bytes(),
        session.bound_payload_bytes
    );
    assert!(session.resource_ledger.semantic_arena_retained_bytes >= old_semantic_retained);
    assert!(session.resource_ledger.inference_session_retained_bytes >= old_session_retained);
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
        session.resource_ledger.inference_session_retained_bytes
    );
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_value_exact_upper_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-value-exact-upper-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Function {
            argument: Box::new(F5cNegative::Top),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Quantified(0)),
        },
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(finalized.into_parts().0);
    let upper_row =
        session.live_components[session.batch.definition_uses()[0].use_value_component].ordinal;
    let negative_function = session
        .negative_function_term(
            session.batch.collected_leaf_term(Leaf::IntPositive),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session.batch.collected_leaf_term(Leaf::IntNegative),
        )
        .unwrap();
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 205);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_value(
            CanonicalValuePairKey {
                lower: ValueEndpointKey::ValueRow(upper_row),
                upper: ValueEndpointKey::NegativeFunction(negative_function),
            },
            &occurrence,
            &cause,
        )
        .unwrap();
    let before = RouteCheckpoint::capture(&session);
    let final_attempts = session.incoming_post_rollback_sample_attempts;
    let final_samples = session.incoming_post_rollback_samples;
    let sample_count = session.resource_boundary_samples;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ValueExactUpper);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish("value-exact-upper-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("value".into(), "ValueExactUpper".into())),
        Some(&1),
        "the changed reserve must be sampled before its failure propagates"
    );
    assert_eq!(trace.named_samples.get("post-rollback"), Some(&1));
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        final_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, final_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        sample_count + trace.samples
    );
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());
    assert_eq!(
        session.independent_nested_capacities.total_bound_bytes(),
        session.bound_payload_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
        session.resource_ledger.inference_session_retained_bytes
    );
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        session.resource_ledger.semantic_arena_retained_bytes
    );

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_value_direct_rows_sample_before_rollback_and_retry() {
    for lane in [
        F5bCapacityLane::ValueDirectLower,
        F5bCapacityLane::ValueDirectUpper,
    ] {
        let batch = collect(module(
            "my source = 1; my sink = source",
            "f5c-value-direct-route",
        ));
        let route_id = batch.definition_uses()[0].id.clone();
        let mut session = InferenceSession::new(batch);
        let draft = GeneralizationDraft {
            quantifier_count: 1,
            recursive_bounds: Vec::new(),
            predicate: F5cPositive::Quantified(0),
        };
        let finalized = InferenceSession::finalize_generalization_draft(
            session.finalization.as_mut().unwrap(),
            &draft,
            false,
        )
        .unwrap();
        let target = session.batch.definition_uses()[0].target.ordinal() as usize;
        session.schemes[target] = Some(finalized.into_parts().0);
        let before = RouteCheckpoint::capture(&session);
        let old_rows_len = session.bounds.len();
        let old_direct_upper_bytes = session.independent_nested_capacities.value_direct_upper;
        let old_semantic_retained_bytes = session.resource_ledger.semantic_arena_retained_bytes;
        let old_session_retained_bytes = session.resource_ledger.inference_session_retained_bytes;
        let old_capacities: Vec<_> = session
            .bounds
            .iter()
            .map(|row| {
                (
                    row.direct_lower_rows.capacity(),
                    row.direct_upper_rows.capacity(),
                )
            })
            .collect();
        let samples = session.resource_boundary_samples;
        let post_attempts = session.incoming_post_rollback_sample_attempts;
        let post_samples = session.incoming_post_rollback_samples;
        incoming_sample_trace::start();
        inject_next_f5b_post_reserve_failure(lane);

        assert_eq!(
            session.route_incoming(&route_id),
            Err(SolveAvailabilityError::IdentityExhausted),
            "{lane:?}"
        );
        assert_eq!(
            F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
            None,
            "{lane:?}"
        );
        before.assert_restored(&session);
        let trace = incoming_sample_trace::finish("value-direct-route", 1);
        assert_eq!(trace.attempts, 1, "{lane:?}");
        assert_eq!(
            trace
                .event_lanes
                .get(&("value".into(), format!("{lane:?}"))),
            Some(&1),
            "{lane:?}"
        );
        assert_eq!(
            trace.named_samples.get("post-rollback"),
            Some(&1),
            "{lane:?}"
        );
        assert_eq!(
            session.incoming_post_rollback_sample_attempts,
            post_attempts + 1,
            "{lane:?}"
        );
        assert_eq!(
            session.incoming_post_rollback_samples,
            post_samples + 1,
            "{lane:?}"
        );
        assert_eq!(
            session.resource_boundary_samples,
            samples + trace.samples,
            "{lane:?}"
        );
        if lane == F5bCapacityLane::ValueDirectLower {
            assert!(
                session
                    .bounds
                    .iter()
                    .zip(&old_capacities)
                    .any(|(row, &(lower, _))| row.direct_lower_rows.capacity() > lower),
                "the preexisting row must retain its changed capacity"
            );
        } else {
            let event = session.incoming_nested_value_direct_upper_event.unwrap();
            assert!(event.fresh_row);
            assert!(event.value_direct_upper_bytes > old_direct_upper_bytes);
            assert!(
                event.semantic_retained_bytes
                    >= old_semantic_retained_bytes + event.value_direct_upper_bytes
                        - old_direct_upper_bytes
            );
            assert!(
                session.resource_ledger.semantic_arena_peak_bytes >= event.semantic_retained_bytes
            );
            assert!(
                event.session_retained_bytes
                    >= old_session_retained_bytes + event.value_direct_upper_bytes
                        - old_direct_upper_bytes
            );
            assert!(
                session.resource_ledger.inference_session_peak_bytes
                    >= event.session_retained_bytes
            );
            assert_eq!(session.bounds.len(), old_rows_len);
            let surviving = IndependentNestedCapacityLedger::from_surviving_rows(
                &session.bounds,
                &session.effect_bounds,
            );
            assert_eq!(surviving.value_direct_upper, old_direct_upper_bytes);
            assert_eq!(session.independent_nested_capacities, surviving);
        }
        assert_eq!(
            session.independent_nested_capacities.total_bound_bytes(),
            session.bound_payload_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.execution_counters.inference_session_retained_bytes,
            session.resource_ledger.inference_session_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.execution_counters.semantic_arena_retained_bytes,
            session.resource_ledger.semantic_arena_retained_bytes,
            "{lane:?}"
        );
        session.route_incoming(&route_id).unwrap();
        assert_eq!(session.store.facts().len(), 1, "{lane:?}");
        assert_eq!(session.store.provenance().len(), 1, "{lane:?}");
        assert_eq!(session.routed_uses.len(), 1, "{lane:?}");
        assert_eq!(session.routed_use_positions.len(), 1, "{lane:?}");
    }
}
