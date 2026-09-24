use super::*;

fn preserve_monotone_store_growth_counters(
    checkpoint: &mut RouteCheckpoint,
    session: &InferenceSession,
) {
    macro_rules! preserve {
        ($field:ident) => {
            checkpoint.store.counters.$field = session.store.counters.$field;
        };
    }
    preserve!(fact_store_growths);
    preserve!(fact_store_rebuilds);
    preserve!(canonical_map_growths);
    preserve!(canonical_map_rebuilds);
    preserve!(consumed_receipt_growths);
    preserve!(consumed_receipt_rebuilds);
    preserve!(provenance_growths);
    preserve!(provenance_rebuilds);
}

#[test]
fn f5c_route_use_owner_failed_reserves_reconcile_after_rollback() {
    for (lane, expected_lanes) in [
        (
            F5bCapacityLane::RoutedUsePositions,
            &["RoutedUsePositions"][..],
        ),
        (
            F5bCapacityLane::RoutedUses,
            &["RoutedUsePositions", "RoutedUses"][..],
        ),
    ] {
        let (mut session, routes) =
            f5c_shared_closed_incoming_fixture("f5c-route-use-owner-reserve");
        let route = routes[0].clone();
        session.routed_uses = Vec::new();
        session.routed_use_positions = HashSet::new();
        let mut before = RouteCheckpoint::capture(&session);
        let receipt_serial = session.store.next_receipt;
        let attempts = session.incoming_route_sample_attempts;
        let boundaries = session.resource_boundary_samples;
        let outer = session.incoming_post_rollback_sample_attempts;
        let post_samples = session.incoming_post_rollback_samples;
        incoming_sample_trace::start();
        inject_next_f5b_post_reserve_failure(lane);
        assert_eq!(
            session.route_incoming(&route),
            Err(SolveAvailabilityError::IdentityExhausted),
            "{lane:?}"
        );
        let trace = incoming_sample_trace::finish(&format!("route-use-{lane:?}"), 1);
        assert_eq!(trace.attempts, 1, "{lane:?}");
        assert_eq!(trace.matched_events, trace.event_samples, "{lane:?}");
        assert_eq!(
            trace.completed_events.len(),
            trace.event_samples,
            "{lane:?}"
        );
        assert_eq!(
            trace.named_samples,
            [("post-rollback".into(), 1)].into_iter().collect(),
            "{lane:?}"
        );
        assert_eq!(trace.samples, trace.event_samples + 1, "{lane:?}");
        assert_eq!(
            session.incoming_route_sample_attempts,
            attempts + trace.samples
        );
        assert_eq!(
            session.resource_boundary_samples,
            boundaries + trace.samples
        );
        assert_eq!(session.incoming_post_rollback_sample_attempts, outer + 1);
        assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);

        let route_events: Vec<_> = trace
            .completed_events
            .iter()
            .enumerate()
            .filter(|(_, event)| event.owner == "routed-use")
            .collect();
        assert_eq!(route_events.len(), expected_lanes.len(), "{lane:?}");
        let mut expected_growths = [0usize; 2];
        let mut expected_event_peaks = None;
        for (position, (event_position, event)) in route_events.into_iter().enumerate() {
            assert_eq!(event.lane, expected_lanes[position], "{lane:?}");
            assert_eq!(
                trace
                    .event_lanes
                    .get(&("routed-use".into(), event.lane.clone())),
                Some(&1),
                "{lane:?}"
            );
            assert!(event_position > 0, "{lane:?}");
            let previous = &trace.completed_events[event_position - 1].sample;
            let index = if event.lane == "RoutedUses" { 0 } else { 1 };
            let slot_size = if index == 0 {
                std::mem::size_of::<RoutedUseProvenance>()
            } else {
                std::mem::size_of::<DefinitionUseId>()
            };
            assert_eq!(event.old_capacity, 0, "{lane:?}");
            assert!(event.new_capacity > event.old_capacity, "{lane:?}");
            let delta = (event.new_capacity - event.old_capacity) * slot_size;
            if index == 1 {
                assert_eq!(
                    event.sample.semantic_retained_bytes, previous.semantic_retained_bytes,
                    "{lane:?}"
                );
            } else {
                assert_eq!(
                    event.sample.semantic_retained_bytes,
                    previous.semantic_retained_bytes + delta,
                    "{lane:?}"
                );
            }
            assert_eq!(
                event.sample.session_retained_bytes,
                previous.session_retained_bytes + delta,
                "{lane:?}"
            );
            let expected_semantic_retained =
                previous.semantic_retained_bytes + if index == 0 { delta } else { 0 };
            let expected_session_retained = previous.session_retained_bytes + delta;
            let expected_semantic_peak =
                previous.semantic_peak_bytes.max(expected_semantic_retained);
            let expected_session_peak = previous.session_peak_bytes.max(
                expected_session_retained + session.resource_ledger.finish_output_retained_bytes,
            );
            assert_eq!(
                event.sample.semantic_peak_bytes, expected_semantic_peak,
                "{lane:?}"
            );
            assert_eq!(
                event.sample.session_peak_bytes, expected_session_peak,
                "{lane:?}"
            );
            expected_event_peaks = Some((expected_semantic_peak, expected_session_peak));
            expected_growths[index] += 1;
        }
        assert_eq!(
            session.execution_counters.routed_use_provenance_growths(),
            0,
            "{lane:?}"
        );
        before.execution_counters.routed_use_provenance_growths =
            session.execution_counters.routed_use_provenance_growths();
        before.assert_restored(&session);
        assert!(session.routed_uses.is_empty(), "{lane:?}");
        assert!(session.routed_use_positions.is_empty(), "{lane:?}");
        for (index, (capacity, slot_size)) in [
            (
                session.routed_uses.capacity(),
                std::mem::size_of::<RoutedUseProvenance>(),
            ),
            (
                session.routed_use_positions.capacity(),
                std::mem::size_of::<DefinitionUseId>(),
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let ledger = &session.resource_ledger.route_use_lanes[index];
            assert_eq!(ledger.actual_capacity, capacity, "{lane:?}");
            assert_eq!(ledger.retained_bytes, capacity * slot_size, "{lane:?}");
            assert!(ledger.peak_bytes >= ledger.retained_bytes, "{lane:?}");
            assert_eq!(ledger.capacity_growths, expected_growths[index], "{lane:?}");
        }
        let post = &trace.completed_named_samples["post-rollback"][0];
        // The independent ledger rebuilds retained totals; peak history carries forward
        // from the already-asserted target event transition.
        let (expected_semantic_peak, expected_session_peak) = expected_event_peaks.unwrap();
        let (independent, nested) = independent_post_rollback_value_row_resources(
            &session,
            expected_semantic_peak,
            expected_session_peak,
        );
        assert_eq!(
            post.semantic_retained_bytes, independent.semantic_arena_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            post.session_retained_bytes, independent.inference_session_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            post.nested_bound_bytes,
            nested.total_bound_bytes(),
            "{lane:?}"
        );
        assert_eq!(
            post.semantic_peak_bytes, independent.semantic_arena_peak_bytes,
            "{lane:?}"
        );
        assert_eq!(
            post.session_peak_bytes, independent.inference_session_peak_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.resource_ledger.semantic_arena_retained_bytes, post.semantic_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.resource_ledger.inference_session_retained_bytes, post.session_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.execution_counters.semantic_arena_retained_bytes(),
            post.semantic_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session
                .execution_counters
                .inference_session_retained_bytes(),
            post.session_retained_bytes,
            "{lane:?}"
        );

        session.route_incoming(&route).unwrap();
        assert_eq!(session.store.facts.len(), 1, "{lane:?}");
        let fact = &session.store.facts[0];
        let fact_id = fact.id();
        let key = FactKey::new(
            fact.lower(),
            fact.upper(),
            session.store.comparisons.clone(),
        );
        assert_eq!(
            session.store.canonical.get(&key),
            Some(&fact_id),
            "{lane:?}"
        );
        assert_eq!(session.store.provenance().len(), 1, "{lane:?}");
        assert_eq!(session.store.provenance()[0].fact(), fact_id, "{lane:?}");
        assert_eq!(session.store.consumed_receipts.len(), 1, "{lane:?}");
        assert!(
            session.store.consumed_receipts.contains(&receipt_serial),
            "{lane:?}"
        );
        assert_eq!(session.store.next_receipt, receipt_serial + 1, "{lane:?}");
        assert_eq!(session.routed_uses.len(), 1, "{lane:?}");
        assert_eq!(session.routed_uses[0].use_id, route, "{lane:?}");
        assert_eq!(session.routed_uses[0].fact, Some(fact_id), "{lane:?}");
        assert_eq!(session.routed_use_positions.len(), 1, "{lane:?}");
        assert!(session.routed_use_positions.contains(&route), "{lane:?}");
    }
}

#[test]
fn f5c_store_changed_failed_reserves_keep_one_outer_sample() {
    for (index, lane) in [
        F5bCapacityLane::StoreFacts,
        F5bCapacityLane::StoreCanonical,
        F5bCapacityLane::StoreConsumedReceipts,
        F5bCapacityLane::StoreProvenance,
    ]
    .into_iter()
    .enumerate()
    {
        let (mut session, routes) = f5c_shared_closed_incoming_fixture("f5c-store-changed-reserve");
        let route = routes[0].clone();
        session.store.facts = Vec::new();
        session.store.canonical = HashMap::new();
        session.store.consumed_receipts = HashSet::new();
        session.store.provenance = Vec::new();
        let mut before = RouteCheckpoint::capture(&session);
        let receipt_serial = session.store.next_receipt;
        let outer = session.incoming_post_rollback_sample_attempts;
        let post_samples = session.incoming_post_rollback_samples;
        let samples = session.incoming_route_sample_attempts;
        let boundary_samples = session.resource_boundary_samples;
        let slot_sizes = [
            std::mem::size_of::<SemanticFact>(),
            std::mem::size_of::<(FactKey, FactId)>(),
            std::mem::size_of::<u64>(),
            std::mem::size_of::<ProvenanceEdge>(),
        ];
        incoming_sample_trace::start();
        inject_next_f5b_post_reserve_failure(lane);
        assert_eq!(
            session.route_incoming(&route),
            Err(SolveAvailabilityError::IdentityExhausted),
            "{lane:?}"
        );
        let trace = incoming_sample_trace::finish(&format!("store-lane-{index}"), 1);
        assert_eq!(trace.attempts, 1, "{lane:?}");
        assert_eq!(trace.matched_events, trace.event_samples, "{lane:?}");
        assert_eq!(
            trace.completed_events.len(),
            trace.event_samples,
            "{lane:?}"
        );
        assert_eq!(
            trace.named_samples,
            [("post-rollback".into(), 1)].into_iter().collect(),
            "{lane:?}"
        );
        assert_eq!(trace.samples, trace.event_samples + 1, "{lane:?}");
        assert_eq!(
            session.incoming_route_sample_attempts,
            samples + trace.samples
        );
        assert_eq!(
            session.resource_boundary_samples,
            boundary_samples + trace.samples
        );
        assert_eq!(session.incoming_post_rollback_sample_attempts, outer + 1);
        assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);

        let store_events: Vec<_> = trace
            .completed_events
            .iter()
            .enumerate()
            .filter(|(_, event)| event.owner == "ConstraintStore")
            .collect();
        assert_eq!(store_events.len(), index + 1, "{lane:?}");
        for (store_index, (position, event)) in store_events.into_iter().enumerate() {
            assert_eq!(event.lane, format!("lane-{store_index}"), "{lane:?}");
            assert_eq!(
                trace
                    .event_lanes
                    .get(&("ConstraintStore".into(), event.lane.clone())),
                Some(&1),
                "{lane:?}"
            );
            assert!(position > 0, "{lane:?}");
            let previous = &trace.completed_events[position - 1].sample;
            assert_eq!(event.old_capacity, 0, "{lane:?}");
            assert!(event.new_capacity > event.old_capacity, "{lane:?}");
            let delta = (event.new_capacity - event.old_capacity) * slot_sizes[store_index];
            assert_eq!(
                event.sample.semantic_retained_bytes, previous.semantic_retained_bytes,
                "{lane:?}"
            );
            assert_eq!(
                event.sample.session_retained_bytes,
                previous.session_retained_bytes + delta,
                "{lane:?}"
            );
            assert_eq!(
                event.sample.semantic_peak_bytes, previous.semantic_peak_bytes,
                "{lane:?}"
            );
            assert_eq!(
                event.sample.session_peak_bytes,
                previous.session_peak_bytes.max(
                    event.sample.session_retained_bytes
                        + session.resource_ledger.finish_output_retained_bytes
                ),
                "{lane:?}"
            );
            assert_eq!(
                session.resource_ledger.route_store_lanes[store_index].actual_capacity,
                event.new_capacity,
                "{lane:?}"
            );
        }

        let expected_growths: [usize; 4] =
            std::array::from_fn(|store_index| usize::from(store_index <= index));
        assert_eq!(
            [
                session.store.counters.fact_store_growths,
                session.store.counters.canonical_map_growths,
                session.store.counters.consumed_receipt_growths,
                session.store.counters.provenance_growths,
            ],
            expected_growths,
            "{lane:?}"
        );
        assert_eq!(
            [
                session.store.counters.fact_store_rebuilds,
                session.store.counters.canonical_map_rebuilds,
                session.store.counters.consumed_receipt_rebuilds,
                session.store.counters.provenance_rebuilds,
            ],
            expected_growths,
            "{lane:?}"
        );

        // Physical store growth/rebuild counters remain monotone across rollback;
        // the assertions above prove their exact event-derived values.
        preserve_monotone_store_growth_counters(&mut before, &session);
        before.assert_restored(&session);
        assert!(session.store.facts.is_empty(), "{lane:?}");
        assert!(session.store.canonical.is_empty(), "{lane:?}");
        assert!(session.store.consumed_receipts.is_empty(), "{lane:?}");
        assert!(session.store.provenance.is_empty(), "{lane:?}");
        assert!(session.routed_uses.is_empty(), "{lane:?}");
        assert!(session.routed_use_positions.is_empty(), "{lane:?}");
        let capacities = [
            session.store.facts.capacity(),
            session.store.canonical.capacity(),
            session.store.consumed_receipts.capacity(),
            session.store.provenance.capacity(),
        ];
        for store_index in 0..4 {
            assert_eq!(
                capacities[store_index] > 0,
                store_index <= index,
                "{lane:?}"
            );
            let ledger = &session.resource_ledger.route_store_lanes[store_index];
            assert_eq!(ledger.actual_capacity, capacities[store_index], "{lane:?}");
            assert_eq!(
                ledger.retained_bytes,
                capacities[store_index] * slot_sizes[store_index],
                "{lane:?}"
            );
            assert_eq!(
                ledger.capacity_growths, expected_growths[store_index],
                "{lane:?}"
            );
            if store_index == index {
                assert!(ledger.peak_bytes > 0, "{lane:?}");
            }
        }
        let post = &trace.completed_named_samples["post-rollback"][0];
        let last_event = &trace.completed_events.last().unwrap().sample;
        let (independent, nested) = independent_post_rollback_value_row_resources(
            &session,
            last_event.semantic_peak_bytes,
            last_event.session_peak_bytes,
        );
        assert_eq!(
            post.semantic_retained_bytes, independent.semantic_arena_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            post.session_retained_bytes, independent.inference_session_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            post.nested_bound_bytes,
            nested.total_bound_bytes(),
            "{lane:?}"
        );
        assert_eq!(
            post.semantic_peak_bytes, independent.semantic_arena_peak_bytes,
            "{lane:?}"
        );
        assert_eq!(
            post.session_peak_bytes, independent.inference_session_peak_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.resource_ledger.semantic_arena_retained_bytes, post.semantic_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.resource_ledger.inference_session_retained_bytes, post.session_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session.execution_counters.semantic_arena_retained_bytes(),
            post.semantic_retained_bytes,
            "{lane:?}"
        );
        assert_eq!(
            session
                .execution_counters
                .inference_session_retained_bytes(),
            post.session_retained_bytes,
            "{lane:?}"
        );
        session.route_incoming(&route).unwrap();
        assert_eq!(session.store.facts.len(), 1, "{lane:?}");
        assert_eq!(session.routed_uses.len(), 1, "{lane:?}");
        let fact = &session.store.facts[0];
        let fact_id = fact.id();
        let canonical_key = FactKey::new(
            fact.lower(),
            fact.upper(),
            session.store.comparisons.clone(),
        );
        assert_eq!(
            session.store.canonical.get(&canonical_key),
            Some(&fact_id),
            "{lane:?}"
        );
        assert_eq!(session.store.provenance().len(), 1, "{lane:?}");
        assert_eq!(session.store.provenance()[0].fact(), fact_id, "{lane:?}");
        assert_eq!(session.store.consumed_receipts.len(), 1, "{lane:?}");
        assert!(
            session.store.consumed_receipts.contains(&receipt_serial),
            "{lane:?}"
        );
        assert_eq!(session.store.next_receipt, receipt_serial + 1, "{lane:?}");
        assert_eq!(session.routed_uses[0].use_id, route, "{lane:?}");
        assert_eq!(session.routed_uses[0].fact, Some(fact_id), "{lane:?}");
        assert_eq!(session.routed_use_positions.len(), 1, "{lane:?}");
        assert!(session.routed_use_positions.contains(&route), "{lane:?}");
    }
}

#[test]
fn f5c_incoming_value_undo_growth_precedes_later_provenance_failure() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-value-undo-later-failure",
    ));
    let route = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 0,
        recursive_bounds: Vec::new(),
        predicate: F5cPositive::Union(vec![
            F5cPositive::Int,
            F5cPositive::Function {
                argument: Box::new(F5cNegative::Top),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(F5cPositive::Int),
            },
        ]),
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
    let previous_capacity = session
        .route_journal_spare
        .as_ref()
        .map_or(0, |journal| journal.value_rows.capacity());
    let samples = session.incoming_route_sample_attempts;
    let outer = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    let resource_samples = session.resource_boundary_samples;
    F5C_SAMPLED_ACTIVE_VALUE_UNDO_CAPACITY.with(|observed| observed.set(0));
    incoming_sample_trace::start();
    session.inject_next_provenance_failure(ConstraintError::ReceiptMismatch);

    assert_eq!(
        session.route_incoming(&route),
        Err(SolveAvailabilityError::ReceiptMismatch)
    );
    let trace = incoming_sample_trace::finish("value-undo-later-provenance", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace
            .event_lanes
            .get(&("journal".into(), "value_rows".into())),
        Some(&1)
    );
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    let (position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "journal" && event.lane == "value_rows")
        .expect("value undo growth must have a completed event-time sample");
    assert!(position > 0);
    let previous = &trace.completed_events[position - 1].sample;
    assert_eq!(event.old_capacity, previous_capacity);
    assert!(event.new_capacity > event.old_capacity);
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<ValueRowUndo>())
        .unwrap();
    assert!(delta > 0);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        previous.semantic_retained_bytes + delta
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        previous.session_retained_bytes + delta
    );
    assert_eq!(
        event.sample.semantic_peak_bytes,
        previous
            .semantic_peak_bytes
            .max(previous.semantic_retained_bytes + delta)
    );
    assert_eq!(
        event.sample.session_peak_bytes,
        previous.session_peak_bytes.max(
            previous.session_retained_bytes
                + delta
                + session.resource_ledger.finish_output_retained_bytes
        )
    );
    let sampled_capacity = F5C_SAMPLED_ACTIVE_VALUE_UNDO_CAPACITY.with(|observed| observed.get());
    assert_eq!(sampled_capacity, event.new_capacity);
    assert_eq!(
        session.incoming_route_sample_attempts,
        samples + trace.samples
    );
    assert_eq!(session.incoming_post_rollback_sample_attempts, outer + 1);
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(
        session.resource_boundary_samples,
        resource_samples + trace.samples
    );
    before.assert_restored(&session);
    assert!(session.route_journal.is_none());
    let retained = session.route_journal_spare.as_ref().unwrap();
    assert_eq!(retained.value_rows.capacity(), event.new_capacity);
    assert!(!retained.value_rows.is_empty());
    assert_eq!(
        retained.checked_independent_retained_bytes().unwrap(),
        retained.checked_retained_bytes().unwrap()
    );
    let post = &trace.completed_named_samples["post-rollback"][0];
    let last_event = &trace.completed_events.last().unwrap().sample;
    assert!(last_event.semantic_peak_bytes >= event.sample.semantic_peak_bytes);
    assert!(last_event.session_peak_bytes >= event.sample.session_peak_bytes);
    assert_eq!(post.semantic_peak_bytes, last_event.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, last_event.session_peak_bytes);
    let (independent, nested) = independent_post_rollback_value_row_resources(
        &session,
        last_event.semantic_peak_bytes,
        last_event.session_peak_bytes,
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
        session.independent_nested_capacities.total_bound_bytes(),
        nested.total_bound_bytes()
    );
    assert_eq!(session.bound_payload_bytes, nested.total_bound_bytes());
    assert_eq!(
        session.resource_ledger.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        post.session_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.semantic_arena_peak_bytes,
        post.semantic_peak_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_peak_bytes,
        post.session_peak_bytes
    );
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
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
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    session.route_incoming(&route).unwrap();
    assert_eq!(session.store.facts().len(), 1);
}

fn check_journal_key_changed_reserve(reported: bool) {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-journal-key-route",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: if reported {
            F5cPositive::Union(vec![
                F5cPositive::Int,
                F5cPositive::Function {
                    argument: Box::new(F5cNegative::Top),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Quantified(0)),
                },
            ])
        } else {
            F5cPositive::Quantified(0)
        },
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let scheme = finalized.into_parts().0;
    if reported {
        let view = session
            .finalization
            .as_ref()
            .unwrap()
            .scheme_view(&scheme)
            .unwrap();
        let PositiveValueView::Union(children) = view.positive_value(view.predicate()).unwrap()
        else {
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
    }
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    session.schemes[target] = Some(scheme);
    if reported {
        let use_row =
            session.live_components[session.batch.definition_uses()[0].use_value_component].ordinal;
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 204);
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
        session.errors.try_reserve(1).unwrap();
    }
    session.typed_pairs.try_reserve(1).unwrap();
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    let spare = session.route_journal_spare.as_mut().unwrap();
    if reported {
        spare.typed_pair_keys.try_reserve(1).unwrap();
        spare.reported_error_keys = Vec::new();
        assert_eq!(spare.reported_error_keys.capacity(), 0);
    } else {
        spare.typed_pair_keys = Vec::new();
        assert_eq!(spare.typed_pair_keys.capacity(), 0);
    }
    assert!(session.typed_pairs.capacity() > 0);
    let baseline_typed_pairs = session.typed_pairs.clone();
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();
    let mut before = RouteCheckpoint::capture(&session);
    before.route_journal_spare_generation = before
        .route_journal_spare_generation
        .map(|generation| generation.checked_add(1).unwrap());
    let sample_count = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    let receipt_serial = session.store.next_receipt;
    let lane = if reported {
        F5bCapacityLane::ReportedErrors
    } else {
        F5bCapacityLane::TypedPairs
    };
    let lane_name = if reported {
        "ReportedErrors"
    } else {
        "TypedPairs"
    };
    let trace_name = if reported {
        "journal-reported-error-keys"
    } else {
        "journal-typed-pair-keys"
    };
    incoming_sample_trace::start();
    inject_f5b_post_reserve_failure_after(lane, 1);
    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    assert_eq!(F5B_POST_RESERVE_FAILURE_SKIP.with(|skip| skip.get()), 0);
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish(trace_name, 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), lane_name.into())),
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
        .find(|(_, event)| event.owner == "typed-route" && event.lane == lane_name)
        .expect("journal reserve must have a completed event-time sample");
    assert!(position > 0);
    let previous = &trace.completed_events[position - 1].sample;
    assert_eq!(event.old_capacity, 0);
    let slot_size = if reported {
        std::mem::size_of::<(ConstraintOccurrenceId, SolverErrorKind)>()
    } else {
        std::mem::size_of::<TypedPairKey>()
    };
    let delta = event.new_capacity.checked_mul(slot_size).unwrap();
    assert!(delta > 0);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        previous.semantic_retained_bytes + delta
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        previous.session_retained_bytes + delta
    );
    assert_eq!(
        event.sample.semantic_peak_bytes,
        previous
            .semantic_peak_bytes
            .max(previous.semantic_retained_bytes + delta)
    );
    assert_eq!(
        event.sample.session_peak_bytes,
        previous.session_peak_bytes.max(
            previous.session_retained_bytes
                + delta
                + session.resource_ledger.finish_output_retained_bytes
        )
    );
    let spare = session.route_journal_spare.as_ref().unwrap();
    if reported {
        assert_eq!(spare.reported_error_keys.capacity(), event.new_capacity);
        assert!(spare.reported_error_keys.is_empty());
        assert!(session.errors.is_empty());
        assert!(session.reported_errors.is_empty());
        assert_eq!(session.typed_pairs, baseline_typed_pairs);
    } else {
        assert_eq!(spare.typed_pair_keys.capacity(), event.new_capacity);
        assert!(spare.typed_pair_keys.is_empty());
        assert!(session.typed_pairs.is_empty());
    }
    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .unwrap();
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
    assert!(session.store.consumed_receipts.is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());
    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    assert_eq!(session.store.provenance().len(), 1);
    let fact = &session.store.facts()[0];
    let canonical_key = FactKey::new(
        fact.lower(),
        fact.upper(),
        session.store.comparisons.clone(),
    );
    assert_eq!(
        session.store.canonical.get(&canonical_key),
        Some(&fact.id())
    );
    if reported {
        assert!(matches!(
            session.store.term_view(fact.lower()),
            Ok(TermView::Leaf(Leaf::IntPositive))
        ));
        assert_eq!(session.errors.len(), 1);
        assert_eq!(session.reported_errors.len(), 1);
    }
    assert_eq!(session.store.provenance()[0].fact(), fact.id());
    assert_eq!(session.store.consumed_receipts.len(), 1);
    assert!(session.store.consumed_receipts.contains(&receipt_serial));
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_uses[0].use_id, route_id);
    assert_eq!(session.routed_uses[0].fact, Some(fact.id()));
    assert_eq!(session.routed_use_positions.len(), 1);
    assert!(session.routed_use_positions.contains(&route_id));
}

#[test]
fn f5c_incoming_journal_typed_pair_keys_growth_rolls_back_and_retries() {
    check_journal_key_changed_reserve(false);
}

#[test]
fn f5c_incoming_journal_reported_error_keys_growth_rolls_back_and_retries() {
    check_journal_key_changed_reserve(true);
}

#[test]
fn f5c_incoming_journal_seen_partial_setup_samples_before_rollback() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-journal-seen-partial",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let before = RouteCheckpoint::capture(&session);
    let events = session.incoming_route_sample_attempts;
    let outer = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    let resource_samples = session.resource_boundary_samples;
    let baseline = &session.resource_ledger;
    let mut retained = (
        baseline.semantic_arena_retained_bytes,
        baseline.inference_session_retained_bytes,
    );
    let mut peaks = (
        baseline.semantic_arena_peak_bytes,
        baseline.inference_session_peak_bytes,
    );
    let finish_bytes = baseline.finish_output_retained_bytes;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::EffectBounds);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    let trace = incoming_sample_trace::finish("journal-seen-partial", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(trace.matched_events, 2);
    assert_eq!(trace.event_samples, 2);
    assert_eq!(trace.samples, 3);
    assert_eq!(trace.completed_events.len(), 2);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    for (event, lane) in trace
        .completed_events
        .iter()
        .zip(["value_row_seen", "effect_row_seen"])
    {
        assert_eq!(
            (event.owner.as_str(), event.lane.as_str()),
            ("journal", lane)
        );
        assert_eq!(event.old_capacity, 0);
        assert!(event.new_capacity > 0);
        let delta = event.new_capacity * std::mem::size_of::<u32>();
        retained.0 += delta;
        retained.1 += delta;
        peaks.0 = peaks.0.max(retained.0);
        peaks.1 = peaks.1.max(retained.1 + finish_bytes);
        assert_eq!(
            (
                event.sample.semantic_retained_bytes,
                event.sample.session_retained_bytes
            ),
            retained
        );
        assert_eq!(
            (
                event.sample.semantic_peak_bytes,
                event.sample.session_peak_bytes
            ),
            peaks
        );
    }
    before.assert_restored(&session);
    let journal = session.route_journal_spare.as_ref().unwrap();
    assert_eq!(
        journal.value_row_seen.capacity(),
        trace.completed_events[0].new_capacity
    );
    assert_eq!(
        journal.effect_row_seen.capacity(),
        trace.completed_events[1].new_capacity
    );
    assert!(journal.value_row_seen.is_empty());
    assert!(journal.effect_row_seen.is_empty());
    let post = &trace.completed_named_samples["post-rollback"][0];
    let (independent, nested) =
        independent_post_rollback_value_row_resources(&session, peaks.0, peaks.1);
    assert_eq!(
        (post.semantic_retained_bytes, post.session_retained_bytes),
        (
            independent.semantic_arena_retained_bytes,
            independent.inference_session_retained_bytes
        )
    );
    assert_eq!(post.nested_bound_bytes, nested.total_bound_bytes());
    assert_eq!((post.semantic_peak_bytes, post.session_peak_bytes), peaks);
    assert_eq!(session.resource_ledger.semantic_arena_peak_bytes, peaks.0);
    assert_eq!(
        session.resource_ledger.inference_session_peak_bytes,
        peaks.1
    );
    assert_eq!(
        (
            session.resource_ledger.semantic_arena_retained_bytes,
            session.resource_ledger.inference_session_retained_bytes
        ),
        (post.semantic_retained_bytes, post.session_retained_bytes)
    );
    assert_eq!(
        (
            session.execution_counters.semantic_arena_peak_bytes,
            session.execution_counters.inference_session_peak_bytes
        ),
        peaks
    );
    assert_eq!(session.incoming_route_sample_attempts, events + 3);
    assert_eq!(session.incoming_post_rollback_sample_attempts, outer + 1);
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);
    assert_eq!(session.resource_boundary_samples, resource_samples + 3);
    assert_eq!(
        session.execution_counters.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
        session.resource_ledger.inference_session_retained_bytes
    );
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
    session.route_incoming(&route_id).unwrap();
}

#[test]
fn f5c_incoming_journal_seen_unchanged_failure_skips_outer_sample() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-journal-seen-unchanged",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let events = session.incoming_route_sample_attempts;
    let outer = session.incoming_post_rollback_sample_attempts;
    inject_next_f5b_reserve_failure(F5bCapacityLane::ValueBounds);
    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(session.incoming_route_sample_attempts, events);
    assert_eq!(session.incoming_post_rollback_sample_attempts, outer);
}

#[test]
fn f5c_incoming_journal_value_seen_changed_failure_samples_once_after_setup() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-journal-value-seen-failure",
    ));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let events = session.incoming_route_sample_attempts;
    let outer = session.incoming_post_rollback_sample_attempts;
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ValueBounds);
    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert!(
        session
            .route_journal_spare
            .as_ref()
            .unwrap()
            .value_row_seen
            .capacity()
            > 0
    );
    assert_eq!(session.incoming_route_sample_attempts, events + 2);
    assert_eq!(session.incoming_post_rollback_sample_attempts, outer + 1);
}

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
    let diagnostic_edges: usize = session
        .typed_pairs
        .values()
        .map(|memo| match memo {
            TypedPairMemo::Value { children, .. } => {
                children.capacity() * std::mem::size_of::<DiagnosticEdge>()
            }
            TypedPairMemo::Effect => 0,
        })
        .sum();
    assert_eq!(session.typed_pair_payload_bytes, diagnostic_edges);
    assert_eq!(
        session.independent_nested_capacities.diagnostic_edges,
        diagnostic_edges
    );
    nested.diagnostic_edges = diagnostic_edges;
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

#[derive(Clone, Copy)]
enum IncomingRouteReserveLane {
    TypedPairs,
    TypedWorklist,
    DiagnosticEdges,
    Delta,
    DeltaIndices,
    ReverseOffsets,
    ReverseCursors,
    ReverseEdges,
    BucketHeads,
    BucketTails,
    BucketCandidates,
    DfsStack,
    FinishOrder,
    SccIndices,
    SccNodes,
    SccOffsets,
    SccPendingChildren,
    SccWorklist,
    NodeWitnesses,
}

fn check_incoming_route_changed_reserve(lane: IncomingRouteReserveLane) {
    let (module_name, trace_name, lane_name, injected_lane, slot_size) = match lane {
        IncomingRouteReserveLane::TypedPairs => (
            "f5c-typed-pairs-route",
            "typed-pairs-route",
            "TypedPairs",
            F5bCapacityLane::TypedPairs,
            std::mem::size_of::<(TypedPairKey, TypedPairMemo)>(),
        ),
        IncomingRouteReserveLane::TypedWorklist => (
            "f5c-typed-worklist-route",
            "typed-worklist-route",
            "TypedWorklist",
            F5bCapacityLane::TypedWorklist,
            std::mem::size_of::<TypedWorkItem>(),
        ),
        IncomingRouteReserveLane::DiagnosticEdges => (
            "f5c-diagnostic-edges-route",
            "diagnostic-edges-route",
            "DiagnosticEdges",
            F5bCapacityLane::DiagnosticEdges,
            std::mem::size_of::<DiagnosticEdge>(),
        ),
        IncomingRouteReserveLane::Delta => (
            "f5c-diagnostic-delta-route",
            "diagnostic-delta-route",
            "DiagnosticDelta",
            F5bCapacityLane::DiagnosticDelta,
            std::mem::size_of::<CanonicalValuePairKey>(),
        ),
        IncomingRouteReserveLane::DeltaIndices => (
            "f5c-diagnostic-delta-indices-route",
            "diagnostic-delta-indices-route",
            "DiagnosticDeltaIndices",
            F5bCapacityLane::DiagnosticDeltaIndices,
            std::mem::size_of::<(CanonicalValuePairKey, usize)>(),
        ),
        IncomingRouteReserveLane::ReverseOffsets => (
            "f5c-diagnostic-reverse-offsets-route",
            "diagnostic-reverse-offsets-route",
            "DiagnosticReverseOffsets",
            F5bCapacityLane::DiagnosticReverseOffsets,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::ReverseCursors => (
            "f5c-diagnostic-reverse-cursors-route",
            "diagnostic-reverse-cursors-route",
            "DiagnosticReverseCursors",
            F5bCapacityLane::DiagnosticReverseCursors,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::ReverseEdges => (
            "f5c-diagnostic-reverse-edges-route",
            "diagnostic-reverse-edges-route",
            "DiagnosticReverseEdges",
            F5bCapacityLane::DiagnosticReverseEdges,
            std::mem::size_of::<DiagnosticReverseEdge>(),
        ),
        IncomingRouteReserveLane::BucketHeads => (
            "f5c-diagnostic-bucket-heads-route",
            "diagnostic-bucket-heads-route",
            "DiagnosticBucketHeads",
            F5bCapacityLane::DiagnosticBucketHeads,
            std::mem::size_of::<Option<usize>>(),
        ),
        IncomingRouteReserveLane::BucketTails => (
            "f5c-diagnostic-bucket-tails-route",
            "diagnostic-bucket-tails-route",
            "DiagnosticBucketTails",
            F5bCapacityLane::DiagnosticBucketTails,
            std::mem::size_of::<Option<usize>>(),
        ),
        IncomingRouteReserveLane::BucketCandidates => (
            "f5c-diagnostic-bucket-candidates-route",
            "diagnostic-bucket-candidates-route",
            "DiagnosticBucketCandidates",
            F5bCapacityLane::DiagnosticBucketCandidates,
            std::mem::size_of::<DiagnosticBucketCandidate>(),
        ),
        IncomingRouteReserveLane::DfsStack => (
            "f5c-diagnostic-dfs-stack-route",
            "diagnostic-dfs-stack-route",
            "DiagnosticDfsStack",
            F5bCapacityLane::DiagnosticDfsStack,
            std::mem::size_of::<(usize, usize)>(),
        ),
        IncomingRouteReserveLane::FinishOrder => (
            "f5c-diagnostic-finish-order-route",
            "diagnostic-finish-order-route",
            "DiagnosticFinishOrder",
            F5bCapacityLane::DiagnosticFinishOrder,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::SccIndices => (
            "f5c-diagnostic-scc-indices-route",
            "diagnostic-scc-indices-route",
            "DiagnosticSccIndices",
            F5bCapacityLane::DiagnosticSccIndices,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::SccNodes => (
            "f5c-diagnostic-scc-nodes-route",
            "diagnostic-scc-nodes-route",
            "DiagnosticSccNodes",
            F5bCapacityLane::DiagnosticSccNodes,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::SccOffsets => (
            "f5c-diagnostic-scc-offsets-route",
            "diagnostic-scc-offsets-route",
            "DiagnosticSccOffsets",
            F5bCapacityLane::DiagnosticSccOffsets,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::SccPendingChildren => (
            "f5c-diagnostic-scc-pending-children-route",
            "diagnostic-scc-pending-children-route",
            "DiagnosticSccPendingChildren",
            F5bCapacityLane::DiagnosticSccPendingChildren,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::SccWorklist => (
            "f5c-diagnostic-scc-worklist-route",
            "diagnostic-scc-worklist-route",
            "DiagnosticSccWorklist",
            F5bCapacityLane::DiagnosticSccWorklist,
            std::mem::size_of::<usize>(),
        ),
        IncomingRouteReserveLane::NodeWitnesses => (
            "f5c-diagnostic-node-witnesses-route",
            "diagnostic-node-witnesses-route",
            "DiagnosticNodeWitnesses",
            F5bCapacityLane::DiagnosticNodeWitnesses,
            std::mem::size_of::<Option<DiagnosticWitness>>(),
        ),
    };
    let batch = collect(module("my source = 1; my sink = source", module_name));
    let route_id = batch.definition_uses()[0].id.clone();
    let mut session = InferenceSession::new(batch);
    let draft = GeneralizationDraft {
        quantifier_count: 1,
        recursive_bounds: Vec::new(),
        predicate: if matches!(
            lane,
            IncomingRouteReserveLane::DiagnosticEdges
                | IncomingRouteReserveLane::ReverseEdges
                | IncomingRouteReserveLane::BucketHeads
                | IncomingRouteReserveLane::BucketTails
                | IncomingRouteReserveLane::BucketCandidates
        ) {
            F5cPositive::Union(vec![
                F5cPositive::Int,
                F5cPositive::Function {
                    argument: Box::new(F5cNegative::Top),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Quantified(0)),
                },
            ])
        } else {
            F5cPositive::Quantified(0)
        },
    };
    let finalized = InferenceSession::finalize_generalization_draft(
        session.finalization.as_mut().unwrap(),
        &draft,
        false,
    )
    .unwrap();
    let target = session.batch.definition_uses()[0].target.ordinal() as usize;
    let scheme = finalized.into_parts().0;
    let union_fixture = matches!(
        lane,
        IncomingRouteReserveLane::DiagnosticEdges
            | IncomingRouteReserveLane::ReverseEdges
            | IncomingRouteReserveLane::BucketHeads
            | IncomingRouteReserveLane::BucketTails
            | IncomingRouteReserveLane::BucketCandidates
    );
    if union_fixture {
        let view = session
            .finalization
            .as_ref()
            .unwrap()
            .scheme_view(&scheme)
            .unwrap();
        let PositiveValueView::Union(children) = view.positive_value(view.predicate()).unwrap()
        else {
            panic!("finalized predicate must be a normalized Union");
        };
        assert!(!children.is_empty());
        assert!(matches!(
            view.positive_value(children[0]).unwrap(),
            PositiveValueView::Int
        ));
    }
    session.schemes[target] = Some(scheme);
    if union_fixture {
        let use_row =
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
        let occurrence =
            ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 204);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session
            .constrain_live_value(
                CanonicalValuePairKey {
                    lower: ValueEndpointKey::ValueRow(use_row),
                    upper: ValueEndpointKey::NegativeFunction(negative_function),
                },
                &occurrence,
                &cause,
            )
            .unwrap();
    }
    if !matches!(lane, IncomingRouteReserveLane::TypedPairs) {
        session.typed_pairs.try_reserve(1).unwrap();
    }
    match lane {
        IncomingRouteReserveLane::Delta => {
            session.diagnostic_delta_indices.try_reserve(1).unwrap();
        }
        IncomingRouteReserveLane::DeltaIndices => {
            session.diagnostic_delta.try_reserve(1).unwrap();
        }
        IncomingRouteReserveLane::ReverseOffsets | IncomingRouteReserveLane::ReverseCursors => {
            session.diagnostic_delta.try_reserve(1).unwrap();
            session.diagnostic_delta_indices.try_reserve(1).unwrap();
        }
        _ => {
            session.diagnostic_delta.try_reserve(1).unwrap();
            session.diagnostic_delta_indices.try_reserve(1).unwrap();
            session.diagnostic_reverse_offsets.try_reserve(2).unwrap();
            session.diagnostic_reverse_cursors.try_reserve(1).unwrap();
            session.diagnostic_dfs_stack.try_reserve(1).unwrap();
            session.diagnostic_finish_order.try_reserve(1).unwrap();
            session.diagnostic_scc_indices.try_reserve(1).unwrap();
            session.diagnostic_scc_nodes.try_reserve(1).unwrap();
            session.diagnostic_scc_offsets.try_reserve(2).unwrap();
            session
                .diagnostic_scc_pending_children
                .try_reserve(1)
                .unwrap();
            session.diagnostic_scc_worklist.try_reserve(1).unwrap();
            session.diagnostic_bucket_heads.try_reserve(1).unwrap();
            session.diagnostic_bucket_tails.try_reserve(1).unwrap();
            session.diagnostic_node_witnesses.try_reserve(1).unwrap();
        }
    }
    session.begin_route_transaction().unwrap();
    session.rollback_route_transaction().unwrap();
    session
        .route_journal_spare
        .as_mut()
        .unwrap()
        .typed_pair_keys
        .try_reserve(1)
        .unwrap();
    match lane {
        IncomingRouteReserveLane::TypedPairs => {
            assert!(session.typed_pairs.is_empty());
            session.typed_pairs = HashMap::new();
            assert_eq!(session.typed_pairs.capacity(), 0);
        }
        IncomingRouteReserveLane::TypedWorklist => session.typed_worklist = VecDeque::new(),
        IncomingRouteReserveLane::DiagnosticEdges => {}
        IncomingRouteReserveLane::Delta => {
            session.diagnostic_delta = Vec::new();
            assert_eq!(session.diagnostic_delta.capacity(), 0);
            assert!(session.diagnostic_delta_indices.capacity() > 0);
        }
        IncomingRouteReserveLane::DeltaIndices => {
            session.diagnostic_delta_indices = HashMap::new();
            assert_eq!(session.diagnostic_delta_indices.capacity(), 0);
            assert!(session.diagnostic_delta.capacity() > 0);
        }
        IncomingRouteReserveLane::ReverseOffsets => {
            session.diagnostic_reverse_offsets = Vec::new();
            assert_eq!(session.diagnostic_reverse_offsets.capacity(), 0);
            assert!(session.diagnostic_delta.capacity() > 0);
            assert!(session.diagnostic_delta_indices.capacity() > 0);
        }
        IncomingRouteReserveLane::ReverseCursors => {
            let required_offset_count = 2; // one diagnostic pair plus its terminal offset
            session
                .diagnostic_reverse_offsets
                .try_reserve(required_offset_count)
                .unwrap();
            session.diagnostic_reverse_cursors = Vec::new();
            assert_eq!(session.diagnostic_reverse_cursors.capacity(), 0);
            assert!(session.diagnostic_reverse_offsets.capacity() >= required_offset_count);
            assert!(session.diagnostic_delta.capacity() > 0);
            assert!(session.diagnostic_delta_indices.capacity() > 0);
        }
        IncomingRouteReserveLane::ReverseEdges => session.diagnostic_reverse_edges = Vec::new(),
        IncomingRouteReserveLane::BucketHeads => session.diagnostic_bucket_heads = Vec::new(),
        IncomingRouteReserveLane::BucketTails => session.diagnostic_bucket_tails = Vec::new(),
        IncomingRouteReserveLane::BucketCandidates => {
            session.diagnostic_bucket_candidates = Vec::new()
        }
        IncomingRouteReserveLane::DfsStack => session.diagnostic_dfs_stack = Vec::new(),
        IncomingRouteReserveLane::FinishOrder => session.diagnostic_finish_order = Vec::new(),
        IncomingRouteReserveLane::SccIndices => session.diagnostic_scc_indices = Vec::new(),
        IncomingRouteReserveLane::SccNodes => session.diagnostic_scc_nodes = Vec::new(),
        IncomingRouteReserveLane::SccOffsets => session.diagnostic_scc_offsets = Vec::new(),
        IncomingRouteReserveLane::SccPendingChildren => {
            session.diagnostic_scc_pending_children = Vec::new()
        }
        IncomingRouteReserveLane::SccWorklist => session.diagnostic_scc_worklist = VecDeque::new(),
        IncomingRouteReserveLane::NodeWitnesses => session.diagnostic_node_witnesses = Vec::new(),
    }
    if !matches!(lane, IncomingRouteReserveLane::TypedPairs) {
        assert!(session.typed_pairs.capacity() > session.typed_pairs.len());
    }
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
    let receipt_serial = session.store.next_receipt;
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(injected_lane);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    before.assert_restored(&session);
    let trace = incoming_sample_trace::finish(trace_name, 1);
    assert_eq!(trace.attempts, 1);
    let summary_owner = if matches!(lane, IncomingRouteReserveLane::DiagnosticEdges) {
        "typed-pair"
    } else {
        "typed-route"
    };
    assert_eq!(
        trace
            .event_lanes
            .get(&(summary_owner.into(), lane_name.into())),
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
        .find(|(_, event)| {
            event.lane == lane_name
                && if matches!(lane, IncomingRouteReserveLane::DiagnosticEdges) {
                    event.owner.starts_with("typed-pair-")
                } else {
                    event.owner == "typed-route"
                }
        })
        .expect("changed incoming-route reserve must have a completed sample");
    assert!(position > 0);
    let previous = &trace.completed_events[position - 1];
    if matches!(lane, IncomingRouteReserveLane::DiagnosticEdges) {
        assert!(event.owner.contains("CanonicalValuePairKey"));
    }
    assert!(previous.sample.semantic_retained_bytes > baseline_semantic);
    assert!(previous.sample.session_retained_bytes > baseline_session);
    assert!(trace.completed_events[..position].iter().any(|earlier| {
        earlier.owner == "typed-route"
            && earlier.lane == "FreshValueBounds"
            && earlier.old_capacity < earlier.new_capacity
    }));
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(slot_size)
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
    let target_capacity = match lane {
        IncomingRouteReserveLane::TypedPairs => Some(session.typed_pairs.capacity()),
        IncomingRouteReserveLane::TypedWorklist => Some(session.typed_worklist.capacity()),
        IncomingRouteReserveLane::DiagnosticEdges => None,
        IncomingRouteReserveLane::Delta => Some(session.diagnostic_delta.capacity()),
        IncomingRouteReserveLane::DeltaIndices => Some(session.diagnostic_delta_indices.capacity()),
        IncomingRouteReserveLane::ReverseOffsets => {
            Some(session.diagnostic_reverse_offsets.capacity())
        }
        IncomingRouteReserveLane::ReverseCursors => {
            Some(session.diagnostic_reverse_cursors.capacity())
        }
        IncomingRouteReserveLane::ReverseEdges => Some(session.diagnostic_reverse_edges.capacity()),
        IncomingRouteReserveLane::BucketHeads => Some(session.diagnostic_bucket_heads.capacity()),
        IncomingRouteReserveLane::BucketTails => Some(session.diagnostic_bucket_tails.capacity()),
        IncomingRouteReserveLane::BucketCandidates => {
            Some(session.diagnostic_bucket_candidates.capacity())
        }
        IncomingRouteReserveLane::DfsStack => Some(session.diagnostic_dfs_stack.capacity()),
        IncomingRouteReserveLane::FinishOrder => Some(session.diagnostic_finish_order.capacity()),
        IncomingRouteReserveLane::SccIndices => Some(session.diagnostic_scc_indices.capacity()),
        IncomingRouteReserveLane::SccNodes => Some(session.diagnostic_scc_nodes.capacity()),
        IncomingRouteReserveLane::SccOffsets => Some(session.diagnostic_scc_offsets.capacity()),
        IncomingRouteReserveLane::SccPendingChildren => {
            Some(session.diagnostic_scc_pending_children.capacity())
        }
        IncomingRouteReserveLane::SccWorklist => Some(session.diagnostic_scc_worklist.capacity()),
        IncomingRouteReserveLane::NodeWitnesses => {
            Some(session.diagnostic_node_witnesses.capacity())
        }
    };
    if let Some(target_capacity) = target_capacity {
        assert_eq!(target_capacity, event.new_capacity);
    }
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
    if union_fixture {
        assert!(matches!(
            session.store.term_view(fact.lower()),
            Ok(TermView::Leaf(Leaf::IntPositive))
        ));
    }
    let provenance = &session.store.provenance()[0];
    assert_eq!(provenance.fact(), fact.id());
    assert_eq!(session.store.consumed_receipts.len(), 1);
    assert!(session.store.consumed_receipts.contains(&receipt_serial));
    assert_eq!(session.routed_uses[0].use_id, route_id);
    assert_eq!(session.routed_uses[0].fact, Some(fact.id()));
    assert!(session.routed_use_positions.contains(&route_id));
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_use_positions.len(), 1);
}

#[test]
fn f5c_incoming_typed_pairs_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::TypedPairs);
}

#[test]
fn f5c_incoming_typed_worklist_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::TypedWorklist);
}

#[test]
fn f5c_incoming_diagnostic_edges_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::DiagnosticEdges);
}

#[test]
fn f5c_incoming_diagnostic_delta_indices_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::DeltaIndices);
}

#[test]
fn f5c_incoming_diagnostic_delta_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::Delta);
}

#[test]
fn f5c_incoming_diagnostic_reverse_offsets_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::ReverseOffsets);
}

#[test]
fn f5c_incoming_diagnostic_reverse_cursors_growth_samples_before_rollback_and_retries() {
    check_incoming_route_changed_reserve(IncomingRouteReserveLane::ReverseCursors);
}

#[test]
fn f5c_incoming_diagnostic_remaining_scratch_growth_samples_before_rollback_and_retries() {
    for lane in [
        IncomingRouteReserveLane::DfsStack,
        IncomingRouteReserveLane::FinishOrder,
        IncomingRouteReserveLane::SccIndices,
        IncomingRouteReserveLane::SccNodes,
        IncomingRouteReserveLane::SccOffsets,
        IncomingRouteReserveLane::SccPendingChildren,
        IncomingRouteReserveLane::SccWorklist,
        IncomingRouteReserveLane::NodeWitnesses,
        IncomingRouteReserveLane::ReverseEdges,
        IncomingRouteReserveLane::BucketHeads,
        IncomingRouteReserveLane::BucketTails,
        IncomingRouteReserveLane::BucketCandidates,
    ] {
        check_incoming_route_changed_reserve(lane);
    }
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
fn f5c_incoming_extrusion_stack_growth_samples_before_rollback_and_retries() {
    let (mut session, routes) =
        f5c_shared_closed_incoming_fixture("f5c-extrusion-stack-event-sample");
    session.extrusion_stack = Vec::new();
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();

    let route_id = routes[0].clone();
    let before = RouteCheckpoint::capture(&session);
    let old_capacity = session.extrusion_stack.capacity();
    assert_eq!(old_capacity, 0);
    let old_value_levels_bytes = session.value_levels.capacity() * std::mem::size_of::<u32>();
    let old_nested_bound_bytes = session.independent_nested_capacities.total_bound_bytes();
    let old_semantic_retained = session.resource_ledger.semantic_arena_retained_bytes;
    let old_session_retained = session.resource_ledger.inference_session_retained_bytes;
    let old_semantic_peak = session.execution_counters.semantic_arena_peak_bytes;
    let old_session_peak = session.execution_counters.inference_session_peak_bytes;
    let finish_output_bytes = session.resource_ledger.finish_output_retained_bytes;
    let route_attempts = session.incoming_route_sample_attempts;
    let resource_samples = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    let receipt_serial = session.store.next_receipt;
    F5C_LAST_TYPED_ROUTE_CAPACITY_EVENT_LANE.with(|observed| observed.set(None));
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::ExtrusionStack);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|injected| injected.get()),
        None
    );
    before.assert_restored(&session);
    assert!(session.extrusion_stack.is_empty());
    assert!(session.extrusion_stack.capacity() > old_capacity);
    assert_eq!(
        F5C_LAST_TYPED_ROUTE_CAPACITY_EVENT_LANE.with(|observed| observed.get()),
        Some(F5bCapacityLane::ExtrusionStack)
    );

    let trace = incoming_sample_trace::finish("extrusion-stack-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "ExtrusionStack".into())),
        Some(&1)
    );
    assert_eq!(
        session.incoming_route_sample_attempts,
        route_attempts + trace.samples
    );
    assert_eq!(
        session.resource_boundary_samples,
        resource_samples + trace.samples
    );
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);

    let (event_position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "typed-route" && event.lane == "ExtrusionStack")
        .expect("extrusion-stack growth must have a completed event sample");
    assert_eq!(event_position + 1, trace.completed_events.len());
    assert_eq!(event.old_capacity, old_capacity);
    assert_eq!(event.new_capacity, session.extrusion_stack.capacity());
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<ExtrusionEndpoint>())
        .unwrap();
    assert!(delta > 0);
    let previous = event_position
        .checked_sub(1)
        .map(|position| &trace.completed_events[position].sample);
    let (
        previous_value_levels,
        previous_nested,
        previous_semantic,
        previous_session,
        previous_semantic_peak,
        previous_session_peak,
    ) = previous.map_or(
        (
            old_value_levels_bytes,
            old_nested_bound_bytes,
            old_semantic_retained,
            old_session_retained,
            old_semantic_peak,
            old_session_peak,
        ),
        |sample| {
            (
                sample.value_levels_bytes,
                sample.nested_bound_bytes,
                sample.semantic_retained_bytes,
                sample.session_retained_bytes,
                sample.semantic_peak_bytes,
                sample.session_peak_bytes,
            )
        },
    );
    assert_eq!(event.sample.value_levels_bytes, previous_value_levels);
    assert_eq!(event.sample.nested_bound_bytes, previous_nested);
    let expected_semantic_retained = previous_semantic + delta;
    let expected_session_retained = previous_session + delta;
    let expected_semantic_peak = previous_semantic_peak.max(expected_semantic_retained);
    let expected_session_peak =
        previous_session_peak.max(expected_session_retained + finish_output_bytes);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        expected_semantic_retained
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        expected_session_retained
    );
    assert_eq!(event.sample.semantic_peak_bytes, expected_semantic_peak);
    assert_eq!(event.sample.session_peak_bytes, expected_session_peak);

    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("exactly one completed post-rollback sample");
    assert_eq!(post.value_levels_bytes, event.sample.value_levels_bytes);
    assert_eq!(post.nested_bound_bytes, event.sample.nested_bound_bytes);
    assert!(post.semantic_retained_bytes < event.sample.semantic_retained_bytes);
    assert!(post.session_retained_bytes < event.sample.session_retained_bytes);
    assert_eq!(post.semantic_peak_bytes, event.sample.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, event.sample.session_peak_bytes);

    let (independent, independent_nested) = independent_post_rollback_value_row_resources(
        &session,
        expected_semantic_peak,
        expected_session_peak,
    );
    assert_eq!(session.independent_nested_capacities, independent_nested);
    assert_eq!(
        post.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(
        post.nested_bound_bytes,
        independent_nested.total_bound_bytes()
    );
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
        session.execution_counters.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
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
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.store.consumed_receipts.is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    let fact = &session.store.facts()[0];
    assert!(session.store.canonical.iter().any(|(key, canonical)| {
        *canonical == fact.id() && key.lower == fact.lower() && key.upper == fact.upper()
    }));
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.store.provenance()[0].fact(), fact.id());
    assert_eq!(session.store.consumed_receipts.len(), 1);
    assert!(session.store.consumed_receipts.contains(&receipt_serial));
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_uses[0].use_id, route_id);
    assert_eq!(session.routed_uses[0].fact, Some(fact.id()));
    assert_eq!(session.routed_use_positions.len(), 1);
    assert!(session.routed_use_positions.contains(&route_id));
}

#[test]
fn f5c_incoming_fresh_value_bounds_growth_samples_before_rollback_and_retries() {
    let batch = collect(module(
        "my source = 1; my sink = source",
        "f5c-fresh-outer-event-sample",
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
    while session.bounds.len() < session.bounds.capacity() {
        session.fresh_value_at_level(1).unwrap();
    }
    session
        .sample_f4_resources(ResourceBoundary::IncomingRoute)
        .unwrap();

    let before = RouteCheckpoint::capture(&session);
    let old_bounds_len = session.bounds.len();
    let old_bounds_capacity = session.bounds.capacity();
    let old_value_levels_bytes = session.value_levels.capacity() * std::mem::size_of::<u32>();
    let old_nested_bound_bytes = session.independent_nested_capacities.total_bound_bytes();
    let old_semantic_retained = session.resource_ledger.semantic_arena_retained_bytes;
    let old_session_retained = session.resource_ledger.inference_session_retained_bytes;
    let old_semantic_peak = session.execution_counters.semantic_arena_peak_bytes;
    let old_session_peak = session.execution_counters.inference_session_peak_bytes;
    let finish_output_bytes = session.resource_ledger.finish_output_retained_bytes;
    let route_attempts = session.incoming_route_sample_attempts;
    let resource_samples = session.resource_boundary_samples;
    let post_attempts = session.incoming_post_rollback_sample_attempts;
    let post_samples = session.incoming_post_rollback_samples;
    let receipt_serial = session.store.next_receipt;
    F5C_LAST_TYPED_ROUTE_CAPACITY_EVENT_LANE.with(|observed| observed.set(None));
    incoming_sample_trace::start();
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::FreshValueBounds);

    assert_eq!(
        session.route_incoming(&route_id),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|injected| injected.get()),
        None
    );
    before.assert_restored(&session);
    assert_eq!(session.bounds.len(), old_bounds_len);
    assert!(session.bounds.capacity() > old_bounds_capacity);
    assert_eq!(
        F5C_LAST_TYPED_ROUTE_CAPACITY_EVENT_LANE.with(|observed| observed.get()),
        Some(F5bCapacityLane::FreshValueBounds)
    );

    let trace = incoming_sample_trace::finish("fresh-value-bounds-route", 1);
    assert_eq!(trace.attempts, 1);
    assert_eq!(trace.matched_events, trace.event_samples);
    assert_eq!(trace.completed_events.len(), trace.event_samples);
    assert_eq!(
        trace.named_samples,
        [("post-rollback".into(), 1)].into_iter().collect()
    );
    assert_eq!(trace.samples, trace.event_samples + 1);
    assert_eq!(
        trace
            .event_lanes
            .get(&("typed-route".into(), "FreshValueBounds".into())),
        Some(&1)
    );
    assert_eq!(
        session.incoming_route_sample_attempts,
        route_attempts + trace.samples
    );
    assert_eq!(
        session.resource_boundary_samples,
        resource_samples + trace.samples
    );
    assert_eq!(
        session.incoming_post_rollback_sample_attempts,
        post_attempts + 1
    );
    assert_eq!(session.incoming_post_rollback_samples, post_samples + 1);

    let (event_position, event) = trace
        .completed_events
        .iter()
        .enumerate()
        .find(|(_, event)| event.owner == "typed-route" && event.lane == "FreshValueBounds")
        .expect("fresh value-bounds growth must have a completed event sample");
    assert_eq!(event.old_capacity, old_bounds_capacity);
    assert_eq!(event.new_capacity, session.bounds.capacity());
    let delta = (event.new_capacity - event.old_capacity)
        .checked_mul(std::mem::size_of::<VariableBounds>())
        .unwrap();
    assert!(delta > 0);
    let previous = event_position
        .checked_sub(1)
        .map(|position| &trace.completed_events[position].sample);
    let (
        previous_value_levels,
        previous_nested,
        previous_semantic,
        previous_session,
        previous_semantic_peak,
        previous_session_peak,
    ) = previous.map_or(
        (
            old_value_levels_bytes,
            old_nested_bound_bytes,
            old_semantic_retained,
            old_session_retained,
            old_semantic_peak,
            old_session_peak,
        ),
        |sample| {
            (
                sample.value_levels_bytes,
                sample.nested_bound_bytes,
                sample.semantic_retained_bytes,
                sample.session_retained_bytes,
                sample.semantic_peak_bytes,
                sample.session_peak_bytes,
            )
        },
    );
    assert_eq!(event.sample.value_levels_bytes, previous_value_levels);
    assert_eq!(event.sample.nested_bound_bytes, previous_nested);
    let expected_semantic_retained = previous_semantic + delta;
    let expected_session_retained = previous_session + delta;
    let expected_semantic_peak = previous_semantic_peak.max(expected_semantic_retained);
    let expected_session_peak =
        previous_session_peak.max(expected_session_retained + finish_output_bytes);
    assert_eq!(
        event.sample.semantic_retained_bytes,
        expected_semantic_retained
    );
    assert_eq!(
        event.sample.session_retained_bytes,
        expected_session_retained
    );
    assert_eq!(event.sample.semantic_peak_bytes, expected_semantic_peak);
    assert_eq!(event.sample.session_peak_bytes, expected_session_peak);

    let post = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("exactly one completed post-rollback sample");
    assert_eq!(post.value_levels_bytes, event.sample.value_levels_bytes);
    assert_eq!(post.nested_bound_bytes, event.sample.nested_bound_bytes);
    assert_eq!(
        post.semantic_retained_bytes,
        event.sample.semantic_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        event.sample.session_retained_bytes
    );
    assert_eq!(post.semantic_peak_bytes, event.sample.semantic_peak_bytes);
    assert_eq!(post.session_peak_bytes, event.sample.session_peak_bytes);

    let (independent, independent_nested) = independent_post_rollback_value_row_resources(
        &session,
        expected_semantic_peak,
        expected_session_peak,
    );
    assert_eq!(session.independent_nested_capacities, independent_nested);
    assert_eq!(
        post.semantic_retained_bytes,
        independent.semantic_arena_retained_bytes
    );
    assert_eq!(
        post.session_retained_bytes,
        independent.inference_session_retained_bytes
    );
    assert_eq!(
        post.nested_bound_bytes,
        independent_nested.total_bound_bytes()
    );
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
        session.execution_counters.semantic_arena_retained_bytes,
        post.semantic_retained_bytes
    );
    assert_eq!(
        session.execution_counters.inference_session_retained_bytes,
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
    assert!(session.store.facts().is_empty());
    assert!(session.store.provenance().is_empty());
    assert!(session.store.consumed_receipts.is_empty());
    assert!(session.routed_uses.is_empty());
    assert!(session.routed_use_positions.is_empty());

    session.route_incoming(&route_id).unwrap();
    assert_eq!(session.store.facts().len(), 1);
    let fact = &session.store.facts()[0];
    assert!(session.store.canonical.iter().any(|(key, canonical)| {
        *canonical == fact.id() && key.lower == fact.lower() && key.upper == fact.upper()
    }));
    assert_eq!(session.store.provenance().len(), 1);
    assert_eq!(session.store.provenance()[0].fact(), fact.id());
    assert_eq!(session.store.consumed_receipts.len(), 1);
    assert!(session.store.consumed_receipts.contains(&receipt_serial));
    assert_eq!(session.routed_uses.len(), 1);
    assert_eq!(session.routed_uses[0].use_id, route_id);
    assert_eq!(session.routed_uses[0].fact, Some(fact.id()));
    assert_eq!(session.routed_use_positions.len(), 1);
    assert!(session.routed_use_positions.contains(&route_id));
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
    let old_nested_bound_bytes = session.independent_nested_capacities.total_bound_bytes();
    let old_finish_output_bytes = session.resource_ledger.finish_output_retained_bytes;
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
    let post_rollback = trace
        .completed_named_samples
        .get("post-rollback")
        .and_then(|samples| (samples.len() == 1).then_some(&samples[0]))
        .expect("post-rollback must have one completed sample");
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
    assert_eq!(event.nested_bound_bytes, old_nested_bound_bytes);
    let expected_semantic_peak = old_semantic_peak.max(old_semantic + delta);
    let expected_session_peak = old_session_peak.max(old_session + delta + old_finish_output_bytes);
    assert_eq!(event.semantic_peak_bytes, expected_semantic_peak);
    assert_eq!(event.session_peak_bytes, expected_session_peak);
    assert!(event.semantic_peak_bytes > old_semantic_peak);
    assert!(event.session_peak_bytes > old_session_peak);
    let (independent, independent_nested) = independent_post_rollback_value_row_resources(
        &session,
        expected_semantic_peak,
        expected_session_peak,
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
        session.resource_ledger.semantic_arena_retained_bytes,
        post_rollback.semantic_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_retained_bytes,
        post_rollback.session_retained_bytes
    );
    assert_eq!(
        session.resource_ledger.semantic_arena_peak_bytes,
        post_rollback.semantic_peak_bytes
    );
    assert_eq!(
        session.resource_ledger.inference_session_peak_bytes,
        post_rollback.session_peak_bytes
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
