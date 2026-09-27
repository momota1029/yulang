use super::*;
use crate::f5c_generalization::{F5cTestObservationFailure, F5cTestReserveFailure, F5cWalkTask};

#[test]
fn flat_all_member_candidate_preserves_order_and_indexed_scheme_parity() {
    let batch = || {
        let batch = collect(module(
            "my left = right; my right = left",
            "f5c-flat-all-members",
        ));
        assert_eq!(batch.counters.scc_maximum_component_size, 2);
        batch
    };
    let mut boxed = InferenceSession::new(batch());
    boxed.admit_all_collected_facts().unwrap();
    boxed.execute_scc_plan().unwrap();

    let mut flat = InferenceSession::new(batch());
    flat.flat_candidate_enabled = true;
    flat.ordering_observer = Some(OrderingObserver {
        capacity: 16,
        events: Vec::new(),
        omitted: 0,
    });
    let component = flat
        .batch
        .scc_components_in_dependency_first_order()
        .next()
        .unwrap()
        .clone();
    let members = flat
        .batch
        .scc_component_members(&component)
        .unwrap()
        .to_vec();
    assert_eq!(members.len(), 2);
    let roots: Vec<_> = members
        .iter()
        .map(|member| {
            InferenceSession::verified_scheme_definition(&flat.batch, member)
                .record
                .root
                .clone()
        })
        .collect();
    flat.admit_all_collected_facts().unwrap();
    flat.execute_scc_plan().unwrap();
    assert_eq!(
        boxed
            .execution_counters
            .closed_normalization_word_comparisons,
        2
    );
    assert_eq!(
        flat.execution_counters
            .closed_normalization_word_comparisons,
        boxed
            .execution_counters
            .closed_normalization_word_comparisons
    );
    let mut reversed = InferenceSession::new(collect(module(
        "my right = left; my left = right",
        "f5c-flat-all-members-reversed",
    )));
    reversed.flat_candidate_enabled = true;
    reversed.admit_all_collected_facts().unwrap();
    reversed.execute_scc_plan().unwrap();
    assert_eq!(
        reversed
            .execution_counters
            .closed_normalization_word_comparisons,
        boxed
            .execution_counters
            .closed_normalization_word_comparisons
    );
    assert_eq!(flat.successful_finalizations, 2);
    assert_eq!(flat.drafts.len(), 2);
    assert_eq!(flat.resource_ledger.flat_all_drafts_members, 2);
    assert!(flat.resource_ledger.flat_all_drafts_bytes > 0);
    assert!(flat.resource_ledger.flat_transfer_raw_bytes > 0);
    assert!(
        flat.resource_ledger.flat_transfer_peak_bytes > flat.resource_ledger.flat_all_drafts_bytes
    );
    assert_eq!(flat.resource_ledger.flat_staged_bytes, 0);
    assert_eq!(flat.resource_ledger.flat_indexed_bytes, 0);
    assert!(flat.resource_ledger.flat_source_peak_bytes > 0);
    assert!(
        flat.resource_ledger.flat_source_peak_bytes >= flat.resource_ledger.flat_all_drafts_bytes
    );
    assert!(flat.resource_ledger.flat_normalization_scratch_peak_bytes > 0);
    assert!(
        flat.resource_ledger.flat_normalization_peak_bytes
            > flat.resource_ledger.flat_transfer_peak_bytes
    );
    assert_eq!(
        flat.resource_ledger.semantic_arena_peak_bytes,
        flat.execution_counters.semantic_arena_peak_bytes
    );
    assert_eq!(
        flat.resource_ledger.inference_session_peak_bytes,
        flat.execution_counters.inference_session_peak_bytes
    );
    assert_eq!(
        boxed.schemes.iter().filter(|item| item.is_some()).count(),
        2
    );
    assert_eq!(flat.schemes.iter().filter(|item| item.is_some()).count(), 2);
    let ordering: Vec<_> = flat
        .ordering_observer
        .as_ref()
        .unwrap()
        .events
        .iter()
        .filter(|event| {
            matches!(
                event,
                ExecutionEvent::Drafted(_)
                    | ExecutionEvent::DraftsVisible(_, _)
                    | ExecutionEvent::Installed(_)
            )
        })
        .cloned()
        .collect();
    assert_eq!(
        ordering,
        [
            ExecutionEvent::Drafted(members[0].clone()),
            ExecutionEvent::Drafted(members[1].clone()),
            ExecutionEvent::DraftsVisible(component, 2),
            ExecutionEvent::Installed(roots[0].clone()),
            ExecutionEvent::Installed(roots[1].clone()),
        ]
    );
    for (left, right) in boxed.schemes.iter().zip(&flat.schemes) {
        if let (Some(left), Some(right)) = (left, right) {
            assert!(
                boxed
                    .finalization
                    .as_ref()
                    .unwrap()
                    .scheme_view(left)
                    .unwrap()
                    .alpha_eq(
                        flat.finalization
                            .as_ref()
                            .unwrap()
                            .scheme_view(right)
                            .unwrap()
                    )
            );
        }
    }
    let events = flat.resource_ledger.boundary_order.clone();
    assert_eq!(
        events,
        [
            ResourceBoundary::SourceDrafts,
            ResourceBoundary::AllDrafts,
            ResourceBoundary::IndexedMapping,
            ResourceBoundary::DraftMember,
            ResourceBoundary::IndexedMapping,
            ResourceBoundary::DraftMember,
            ResourceBoundary::SchemeInstall,
            ResourceBoundary::SchemeInstall,
        ]
    );

    let mut failed = InferenceSession::new(batch());
    failed.flat_candidate_enabled = true;
    failed.flat_candidate_failure_after = Some(1);
    failed.admit_all_collected_facts().unwrap();
    assert_eq!(
        failed.execute_scc_plan(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(failed.successful_finalizations, 1);
    assert!(failed.schemes.iter().all(Option::is_none));
    let failed_events = failed.resource_ledger.boundary_order.clone();
    assert_eq!(
        failed_events,
        [
            ResourceBoundary::SourceDrafts,
            ResourceBoundary::AllDrafts,
            ResourceBoundary::IndexedMapping,
            ResourceBoundary::DraftMember,
        ]
    );

    let mut failed_during_batch = InferenceSession::new(batch());
    failed_during_batch.flat_candidate_enabled = true;
    failed_during_batch.flat_candidate_normalization_failure_after = Some(0);
    failed_during_batch.admit_all_collected_facts().unwrap();
    assert_eq!(
        failed_during_batch.execute_scc_plan(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(failed_during_batch.successful_finalizations, 0);
    assert!(failed_during_batch.schemes.iter().all(Option::is_none));
    assert!(failed_during_batch.resource_ledger.flat_source_peak_bytes > 0);
    assert!(failed_during_batch.resource_ledger.flat_transfer_peak_bytes > 0);
    assert!(
        failed_during_batch
            .resource_ledger
            .flat_normalization_peak_bytes
            > 0
    );
}

#[test]
fn flat_batch_precommit_failures_restore_counters_and_publish_no_schemes() {
    let batch = || {
        collect(module(
            "my left = right; my right = left",
            "f5c-flat-precommit",
        ))
    };
    for failure in [
        FlatCandidatePrecommitFailure::LedgerAfterStage,
        FlatCandidatePrecommitFailure::CounterAfterNormalization,
    ] {
        let mut session = InferenceSession::new(batch());
        session.flat_candidate_enabled = true;
        session.flat_candidate_precommit_failure = Some(failure);
        session.admit_all_collected_facts().unwrap();
        let before = session.execution_counters.clone();
        assert_eq!(
            session.execute_scc_plan(),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert!(session.schemes.iter().all(Option::is_none));
        assert_eq!(session.successful_finalizations, 0);
        assert_eq!(
            session.execution_counters.closed_normalized_key_writes,
            before.closed_normalized_key_writes
        );
        assert_eq!(
            session
                .execution_counters
                .closed_normalization_word_comparisons,
            before.closed_normalization_word_comparisons
        );
        assert_eq!(
            session
                .execution_counters
                .closed_normalization_index_requested_slots,
            before.closed_normalization_index_requested_slots
        );
        assert_eq!(
            session
                .execution_counters
                .closed_normalization_index_capacity_growths,
            before.closed_normalization_index_capacity_growths
        );
        assert_eq!(
            session
                .execution_counters
                .closed_normalization_index_peak_bytes,
            before.closed_normalization_index_peak_bytes
        );
        assert_eq!(
            session
                .resource_ledger
                .closed_normalization_index_requested_slots,
            0
        );
        assert_eq!(
            session
                .resource_ledger
                .closed_normalization_index_retained_bytes,
            0
        );
        assert_eq!(
            session
                .resource_ledger
                .closed_normalization_index_peak_bytes,
            0
        );
        assert_eq!(
            session
                .execution_counters
                .generalization_shared_summary_admissions,
            before.generalization_shared_summary_admissions
        );
        assert_eq!(session.resource_ledger.flat_staged_bytes, 0);
        assert_eq!(session.resource_ledger.flat_indexed_bytes, 0);
        assert!(session.resource_ledger.flat_source_peak_bytes > 0);
        assert!(session.resource_ledger.flat_transfer_peak_bytes > 0);
        if failure == FlatCandidatePrecommitFailure::CounterAfterNormalization {
            assert!(session.resource_ledger.flat_normalization_peak_bytes > 0);
            assert!(
                session
                    .resource_ledger
                    .flat_normalization_scratch_peak_bytes
                    > 0
            );
        }
    }

    let mut session = InferenceSession::new(batch());
    session.flat_candidate_enabled = true;
    session.flat_candidate_precommit_failure =
        Some(FlatCandidatePrecommitFailure::LedgerAfterStage);
    session.admit_all_collected_facts().unwrap();
    let previous = (111_111, 222_222, 333_333, 444_444);
    session.resource_ledger.flat_source_peak_bytes = previous.0;
    session.resource_ledger.flat_transfer_peak_bytes = previous.1;
    session.resource_ledger.flat_normalization_peak_bytes = previous.2;
    session
        .resource_ledger
        .flat_normalization_scratch_peak_bytes = previous.3;
    assert_eq!(
        session.execute_scc_plan(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        (
            session.resource_ledger.flat_source_peak_bytes,
            session.resource_ledger.flat_transfer_peak_bytes,
            session.resource_ledger.flat_normalization_peak_bytes,
            session
                .resource_ledger
                .flat_normalization_scratch_peak_bytes,
        ),
        previous
    );
}

#[test]
fn flat_batch_compound_members_keep_boxed_counters_and_indexed_schemes() {
    use crate::f5c_generalization::F5cStagedCandidate;

    fn fixture(reverse: bool) -> (InferenceSession, [u32; 2]) {
        let batch = collect(module("my f = 1", "f5c-flat-compound-batch"));
        let mut session = InferenceSession::new(batch);
        let mut roots = [0; 2];
        for root in &mut roots {
            *root = session.fresh_value_at_level(1).unwrap();
            let relay = session.fresh_value_at_level(1).unwrap();
            let quantified = session.fresh_value_at_level(1).unwrap();
            let first = session.fresh_value_at_level(1).unwrap();
            let second = session.fresh_value_at_level(1).unwrap();
            session.bounds[first as usize]
                .exact_non_variable_lowers
                .push(ValueEndpointKey::IntPositive);
            session.bounds[second as usize]
                .exact_non_variable_uppers
                .push(ValueEndpointKey::IntNegative);
            session.bounds[*root as usize]
                .direct_lower_rows
                .push(quantified);
            session.bounds[*root as usize]
                .direct_upper_rows
                .push(quantified);
            session.bounds[relay as usize].direct_lower_rows.push(*root);
            let argument = session.negative_top_term().unwrap();
            let result = session.live_value_term(Polarity::Positive, relay).unwrap();
            let function = session
                .positive_function_term(
                    argument,
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    result,
                )
                .unwrap();
            let lower = &mut session.bounds[*root as usize].exact_non_variable_lowers;
            lower.extend(if reverse {
                [
                    ValueEndpointKey::ValueRow(first),
                    ValueEndpointKey::PositiveFunction(function),
                ]
            } else {
                [
                    ValueEndpointKey::PositiveFunction(function),
                    ValueEndpointKey::ValueRow(first),
                ]
            });
            let upper = &mut session.bounds[*root as usize].exact_non_variable_uppers;
            upper.extend(if reverse {
                [
                    ValueEndpointKey::ValueRow(second),
                    ValueEndpointKey::TopNegative,
                ]
            } else {
                [
                    ValueEndpointKey::TopNegative,
                    ValueEndpointKey::ValueRow(second),
                ]
            });
        }
        (session, roots)
    }

    let mut baseline = None;
    for reverse in [false, true] {
        let (session, roots) = fixture(reverse);
        let boxed_meter = DraftHeapMeter::default();
        let mut boxed_memo = F5cComponentExpansionMemo::default();
        let mut boxed = Vec::new();
        for root in roots {
            let (draft, memo, _, _) =
                F5cGeneralizer::with_memo(&session, &boxed_meter, boxed_memo, 0)
                    .build_component(root);
            boxed.push(draft.unwrap());
            boxed_memo = memo;
        }
        let boxed_stats =
            crate::f5c_normalization::normalize_component(&boxed_meter, &mut boxed).unwrap();
        assert!(boxed.iter().all(|draft| draft.quantifier_count > 0));
        assert!(boxed.iter().all(|draft| !draft.recursive_bounds.is_empty()));
        let flat_meter = DraftHeapMeter::default();
        let mut staged = TrackedVec::<F5cStagedCandidate<'_>>::new(&flat_meter);
        staged.try_reserve(2).unwrap();
        let mut flat_memo = F5cComponentExpansionMemo::default();
        let checkpoint = flat_memo.begin_flat_batch();
        for root in roots {
            let (result, memo, _, _) =
                F5cGeneralizer::with_memo(&session, &flat_meter, flat_memo, 0)
                    .build_and_stage_flat_raw_candidate(root, &mut staged);
            result.unwrap();
            flat_memo = memo;
        }
        assert!(staged.iter().all(|member| {
            member
                .candidate
                .draft
                .positive_nodes
                .iter()
                .any(|node| matches!(node, crate::f5c_draft::PositiveNode::Union(_)))
        }));
        assert!(staged.iter().all(|member| {
            member
                .candidate
                .draft
                .negative_nodes
                .iter()
                .any(|node| matches!(node, crate::f5c_draft::NegativeNode::Intersection(_)))
        }));
        let flat_stats = crate::f5c_normalization::normalize_flat_batch_metered(
            &mut flat_memo,
            &flat_meter,
            &mut staged,
            None,
        )
        .unwrap();
        let resource = flat_stats.resource.as_ref().unwrap();
        let snapshot_bytes = resource
            .index_peak_capacities
            .iter()
            .zip(resource.index_peak_sizes.iter())
            .map(|(capacity, size)| capacity * size)
            .sum::<usize>();
        assert_eq!(resource.index_peak_bytes, snapshot_bytes);
        assert!(
            resource.physical_index.capacities[crate::f5c_normalization::FLAT_CANDIDATE_LANE_COUNT
                - 7
                ..crate::f5c_normalization::FLAT_CANDIDATE_LANE_COUNT - 1]
                .iter()
                .all(|capacity| *capacity == 0)
        );
        let mut independent = IndependentResourceLedger::default();
        independent
            .record_flat_normalization_index(resource, 0)
            .unwrap();
        assert_eq!(
            independent.closed_normalization_index_peak_bytes,
            resource.index_peak_bytes
        );
        let mut observer_snapshot_changed = resource.clone();
        observer_snapshot_changed.index_peak_capacities.fill(0);
        IndependentResourceLedger::default()
            .record_flat_normalization_index(&observer_snapshot_changed, 0)
            .unwrap();
        for change in [
            |lane: &mut crate::f5c_normalization::FlatCandidateLane| lane.requested_slots += 1,
            |lane: &mut crate::f5c_normalization::FlatCandidateLane| lane.growths += 1,
            |lane: &mut crate::f5c_normalization::FlatCandidateLane| lane.peak_capacity += 1,
            |lane: &mut crate::f5c_normalization::FlatCandidateLane| lane.slot_size += 1,
        ] {
            let mut changed = resource.clone();
            change(&mut changed.lanes[0]);
            assert_eq!(
                IndependentResourceLedger::default().record_flat_normalization_index(&changed, 0),
                Err(crate::SolveAvailabilityError::IdentityExhausted)
            );
        }
        let mut changed_joint = resource.clone();
        changed_joint.joint_peak_bytes += 1;
        assert_eq!(
            IndependentResourceLedger::default().record_flat_normalization_index(&changed_joint, 0),
            Err(crate::SolveAvailabilityError::IdentityExhausted)
        );
        let mut missing_physical_event = resource.clone();
        missing_physical_event.physical_index = Default::default();
        assert_eq!(
            IndependentResourceLedger::default()
                .record_flat_normalization_index(&missing_physical_event, 0),
            Err(crate::SolveAvailabilityError::IdentityExhausted)
        );
        flat_memo.finish_flat_batch(checkpoint, true).unwrap();
        let counters = (
            flat_stats.key_writes,
            flat_stats.child_comparisons,
            flat_stats.descriptor_words,
            flat_stats.word_comparisons,
            flat_stats.duplicates,
        );
        assert!(counters.3 > 0);
        assert_eq!(
            counters,
            (
                boxed_stats.key_writes,
                boxed_stats.child_comparisons,
                boxed_stats.descriptor_words,
                boxed_stats.word_comparisons,
                boxed_stats.duplicates,
            )
        );
        if let Some(expected) = baseline {
            assert_eq!(counters, expected);
        } else {
            baseline = Some(counters);
        }
        for (candidate, boxed) in staged.iter().zip(&boxed) {
            assert_eq!(
                candidate.candidate.draft.quantifier_count,
                boxed.quantifier_count
            );
            assert_eq!(
                candidate.candidate.draft.recursive_bounds.len(),
                boxed.recursive_bounds.len()
            );
            let indexed = candidate.candidate.draft.indexed(&flat_meter).unwrap();
            let mut indexed_session = ClosedTypeFinalizationSession::try_new().unwrap();
            let (indexed_scheme, _) = indexed_session
                .finalize_indexed_scheme(indexed.as_ref())
                .unwrap()
                .into_parts();
            let mut boxed_session = ClosedTypeFinalizationSession::try_new().unwrap();
            let (boxed_scheme, _) = InferenceSession::finalize_generalization_draft_raw(
                &mut boxed_session,
                boxed,
                false,
            )
            .unwrap()
            .into_parts();
            assert!(
                indexed_session
                    .scheme_view(&indexed_scheme)
                    .unwrap()
                    .alpha_eq(boxed_session.scheme_view(&boxed_scheme).unwrap())
            );
        }
    }
}

#[test]
fn flat_all_member_compound_route_matches_boxed_normalization() {
    fn fixture(reverse: bool, flat: bool) -> InferenceSession {
        let batch = collect(module(
            "my left = right; my right = left",
            "f5c-flat-compound-route",
        ));
        let mut session = InferenceSession::new(batch);
        session.flat_candidate_enabled = flat;
        session.admit_all_collected_facts().unwrap();
        let component = session
            .batch
            .scc_components_in_dependency_first_order()
            .find(|component| {
                session
                    .batch
                    .scc_component_members(component)
                    .unwrap()
                    .len()
                    == 2
            })
            .unwrap()
            .clone();
        let members = session
            .batch
            .scc_component_members(&component)
            .unwrap()
            .to_vec();
        let mut seen_roots = std::collections::HashSet::new();
        for member in members {
            let verified = InferenceSession::verified_scheme_definition(&session.batch, &member);
            let position = session
                .batch
                .root_component_positions
                .get(&verified.record.root)
                .unwrap()
                .component;
            if !seen_roots.insert(position) {
                continue;
            }
            let root = session.fresh_value_at_level(1).unwrap();
            session.live_components[position].ordinal = root;
            let relay = session.fresh_value_at_level(1).unwrap();
            let quantified = session.fresh_value_at_level(1).unwrap();
            let first = session.fresh_value_at_level(1).unwrap();
            let second = session.fresh_value_at_level(1).unwrap();
            session.bounds[first as usize]
                .exact_non_variable_lowers
                .push(ValueEndpointKey::IntPositive);
            session.bounds[second as usize]
                .exact_non_variable_uppers
                .push(ValueEndpointKey::IntNegative);
            session.bounds[root as usize]
                .direct_lower_rows
                .push(quantified);
            session.bounds[root as usize]
                .direct_upper_rows
                .push(quantified);
            session.bounds[relay as usize].direct_lower_rows.push(root);
            let argument = session.negative_top_term().unwrap();
            let result = session.live_value_term(Polarity::Positive, relay).unwrap();
            let function = session
                .positive_function_term(
                    argument,
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    result,
                )
                .unwrap();
            session.bounds[root as usize]
                .exact_non_variable_lowers
                .extend(if reverse {
                    [
                        ValueEndpointKey::ValueRow(first),
                        ValueEndpointKey::PositiveFunction(function),
                    ]
                } else {
                    [
                        ValueEndpointKey::PositiveFunction(function),
                        ValueEndpointKey::ValueRow(first),
                    ]
                });
            session.bounds[root as usize]
                .exact_non_variable_uppers
                .extend(if reverse {
                    [
                        ValueEndpointKey::ValueRow(second),
                        ValueEndpointKey::TopNegative,
                    ]
                } else {
                    [
                        ValueEndpointKey::TopNegative,
                        ValueEndpointKey::ValueRow(second),
                    ]
                });
        }
        assert_eq!(seen_roots.len(), 2);
        session
    }

    for reverse in [false, true] {
        let mut boxed = fixture(reverse, false);
        let mut flat = fixture(reverse, true);
        boxed.execute_scc_plan().unwrap();
        flat.execute_scc_plan().unwrap();
        let published = |session: &InferenceSession| {
            let counters = &session.execution_counters;
            (
                counters.closed_normalized_key_writes,
                counters.closed_normalization_child_comparisons,
                counters.closed_normalization_descriptor_words,
                counters.closed_normalization_word_comparisons,
            )
        };
        assert_eq!(published(&flat), published(&boxed));
        assert!(published(&flat).3 > 0);
        assert!(
            flat.execution_counters
                .closed_normalization_index_requested_slots
                > 0
        );
        assert!(
            flat.execution_counters
                .closed_normalization_index_capacity_growths
                > 0
        );
        assert!(
            flat.execution_counters
                .closed_normalization_index_peak_bytes
                > 0
        );
        assert_eq!(
            flat.execution_counters
                .closed_normalization_index_actual_capacity,
            0
        );
        assert_eq!(
            flat.execution_counters
                .closed_normalization_index_retained_bytes,
            0
        );
        let lanes = &flat.resource_ledger.closed_normalization_index_lanes;
        assert!(
            lanes[..crate::f5c_normalization::LANE_COUNT]
                .iter()
                .any(|lane| lane.peak_capacity > 0)
        );
        assert!(lanes[crate::f5c_normalization::LANE_COUNT + 14].peak_capacity > 0);
        let output_lanes = &lanes
            [crate::f5c_normalization::LANE_COUNT + 8..crate::f5c_normalization::LANE_COUNT + 14];
        assert!(output_lanes.iter().any(|lane| lane.peak_capacity > 0));
        for lane in output_lanes {
            assert_eq!(lane.actual_capacity, 0);
            assert_eq!(lane.retained_bytes, 0);
        }
        assert!(
            lanes
                .iter()
                .all(|lane| lane.actual_capacity == 0 && lane.retained_bytes == 0)
        );
        for (left, right) in boxed.schemes.iter().zip(&flat.schemes) {
            if let (Some(left), Some(right)) = (left, right) {
                let flat_view = flat
                    .finalization
                    .as_ref()
                    .unwrap()
                    .scheme_view(right)
                    .unwrap();
                assert!(flat_view.quantifier_count() > 0);
                assert!(!flat_view.recursive_bounds().is_empty());
                assert!(
                    boxed
                        .finalization
                        .as_ref()
                        .unwrap()
                        .scheme_view(left)
                        .unwrap()
                        .alpha_eq(flat_view)
                );
            }
        }
    }
}

#[test]
fn physical_set_duplicate_at_capacity_keeps_growth_and_counts_attempt() {
    use crate::f5c_generalization::F5cWalkerLaneKind as Lane;
    for kind in [
        Lane::ClosureConnected,
        Lane::ClosureNeighbors,
        Lane::ClosureResult,
        Lane::RawPositiveIncidences,
        Lane::RawNegativeIncidences,
    ] {
        let mut memo = F5cComponentExpansionMemo::default();
        let mut set = HashSet::new();
        memo.insert_physical_set(&mut set, 0, kind).unwrap();
        let capacity = set.capacity();
        for value in 1..capacity as u32 {
            memo.insert_physical_set(&mut set, value, kind).unwrap();
        }
        assert_eq!(set.len(), capacity);
        let before = memo.walker_resources.lanes[kind as usize];
        memo.insert_physical_set(&mut set, 0, kind).unwrap();
        let after = memo.walker_resources.lanes[kind as usize];
        assert_eq!(set.capacity(), capacity);
        assert_eq!(after.actual_capacity, before.actual_capacity);
        assert_eq!(after.capacity_growths, before.capacity_growths);
        assert_eq!(after.requested_slots, before.requested_slots + 1);
        assert_eq!(after.peak_bytes, before.peak_bytes);
        drop(set);
        memo.walker_resources.release(kind);
        assert_eq!(
            memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
        let mut retry = HashSet::new();
        memo.insert_physical_set(&mut retry, 0, kind).unwrap();
        assert_eq!(
            memo.walker_resources.lanes[kind as usize].actual_capacity,
            retry.capacity()
        );
        drop(retry);
        memo.walker_resources.release(kind);
        assert_eq!(
            memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
}

#[test]
fn raw_forest_census_matches_boxed_and_flat_exact_sets() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_draft::{FlatDraft, NegativeNode, PositiveNode};
    use std::collections::{HashMap, HashSet};

    let mut flat = FlatDraft::default();
    let predicate_variable = flat.positive(PositiveNode::Variable(10)).unwrap();
    let predicate_argument = flat.negative(NegativeNode::Variable(11)).unwrap();
    let predicate_result = flat.positive(PositiveNode::Variable(12)).unwrap();
    let predicate_function = flat
        .positive(PositiveNode::Function {
            argument: predicate_argument,
            result: predicate_result,
        })
        .unwrap();
    let predicate_span = flat
        .positive_span(&[predicate_variable, predicate_function])
        .unwrap();
    flat.predicate = Some(flat.positive(PositiveNode::Union(predicate_span)).unwrap());
    let lower_first = flat.positive(PositiveNode::Variable(20)).unwrap();
    let upper_first = flat.negative(NegativeNode::Variable(21)).unwrap();
    let lower_second = flat.positive(PositiveNode::Variable(30)).unwrap();
    let upper_argument = flat.positive(PositiveNode::Variable(32)).unwrap();
    let upper_result = flat.negative(NegativeNode::Variable(33)).unwrap();
    let upper_second = flat
        .negative(NegativeNode::Function {
            argument: upper_argument,
            result: upper_result,
        })
        .unwrap();
    let order = [2, 1];
    let flat_bounds = HashMap::from([
        (1, (lower_first, upper_first)),
        (2, (lower_second, upper_second)),
    ]);
    let boxed_predicate = F5cPositive::Union(test_tracked(
        &test_source_meter,
        vec![
            F5cPositive::Variable(10),
            F5cPositive::Function {
                argument: test_tracked_one(&test_source_meter, F5cNegative::Variable(11)),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: test_tracked_one(&test_source_meter, F5cPositive::Variable(12)),
            },
        ],
    ));
    let boxed_bounds = HashMap::from([
        (1, (F5cPositive::Variable(20), F5cNegative::Variable(21))),
        (
            2,
            (
                F5cPositive::Variable(30),
                F5cNegative::Function {
                    argument: test_tracked_one(&test_source_meter, F5cPositive::Variable(32)),
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: test_tracked_one(&test_source_meter, F5cNegative::Variable(33)),
                },
            ),
        ),
    ]);
    let mut boxed_memo = F5cComponentExpansionMemo::default();
    let mut indexed_memo = F5cComponentExpansionMemo::default();
    let boxed = F5cGeneralizer::boxed_raw_forest_incidences_for_test(
        &mut boxed_memo,
        &boxed_predicate,
        &order,
        &boxed_bounds,
    )
    .unwrap();
    let indexed = F5cGeneralizer::flat_raw_forest_incidences_for_test(
        &mut indexed_memo,
        &flat,
        &order,
        &flat_bounds,
    )
    .unwrap();
    assert_eq!(
        boxed,
        (
            HashSet::from([10, 12, 20, 30, 32]),
            HashSet::from([11, 21, 33])
        )
    );
    assert_eq!(indexed, boxed);
    for (memo, sets) in [(&boxed_memo, &boxed), (&indexed_memo, &indexed)] {
        for (kind, set) in [
            (F5cWalkerLaneKind::RawPositiveIncidences, &sets.0),
            (F5cWalkerLaneKind::RawNegativeIncidences, &sets.1),
        ] {
            let lane = memo.walker_resources.lanes[kind as usize];
            let independent = memo.walker_resources.independent_lanes[kind as usize];
            assert_eq!(lane.actual_capacity, set.capacity());
            assert_eq!(lane.requested_slots, independent.requested_slots);
            assert_eq!(lane.capacity_growths, independent.capacity_growths);
            assert_eq!(lane.peak_bytes, independent.peak_bytes);
        }
    }
    drop(boxed);
    drop(indexed);
    for memo in [&mut boxed_memo, &mut indexed_memo] {
        memo.walker_resources
            .release(F5cWalkerLaneKind::RawPositiveIncidences);
        memo.walker_resources
            .release(F5cWalkerLaneKind::RawNegativeIncidences);
        assert_eq!(memo.walker_resources.retained_bytes().unwrap(), 0);
    }
}

#[test]
fn raw_incidence_failure_releases_sets_and_retry_recounts_capacity() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_generalization::F5cWalkerLaneKind as Lane;
    let predicate = F5cPositive::Union(test_tracked(
        &test_source_meter,
        vec![F5cPositive::Variable(1), F5cPositive::Variable(2)],
    ));
    let mut memo = F5cComponentExpansionMemo::default();
    memo.work_meter.set(usize::MAX - 7);
    assert_eq!(
        F5cGeneralizer::boxed_raw_forest_incidences_for_test(
            &mut memo,
            &predicate,
            &[],
            &HashMap::new()
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    for kind in [Lane::RawPositiveIncidences, Lane::RawNegativeIncidences] {
        assert_eq!(
            memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
    assert!(memo.walker_resources.lanes[Lane::RawPositiveIncidences as usize].peak_bytes > 0);
    memo.work_meter.set(0);
    let (positive, negative) = F5cGeneralizer::boxed_raw_forest_incidences_for_test(
        &mut memo,
        &predicate,
        &[],
        &HashMap::new(),
    )
    .unwrap();
    assert_eq!(positive, HashSet::from([1, 2]));
    assert!(negative.is_empty());
    assert_eq!(
        memo.walker_resources.lanes[Lane::RawPositiveIncidences as usize].actual_capacity,
        positive.capacity()
    );
    drop(positive);
    drop(negative);
    memo.walker_resources.release(Lane::RawPositiveIncidences);
    memo.walker_resources.release(Lane::RawNegativeIncidences);
}

#[test]
fn r_candidate_fixed_point_matches_boxed_and_flat() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_draft::{FlatDraft, NegativeNode, PositiveNode};
    use crate::f5c_generalization::F5cGuardedTrace;
    use std::collections::{HashMap, HashSet};

    let mut flat = FlatDraft::default();
    flat.predicate = Some(flat.positive(PositiveNode::Variable(1)).unwrap());
    let argument = flat.negative(NegativeNode::Top).unwrap();
    let guarded_one = flat.positive(PositiveNode::Variable(1)).unwrap();
    let guarded_two = flat.positive(PositiveNode::Variable(2)).unwrap();
    let lower_one = flat
        .positive(PositiveNode::Function {
            argument,
            result: guarded_one,
        })
        .unwrap();
    let lower_two = flat
        .positive(PositiveNode::Function {
            argument,
            result: guarded_two,
        })
        .unwrap();
    let upper = flat.negative(NegativeNode::Top).unwrap();
    let flat_bounds = HashMap::from([(1, (lower_one, upper)), (2, (lower_two, upper))]);
    let boxed_bound = |owner| {
        (
            F5cPositive::Function {
                argument: test_tracked_one(&test_source_meter, F5cNegative::Top),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: test_tracked_one(&test_source_meter, F5cPositive::Variable(owner)),
            },
            F5cNegative::Top,
        )
    };
    let boxed_bounds = HashMap::from([(1, boxed_bound(1)), (2, boxed_bound(2))]);
    let reentries = [1, 2].map(|owner| F5cGuardedTrace {
        owner,
        entry_polarity: Polarity::Positive,
        reentry_polarity: Polarity::Positive,
        path: Vec::new(),
    });
    let index = HashMap::from([(1, vec![0]), (2, vec![1])]);
    let empty = HashSet::new();
    let mut boxed_memo = F5cComponentExpansionMemo::default();
    let boxed = F5cGeneralizer::boxed_r_candidates_for_test(
        &test_source_meter,
        &mut boxed_memo,
        &F5cPositive::Variable(1),
        &boxed_bounds,
        &reentries,
        &index,
        |_| true,
        &empty,
        &empty,
    )
    .unwrap();
    let mut flat_memo = F5cComponentExpansionMemo::default();
    let indexed = F5cGeneralizer::flat_r_candidates_for_test(
        &mut flat_memo,
        &flat,
        &flat_bounds,
        &reentries,
        &index,
        |_| true,
        &empty,
        &empty,
    )
    .unwrap();
    assert_eq!(boxed, HashSet::from([1]));
    assert_eq!(indexed, boxed);
    assert_eq!(
        boxed_memo.walker_resources.lanes[F5cWalkerLaneKind::RCandidates as usize].actual_capacity,
        boxed.capacity()
    );
    assert_eq!(
        flat_memo.walker_resources.lanes[F5cWalkerLaneKind::RCandidates as usize].actual_capacity,
        indexed.capacity()
    );
    for memo in [&boxed_memo, &flat_memo] {
        let (physical, reported) = memo.r_fixed_point_live_sample.unwrap();
        assert_eq!(physical, reported);
        assert!(physical[0] > 0 && physical[1] > 0);
        assert!(physical[3] > 0 && physical[4] > 0 && physical[5] > 0);
        for kind in [
            F5cWalkerLaneKind::RPrevious,
            F5cWalkerLaneKind::RSurvivingBounds,
            F5cWalkerLaneKind::RReachable,
            F5cWalkerLaneKind::RFrontier,
            F5cWalkerLaneKind::RReferenced,
        ] {
            assert_eq!(
                memo.walker_resources.lanes[kind as usize].actual_capacity,
                0
            );
        }
    }
    drop(indexed);
    drop(boxed);
    for memo in [&mut boxed_memo, &mut flat_memo] {
        memo.walker_resources
            .release(F5cWalkerLaneKind::RCandidates);
    }
    let failed_lane = F5cWalkerLaneKind::RReferenced as usize;
    boxed_memo.walker_resources.lanes[failed_lane].requested_slots = usize::MAX;
    let failed = F5cGeneralizer::boxed_r_candidates_for_test(
        &test_source_meter,
        &mut boxed_memo,
        &F5cPositive::Variable(1),
        &boxed_bounds,
        &reentries,
        &index,
        |_| true,
        &empty,
        &empty,
    );
    assert!(failed.is_err());
    for kind in [
        F5cWalkerLaneKind::RCandidates,
        F5cWalkerLaneKind::RPrevious,
        F5cWalkerLaneKind::RSurvivingBounds,
        F5cWalkerLaneKind::RReachable,
        F5cWalkerLaneKind::RFrontier,
        F5cWalkerLaneKind::RReferenced,
    ] {
        assert_eq!(
            boxed_memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
    boxed_memo.walker_resources.lanes[failed_lane].requested_slots = 0;
    let retry = F5cGeneralizer::boxed_r_candidates_for_test(
        &test_source_meter,
        &mut boxed_memo,
        &F5cPositive::Variable(1),
        &boxed_bounds,
        &reentries,
        &index,
        |_| true,
        &empty,
        &empty,
    )
    .unwrap();
    assert_eq!(retry, HashSet::from([1]));
    drop(retry);
    boxed_memo
        .walker_resources
        .release(F5cWalkerLaneKind::RCandidates);

    let previous_lane = F5cWalkerLaneKind::RPrevious as usize;
    let mut failed_work = [0; 2];
    for (failure_index, requested_slots) in [usize::MAX, usize::MAX - 1].into_iter().enumerate() {
        boxed_memo.walker_resources.lanes[previous_lane].requested_slots = requested_slots;
        boxed_memo.work_meter.set(0);
        let failed = F5cGeneralizer::boxed_r_candidates_for_test(
            &test_source_meter,
            &mut boxed_memo,
            &F5cPositive::Variable(1),
            &boxed_bounds,
            &reentries,
            &index,
            |_| true,
            &empty,
            &empty,
        );
        assert!(failed.is_err());
        failed_work[failure_index] = boxed_memo.work_meter.get();
        assert_eq!(
            boxed_memo.walker_resources.lanes[previous_lane].actual_capacity,
            0
        );
    }
    assert_eq!(failed_work[1], failed_work[0] + 1);
}

#[test]
fn post_r_selected_owners_and_q_r_ordinals_match_boxed_and_flat() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_draft::{FlatDraft, NegativeNode, PositiveNode};
    use crate::f5c_generalization::F5cGuardedTrace;
    use std::collections::{HashMap, HashSet};

    let mut flat = FlatDraft::default();
    let predicate_owner = flat.positive(PositiveNode::Variable(1)).unwrap();
    let predicate_q_first = flat.positive(PositiveNode::Variable(4)).unwrap();
    let predicate_q_second = flat.positive(PositiveNode::Variable(3)).unwrap();
    let predicate_span = flat
        .positive_span(&[predicate_owner, predicate_q_first, predicate_q_second])
        .unwrap();
    flat.predicate = Some(flat.positive(PositiveNode::Union(predicate_span)).unwrap());
    let argument = flat.negative(NegativeNode::Top).unwrap();
    let lower = flat
        .positive(PositiveNode::Function {
            argument,
            result: predicate_owner,
        })
        .unwrap();
    let upper_three = flat.negative(NegativeNode::Variable(3)).unwrap();
    let upper_four = flat.negative(NegativeNode::Variable(4)).unwrap();
    let upper_span = flat.negative_span(&[upper_three, upper_four]).unwrap();
    let upper = flat
        .negative(NegativeNode::Intersection(upper_span))
        .unwrap();
    let flat_bounds = HashMap::from([(1, (lower, upper))]);
    let boxed_predicate = F5cPositive::Union(test_tracked(
        &test_source_meter,
        vec![
            F5cPositive::Variable(1),
            F5cPositive::Variable(4),
            F5cPositive::Variable(3),
        ],
    ));
    let boxed_bounds = HashMap::from([(
        1,
        (
            F5cPositive::Function {
                argument: test_tracked_one(&test_source_meter, F5cNegative::Top),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: test_tracked_one(&test_source_meter, F5cPositive::Variable(1)),
            },
            F5cNegative::Intersection(test_tracked(
                &test_source_meter,
                vec![F5cNegative::Variable(3), F5cNegative::Variable(4)],
            )),
        ),
    )]);
    let traces = [F5cGuardedTrace {
        owner: 1,
        entry_polarity: Polarity::Positive,
        reentry_polarity: Polarity::Positive,
        path: Vec::new(),
    }];
    let candidates = HashSet::from([1]);
    let positive = HashSet::from([1, 3, 4]);
    let negative = HashSet::from([3, 4]);
    let mut boxed_memo = F5cComponentExpansionMemo::default();
    let boxed = F5cGeneralizer::boxed_post_r_for_test(
        &test_source_meter,
        &mut boxed_memo,
        &boxed_predicate,
        &boxed_bounds,
        &[1],
        &traces,
        &candidates,
        &[1, 3, 4],
        &positive,
        &negative,
    )
    .unwrap();
    let mut flat_memo = F5cComponentExpansionMemo::default();
    let (indexed, output) = F5cGeneralizer::flat_post_r_for_test(
        &mut flat_memo,
        &flat,
        &flat_bounds,
        &[1],
        &traces,
        &candidates,
        &[1, 3, 4],
        &positive,
        &negative,
    )
    .unwrap();
    assert_eq!(boxed.recursive_owners, vec![1]);
    assert_eq!(indexed.recursive_owners, boxed.recursive_owners);
    assert_eq!(boxed.q, HashMap::from([(4, 0), (3, 1)]));
    assert_eq!(indexed.q, boxed.q);
    assert_eq!(boxed.r, HashMap::from([(1, 2)]));
    assert_eq!(indexed.r, boxed.r);
    assert_eq!(indexed.retained_bounds.len(), 1);
    assert!(
        flat_memo.walker_resources.lanes[F5cWalkerLaneKind::RetainedOwnerBounds as usize]
            .actual_capacity
            >= 1
    );
    assert!(
        output
            .positive_nodes
            .get(indexed.retained_predicate.0 as usize)
            .is_some()
    );
    drop(indexed);
    crate::f5c_replay::release_flat_output(&mut flat_memo, output);
    crate::f5c_generalization::release_flat_post_r_lanes(&mut flat_memo);
    assert_eq!(
        flat_memo.walker_resources.lanes[F5cWalkerLaneKind::RetainedOwnerBounds as usize]
            .actual_capacity,
        0
    );
}

#[test]
fn post_r_trace_order_overrides_raw_order_for_two_retained_owners() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_draft::{FlatDraft, NegativeNode, PositiveNode};
    use crate::f5c_generalization::F5cGuardedTrace;
    use std::collections::{HashMap, HashSet};

    let mut flat = FlatDraft::default();
    let row_one = flat.positive(PositiveNode::Variable(1)).unwrap();
    let row_two = flat.positive(PositiveNode::Variable(2)).unwrap();
    let q_four = flat.positive(PositiveNode::Variable(4)).unwrap();
    let q_five = flat.positive(PositiveNode::Variable(5)).unwrap();
    let q_six = flat.positive(PositiveNode::Variable(6)).unwrap();
    let q_seven = flat.positive(PositiveNode::Variable(7)).unwrap();
    let predicate_span = flat.positive_span(&[row_two, q_four, row_one]).unwrap();
    flat.predicate = Some(flat.positive(PositiveNode::Union(predicate_span)).unwrap());
    let argument = flat.negative(NegativeNode::Top).unwrap();
    let one_result_span = flat.positive_span(&[row_one, q_six, q_seven]).unwrap();
    let one_result = flat.positive(PositiveNode::Union(one_result_span)).unwrap();
    let lower_one = flat
        .positive(PositiveNode::Function {
            argument,
            result: one_result,
        })
        .unwrap();
    let two_result_span = flat.positive_span(&[row_two, q_five]).unwrap();
    let two_result = flat.positive(PositiveNode::Union(two_result_span)).unwrap();
    let lower_two = flat
        .positive(PositiveNode::Function {
            argument,
            result: two_result,
        })
        .unwrap();
    let upper_one_four = flat.negative(NegativeNode::Variable(4)).unwrap();
    let upper_one_seven = flat.negative(NegativeNode::Variable(7)).unwrap();
    let upper_one_eight = flat.negative(NegativeNode::Variable(8)).unwrap();
    let upper_one_span = flat
        .negative_span(&[upper_one_four, upper_one_seven, upper_one_eight])
        .unwrap();
    let upper_one = flat
        .negative(NegativeNode::Intersection(upper_one_span))
        .unwrap();
    let upper_two_five = flat.negative(NegativeNode::Variable(5)).unwrap();
    let upper_two_six = flat.negative(NegativeNode::Variable(6)).unwrap();
    let upper_two_span = flat
        .negative_span(&[upper_two_five, upper_two_six])
        .unwrap();
    let upper_two = flat
        .negative(NegativeNode::Intersection(upper_two_span))
        .unwrap();
    let flat_bounds = HashMap::from([(1, (lower_one, upper_one)), (2, (lower_two, upper_two))]);
    let boxed_predicate = F5cPositive::Union(test_tracked(
        &test_source_meter,
        vec![
            F5cPositive::Variable(2),
            F5cPositive::Variable(4),
            F5cPositive::Variable(1),
        ],
    ));
    let boxed_function = |result| F5cPositive::Function {
        argument: test_tracked_one(&test_source_meter, F5cNegative::Top),
        argument_effect: F5cNegativeEffect::Empty,
        result_effect: F5cPositiveEffect::Bottom,
        result: test_tracked_one(&test_source_meter, result),
    };
    let boxed_bounds = HashMap::from([
        (
            1,
            (
                boxed_function(F5cPositive::Union(test_tracked(
                    &test_source_meter,
                    vec![
                        F5cPositive::Variable(1),
                        F5cPositive::Variable(6),
                        F5cPositive::Variable(7),
                    ],
                ))),
                F5cNegative::Intersection(test_tracked(
                    &test_source_meter,
                    vec![
                        F5cNegative::Variable(4),
                        F5cNegative::Variable(7),
                        F5cNegative::Variable(8),
                    ],
                )),
            ),
        ),
        (
            2,
            (
                boxed_function(F5cPositive::Union(test_tracked(
                    &test_source_meter,
                    vec![F5cPositive::Variable(2), F5cPositive::Variable(5)],
                ))),
                F5cNegative::Intersection(test_tracked(
                    &test_source_meter,
                    vec![F5cNegative::Variable(5), F5cNegative::Variable(6)],
                )),
            ),
        ),
    ]);
    let traces = [2, 1, 2].map(|owner| F5cGuardedTrace {
        owner,
        entry_polarity: Polarity::Positive,
        reentry_polarity: Polarity::Positive,
        path: Vec::new(),
    });
    let candidates = HashSet::from([1, 2]);
    let positive = HashSet::from([1, 2, 4, 5, 6, 7, 8]);
    let negative = HashSet::from([4, 5, 6, 7, 8]);
    let mut boxed_memo = F5cComponentExpansionMemo::default();
    let boxed = F5cGeneralizer::boxed_post_r_for_test(
        &test_source_meter,
        &mut boxed_memo,
        &boxed_predicate,
        &boxed_bounds,
        &[1, 2],
        &traces,
        &candidates,
        &[1, 2, 4, 5, 6, 7, 8],
        &positive,
        &negative,
    )
    .unwrap();
    let mut flat_memo = F5cComponentExpansionMemo::default();
    let (indexed, output) = F5cGeneralizer::flat_post_r_for_test(
        &mut flat_memo,
        &flat,
        &flat_bounds,
        &[1, 2],
        &traces,
        &candidates,
        &[1, 2, 4, 5, 6, 7, 8],
        &positive,
        &negative,
    )
    .unwrap();
    assert_eq!(boxed.recursive_owners, vec![2, 1]);
    assert_eq!(indexed.recursive_owners, boxed.recursive_owners);
    assert_eq!(
        boxed.q,
        HashMap::from([(4, 0), (5, 1), (6, 2), (7, 3), (8, 4)])
    );
    assert_eq!(indexed.q, boxed.q);
    assert_eq!(boxed.r, HashMap::from([(2, 5), (1, 6)]));
    assert_eq!(indexed.r, boxed.r);
    assert_eq!(indexed.retained_bounds.len(), 2);
    for (kind, capacity) in [
        (
            F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
            boxed.retained_bounds.capacity(),
        ),
        (
            F5cWalkerLaneKind::PostRRecursiveOwners,
            boxed.recursive_owners.capacity(),
        ),
        (
            F5cWalkerLaneKind::PostRRecursiveSet,
            boxed.recursive_set.capacity(),
        ),
        (F5cWalkerLaneKind::PostRQuantifiers, boxed.q.capacity()),
        (F5cWalkerLaneKind::PostRRecursives, boxed.r.capacity()),
    ] {
        assert!(capacity > 0);
        assert_eq!(
            boxed_memo.walker_resources.lanes[kind as usize].actual_capacity,
            capacity
        );
        assert!(
            boxed_memo.walker_resources.lanes[kind as usize].peak_bytes
                >= capacity * kind.slot_size()
        );
    }
    for kind in [
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
    ] {
        for memo in [&boxed_memo, &flat_memo] {
            let (physical, reported) = memo
                .post_r_temporary_live_samples
                .iter()
                .find_map(|(sample_kind, physical, reported)| {
                    ((*sample_kind as usize) == (kind as usize)).then_some((*physical, *reported))
                })
                .expect("temporary post-R collection must be sampled while live");
            assert!(physical > 0);
            assert_eq!(physical, reported);
            assert!(
                memo.walker_resources.lanes[kind as usize].peak_bytes
                    >= physical * kind.slot_size()
            );
        }
        assert!(boxed_memo.walker_resources.lanes[kind as usize].peak_bytes > 0);
        assert_eq!(
            boxed_memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
    for lane in [
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert!(flat_memo.walker_resources.lanes[lane as usize].actual_capacity > 0);
    }
    for lane in [
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
    ] {
        assert!(flat_memo.walker_resources.lanes[lane as usize].peak_bytes > 0);
        assert_eq!(
            flat_memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
    }
    let mut late_boxed_memo = F5cComponentExpansionMemo::default();
    late_boxed_memo.walker_resources.lanes[F5cWalkerLaneKind::PostRQuantifiers as usize]
        .requested_slots = usize::MAX;
    assert_eq!(
        F5cGeneralizer::boxed_post_r_for_test(
            &test_source_meter,
            &mut late_boxed_memo,
            &boxed_predicate,
            &boxed_bounds,
            &[1, 2],
            &traces,
            &candidates,
            &[1, 2, 4, 5, 6, 7, 8],
            &positive,
            &negative,
        )
        .err(),
        Some(SolveAvailabilityError::IdentityExhausted)
    );
    for kind in [
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
    ] {
        let (physical, reported) = late_boxed_memo
            .post_r_temporary_live_samples
            .iter()
            .find_map(|(sample_kind, physical, reported)| {
                ((*sample_kind as usize) == (kind as usize)).then_some((*physical, *reported))
            })
            .expect("late failure must follow temporary post-R growth");
        assert!(physical > 0);
        assert_eq!(physical, reported);
    }
    for kind in [
        F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert_eq!(
            late_boxed_memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
    late_boxed_memo.walker_resources.lanes[F5cWalkerLaneKind::PostRQuantifiers as usize]
        .requested_slots = 0;
    let retried = F5cGeneralizer::boxed_post_r_for_test(
        &test_source_meter,
        &mut late_boxed_memo,
        &boxed_predicate,
        &boxed_bounds,
        &[1, 2],
        &traces,
        &candidates,
        &[1, 2, 4, 5, 6, 7, 8],
        &positive,
        &negative,
    )
    .unwrap();
    assert_eq!(retried.recursive_owners, boxed.recursive_owners);
    assert_eq!(retried.q, boxed.q);
    assert_eq!(retried.r, boxed.r);
    drop(indexed);
    crate::f5c_replay::release_flat_output(&mut flat_memo, output);
    crate::f5c_generalization::release_flat_post_r_lanes(&mut flat_memo);
    for lane in [
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert_eq!(
            flat_memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
    }
    let mut missing_boxed_memo = F5cComponentExpansionMemo::default();
    assert_eq!(
        F5cGeneralizer::boxed_post_r_for_test(
            &test_source_meter,
            &mut missing_boxed_memo,
            &boxed_predicate,
            &boxed_bounds,
            &[1],
            &traces,
            &candidates,
            &[1, 2, 4, 5, 6, 7, 8],
            &positive,
            &negative,
        )
        .err(),
        Some(SolveAvailabilityError::IdentityExhausted)
    );
    let mut missing_flat_memo = F5cComponentExpansionMemo::default();
    assert_eq!(
        F5cGeneralizer::flat_post_r_for_test(
            &mut missing_flat_memo,
            &flat,
            &flat_bounds,
            &[1],
            &traces,
            &candidates,
            &[1, 2, 4, 5, 6, 7, 8],
            &positive,
            &negative,
        )
        .err(),
        Some(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        missing_flat_memo.walker_resources.lanes[F5cWalkerLaneKind::RetainedOwnerBounds as usize]
            .actual_capacity,
        0
    );
    for lane in [
        F5cWalkerLaneKind::BoxedRetainedOwnerBounds,
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert_eq!(
            missing_boxed_memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
    }
}

#[test]
fn post_r_failure_aborts_memo_after_replay_output_and_retries_warm_lookup() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_generalization::F5cGuardedTrace;
    use std::collections::{HashMap, HashSet};

    let batch = collect(module("my f = 1", "f5c-post-r-rollback"));
    let mut session = InferenceSession::new(batch);
    let warm = session.fresh_value_at_level(1).unwrap();
    let owner = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[owner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[relay as usize].direct_lower_rows.push(owner);
    let (result, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(warm);
    assert!(result.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    generalizer.memo.reset_active_scratch();
    let before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.parent_heads.clone(),
        generalizer.memo.reverse_parents.clone(),
        generalizer.memo.incidence_heads.clone(),
        generalizer.memo.incidences.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.root_edges.clone(),
        (
            generalizer.memo.root_edge_marks.clone(),
            generalizer.memo.root_edge_mark_epoch,
            generalizer.memo.root_undo.clone(),
            generalizer.memo.visit_epochs.clone(),
            generalizer.memo.visit_epoch,
        ),
    );
    let forest = generalizer.build_raw_forest(owner).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let work_before = generalizer.memo.work_meter.get();
    let trace = F5cGuardedTrace {
        owner,
        entry_polarity: Polarity::Positive,
        reentry_polarity: Polarity::Positive,
        path: Vec::new(),
    };
    let error = generalizer.flat_r_q_with_raw_forest_candidate_for_test(
        forest,
        &[trace],
        &HashMap::from([(owner, vec![0])]),
        &[],
        |_| true,
        &positive,
        &negative,
        &HashSet::new(),
        &HashSet::new(),
        true,
    );
    assert!(matches!(
        error,
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(crate::f5c_replay::failed_after_flat_output_count() > 0);
    assert!(generalizer.memo.work_meter.get() > work_before);
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.parent_heads.clone(),
            generalizer.memo.reverse_parents.clone(),
            generalizer.memo.incidence_heads.clone(),
            generalizer.memo.incidences.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.root_edges.clone(),
            (
                generalizer.memo.root_edge_marks.clone(),
                generalizer.memo.root_edge_mark_epoch,
                generalizer.memo.root_undo.clone(),
                generalizer.memo.visit_epochs.clone(),
                generalizer.memo.visit_epoch,
            ),
        ),
        before,
    );
    for lane in [
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
        assert_eq!(
            generalizer.memo.walker_resources.independent_lanes[lane as usize].actual_capacity,
            0
        );
    }
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    generalizer.memo.work_meter.set(0);
    assert!(matches!(
        generalizer.positive_row(warm, false).unwrap(),
        F5cPositive::Shared(_)
    ));
}

#[test]
fn post_r_success_retains_predicate_output_until_forest_release() {
    let test_source_meter = DraftHeapMeter::default();
    use std::collections::{HashMap, HashSet};
    let batch = collect(module("my f = 1", "f5c-post-r-success"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(root).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let (selection, output, forest) = generalizer
        .flat_r_q_with_raw_forest_candidate_for_test(
            forest,
            &[],
            &HashMap::new(),
            &[],
            |_| true,
            &positive,
            &negative,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    assert!(selection.retained_bounds.is_empty());
    assert!(selection.recursive_owners.is_empty());
    assert!(selection.q.is_empty() && selection.r.is_empty());
    assert!(
        output
            .positive_nodes
            .get(selection.retained_predicate.0 as usize)
            .is_some()
    );
    generalizer.release_flat_r_q_for_test(selection, output, forest);
}

#[test]
fn selected_flat_candidate_completes_under_open_raw_forest() {
    let test_source_meter = DraftHeapMeter::default();
    use std::collections::{HashMap, HashSet};
    let batch = collect(module("my f = 1", "f5c-flat-selected-candidate"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(root).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let (selection, output, forest) = generalizer
        .flat_r_q_with_raw_forest_candidate_for_test(
            forest,
            &[],
            &HashMap::new(),
            &[],
            |_| true,
            &positive,
            &negative,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    let selected_positive_slots = output.positive_nodes.len();
    let candidate = generalizer
        .flat_finish_selected_candidate(
            selection,
            output,
            forest,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    let draft = &candidate.draft;
    assert_eq!(draft.quantifier_count, 0);
    assert!(draft.recursive_bounds.is_empty());
    assert_eq!(
        draft.positive_nodes[draft.predicate.unwrap().0 as usize],
        crate::f5c_draft::PositiveNode::Int
    );
    assert_eq!(candidate.stats.key_writes, 1);
    assert_eq!(
        generalizer.memo.walker_resources.flat_candidate_lanes
            [crate::f5c_normalization::LANE_COUNT]
            .requested_slots,
        selected_positive_slots,
    );
    assert_eq!(
        generalizer.memo.walker_resources.flat_candidate_lanes
            [crate::f5c_normalization::LANE_COUNT + 8]
            .requested_slots,
        draft.positive_nodes.len(),
    );
    assert_eq!(
        generalizer.memo.walker_resources.lanes
            [F5cWalkerLaneKind::NormalizedPositiveNodes as usize]
            .requested_slots,
        0,
    );
    assert_eq!(
        generalizer.memo.walker_resources.lanes
            [F5cWalkerLaneKind::NormalizedRecursiveBounds as usize]
            .requested_slots,
        0,
    );
    let main_requests = generalizer
        .memo
        .walker_resources
        .lanes
        .iter()
        .map(|lane| lane.requested_slots)
        .sum::<usize>();
    let flat_requests = generalizer
        .memo
        .walker_resources
        .flat_candidate_lanes
        .iter()
        .map(|lane| lane.requested_slots)
        .sum::<usize>();
    assert_eq!(
        generalizer.memo.walker_resources.requested_slots().unwrap(),
        main_requests + flat_requests,
    );
    assert!(
        generalizer.memo.walker_resources.lanes
            [F5cWalkerLaneKind::NormalizedPositiveNodes as usize]
            .actual_capacity
            > 0
    );
    generalizer.release_normalized_candidate(candidate);
    assert_eq!(
        generalizer.memo.walker_resources.lanes
            [F5cWalkerLaneKind::NormalizedPositiveNodes as usize]
            .actual_capacity,
        0
    );
}

#[test]
fn flat_candidate_entrypoint_returns_normalized_draft() {
    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-entrypoint"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &source_meter);
    let candidate = generalizer.build_flat_candidate(root, false).unwrap();
    assert_eq!(candidate.draft.quantifier_count, 0);
    let predicate = candidate.draft.predicate.unwrap();
    assert!(matches!(
        candidate.draft.positive_nodes[predicate.0 as usize],
        crate::f5c_draft::PositiveNode::Int
    ));
    assert!(candidate.stats.key_writes > 0);
    for kind in [
        F5cWalkerLaneKind::NormalizedPositiveNodes,
        F5cWalkerLaneKind::NormalizedNegativeNodes,
        F5cWalkerLaneKind::NormalizedPositiveChildren,
        F5cWalkerLaneKind::NormalizedNegativeChildren,
        F5cWalkerLaneKind::NormalizedRecursiveBounds,
        F5cWalkerLaneKind::NormalizedInsertionOrder,
    ] {
        let lane = &generalizer.memo.walker_resources.lanes[kind as usize];
        assert_eq!(
            lane.actual_capacity,
            match kind {
                F5cWalkerLaneKind::NormalizedPositiveNodes =>
                    candidate.draft.positive_nodes.capacity(),
                F5cWalkerLaneKind::NormalizedNegativeNodes =>
                    candidate.draft.negative_nodes.capacity(),
                F5cWalkerLaneKind::NormalizedPositiveChildren =>
                    candidate.draft.positive_children.capacity(),
                F5cWalkerLaneKind::NormalizedNegativeChildren =>
                    candidate.draft.negative_children.capacity(),
                F5cWalkerLaneKind::NormalizedRecursiveBounds =>
                    candidate.draft.recursive_bounds.capacity(),
                F5cWalkerLaneKind::NormalizedInsertionOrder =>
                    candidate.draft.insertion_order.capacity(),
                _ => unreachable!(),
            }
        );
    }
    assert!(matches!(
        generalizer.build_flat_candidate(root, false),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    generalizer.release_normalized_candidate(candidate);
    for kind in [
        F5cWalkerLaneKind::NormalizedPositiveNodes,
        F5cWalkerLaneKind::NormalizedNegativeNodes,
        F5cWalkerLaneKind::NormalizedPositiveChildren,
        F5cWalkerLaneKind::NormalizedNegativeChildren,
        F5cWalkerLaneKind::NormalizedRecursiveBounds,
        F5cWalkerLaneKind::NormalizedInsertionOrder,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
    let retried = generalizer.build_flat_candidate(root, false).unwrap();
    generalizer.release_normalized_candidate(retried);
}

#[test]
fn staged_flat_candidate_rejects_second_live_publication_and_retries() {
    use std::collections::{HashMap, HashSet};

    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-staged-live-owner"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &source_meter);
    let candidate_a = generalizer.build_flat_candidate(root, false).unwrap();
    let draft_a_before = (
        candidate_a.draft.quantifier_count,
        candidate_a.draft.predicate,
        candidate_a.draft.positive_nodes.clone(),
        candidate_a.draft.negative_nodes.clone(),
        candidate_a.draft.positive_children.clone(),
        candidate_a.draft.negative_children.clone(),
        candidate_a.draft.recursive_bounds.clone(),
        candidate_a.draft.insertion_order.clone(),
    );
    let stats_a_before = (
        candidate_a.stats.key_writes,
        candidate_a.stats.child_comparisons,
        candidate_a.stats.descriptor_words,
        candidate_a.stats.word_comparisons,
        candidate_a.stats.duplicates,
    );
    let memo_before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.parent_heads.clone(),
        generalizer.memo.reverse_parents.clone(),
        generalizer.memo.incidence_heads.clone(),
        generalizer.memo.incidences.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.root_edges.clone(),
        (
            generalizer.memo.root_edge_marks.clone(),
            generalizer.memo.root_edge_mark_epoch,
            generalizer.memo.root_undo.clone(),
            generalizer.memo.visit_epochs.clone(),
            generalizer.memo.visit_epoch,
        ),
    );
    let output_lanes = [
        F5cWalkerLaneKind::NormalizedPositiveNodes,
        F5cWalkerLaneKind::NormalizedNegativeNodes,
        F5cWalkerLaneKind::NormalizedPositiveChildren,
        F5cWalkerLaneKind::NormalizedNegativeChildren,
        F5cWalkerLaneKind::NormalizedRecursiveBounds,
        F5cWalkerLaneKind::NormalizedInsertionOrder,
    ];
    let retained = output_lanes.map(|kind| {
        let lane = &generalizer.memo.walker_resources.lanes[kind as usize];
        (lane.actual_capacity, lane.requested_slots)
    });
    let idle_checkpoint_before = generalizer.component_idle_checkpoint_for_test();

    let forest = generalizer.build_raw_forest(root).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let (selection, output, forest) = generalizer
        .flat_r_q_with_raw_forest_candidate_for_test(
            forest,
            &[],
            &HashMap::new(),
            &[],
            |_| true,
            &positive,
            &negative,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    assert!(matches!(
        generalizer.flat_finish_selected_candidate(
            selection,
            output,
            forest,
            &HashSet::new(),
            &HashSet::new(),
            false,
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    assert!(generalizer.memo.work.is_empty());
    assert!(generalizer.memo.conflict_journal.is_empty());
    assert!(generalizer.active.is_empty());
    assert!(generalizer.active_set.is_empty());
    assert!(generalizer.frames.is_empty());
    assert!(generalizer.path.is_empty());
    assert!(generalizer.order.is_empty());
    assert!(generalizer.order_seen.is_empty());
    assert!(generalizer.reentries.is_empty());
    assert_eq!(idle_checkpoint_before.0, false);
    assert_eq!(idle_checkpoint_before.1, false);
    assert_eq!(idle_checkpoint_before.2, false);
    assert_eq!(
        generalizer.component_idle_checkpoint_for_test(),
        idle_checkpoint_before,
    );
    assert_eq!(
        (
            candidate_a.draft.quantifier_count,
            candidate_a.draft.predicate,
            candidate_a.draft.positive_nodes.clone(),
            candidate_a.draft.negative_nodes.clone(),
            candidate_a.draft.positive_children.clone(),
            candidate_a.draft.negative_children.clone(),
            candidate_a.draft.recursive_bounds.clone(),
            candidate_a.draft.insertion_order.clone(),
        ),
        draft_a_before,
    );
    assert_eq!(
        (
            candidate_a.stats.key_writes,
            candidate_a.stats.child_comparisons,
            candidate_a.stats.descriptor_words,
            candidate_a.stats.word_comparisons,
            candidate_a.stats.duplicates,
        ),
        stats_a_before,
    );
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.parent_heads.clone(),
            generalizer.memo.reverse_parents.clone(),
            generalizer.memo.incidence_heads.clone(),
            generalizer.memo.incidences.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.root_edges.clone(),
            (
                generalizer.memo.root_edge_marks.clone(),
                generalizer.memo.root_edge_mark_epoch,
                generalizer.memo.root_undo.clone(),
                generalizer.memo.visit_epochs.clone(),
                generalizer.memo.visit_epoch,
            ),
        ),
        memo_before,
    );
    for (kind, expected) in output_lanes.into_iter().zip(retained) {
        let lane = &generalizer.memo.walker_resources.lanes[kind as usize];
        assert_eq!((lane.actual_capacity, lane.requested_slots), expected);
    }
    for kind in [
        F5cWalkerLaneKind::RawOwnerOrder,
        F5cWalkerLaneKind::RawOwnerBounds,
        F5cWalkerLaneKind::RawCallbackTrace,
        F5cWalkerLaneKind::DraftPositiveNodes,
        F5cWalkerLaneKind::DraftNegativeNodes,
        F5cWalkerLaneKind::DraftPositiveChildren,
        F5cWalkerLaneKind::DraftNegativeChildren,
        F5cWalkerLaneKind::DraftRecursiveBounds,
        F5cWalkerLaneKind::DraftInsertionOrder,
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }

    generalizer.release_normalized_candidate(candidate_a);
    let candidate_b = generalizer.build_flat_candidate(root, false).unwrap();
    generalizer.release_normalized_candidate(candidate_b);
}

#[test]
fn staged_flat_candidates_transfer_six_buffers_and_retry() {
    use crate::f5c_generalization::F5cStagedCandidate;
    fn vector_bytes<T>(values: &Vec<T>) -> u128 {
        values.capacity() as u128 * std::mem::size_of::<T>() as u128
    }
    fn physical_snapshot(
        generalizer: &mut F5cGeneralizer<'_, '_>,
        staged: &TrackedVec<'_, F5cStagedCandidate<'_>>,
        source_meter: &DraftHeapMeter,
    ) -> u128 {
        let source = staged.capacity() as u128
            * std::mem::size_of::<F5cStagedCandidate<'_>>() as u128
            + staged.iter().fold(0, |sum, member| {
                let draft = &member.candidate.draft;
                sum + vector_bytes(&draft.positive_nodes)
                    + vector_bytes(&draft.negative_nodes)
                    + vector_bytes(&draft.positive_children)
                    + vector_bytes(&draft.negative_children)
                    + vector_bytes(&draft.recursive_bounds)
                    + vector_bytes(&draft.insertion_order)
            });
        assert_eq!(source_meter.current_bytes(), Some(source as usize));
        generalizer.observe_staged_physical_source(source);
        let joint = &generalizer.memo.walker_resources.physical_joint;
        assert!(!joint.aggregate_overflow);
        assert_eq!(joint.staged_source_current, source);
        assert_eq!(joint.source_current, 0);
        assert_eq!(
            joint.memo_current as usize,
            generalizer.memo.retained_bytes().unwrap()
        );
        assert_eq!(
            joint.walker_current as usize,
            generalizer.memo.walker_resources.retained_bytes().unwrap()
        );
        let total = source + joint.memo_current + joint.walker_current;
        assert!(joint.peak >= total);
        total
    }
    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-two-staged"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut staged = TrackedVec::new(&source_meter);
    staged.try_reserve(2).unwrap();
    let baseline = source_meter.current_bytes().unwrap();
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &source_meter);
    physical_snapshot(&mut generalizer, &staged, &source_meter);
    let kinds = [
        F5cWalkerLaneKind::NormalizedPositiveNodes,
        F5cWalkerLaneKind::NormalizedNegativeNodes,
        F5cWalkerLaneKind::NormalizedPositiveChildren,
        F5cWalkerLaneKind::NormalizedNegativeChildren,
        F5cWalkerLaneKind::NormalizedRecursiveBounds,
        F5cWalkerLaneKind::NormalizedInsertionOrder,
    ];
    let mut sizes = [0; 2];
    for (fail_preflight, fail_observe) in [(true, false), (false, true)] {
        let candidate = generalizer.build_flat_candidate(root, false).unwrap();
        let before_requests = kinds
            .map(|kind| generalizer.memo.walker_resources.lanes[kind as usize].requested_slots);
        assert_eq!(
            generalizer.stage_normalized_candidate_with_failure(
                &mut staged,
                candidate,
                fail_preflight,
                fail_observe,
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert!(staged.is_empty());
        assert_eq!(source_meter.current_bytes(), Some(baseline));
        physical_snapshot(&mut generalizer, &staged, &source_meter);
        for (kind, requested) in kinds.iter().zip(before_requests) {
            let lane = &generalizer.memo.walker_resources.lanes[*kind as usize];
            assert_eq!(lane.actual_capacity, 0);
            assert_eq!(lane.requested_slots, requested);
        }
    }
    for slot in 0..2 {
        let candidate = generalizer.build_flat_candidate(root, false).unwrap();
        physical_snapshot(&mut generalizer, &staged, &source_meter);
        let before_requests = kinds
            .map(|kind| generalizer.memo.walker_resources.lanes[kind as usize].requested_slots);
        let bytes = kinds
            .iter()
            .map(|kind| {
                let lane = &generalizer.memo.walker_resources.lanes[*kind as usize];
                lane.actual_capacity * kind.slot_size()
            })
            .sum::<usize>();
        sizes[slot] = bytes;
        let before = &generalizer.memo.walker_resources.physical_joint;
        assert!(!before.aggregate_overflow);
        assert_eq!(
            before.walker_current as usize,
            generalizer.memo.walker_resources.retained_bytes().unwrap()
        );
        let walker_before = before.walker_current;
        generalizer
            .stage_normalized_candidate(&mut staged, candidate)
            .unwrap();
        assert_eq!(
            source_meter.current_bytes().unwrap(),
            baseline + sizes[..=slot].iter().sum::<usize>()
        );
        for (kind, requested) in kinds.iter().zip(before_requests) {
            let lane = &generalizer.memo.walker_resources.lanes[*kind as usize];
            assert_eq!(lane.actual_capacity, 0);
            assert_eq!(lane.requested_slots, requested);
        }
        assert_eq!(staged.len(), slot + 1);
        physical_snapshot(&mut generalizer, &staged, &source_meter);
        let after = &generalizer.memo.walker_resources.physical_joint;
        assert!(!after.aggregate_overflow);
        assert_eq!(
            after.walker_current as usize,
            generalizer.memo.walker_resources.retained_bytes().unwrap()
        );
        assert_eq!(
            walker_before as usize - after.walker_current as usize,
            bytes
        );
        assert_eq!(
            staged[slot].candidate.draft.predicate,
            Some(crate::f5c_draft::PositiveId(0))
        );
    }
    staged.clear();
    assert_eq!(source_meter.current_bytes(), Some(baseline));
    physical_snapshot(&mut generalizer, &staged, &source_meter);
    let retry = generalizer.build_flat_candidate(root, false).unwrap();
    physical_snapshot(&mut generalizer, &staged, &source_meter);
    generalizer.release_normalized_candidate(retry);
    physical_snapshot(&mut generalizer, &staged, &source_meter);
}

#[test]
fn staged_second_root_failure_restores_only_its_memo_transaction() {
    use crate::f5c_generalization::F5cStagedCandidate;

    macro_rules! semantic_memo {
        ($memo:expr) => {{
            let memo = &$memo;
            (
                (memo.roots.clone(), memo.nodes.clone()),
                (
                    memo.children.clone(),
                    memo.parent_heads.clone(),
                    memo.reverse_parents.clone(),
                    memo.incidence_heads.clone(),
                    memo.incidences.clone(),
                ),
                (
                    memo.root_heads.clone(),
                    memo.root_edges.clone(),
                    memo.root_edge_marks.clone(),
                    memo.root_undo.clone(),
                ),
            )
        }};
    }

    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-stage-atomic-roots"));
    let mut session = InferenceSession::new(batch);
    let a = session.fresh_value_at_level(1).unwrap();
    let b = session.fresh_value_at_level(1).unwrap();
    for root in [a, b] {
        let child = session.fresh_value_at_level(1).unwrap();
        session.bounds[child as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::IntPositive);
        session.bounds[root as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::ValueRow(child));
    }
    let mut staged = TrackedVec::<F5cStagedCandidate<'_>>::new(&source_meter);
    staged.try_reserve(2).unwrap();
    let memo = F5cComponentExpansionMemo::default();
    let (a_result, memo, _, _) = F5cGeneralizer::with_memo(&session, &source_meter, memo, 0)
        .build_and_stage_flat_candidate(a, &mut staged);
    a_result.unwrap();
    let mut ledger = IndependentResourceLedger::default();
    ledger.record_flat_staged(&staged, &source_meter).unwrap();
    assert_eq!(ledger.flat_staged_census_members, 1);
    ledger.record_flat_transfer(&memo).unwrap();
    let post_a = semantic_memo!(memo);
    let a_draft = staged[0].candidate.draft.positive_nodes.clone();
    let a_meter = source_meter.current_bytes();

    let (b_failure, memo, _, _) = F5cGeneralizer::with_memo(&session, &source_meter, memo, 0)
        .build_and_stage_flat_candidate_with_failure(b, &mut staged);
    assert_eq!(b_failure, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(semantic_memo!(memo), post_a);
    assert_eq!(staged.len(), 1);
    assert_eq!(staged[0].candidate.draft.positive_nodes, a_draft);
    assert_eq!(source_meter.current_bytes(), a_meter);

    let (b_result, memo, _, _) = F5cGeneralizer::with_memo(&session, &source_meter, memo, 0)
        .build_and_stage_flat_candidate(b, &mut staged);
    b_result.unwrap();
    ledger.record_flat_staged(&staged, &source_meter).unwrap();
    assert_eq!(ledger.flat_staged_census_members, 2);
    ledger.record_flat_staged(&staged, &source_meter).unwrap();
    assert_eq!(ledger.flat_staged_census_members, 2);
    ledger
        .reconcile_flat_staged(&staged, &source_meter)
        .unwrap();
    assert_eq!(ledger.flat_staged_census_members, 4);
    ledger.record_flat_transfer(&memo).unwrap();
    assert!(ledger.flat_transfer_raw_bytes > 0);
    assert!(ledger.flat_transfer_peak_bytes > ledger.flat_staged_bytes);
    assert_eq!(staged.len(), 2);
    assert_eq!(staged[0].candidate.draft.positive_nodes, a_draft);
    assert!(memo.roots.len() > post_a.0.0.len());
    assert_eq!(memo.transfer_raw_staged_samples.len(), 2);
    for (raw, staged_source, simultaneous) in &memo.transfer_raw_staged_samples {
        assert!(*raw > 0);
        assert!(*staged_source >= a_meter.unwrap() as u128);
        assert!(*simultaneous >= raw + staged_source);
    }
    staged.clear();
    assert_eq!(
        source_meter.current_bytes(),
        Some(staged.capacity() * std::mem::size_of::<F5cStagedCandidate<'_>>())
    );
}

#[test]
fn staged_batch_normalization_failure_discards_all_members_and_restores_memo() {
    use crate::f5c_generalization::F5cStagedCandidate;

    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-stage-normalization-failure"));
    let mut session = InferenceSession::new(batch);
    let a = session.fresh_value_at_level(1).unwrap();
    let b = session.fresh_value_at_level(1).unwrap();
    for root in [a, b] {
        let child = session.fresh_value_at_level(1).unwrap();
        session.bounds[child as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::IntPositive);
        session.bounds[root as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::ValueRow(child));
    }
    let mut staged = TrackedVec::<F5cStagedCandidate<'_>>::new(&source_meter);
    staged.try_reserve(2).unwrap();
    let baseline_bytes = source_meter.current_bytes();
    let mut memo = F5cComponentExpansionMemo::default();
    let checkpoint = memo.begin_flat_batch();
    let baseline_roots = memo.roots.clone();
    let baseline_nodes = memo.nodes.clone();
    let baseline_children = memo.children.clone();
    let baseline_parent_heads = memo.parent_heads.clone();
    let baseline_reverse = memo.reverse_parents.clone();
    let baseline_incidence_heads = memo.incidence_heads.clone();
    let baseline_incidences = memo.incidences.clone();
    let baseline_root_heads = memo.root_heads.clone();
    let baseline_root_edges = memo.root_edges.clone();
    let baseline_root_edge_marks = memo.root_edge_marks.clone();
    for (index, root) in [a, b].into_iter().enumerate() {
        let mut generalizer = F5cGeneralizer::with_memo(&session, &source_meter, memo, 0);
        if index == 1 {
            let key = *generalizer
                .memo
                .roots
                .keys()
                .find(|key| key.polarity == Polarity::Positive)
                .expect("first member retains a positive memo root");
            let value = generalizer
                .walk_flat(F5cWalkTask::EnterRow {
                    row: key.row,
                    polarity: key.polarity,
                    root: false,
                })
                .unwrap();
            assert!(value.positive_shared_id().is_some());
            assert_eq!(generalizer.shared_summary_hits, 1);
        }
        let (result, returned, _, _) =
            generalizer.build_and_stage_flat_raw_candidate(root, &mut staged);
        result.unwrap();
        memo = returned;
    }
    assert_eq!(staged.len(), 2);
    assert!(!memo.root_undo.is_empty());
    assert_eq!(
        crate::f5c_normalization::normalize_flat_batch_metered(
            &mut memo,
            &source_meter,
            &mut staged,
            Some(0),
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    let map_lane = crate::f5c_normalization::LANE_COUNT + 4;
    assert_eq!(
        memo.walker_resources.flat_candidate_lanes[map_lane].observations,
        1
    );
    let mut independent = IndependentResourceLedger::default();
    independent.record_flat_normalization_peaks(&memo).unwrap();
    assert!(independent.flat_normalization_peak_bytes > 0);
    let earlier_peak = independent.flat_normalization_peak_bytes;
    let earlier_scratch_peak = independent.flat_normalization_scratch_peak_bytes;
    independent
        .record_flat_normalization_peaks(&F5cComponentExpansionMemo::default())
        .unwrap();
    assert_eq!(independent.flat_normalization_peak_bytes, earlier_peak);
    assert_eq!(
        independent.flat_normalization_scratch_peak_bytes,
        earlier_scratch_peak
    );
    staged.clear();
    memo.finish_flat_batch(checkpoint, false).unwrap();
    assert_eq!(source_meter.current_bytes(), baseline_bytes);
    assert_eq!(memo.roots, baseline_roots);
    assert_eq!(memo.nodes, baseline_nodes);
    assert_eq!(memo.children, baseline_children);
    assert_eq!(memo.parent_heads, baseline_parent_heads);
    assert_eq!(memo.reverse_parents, baseline_reverse);
    assert_eq!(memo.incidence_heads, baseline_incidence_heads);
    assert_eq!(memo.incidences, baseline_incidences);
    assert_eq!(memo.root_heads, baseline_root_heads);
    assert_eq!(memo.root_edges, baseline_root_edges);
    assert_eq!(memo.root_edge_marks, baseline_root_edge_marks);
    assert!(memo.root_undo.is_empty());

    let retry_checkpoint = memo.begin_flat_batch();
    for root in [a, b] {
        let (result, returned, _, _) = F5cGeneralizer::with_memo(&session, &source_meter, memo, 0)
            .build_and_stage_flat_raw_candidate(root, &mut staged);
        result.unwrap();
        memo = returned;
    }
    crate::f5c_normalization::normalize_flat_batch_metered(
        &mut memo,
        &source_meter,
        &mut staged,
        None,
    )
    .unwrap();
    assert_eq!(
        memo.walker_resources.flat_candidate_lanes[map_lane].observations,
        2
    );
    memo.finish_flat_batch(retry_checkpoint, true).unwrap();
    assert_eq!(staged.len(), 2);
}

#[test]
fn flat_candidate_entrypoint_late_r_q_failure_releases_transient_lanes() {
    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-entrypoint-rollback"));
    let mut session = InferenceSession::new(batch);
    let warm = session.fresh_value_at_level(1).unwrap();
    let owner = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[owner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[relay as usize].direct_lower_rows.push(owner);

    let (warm_result, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &source_meter).build_component(warm);
    assert!(warm_result.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, &source_meter, memo, 0);
    generalizer.memo.reset_active_scratch();
    let before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.root_edges.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.incidences.clone(),
    );
    let failed = generalizer.build_flat_candidate(owner, true);
    assert!(matches!(
        failed,
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(crate::f5c_replay::failed_after_flat_output_count() > 0);
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.root_edges.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.incidences.clone(),
        ),
        before,
    );
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    assert!(generalizer.memo.conflict_journal.is_empty());
    assert!(generalizer.memo.work.is_empty());
    assert!(generalizer.order.is_empty());
    assert!(generalizer.reentries.is_empty());
    for lane in [
        F5cWalkerLaneKind::BoxedPositiveOnly,
        F5cWalkerLaneKind::BoxedNegativeOnly,
        F5cWalkerLaneKind::Order,
        F5cWalkerLaneKind::Reentries,
        F5cWalkerLaneKind::ReentryPaths,
        F5cWalkerLaneKind::BoxedReentriesByOwner,
        F5cWalkerLaneKind::BoxedReentryIndices,
        F5cWalkerLaneKind::RawPositiveIncidences,
        F5cWalkerLaneKind::RawNegativeIncidences,
        F5cWalkerLaneKind::RawOwnerOrder,
        F5cWalkerLaneKind::RawOwnerBounds,
        F5cWalkerLaneKind::RawCallbackTrace,
        F5cWalkerLaneKind::DraftPositiveNodes,
        F5cWalkerLaneKind::DraftNegativeNodes,
        F5cWalkerLaneKind::DraftPositiveChildren,
        F5cWalkerLaneKind::DraftNegativeChildren,
        F5cWalkerLaneKind::DraftRecursiveBounds,
        F5cWalkerLaneKind::DraftInsertionOrder,
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRSurvivingBounds,
        F5cWalkerLaneKind::PostRSurvivingTraces,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostROccurrenceOrder,
        F5cWalkerLaneKind::PostROccurrenceSeen,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
        assert_eq!(
            generalizer.memo.walker_resources.independent_lanes[lane as usize].actual_capacity,
            0
        );
    }
    generalizer.memo.work_meter.set(0);
    let retried = generalizer.build_flat_candidate(owner, false).unwrap();
    assert!(retried.draft.predicate.is_some());
    generalizer.release_normalized_candidate(retried);
}

#[test]
fn flat_candidate_entrypoint_preparation_failure_releases_one_sided_lane() {
    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-preparation-rollback"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[relay as usize].direct_lower_rows.push(root);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &source_meter);
    generalizer.memo.fail_reserve_at =
        Some((F5cTestReserveFailure::FlatPreparationAfterPositiveOnly, 0));
    assert!(matches!(
        generalizer.build_flat_candidate(root, false),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(generalizer.memo.fail_reserve_at, None);
    for lane in [
        F5cWalkerLaneKind::BoxedPositiveOnly,
        F5cWalkerLaneKind::BoxedNegativeOnly,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
    }
    generalizer.memo.work_meter.set(0);
    let candidate = generalizer.build_flat_candidate(root, false).unwrap();
    generalizer.release_normalized_candidate(candidate);
}

#[test]
fn flat_candidate_closure_observation_failure_releases_all_closure_lanes() {
    let source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-closure-release-rollback"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.value_metadata[root as usize].non_generic = true;
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &source_meter);
    generalizer.memo.fail_observation_at = Some(F5cTestObservationFailure::ClosureRelease);
    assert!(matches!(
        generalizer.non_generic_closure(),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(generalizer.memo.fail_observation_at.is_none());
    for lane in [
        F5cWalkerLaneKind::ClosureAdjacency,
        F5cWalkerLaneKind::ClosureNeighbors,
        F5cWalkerLaneKind::ClosureConnected,
        F5cWalkerLaneKind::ClosureFrontier,
        F5cWalkerLaneKind::ClosureResult,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
    }
    assert!(generalizer.non_generic_closure().unwrap().contains(&root));
}

#[test]
fn selected_flat_normalization_work_failure_aborts_forest_and_retries_warm_root() {
    let test_source_meter = DraftHeapMeter::default();
    use std::collections::{HashMap, HashSet};
    let batch = collect(module("my f = 1", "f5c-flat-normalization-rollback"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let (built, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(root);
    assert!(built.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    generalizer.memo.reset_active_scratch();
    let before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.parent_heads.clone(),
        generalizer.memo.reverse_parents.clone(),
        generalizer.memo.incidence_heads.clone(),
        generalizer.memo.incidences.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.root_edges.clone(),
        (
            generalizer.memo.root_edge_marks.clone(),
            generalizer.memo.root_edge_mark_epoch,
            generalizer.memo.root_undo.clone(),
            generalizer.memo.visit_epochs.clone(),
            generalizer.memo.visit_epoch,
        ),
    );
    let forest = generalizer.build_raw_forest(root).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let (selection, output, forest) = generalizer
        .flat_r_q_with_raw_forest_candidate_for_test(
            forest,
            &[],
            &HashMap::new(),
            &[],
            |_| true,
            &positive,
            &negative,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    assert!(matches!(
        generalizer.flat_finish_selected_candidate(
            selection,
            output,
            forest,
            &HashSet::new(),
            &HashSet::new(),
            true,
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.parent_heads.clone(),
            generalizer.memo.reverse_parents.clone(),
            generalizer.memo.incidence_heads.clone(),
            generalizer.memo.incidences.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.root_edges.clone(),
            (
                generalizer.memo.root_edge_marks.clone(),
                generalizer.memo.root_edge_mark_epoch,
                generalizer.memo.root_undo.clone(),
                generalizer.memo.visit_epochs.clone(),
                generalizer.memo.visit_epoch,
            ),
        ),
        before,
    );
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    let normalizer_map = generalizer.memo.walker_resources.flat_candidate_lanes
        [crate::f5c_normalization::LANE_COUNT];
    assert!(normalizer_map.observations > 0);
    assert!(normalizer_map.growths > 0);
    assert!(normalizer_map.peak_capacity > 0);
    assert!(normalizer_map.requested_slots > 0);
    assert!(
        generalizer.memo.walker_resources.requested_slots().unwrap()
            >= normalizer_map.requested_slots
    );
    for lane in [
        F5cWalkerLaneKind::RawOwnerOrder,
        F5cWalkerLaneKind::RawOwnerBounds,
        F5cWalkerLaneKind::RawCallbackTrace,
        F5cWalkerLaneKind::DraftPositiveNodes,
        F5cWalkerLaneKind::DraftNegativeNodes,
        F5cWalkerLaneKind::DraftPositiveChildren,
        F5cWalkerLaneKind::DraftNegativeChildren,
        F5cWalkerLaneKind::DraftRecursiveBounds,
        F5cWalkerLaneKind::DraftInsertionOrder,
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        F5cWalkerLaneKind::RetainedOwnerBounds,
        F5cWalkerLaneKind::PostRRecursiveOwners,
        F5cWalkerLaneKind::PostRRecursiveSet,
        F5cWalkerLaneKind::PostRQuantifiers,
        F5cWalkerLaneKind::PostRRecursives,
        F5cWalkerLaneKind::SelectedRecursiveBounds,
        F5cWalkerLaneKind::SelectedPositiveEliminated,
        F5cWalkerLaneKind::SelectedNegativeEliminated,
        F5cWalkerLaneKind::SubstitutePositiveSeen,
        F5cWalkerLaneKind::SubstituteNegativeSeen,
        F5cWalkerLaneKind::SubstituteStack,
        F5cWalkerLaneKind::NormalizedPositiveNodes,
        F5cWalkerLaneKind::NormalizedNegativeNodes,
        F5cWalkerLaneKind::NormalizedPositiveChildren,
        F5cWalkerLaneKind::NormalizedNegativeChildren,
        F5cWalkerLaneKind::NormalizedRecursiveBounds,
        F5cWalkerLaneKind::NormalizedInsertionOrder,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
    }
    generalizer.memo.work_meter.set(0);
    assert!(matches!(
        generalizer.positive_row(root, false).unwrap(),
        F5cPositive::Shared(_)
    ));
}

#[test]
fn selected_flat_normalizer_request_overflow_preserves_shared_lane_counters() {
    let test_source_meter = DraftHeapMeter::default();
    use std::collections::{HashMap, HashSet};
    let batch = collect(module("my f = 1", "f5c-flat-normalizer-request-overflow"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(root).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let (selection, output, forest) = generalizer
        .flat_r_q_with_raw_forest_candidate_for_test(
            forest,
            &[],
            &HashMap::new(),
            &[],
            |_| true,
            &positive,
            &negative,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    let lane = crate::f5c_normalization::LANE_COUNT;
    generalizer.memo.walker_resources.flat_candidate_lanes[lane].requested_slots = usize::MAX;
    let before = generalizer.memo.walker_resources.flat_candidate_lanes;
    assert!(matches!(
        generalizer.flat_finish_selected_candidate(
            selection,
            output,
            forest,
            &HashSet::new(),
            &HashSet::new(),
            false,
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    for (actual, expected) in generalizer
        .memo
        .walker_resources
        .flat_candidate_lanes
        .iter()
        .zip(before.iter())
    {
        assert_eq!(actual.requested_slots, expected.requested_slots);
        assert_eq!(actual.observations, expected.observations);
        assert_eq!(actual.growths, expected.growths);
        assert_eq!(actual.peak_capacity, expected.peak_capacity);
    }
    assert!(generalizer.memo.active_rows.is_empty());
    let retry = generalizer.build_raw_forest(root).unwrap();
    generalizer.release_raw_forest(retry);
}

#[test]
fn selected_flat_published_output_growth_overflow_aborts_forest() {
    let test_source_meter = DraftHeapMeter::default();
    use std::collections::{HashMap, HashSet};
    let batch = collect(module("my f = 1", "f5c-flat-output-request-overflow"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(root).unwrap();
    let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
    let (selection, output, forest) = generalizer
        .flat_r_q_with_raw_forest_candidate_for_test(
            forest,
            &[],
            &HashMap::new(),
            &[],
            |_| true,
            &positive,
            &negative,
            &HashSet::new(),
            &HashSet::new(),
            false,
        )
        .unwrap();
    let lane = F5cWalkerLaneKind::NormalizedPositiveNodes as usize;
    generalizer.memo.walker_resources.lanes[lane].capacity_growths = usize::MAX;
    assert!(matches!(
        generalizer.flat_finish_selected_candidate(
            selection,
            output,
            forest,
            &HashSet::new(),
            &HashSet::new(),
            false,
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(
        generalizer.memo.walker_resources.lanes[lane].capacity_growths,
        usize::MAX
    );
    assert_eq!(
        generalizer.memo.walker_resources.lanes[lane].actual_capacity,
        0
    );
    assert!(generalizer.memo.active_rows.is_empty());
    let retry = generalizer.build_raw_forest(root).unwrap();
    generalizer.release_raw_forest(retry);
}

#[test]
fn selected_flat_candidate_matches_boxed_q_r_and_normalization_counters() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_draft::{FlatDraft, NegativeId, NegativeNode, PositiveId, PositiveNode};
    use std::collections::{HashMap, HashSet};

    fn expand_positive<'meter>(
        meter: &'meter DraftHeapMeter,
        draft: &FlatDraft,
        id: PositiveId,
    ) -> F5cPositive<'meter> {
        match draft.positive_nodes[id.0 as usize] {
            PositiveNode::Bottom => F5cPositive::Bottom,
            PositiveNode::Int => F5cPositive::Int,
            PositiveNode::Quantified(n) => F5cPositive::Quantified(n),
            PositiveNode::Recursive(n) => F5cPositive::Recursive(n),
            PositiveNode::Union(span) => F5cPositive::Union(test_tracked(
                meter,
                draft.positive_children[span.start as usize..(span.start + span.len) as usize]
                    .iter()
                    .map(|&child| expand_positive(meter, draft, child))
                    .collect::<Vec<_>>(),
            )),
            PositiveNode::Function { argument, result } => F5cPositive::Function {
                argument: test_tracked_one(meter, expand_negative(meter, draft, argument)),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: test_tracked_one(meter, expand_positive(meter, draft, result)),
            },
            PositiveNode::Variable(_) => panic!("selected normalized positive is classified"),
        }
    }
    fn expand_negative<'meter>(
        meter: &'meter DraftHeapMeter,
        draft: &FlatDraft,
        id: NegativeId,
    ) -> F5cNegative<'meter> {
        match draft.negative_nodes[id.0 as usize] {
            NegativeNode::Top => F5cNegative::Top,
            NegativeNode::Bottom => F5cNegative::Bottom,
            NegativeNode::Int => F5cNegative::Int,
            NegativeNode::Quantified(n) => F5cNegative::Quantified(n),
            NegativeNode::Recursive(n) => F5cNegative::Recursive(n),
            NegativeNode::Intersection(span) => F5cNegative::Intersection(test_tracked(
                meter,
                draft.negative_children[span.start as usize..(span.start + span.len) as usize]
                    .iter()
                    .map(|&child| expand_negative(meter, draft, child))
                    .collect::<Vec<_>>(),
            )),
            NegativeNode::Function { argument, result } => F5cNegative::Function {
                argument: test_tracked_one(meter, expand_positive(meter, draft, argument)),
                argument_effect: F5cPositiveEffect::Bottom,
                result_effect: F5cNegativeEffect::Empty,
                result: test_tracked_one(meter, expand_negative(meter, draft, result)),
            },
            NegativeNode::Variable(_) => panic!("selected normalized negative is classified"),
        }
    }
    let batch = collect(module("my f = 1", "f5c-flat-selected-parity"));
    let mut session = InferenceSession::new(batch);
    let owner = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    let quantified = session.fresh_value_at_level(1).unwrap();
    let warm = session.fresh_value_at_level(1).unwrap();
    let bound_only = session.fresh_value_at_level(1).unwrap();
    let second_owner = session.fresh_value_at_level(1).unwrap();
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[owner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[owner as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(warm),
            ValueEndpointKey::ValueRow(warm),
        ]);
    session.bounds[owner as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::ValueRow(bound_only));
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[bound_only as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::IntNegative);
    session.bounds[owner as usize]
        .direct_lower_rows
        .push(quantified);
    session.bounds[owner as usize]
        .direct_lower_rows
        .push(second_owner);
    session.bounds[owner as usize]
        .direct_upper_rows
        .push(quantified);
    session.bounds[relay as usize].direct_lower_rows.push(owner);
    let second_result = session
        .live_value_term(Polarity::Positive, second_owner)
        .unwrap();
    let second_function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            second_result,
        )
        .unwrap();
    session.bounds[second_owner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(second_function));

    let mut endpoint_generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let endpoint_candidate = endpoint_generalizer
        .build_flat_candidate(owner, false)
        .unwrap();
    assert_eq!(endpoint_candidate.draft.quantifier_count, 1);
    assert_eq!(endpoint_candidate.draft.recursive_bounds.len(), 2);
    endpoint_generalizer.release_normalized_candidate(endpoint_candidate);

    let mut baseline = None;
    for reverse_bounds in [false, true] {
        let (warm_result, mut boxed_memo, _, _) =
            F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(warm);
        assert!(warm_result.is_ok());
        boxed_memo.boxed_materialization_callback_trace.clear();
        let (boxed_result, boxed_memo, boxed_hits, _) =
            F5cGeneralizer::with_memo(&session, &test_source_meter, boxed_memo, 0)
                .build_component(owner);
        let boxed_callbacks = boxed_memo.boxed_materialization_callback_trace;
        let mut boxed = boxed_result.unwrap();
        let boxed_stats = crate::f5c_normalization::normalize_component(
            &test_source_meter,
            std::slice::from_mut(&mut boxed),
        )
        .unwrap();
        let (warm_result, memo, _, _) =
            F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(warm);
        assert!(warm_result.is_ok());
        let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
        let forest = generalizer
            .build_raw_forest_with_bound_reinsertion_for_test(owner, reverse_bounds)
            .unwrap();
        assert_eq!(forest.raw_owner_order, vec![owner, second_owner]);
        assert_eq!(forest.callback_trace, boxed_callbacks);
        assert_eq!(generalizer.shared_summary_hits, boxed_hits);
        assert!(boxed_hits > 0);
        assert!(boxed_callbacks.contains(&(warm, Polarity::Positive)));
        assert!(boxed_callbacks.contains(&(bound_only, Polarity::Negative)));
        // Both insertion orders retain the same explicit owner traversal order.
        let first_bound = boxed_callbacks
            .iter()
            .position(|&(row, _)| row == bound_only)
            .unwrap();
        assert!(
            boxed_callbacks[..first_bound]
                .iter()
                .any(|&(row, _)| row == warm)
        );
        assert!(
            boxed_callbacks
                .iter()
                .filter(|&&(row, _)| row == warm)
                .count()
                > 1
        );
        let (positive, negative) = generalizer.flat_raw_forest_incidences(&forest).unwrap();
        let traces = generalizer.reentries.clone();
        let order = generalizer.order.clone();
        let mut by_owner = HashMap::<u32, Vec<usize>>::new();
        for (index, trace) in traces.iter().enumerate() {
            by_owner.entry(trace.owner).or_default().push(index);
        }
        let positive_only = positive
            .difference(&negative)
            .copied()
            .collect::<HashSet<_>>();
        let negative_only = negative
            .difference(&positive)
            .copied()
            .collect::<HashSet<_>>();
        let (selection, output, forest) = generalizer
            .flat_r_q_with_raw_forest_candidate_for_test(
                forest,
                &traces,
                &by_owner,
                &order,
                |_| true,
                &positive,
                &negative,
                &positive_only,
                &negative_only,
                false,
            )
            .unwrap();
        assert_eq!(selection.recursive_owners, vec![owner, second_owner]);
        assert_eq!(selection.q, HashMap::from([(quantified, 0)]));
        assert_eq!(selection.r, HashMap::from([(owner, 1), (second_owner, 2)]));
        let parity = (
            boxed_callbacks,
            boxed_hits,
            selection.q.clone(),
            selection.r.clone(),
        );
        if let Some(expected) = &baseline {
            assert_eq!(&parity, expected);
        } else {
            baseline = Some(parity);
        }
        assert!(
            output
                .positive_nodes
                .iter()
                .any(|node| matches!(node, PositiveNode::Variable(_)))
        );
        let candidate = generalizer
            .flat_finish_selected_candidate(
                selection,
                output,
                forest,
                &positive_only,
                &negative_only,
                false,
            )
            .unwrap();
        assert_eq!(candidate.draft.quantifier_count, boxed.quantifier_count);
        assert_eq!(
            candidate.draft.recursive_bounds.len(),
            boxed.recursive_bounds.len()
        );
        assert_eq!(
            candidate.draft.recursive_bounds[0].ordinal,
            boxed.recursive_bounds[0].ordinal
        );
        assert_eq!(
            expand_positive(
                &test_source_meter,
                &candidate.draft,
                candidate.draft.predicate.unwrap()
            ),
            boxed.predicate
        );
        for (flat, boxed) in candidate
            .draft
            .recursive_bounds
            .iter()
            .zip(&boxed.recursive_bounds)
        {
            assert_eq!(
                expand_positive(&test_source_meter, &candidate.draft, flat.lower),
                boxed.lower
            );
            assert_eq!(
                expand_negative(&test_source_meter, &candidate.draft, flat.upper),
                boxed.upper
            );
        }
        assert_eq!(candidate.stats.key_writes, boxed_stats.key_writes);
        assert_eq!(
            candidate.stats.child_comparisons,
            boxed_stats.child_comparisons
        );
        assert_eq!(
            candidate.stats.descriptor_words,
            boxed_stats.descriptor_words
        );
        assert_eq!(
            candidate.stats.word_comparisons,
            boxed_stats.word_comparisons
        );
        assert_eq!(candidate.stats.duplicates, boxed_stats.duplicates);
        let indexed = candidate.draft.indexed(&test_source_meter).unwrap();
        assert!(indexed.retained_bytes().unwrap() > 0);
        assert_eq!(indexed.as_ref().recursive_bounds[0].ordinal, 1);
        assert_eq!(indexed.as_ref().recursive_bounds[1].ordinal, 2);
        let mut indexed_session = ClosedTypeFinalizationSession::try_new().unwrap();
        let (indexed_scheme, _) = indexed_session
            .finalize_indexed_scheme(indexed.as_ref())
            .unwrap()
            .into_parts();
        let mut boxed_session = ClosedTypeFinalizationSession::try_new().unwrap();
        let (boxed_scheme, _) =
            InferenceSession::finalize_generalization_draft_raw(&mut boxed_session, &boxed, false)
                .unwrap()
                .into_parts();
        assert!(
            indexed_session
                .scheme_view(&indexed_scheme)
                .unwrap()
                .alpha_eq(boxed_session.scheme_view(&boxed_scheme).unwrap())
        );
        for (index, lane, length) in [
            (
                0,
                F5cWalkerLaneKind::NormalizedPositiveNodes,
                candidate.draft.positive_nodes.len(),
            ),
            (
                1,
                F5cWalkerLaneKind::NormalizedNegativeNodes,
                candidate.draft.negative_nodes.len(),
            ),
            (
                2,
                F5cWalkerLaneKind::NormalizedPositiveChildren,
                candidate.draft.positive_children.len(),
            ),
            (
                3,
                F5cWalkerLaneKind::NormalizedNegativeChildren,
                candidate.draft.negative_children.len(),
            ),
            (
                4,
                F5cWalkerLaneKind::NormalizedRecursiveBounds,
                candidate.draft.recursive_bounds.len(),
            ),
            (
                5,
                F5cWalkerLaneKind::NormalizedInsertionOrder,
                candidate.draft.insertion_order.len(),
            ),
        ] {
            assert_eq!(
                generalizer.memo.walker_resources.lanes[lane as usize].requested_slots,
                0
            );
            assert_eq!(
                generalizer.memo.walker_resources.flat_candidate_lanes
                    [crate::f5c_normalization::LANE_COUNT + 8 + index]
                    .requested_slots,
                length
            );
        }
        for lane in [
            0,
            8,
            crate::f5c_normalization::LANE_COUNT,
            crate::f5c_normalization::LANE_COUNT + 5,
        ] {
            assert!(
                generalizer.memo.walker_resources.flat_candidate_lanes[lane].requested_slots > 0
            );
        }
        assert_eq!(
            generalizer.memo.walker_resources.flat_candidate_lanes
                [crate::f5c_normalization::LANE_COUNT + 8]
                .requested_slots,
            candidate.draft.positive_nodes.len(),
        );
        assert_eq!(
            candidate
                .draft
                .positive_nodes
                .iter()
                .filter(|node| matches!(node, PositiveNode::Recursive(1)))
                .count(),
            1
        );
        assert!(
            !candidate
                .draft
                .positive_nodes
                .iter()
                .any(|node| matches!(node, PositiveNode::Variable(_)))
        );
        assert!(
            !candidate
                .draft
                .negative_nodes
                .iter()
                .any(|node| matches!(node, NegativeNode::Variable(_)))
        );
        generalizer.release_normalized_candidate(candidate);
    }
}

#[test]
fn indexed_flat_conversion_rejects_incomplete_and_overflowing_input() {
    use crate::f5c_draft::{ChildSpan, FlatDraft, PositiveNode};
    let meter = DraftHeapMeter::default();
    let mut draft = FlatDraft::default();
    assert!(matches!(
        draft.indexed(&meter),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    draft.predicate = Some(draft.positive(PositiveNode::Variable(0)).unwrap());
    let baseline = meter.current_bytes().unwrap();
    assert!(matches!(
        draft.indexed(&meter),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(meter.current_bytes().unwrap(), baseline);
    draft.positive_nodes[0] = PositiveNode::Union(ChildSpan {
        start: u32::MAX,
        len: 1,
    });
    assert!(matches!(
        draft.indexed(&meter),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(meter.current_bytes().unwrap(), baseline);
    draft.positive_nodes[0] = PositiveNode::Int;
    draft.quantifier_count = u32::MAX;
    let upper = draft.negative(crate::f5c_draft::NegativeNode::Top).unwrap();
    let bound = crate::f5c_draft::RecursiveBound {
        ordinal: 0,
        lower: draft.predicate.unwrap(),
        upper,
    };
    let bounds_capacity = draft.recursive_bounds.capacity();
    assert!(matches!(
        draft.bound(bound),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(draft.recursive_bounds.len(), 0);
    assert_eq!(draft.recursive_bounds.capacity(), bounds_capacity);
    draft.quantifier_count = 0;
    draft.bound(bound).unwrap();
    draft.quantifier_count = u32::MAX;
    assert!(matches!(
        draft.indexed(&meter),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(meter.current_bytes().unwrap(), baseline);
    if usize::BITS > u32::BITS {
        assert!(matches!(
            crate::f5c_draft::indexed_count_for_test(
                usize::try_from(u64::from(u32::MAX) + 1).unwrap()
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
    }
}

#[test]
fn normalized_q_r_duplicate_dag_finalizes_like_callback() {
    use crate::f5c_draft::{FlatDraft, NegativeNode, PositiveNode, RecursiveBound};
    use crate::f5c_generalization::F5cRecursiveBound;
    let meter = DraftHeapMeter::default();
    let mut draft = FlatDraft::default();
    draft.quantifier_count = 1;
    let argument = draft.negative(NegativeNode::Top).unwrap();
    let result = draft.positive(PositiveNode::Recursive(1)).unwrap();
    let function = draft
        .positive(PositiveNode::Function { argument, result })
        .unwrap();
    let duplicate_function = draft
        .positive(PositiveNode::Function { argument, result })
        .unwrap();
    assert_ne!(function, duplicate_function);
    let quantified = draft.positive(PositiveNode::Quantified(0)).unwrap();
    let span = draft
        .positive_span(&[function, duplicate_function, quantified])
        .unwrap();
    draft.predicate = Some(draft.positive(PositiveNode::Union(span)).unwrap());
    draft
        .bound(RecursiveBound {
            ordinal: 1,
            lower: function,
            upper: argument,
        })
        .unwrap();
    let (normalized, stats) = crate::f5c_normalization::normalize_flat(&draft).unwrap();
    assert!(stats.duplicates > 0);
    let root = normalized.predicate.unwrap();
    let PositiveNode::Union(span) = normalized.positive_nodes[root.0 as usize] else {
        panic!("union root")
    };
    assert_eq!(span.len, 2);
    assert!(
        normalized.positive_children[span.start as usize..(span.start + span.len) as usize]
            .contains(&normalized.recursive_bounds[0].lower)
    );
    let indexed = normalized.indexed(&meter).unwrap();
    assert_eq!(indexed.as_ref().quantifier_count, 1);
    assert_eq!(indexed.as_ref().recursive_bounds[0].ordinal, 1);
    let retained = indexed.retained_bytes().unwrap();
    assert!(retained > 0);
    assert_eq!(meter.current_bytes().unwrap(), retained);
    let mut indexed_session = ClosedTypeFinalizationSession::try_new().unwrap();
    let (indexed_scheme, _) = indexed_session
        .finalize_indexed_scheme(indexed.as_ref())
        .unwrap()
        .into_parts();

    let boxed_function = || F5cPositive::Function {
        argument: test_tracked_one(&meter, F5cNegative::Top),
        argument_effect: F5cNegativeEffect::Empty,
        result_effect: F5cPositiveEffect::Bottom,
        result: test_tracked_one(&meter, F5cPositive::Recursive(1)),
    };
    let mut boxed = GeneralizationDraft {
        quantifier_count: 1,
        predicate: F5cPositive::Union(test_tracked(
            &meter,
            vec![
                boxed_function(),
                boxed_function(),
                F5cPositive::Quantified(0),
            ],
        )),
        recursive_bounds: vec![F5cRecursiveBound {
            ordinal: 1,
            lower: boxed_function(),
            upper: F5cNegative::Top,
        }],
    };
    crate::f5c_normalization::normalize_component(&meter, std::slice::from_mut(&mut boxed))
        .unwrap();
    let mut boxed_session = ClosedTypeFinalizationSession::try_new().unwrap();
    let (boxed_scheme, _) =
        InferenceSession::finalize_generalization_draft_raw(&mut boxed_session, &boxed, false)
            .unwrap()
            .into_parts();
    assert!(
        indexed_session
            .scheme_view(&indexed_scheme)
            .unwrap()
            .alpha_eq(boxed_session.scheme_view(&boxed_scheme).unwrap())
    );
    drop(boxed);
    drop(indexed);
    assert_eq!(meter.current_bytes().unwrap(), 0);
}

#[test]
fn flat_r_replay_failure_aborts_raw_forest_and_retries_warm_lookup() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_generalization::F5cGuardedTrace;
    use std::collections::{HashMap, HashSet};

    let batch = collect(module("my f = 1", "f5c-flat-r-rollback"));
    let mut session = InferenceSession::new(batch);
    let warm = session.fresh_value_at_level(1).unwrap();
    let owner = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[owner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[relay as usize].direct_lower_rows.push(owner);
    let (result, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(warm);
    assert!(result.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    generalizer.memo.reset_active_scratch();
    let before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.parent_heads.clone(),
        generalizer.memo.reverse_parents.clone(),
        generalizer.memo.incidence_heads.clone(),
        generalizer.memo.incidences.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.root_edges.clone(),
        (
            generalizer.memo.root_edge_marks.clone(),
            generalizer.memo.root_edge_mark_epoch,
            generalizer.memo.root_undo.clone(),
            generalizer.memo.visit_epochs.clone(),
            generalizer.memo.visit_epoch,
        ),
    );
    let forest = generalizer.build_raw_forest(owner).unwrap();
    assert_eq!(forest.raw_owner_order, vec![owner]);
    let trace = F5cGuardedTrace {
        owner,
        entry_polarity: Polarity::Positive,
        reentry_polarity: Polarity::Positive,
        path: Vec::new(),
    };
    let index = HashMap::from([(owner, vec![0])]);
    let work_before = generalizer.memo.work_meter.get();
    crate::f5c_replay::inject_failure_after_flat_output();
    let error = generalizer.flat_r_with_raw_forest_for_test(
        forest,
        &[trace],
        &index,
        |_| true,
        &HashSet::new(),
        &HashSet::new(),
    );
    assert_eq!(error.err(), Some(SolveAvailabilityError::IdentityExhausted));
    assert!(crate::f5c_replay::failed_after_flat_output_count() > 0);
    assert!(generalizer.memo.work_meter.get() > work_before);
    for lane in [
        F5cWalkerLaneKind::ReplayActivePositive,
        F5cWalkerLaneKind::ReplayActiveNegative,
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
    ] {
        assert_eq!(
            generalizer.memo.walker_resources.lanes[lane as usize].actual_capacity,
            0
        );
        assert_eq!(
            generalizer.memo.walker_resources.independent_lanes[lane as usize].actual_capacity,
            0
        );
    }
    assert!(
        generalizer.memo.walker_resources.lanes[F5cWalkerLaneKind::ReplayActivePositive as usize]
            .peak_bytes
            > 0
    );
    assert!(
        generalizer.memo.walker_resources.lanes
            [F5cWalkerLaneKind::ReplayOutputPositiveNodes as usize]
            .peak_bytes
            > 0
    );
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.parent_heads.clone(),
            generalizer.memo.reverse_parents.clone(),
            generalizer.memo.incidence_heads.clone(),
            generalizer.memo.incidences.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.root_edges.clone(),
            (
                generalizer.memo.root_edge_marks.clone(),
                generalizer.memo.root_edge_mark_epoch,
                generalizer.memo.root_undo.clone(),
                generalizer.memo.visit_epochs.clone(),
                generalizer.memo.visit_epoch,
            ),
        ),
        before,
    );
    assert!(generalizer.memo.root_undo.is_empty());
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    assert!(generalizer.memo.work.is_empty());
    assert!(generalizer.memo.conflict_journal.is_empty());
    assert!(generalizer.active.is_empty() && generalizer.active_set.is_empty());
    assert!(generalizer.frames.is_empty() && generalizer.path.is_empty());
    assert!(generalizer.flat_sink.arena_is_empty());
    generalizer.memo.work_meter.set(0);
    assert!(matches!(
        generalizer.positive_row(warm, false).unwrap(),
        F5cPositive::Shared(_)
    ));
}

#[test]
fn raw_forest_orders_recursive_bounds_and_defaults() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-forest"));
    let mut session = InferenceSession::new(batch);
    let owner = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[owner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[relay as usize].direct_lower_rows.push(owner);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(owner).unwrap();
    let (positive_incidences, negative_incidences) =
        generalizer.flat_raw_forest_incidences(&forest).unwrap();
    assert!(positive_incidences.contains(&owner));
    assert!(negative_incidences.is_empty());
    assert_eq!(forest.raw_owner_order, vec![owner]);
    assert_eq!(forest.raw_bounds.len(), 1);
    assert!(forest.draft.predicate.is_some());
    assert!(forest.callback_trace.is_empty());
    let (lower, upper) = forest.raw_bounds[&owner];
    assert!(matches!(
        forest.draft.negative_nodes[upper.0 as usize],
        crate::f5c_draft::NegativeNode::Top
    ));
    assert!((lower.0 as usize) < forest.draft.positive_nodes.len());
    generalizer.release_raw_forest(forest);
}

#[test]
fn raw_forest_warm_shared_predicate_marks_and_failed_trace_retries() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-warm"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(row));
    let (built, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(row);
    assert!(built.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let before = generalizer.memo.roots.clone();
    generalizer.memo.walker_resources.lanes
        [crate::f5c_generalization::F5cWalkerLaneKind::RawCallbackTrace as usize]
        .requested_slots = usize::MAX;
    assert!(generalizer.build_raw_forest(root).is_err());
    assert_eq!(generalizer.memo.roots, before);
    assert!(generalizer.flat_sink.arena_is_empty());
    generalizer.memo.walker_resources.lanes
        [crate::f5c_generalization::F5cWalkerLaneKind::RawCallbackTrace as usize]
        .requested_slots = 0;
    let forest = generalizer.build_raw_forest(root).unwrap();
    assert_eq!(forest.callback_trace, vec![(row, Polarity::Positive)]);
    generalizer.release_raw_forest(forest);
}

#[test]
fn raw_forest_later_bound_shared_callback_follows_predicate() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-later-bound"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    let relay = session.fresh_value_at_level(1).unwrap();
    let warm = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::IntNegative);
    let argument = session.negative_top_term().unwrap();
    let result = session.live_value_term(Polarity::Positive, relay).unwrap();
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    session.bounds[root as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::ValueRow(warm));
    session.bounds[relay as usize].direct_lower_rows.push(root);
    let mut warming = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    warming
        .walk_flat(F5cWalkTask::EnterRow {
            row: warm,
            polarity: Polarity::Negative,
            root: false,
        })
        .unwrap();
    let memo = std::mem::take(&mut warming.memo);
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let forest = generalizer.build_raw_forest(root).unwrap();
    assert_eq!(forest.raw_owner_order, vec![root]);
    assert!(forest.callback_trace.contains(&(warm, Polarity::Negative)));
    assert_eq!(
        forest.callback_trace.last(),
        Some(&(warm, Polarity::Negative))
    );
    generalizer.release_raw_forest(forest);
}

#[test]
fn raw_forest_release_advances_memo_checkpoint_before_later_failure() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-success-failure"));
    let mut session = InferenceSession::new(batch);
    let child = session.fresh_value_at_level(1).unwrap();
    let first = session.fresh_value_at_level(1).unwrap();
    let later = session.fresh_value_at_level(1).unwrap();
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[first as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    session.bounds[later as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(first).unwrap();
    let before = generalizer.memo.roots.clone();
    let child_key = crate::f5c_generalization::F5cExpansionKey {
        row: child,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    };
    let child_id = before[&child_key];
    assert!(generalizer.build_raw_forest(later).is_err());
    assert_eq!(generalizer.memo.roots, before);
    generalizer.release_raw_forest(forest);
    assert!(generalizer.order.is_empty() && generalizer.reentries.is_empty());
    assert_eq!(generalizer.memo.generalizer_scratch_capacities, [0; 4]);
    let lane = crate::f5c_generalization::F5cWalkerLaneKind::RawCallbackTrace as usize;
    generalizer.memo.walker_resources.lanes[lane].requested_slots = usize::MAX;
    assert!(generalizer.build_raw_forest(later).is_err());
    assert_eq!(generalizer.memo.roots, before);
    assert_eq!(generalizer.memo.roots[&child_key], child_id);
    assert!((child_id.0 as usize) < generalizer.memo.nodes.len());
    generalizer.memo.walker_resources.lanes[lane].requested_slots = 0;
    let retry = generalizer.build_raw_forest(later).unwrap();
    assert_eq!(retry.callback_trace, vec![(child, Polarity::Positive)]);
    generalizer.release_raw_forest(retry);
}

#[test]
fn raw_forest_late_failure_rolls_back_memo_and_retries() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-late-failure"));
    let mut session = InferenceSession::new(batch);
    let child = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    let mut warming = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    warming
        .walk_flat(F5cWalkTask::EnterRow {
            row: child,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let memo = std::mem::take(&mut warming.memo);
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let child_key = crate::f5c_generalization::F5cExpansionKey {
        row: child,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    };
    assert!(generalizer.memo.roots.contains_key(&child_key));
    let before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.root_edges.clone(),
        generalizer.memo.root_edge_marks.clone(),
        generalizer.memo.root_undo.clone(),
    );
    let before_nodes = (
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.parent_heads.clone(),
        generalizer.memo.reverse_parents.clone(),
        generalizer.memo.incidence_heads.clone(),
        generalizer.memo.incidences.clone(),
    );
    // The raw forest API has no later Q/R stage; invalidate a retained root
    // inside its memo transaction, then let the forest re-admit that key.
    generalizer.memo.invalidate_row(child).unwrap();
    assert!(!generalizer.memo.roots.contains_key(&child_key));
    let forest = generalizer.build_raw_forest(root).unwrap();
    assert!(generalizer.memo.roots.contains_key(&child_key));
    assert!(
        generalizer
            .memo
            .root_undo
            .iter()
            .any(|event| matches!(event, crate::f5c_generalization::F5cRootUndo::Invalidate(_)))
    );
    assert!(
        generalizer
            .memo
            .root_undo
            .iter()
            .any(|event| matches!(event, crate::f5c_generalization::F5cRootUndo::Admit(_)))
    );
    generalizer.abort_raw_forest(forest).unwrap();
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.root_edges.clone(),
            generalizer.memo.root_edge_marks.clone(),
            generalizer.memo.root_undo.clone(),
        ),
        before
    );
    assert_eq!(
        (
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.parent_heads.clone(),
            generalizer.memo.reverse_parents.clone(),
            generalizer.memo.incidence_heads.clone(),
            generalizer.memo.incidences.clone(),
        ),
        before_nodes
    );
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    assert!(generalizer.memo.work.is_empty());
    assert!(generalizer.memo.conflict_journal.is_empty());
    assert_eq!(generalizer.memo.root_edge_mark_epoch, 0);
    assert_eq!(generalizer.memo.visit_epoch, 0);
    assert!(
        generalizer
            .memo
            .visit_epochs
            .iter()
            .all(|epoch| *epoch == 0)
    );
    assert!(generalizer.flat_sink.arena_is_empty());
    let retry = generalizer.build_raw_forest(root).unwrap();
    assert_eq!(retry.callback_trace, vec![(child, Polarity::Positive)]);
    generalizer.release_raw_forest(retry);
}

#[test]
fn raw_forest_failed_rollback_releases_lifecycle_without_reuse() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-rollback-failure"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let forest = generalizer.build_raw_forest(row).unwrap();
    generalizer.memo.root_edge_marks.push(0);
    assert!(generalizer.abort_raw_forest(forest).is_err());
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    assert!(generalizer.memo.work.is_empty());
    assert!(generalizer.memo.conflict_journal.is_empty());
    assert!(generalizer.build_raw_forest(row).is_err());
    assert!(
        generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row,
                polarity: Polarity::Positive,
                root: false,
            })
            .is_err()
    );
}

#[test]
fn raw_forest_construction_error_with_failed_rollback_rejects_reuse() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-raw-construction-rollback-failure"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    generalizer.memo.root_edge_marks.push(0);
    let roots_lane = crate::f5c_generalization::F5cWalkerLaneKind::RawRoots as usize;
    generalizer.memo.walker_resources.lanes[roots_lane].requested_slots = usize::MAX;
    assert!(generalizer.build_raw_forest(row).is_err());
    generalizer.memo.walker_resources.lanes[roots_lane].requested_slots = 0;
    assert!(generalizer.build_raw_forest(row).is_err());
    assert!(
        generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row,
                polarity: Polarity::Positive,
                root: false,
            })
            .is_err()
    );
}

#[test]
fn raw_forest_table_overflow_preflights_before_allocation_and_retries() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_generalization::F5cWalkerLaneKind;
    for kind in [
        F5cWalkerLaneKind::RawOwnerSeen,
        F5cWalkerLaneKind::RawOwnerBounds,
    ] {
        let batch = collect(module("my f = 1", "f5c-raw-table-overflow"));
        let mut session = InferenceSession::new(batch);
        let root = session.fresh_value_at_level(1).unwrap();
        let relay = session.fresh_value_at_level(1).unwrap();
        let argument = session.negative_top_term().unwrap();
        let result = session.live_value_term(Polarity::Positive, relay).unwrap();
        let function = session
            .positive_function_term(
                argument,
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                result,
            )
            .unwrap();
        session.bounds[root as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::PositiveFunction(function));
        session.bounds[relay as usize].direct_lower_rows.push(root);
        let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
        let before = generalizer.memo.roots.clone();
        generalizer.memo.walker_resources.lanes[kind as usize].requested_slots = usize::MAX;
        assert!(generalizer.build_raw_forest(root).is_err());
        assert_eq!(generalizer.memo.roots, before);
        assert!(generalizer.flat_sink.arena_is_empty());
        assert_eq!(
            generalizer.memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
        assert_eq!(
            generalizer.memo.walker_resources.independent_lanes[kind as usize].actual_capacity,
            0
        );
        generalizer.memo.walker_resources.lanes[kind as usize].requested_slots = 0;
        let forest = generalizer.build_raw_forest(root).unwrap();
        assert_eq!(forest.raw_owner_order, vec![root]);
        generalizer.release_raw_forest(forest);
    }
}

#[test]
fn flat_one_root_deduplicates_local_values_before_promotion() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-local-dedup"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .extend([ValueEndpointKey::IntPositive, ValueEndpointKey::IntPositive]);

    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let id = generalizer.memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    assert_eq!(value.positive_shared_id(), Some(id));
    assert!(value.cacheable);
    assert!(matches!(
        generalizer.memo.nodes[id.0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::PositiveInt
    ));
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].incidence,
        Some((row, Polarity::Positive))
    );
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].transitive_incidence_count,
        1
    );
    assert_eq!(generalizer.memo.nodes.len(), 1);
}

#[test]
fn flat_negative_intersection_keeps_first_seen_survivors() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-negative-dedup"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_uppers
        .extend([
            ValueEndpointKey::IntNegative,
            ValueEndpointKey::TopNegative,
            ValueEndpointKey::IntNegative,
        ]);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row,
            polarity: Polarity::Negative,
            root: false,
        })
        .unwrap();
    assert!(value.cacheable);
    let id = generalizer.memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row,
        polarity: Polarity::Negative,
        frozen_bound_epoch: 0,
    }];
    let crate::f5c_generalization::F5cSummaryNodeKind::NegativeIntersection { start, len } =
        generalizer.memo.nodes[id.0 as usize].kind
    else {
        panic!("two distinct upper members must form an intersection");
    };
    assert_eq!(len, 2);
    let children = generalizer.memo.child_slice(start, len).unwrap();
    assert!(matches!(
        generalizer.memo.nodes[children[0].0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::NegativeInt
    ));
    assert!(matches!(
        generalizer.memo.nodes[children[1].0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::NegativeTop
    ));
}

#[test]
fn flat_promotion_links_warm_shared_child_and_keeps_first_seen_order() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-warm-order"));
    let mut session = InferenceSession::new(batch);
    let warm = session.fresh_value_at_level(1).unwrap();
    let holder = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[holder as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(warm));
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(warm),
            ValueEndpointKey::BottomPositive,
            ValueEndpointKey::ValueRow(warm),
        ]);
    let (warm_result, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(holder);
    assert!(warm_result.is_ok());
    let warm_id = memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: warm,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: root,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let id = generalizer.memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: root,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    assert_eq!(value.positive_shared_id(), Some(id));
    let crate::f5c_generalization::F5cSummaryNodeKind::PositiveUnion { start, len } =
        generalizer.memo.nodes[id.0 as usize].kind
    else {
        panic!("distinct shared and local children must form a union");
    };
    assert_eq!(len, 2);
    let children = generalizer.memo.child_slice(start, len).unwrap();
    assert_eq!(children[0], warm_id);
    assert!(matches!(
        generalizer.memo.nodes[children[1].0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::PositiveBottom
    ));
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].transitive_incidence_count,
        2
    );
    assert_eq!(generalizer.shared_summary_hits, 2);
    assert!(generalizer.memo.parent_heads[warm_id.0 as usize].is_some());
    let resources = &generalizer.memo.walker_resources;
    let capacities = generalizer.flat_sink.promotion_observation.unwrap();
    assert!(capacities[..4].iter().any(|&bytes| bytes > 0));
    assert!(capacities[4..8].iter().any(|&bytes| bytes > 0));
    assert!(capacities[8] > 0 && capacities[9] > 0);
    let simultaneous_bytes: usize = capacities.iter().sum();
    assert_eq!(
        resources.simultaneous_memo_peak_bytes,
        resources.independent_simultaneous_memo_peak_bytes
    );
    assert!(resources.simultaneous_memo_peak_bytes >= simultaneous_bytes);
    assert!(resources.independent_simultaneous_memo_peak_bytes >= simultaneous_bytes);
}

#[test]
fn flat_shared_root_promotion_adds_alias_incidence() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-alias-incidence"));
    let mut session = InferenceSession::new(batch);
    let warm = session.fresh_value_at_level(1).unwrap();
    let holder = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[holder as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(warm));
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(warm));
    let (built, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(holder);
    assert!(built.is_ok());
    let warm_id = memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: warm,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: root,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let id = value.positive_shared_id().unwrap();
    let crate::f5c_generalization::F5cSummaryNodeKind::PositiveAlias { start } =
        generalizer.memo.nodes[id.0 as usize].kind
    else {
        panic!("shared root must acquire an incidence alias");
    };
    assert_eq!(generalizer.memo.child_slice(start, 1).unwrap(), [warm_id]);
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].incidence,
        Some((root, Polarity::Positive))
    );
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].transitive_incidence_count,
        2
    );
    assert_eq!(generalizer.shared_summary_hits, 1);
}

#[test]
fn flat_positive_function_promotes_pure_fields_in_child_order() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-function"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    let argument = session.negative_top_term().unwrap();
    let result = session.batch.collected_leaf_term(Leaf::IntPositive);
    let function = session
        .positive_function_term(
            argument,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            result,
        )
        .unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let id = generalizer.memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    assert_eq!(value.positive_shared_id(), Some(id));
    let crate::f5c_generalization::F5cSummaryNodeKind::PositiveFunction { argument, result } =
        generalizer.memo.nodes[id.0 as usize].kind
    else {
        panic!("function must retain ordered children");
    };
    assert!(matches!(
        generalizer.memo.nodes[argument.0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::NegativeTop
    ));
    assert!(matches!(
        generalizer.memo.nodes[result.0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::PositiveInt
    ));
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].transitive_incidence_count,
        1
    );
}

#[test]
fn flat_promotion_failure_rolls_back_arena_and_memo_then_retries() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-promotion-retry"));
    let mut session = InferenceSession::new(batch);
    let warm = session.fresh_value_at_level(1).unwrap();
    let holder = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[holder as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(warm));
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(warm),
            ValueEndpointKey::BottomPositive,
        ]);
    let (built, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(holder);
    assert!(built.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let before = (
        generalizer.memo.roots.clone(),
        generalizer.memo.nodes.clone(),
        generalizer.memo.children.clone(),
        generalizer.memo.parent_heads.clone(),
        generalizer.memo.reverse_parents.clone(),
        generalizer.memo.incidence_heads.clone(),
        generalizer.memo.incidences.clone(),
        generalizer.memo.root_heads.clone(),
        generalizer.memo.root_edges.clone(),
    );
    generalizer.memo.fail_reserve_at = Some((
        F5cTestReserveFailure::ChildrenAfterReserve,
        generalizer.memo.children.len(),
    ));
    assert!(
        generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row: root,
                polarity: Polarity::Positive,
                root: false,
            },)
            .is_err()
    );
    assert!(generalizer.flat_sink.arena_is_empty());
    assert_eq!(
        (
            generalizer.memo.roots.clone(),
            generalizer.memo.nodes.clone(),
            generalizer.memo.children.clone(),
            generalizer.memo.parent_heads.clone(),
            generalizer.memo.reverse_parents.clone(),
            generalizer.memo.incidence_heads.clone(),
            generalizer.memo.incidences.clone(),
            generalizer.memo.root_heads.clone(),
            generalizer.memo.root_edges.clone(),
        ),
        before,
    );
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    assert!(generalizer.memo.walker_resources.retained_bytes().unwrap() > 0);
    assert_eq!(generalizer.shared_summary_hits, 0);
    assert_eq!(generalizer.uncacheable_states, 0);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: root,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    assert!(value.positive_shared_id().is_some());
    assert_eq!(generalizer.shared_summary_hits, 1);
}

#[test]
fn flat_post_admission_failure_removes_root_and_source_nodes() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-after-admit"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    generalizer.memo.fail_observation_at = Some(F5cTestObservationFailure::Admit);
    assert!(
        generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row,
                polarity: Polarity::Positive,
                root: false,
            },)
            .is_err()
    );
    assert!(generalizer.flat_sink.arena_is_empty());
    assert!(generalizer.memo.roots.is_empty());
    assert!(generalizer.memo.nodes.is_empty());
    assert!(generalizer.memo.children.is_empty());
    assert!(generalizer.memo.root_edges.is_empty());
    assert!(generalizer.memo.root_undo.is_empty());
    assert!(generalizer.memo.active_rows.is_empty());
    assert!(generalizer.memo.active_conflicts.is_empty());
    let memo = generalizer.memo;
    let mut retry = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    assert!(
        retry
            .walk_flat(F5cWalkTask::EnterRow {
                row,
                polarity: Polarity::Positive,
                root: false,
            },)
            .unwrap()
            .positive_shared_id()
            .is_some()
    );
}

#[test]
fn flat_failed_component_restores_uncacheable_count_before_retry() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-uncacheable-retry"));
    let mut session = InferenceSession::new(batch);
    let recursive = session.fresh_value_at_level(1).unwrap();
    let later = session.fresh_value_at_level(1).unwrap();
    session.bounds[recursive as usize]
        .direct_lower_rows
        .push(recursive);
    session.bounds[later as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    assert!(
        !generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row: recursive,
                polarity: Polarity::Positive,
                root: false
            },)
            .unwrap()
            .cacheable
    );
    assert!(generalizer.uncacheable_states > 0);
    generalizer.memo.fail_observation_at = Some(F5cTestObservationFailure::Admit);
    assert!(
        generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row: later,
                polarity: Polarity::Positive,
                root: false
            },)
            .is_err()
    );
    assert_eq!(generalizer.uncacheable_states, 0);
    assert_eq!(generalizer.shared_summary_hits, 0);
    assert!(
        generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row: later,
                polarity: Polarity::Positive,
                root: false
            },)
            .unwrap()
            .cacheable
    );
}

#[test]
fn flat_distinct_shared_ids_and_matching_local_value_remain_distinct() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-tagged-equality"));
    let mut session = InferenceSession::new(batch);
    let first = session.fresh_value_at_level(1).unwrap();
    let second = session.fresh_value_at_level(1).unwrap();
    let holder = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    for row in [first, second] {
        session.bounds[row as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::IntPositive);
    }
    session.bounds[holder as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(first),
            ValueEndpointKey::ValueRow(second),
        ]);
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(first),
            ValueEndpointKey::ValueRow(second),
            ValueEndpointKey::IntPositive,
        ]);
    let (built, memo, _, _) =
        F5cGeneralizer::with_source_meter(&session, &test_source_meter).build_component(holder);
    assert!(built.is_ok());
    let first_id = memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: first,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    let second_id = memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: second,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    assert_ne!(first_id, second_id);
    let mut generalizer = F5cGeneralizer::with_memo(&session, &test_source_meter, memo, 0);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: root,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let id = value.positive_shared_id().unwrap();
    let crate::f5c_generalization::F5cSummaryNodeKind::PositiveUnion { start, len } =
        generalizer.memo.nodes[id.0 as usize].kind
    else {
        panic!("tagged values must remain separate union children");
    };
    assert_eq!(len, 3);
    let children = generalizer.memo.child_slice(start, len).unwrap();
    assert_eq!(children[..2], [first_id, second_id]);
    assert!(matches!(
        generalizer.memo.nodes[children[2].0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::PositiveInt
    ));
    assert_eq!(
        generalizer.memo.nodes[id.0 as usize].transitive_incidence_count,
        3
    );
}

#[test]
fn flat_negative_function_and_tainted_row_keep_cacheability() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-negative-taint"));
    let mut session = InferenceSession::new(batch);
    let function_row = session.fresh_value_at_level(1).unwrap();
    let recursive_row = session.fresh_value_at_level(1).unwrap();
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
    session.bounds[function_row as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::NegativeFunction(negative_function));
    session.bounds[recursive_row as usize]
        .direct_lower_rows
        .push(recursive_row);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let function = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: function_row,
            polarity: Polarity::Negative,
            root: false,
        })
        .unwrap();
    assert!(function.cacheable);
    let function_id = generalizer.memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: function_row,
        polarity: Polarity::Negative,
        frozen_bound_epoch: 0,
    }];
    let crate::f5c_generalization::F5cSummaryNodeKind::NegativeFunction { argument, result } =
        generalizer.memo.nodes[function_id.0 as usize].kind
    else {
        panic!("negative function must be promoted");
    };
    assert!(matches!(
        generalizer.memo.nodes[argument.0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::PositiveInt
    ));
    assert!(matches!(
        generalizer.memo.nodes[result.0 as usize].kind,
        crate::f5c_generalization::F5cSummaryNodeKind::NegativeInt
    ));
    let recursive = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: recursive_row,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    assert!(!recursive.cacheable);
    assert!(
        !generalizer
            .memo
            .roots
            .contains_key(&crate::f5c_generalization::F5cExpansionKey {
                row: recursive_row,
                polarity: Polarity::Positive,
                frozen_bound_epoch: 0
            })
    );
}

#[test]
fn flat_nested_local_functions_deduplicate_in_both_polarities() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-nested-local-equality"));
    let mut session = InferenceSession::new(batch);
    let positive_row = session.fresh_value_at_level(1).unwrap();
    let negative_row = session.fresh_value_at_level(1).unwrap();
    let negative_top = session.negative_top_term().unwrap();
    let positive_inner = session
        .positive_function_term(
            negative_top,
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            session.batch.collected_leaf_term(Leaf::IntPositive),
        )
        .unwrap();
    let negative_inner = session
        .negative_function_term(
            session.batch.collected_leaf_term(Leaf::IntPositive),
            session
                .batch
                .collected_leaf_term(Leaf::EffectBottomPositive),
            session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
            session.batch.collected_leaf_term(Leaf::IntNegative),
        )
        .unwrap();
    for _ in 0..2 {
        let positive = session
            .positive_function_term(
                negative_inner,
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                positive_inner,
            )
            .unwrap();
        session.bounds[positive_row as usize]
            .exact_non_variable_lowers
            .push(ValueEndpointKey::PositiveFunction(positive));
        let negative = session
            .negative_function_term(
                positive_inner,
                session
                    .batch
                    .collected_leaf_term(Leaf::EffectBottomPositive),
                session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                negative_inner,
            )
            .unwrap();
        session.bounds[negative_row as usize]
            .exact_non_variable_uppers
            .push(ValueEndpointKey::NegativeFunction(negative));
    }
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    for (row, polarity) in [
        (positive_row, Polarity::Positive),
        (negative_row, Polarity::Negative),
    ] {
        let value = generalizer
            .walk_flat(F5cWalkTask::EnterRow {
                row,
                polarity,
                root: false,
            })
            .unwrap();
        assert!(value.cacheable);
        let id = generalizer.memo.roots[&crate::f5c_generalization::F5cExpansionKey {
            row,
            polarity,
            frozen_bound_epoch: 0,
        }];
        assert!(matches!(
            generalizer.memo.nodes[id.0 as usize].kind,
            crate::f5c_generalization::F5cSummaryNodeKind::PositiveFunction { .. }
                | crate::f5c_generalization::F5cSummaryNodeKind::NegativeFunction { .. }
        ));
        assert_eq!(
            generalizer.memo.nodes[id.0 as usize].transitive_incidence_count,
            1
        );
    }
}

#[test]
fn flat_producer_and_arena_drop_on_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let test_source_meter = DraftHeapMeter::default();
            let batch = collect(module("my f = 1", "f5c-flat-small-stack"));
            let mut session = InferenceSession::new(batch);
            let row = session.fresh_value_at_level(1).unwrap();
            let argument = session.negative_top_term().unwrap();
            let mut result = session.batch.collected_leaf_term(Leaf::IntPositive);
            for _ in 0..128 {
                result = session
                    .positive_function_term(
                        argument,
                        session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                        session
                            .batch
                            .collected_leaf_term(Leaf::EffectBottomPositive),
                        result,
                    )
                    .unwrap();
            }
            session.bounds[row as usize]
                .exact_non_variable_lowers
                .push(ValueEndpointKey::PositiveFunction(result));
            let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
            let value = generalizer
                .walk_flat(F5cWalkTask::EnterRow {
                    row,
                    polarity: Polarity::Positive,
                    root: true,
                })
                .unwrap();
            assert!(value.cacheable);
            assert!(value.positive_shared_id().is_none());
            assert!(generalizer.memo.walker_resources.retained_bytes().unwrap() > 0);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn flat_local_root_remains_readable_across_successive_walks() {
    let test_source_meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "f5c-flat-forest-lifetime"));
    let mut session = InferenceSession::new(batch);
    let first = session.fresh_value_at_level(1).unwrap();
    let second = session.fresh_value_at_level(1).unwrap();
    session.bounds[first as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[second as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::BottomPositive);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let first_root = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: first,
            polarity: Polarity::Positive,
            root: true,
        })
        .unwrap();
    assert!(generalizer.flat_sink.local_positive_is(first_root, true));
    let second_root = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row: second,
            polarity: Polarity::Positive,
            root: true,
        })
        .unwrap();
    assert!(generalizer.flat_sink.local_positive_is(first_root, true));
    assert!(generalizer.flat_sink.local_positive_is(second_root, false));
}

#[test]
fn checked_materialization_observes_co_resident_source_memo_draft_and_scratch() {
    let test_source_meter = DraftHeapMeter::default();
    use crate::f5c_draft::FlatDraft;
    use crate::f5c_generalization::F5cWalkerLaneKind;
    use crate::f5c_materialization::materialize_summary_flat_checked;

    let batch = collect(module("my f = 1", "f5c-flat-co-resident-materialization"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::IntPositive,
            ValueEndpointKey::BottomPositive,
        ]);
    let mut generalizer = F5cGeneralizer::with_source_meter(&session, &test_source_meter);
    let value = generalizer
        .walk_flat(F5cWalkTask::EnterRow {
            row,
            polarity: Polarity::Positive,
            root: false,
        })
        .unwrap();
    let shared = value.positive_shared_id().unwrap();
    let source = generalizer.flat_sink.source_capacities();
    assert!(source[0] > 0 && source[2] > 0);
    assert!(generalizer.memo.nodes.capacity() > 0);

    let mut draft = FlatDraft::default();
    materialize_summary_flat_checked(
        &mut generalizer.memo,
        &mut draft,
        shared,
        Polarity::Positive,
        |_, _, _, _| Ok(()),
    )
    .unwrap();
    let memo = &generalizer.memo;
    let scratch = memo.checked_materialization_scratch_sample.unwrap();
    assert!(scratch[11] > 0 && scratch[12] > 0);
    let actual = [
        (F5cWalkerLaneKind::SourcePositiveNodes, source[0]),
        (F5cWalkerLaneKind::SourceNegativeNodes, source[1]),
        (F5cWalkerLaneKind::SourcePositiveChildren, source[2]),
        (F5cWalkerLaneKind::SourceNegativeChildren, source[3]),
        (
            F5cWalkerLaneKind::DraftPositiveNodes,
            draft.positive_nodes.capacity(),
        ),
        (
            F5cWalkerLaneKind::DraftNegativeNodes,
            draft.negative_nodes.capacity(),
        ),
        (
            F5cWalkerLaneKind::DraftPositiveChildren,
            draft.positive_children.capacity(),
        ),
        (
            F5cWalkerLaneKind::DraftNegativeChildren,
            draft.negative_children.capacity(),
        ),
        (
            F5cWalkerLaneKind::DraftRecursiveBounds,
            draft.recursive_bounds.capacity(),
        ),
        (
            F5cWalkerLaneKind::DraftInsertionOrder,
            draft.insertion_order.capacity(),
        ),
    ];
    for (kind, capacity) in actual {
        assert_eq!(
            memo.walker_resources.lanes[kind as usize].actual_capacity,
            capacity
        );
        assert_eq!(
            memo.walker_resources.independent_lanes[kind as usize].actual_capacity,
            capacity
        );
    }
    assert!(draft.positive_nodes.capacity() > 0 && draft.positive_children.capacity() > 0);
    assert_eq!(draft.recursive_bounds.capacity(), 0);
    let source_and_draft_bytes: usize = actual
        .iter()
        .map(|(kind, capacity)| capacity * kind.slot_size())
        .sum();
    assert_eq!(
        F5cWalkerLaneKind::FlatMaterializeTasks.slot_size(),
        std::mem::size_of::<crate::f5c_materialization::FlatTask>()
    );
    assert_eq!(
        F5cWalkerLaneKind::FlatMaterializeValues.slot_size(),
        std::mem::size_of::<crate::f5c_draft::NodeRef>()
    );
    let sampled_lanes = [
        F5cWalkerLaneKind::SourcePositiveNodes,
        F5cWalkerLaneKind::SourceNegativeNodes,
        F5cWalkerLaneKind::SourcePositiveChildren,
        F5cWalkerLaneKind::SourceNegativeChildren,
        F5cWalkerLaneKind::DraftPositiveNodes,
        F5cWalkerLaneKind::DraftNegativeNodes,
        F5cWalkerLaneKind::DraftPositiveChildren,
        F5cWalkerLaneKind::DraftNegativeChildren,
        F5cWalkerLaneKind::DraftRecursiveBounds,
        F5cWalkerLaneKind::DraftInsertionOrder,
        F5cWalkerLaneKind::FlatMaterializeTasks,
        F5cWalkerLaneKind::FlatMaterializeValues,
    ];
    let sampled_bytes: usize = sampled_lanes
        .iter()
        .zip(&scratch[1..])
        .map(|(kind, capacity)| kind.slot_size() * capacity)
        .sum();
    let simultaneous = scratch[0] + sampled_bytes;
    assert!(sampled_bytes >= source_and_draft_bytes);
    assert_eq!(&scratch[1..5], &source);
    assert_eq!(
        &scratch[5..11],
        &actual[4..]
            .iter()
            .map(|(_, capacity)| *capacity)
            .collect::<Vec<_>>()
    );
    assert_eq!(scratch[0], memo.retained_bytes().unwrap());
    let mut ledger = IndependentResourceLedger::default();
    ledger.record_component_expansion_memo(memo).unwrap();
    for (kind, capacity) in sampled_lanes.iter().zip(&scratch[1..]) {
        if matches!(
            kind,
            F5cWalkerLaneKind::FlatMaterializeTasks | F5cWalkerLaneKind::FlatMaterializeValues
        ) {
            assert!(
                memo.walker_resources.independent_lanes[*kind as usize].peak_bytes
                    >= capacity * kind.slot_size()
            );
            assert_eq!(
                ledger.generalization_walker_lanes[*kind as usize].peak_bytes,
                memo.walker_resources.independent_lanes[*kind as usize].peak_bytes
            );
        } else {
            assert_eq!(
                ledger.generalization_walker_lanes[*kind as usize].actual_capacity,
                *capacity
            );
        }
    }
    assert!(memo.walker_resources.simultaneous_memo_peak_bytes >= simultaneous);
    assert!(
        memo.walker_resources
            .independent_simultaneous_memo_peak_bytes
            >= simultaneous
    );
}
