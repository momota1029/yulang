use super::*;
use crate::f5c_generalization::{F5cTestObservationFailure, F5cTestReserveFailure};

macro_rules! persistent_memo_state {
    ($memo:expr) => {{
        let memo = &$memo;
        (
            memo.roots.clone(),
            memo.nodes.clone(),
            memo.children.clone(),
            memo.parent_heads.clone(),
            memo.reverse_parents.clone(),
            memo.incidence_heads.clone(),
            memo.incidences.clone(),
            memo.root_heads.clone(),
            memo.root_edges.clone(),
            memo.root_edge_marks.clone(),
        )
    }};
}

#[test]
fn warm_child_conflict_failure_and_retry_preserve_persistent_memo() {
    let batch = collect(module("my f = 1", "f5c-transaction-warm-child"));
    let mut session = InferenceSession::new(batch);
    let ancestor = session.fresh_value_at_level(1).unwrap();
    let child = session.fresh_value_at_level(1).unwrap();
    let sibling = session.fresh_value_at_level(1).unwrap();
    let failing_root = session.fresh_value_at_level(1).unwrap();
    let retry_root = session.fresh_value_at_level(1).unwrap();
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[sibling as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[ancestor as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    session.bounds[failing_root as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(child),
            ValueEndpointKey::ValueRow(sibling),
        ]);
    session.bounds[retry_root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));

    let mut memo = F5cComponentExpansionMemo::default();
    let summary = memo
        .positive_node(&F5cPositive::Int, Some((ancestor, Polarity::Positive)))
        .unwrap();
    let key = F5cExpansionKey {
        row: child,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    };
    memo.admit(key, summary).unwrap();
    memo.root_undo.clear();
    let (success, memo, hits, _) =
        F5cGeneralizer::with_memo(&session, memo, 0).build_component(ancestor);
    assert!(success.is_ok());
    assert_eq!(hits, 0);
    assert!(memo.conflict_journal.is_empty());
    assert!(!memo.conflicts_active(key));
    assert!(memo.root_edge_mark_epoch > 0);
    assert!(memo.root_edge_marks.iter().any(|mark| *mark != 0));
    assert!(memo.visit_epoch > 0);
    assert!(memo.visit_epochs.iter().any(|epoch| *epoch != 0));
    let before = (
        memo.roots.clone(),
        memo.nodes.clone(),
        memo.children.clone(),
        memo.parent_heads.clone(),
        memo.reverse_parents.clone(),
        memo.incidence_heads.clone(),
        memo.incidences.clone(),
        memo.root_heads.clone(),
        memo.root_edges.clone(),
    );
    let mut memo = memo;
    memo.fail_reserve_at = Some((F5cTestReserveFailure::RootUndo, 0));
    let (failed, memo, hits, _) =
        F5cGeneralizer::with_memo(&session, memo, 0).build_component(failing_root);
    assert_eq!(failed, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(hits, 1);
    assert_eq!(
        (
            memo.roots.clone(),
            memo.nodes.clone(),
            memo.children.clone(),
            memo.parent_heads.clone(),
            memo.reverse_parents.clone(),
            memo.incidence_heads.clone(),
            memo.incidences.clone(),
            memo.root_heads.clone(),
            memo.root_edges.clone(),
        ),
        before
    );
    assert!(memo.active_rows.is_empty() && memo.active_conflicts.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty() && memo.root_undo.is_empty());
    assert!(memo.root_edge_marks.iter().all(|mark| *mark == 0));
    assert_eq!(memo.root_edge_mark_epoch, 0);
    assert!(memo.visit_epochs.iter().all(|epoch| *epoch == 0));
    assert_eq!(memo.visit_epoch, 0);
    assert_eq!(memo.generalizer_scratch_capacities, [0; 3]);
    let mut raw = F5cGeneralizer::with_memo(&session, memo, 0);
    assert_eq!(
        raw.positive_row(child, false),
        Ok(F5cPositive::Shared(summary))
    );
    assert_eq!(raw.shared_summary_hits, 1);
    let memo = raw.memo;
    let (retry, memo, hits, _) =
        F5cGeneralizer::with_memo(&session, memo, 0).build_component(retry_root);
    assert!(retry.is_ok());
    assert_eq!(hits, 1);
    assert_eq!(memo.roots.get(&key), Some(&summary));
    assert!(memo.active_rows.is_empty() && memo.active_conflicts.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty() && memo.root_undo.is_empty());
}

#[test]
fn child_reserve_failure_keeps_append_atomic_and_accounts_retained_capacity() {
    let mut memo = F5cComponentExpansionMemo::default();
    let ids = vec![F5cSummaryNodeId(0); 256];
    let before_len = memo.children.len();
    let before_capacity = memo.children.capacity();
    let before_requested = memo.child_lane.requested_slots;
    let before_growths = memo.child_lane.capacity_growths;
    memo.fail_reserve_at = Some((F5cTestReserveFailure::ChildrenAfterReserve, before_len));

    assert_eq!(
        memo.push_children(&ids),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(memo.children.len(), before_len);
    assert!(memo.children.capacity() > before_capacity);
    assert_eq!(
        memo.child_lane.requested_slots,
        before_requested + ids.len()
    );
    assert_eq!(memo.child_lane.capacity_growths, before_growths + 1);
    assert_eq!(
        memo.child_lane.peak_bytes,
        memo.child_retained_bytes().unwrap()
    );
    assert_eq!(
        memo.independent_child_growths,
        memo.child_lane.capacity_growths
    );
    assert!(
        memo.capacity_samples
            .iter()
            .any(|sample| sample[2] == memo.children.capacity())
    );

    assert_eq!(
        memo.push_children(&ids),
        Ok((before_len as u32, ids.len() as u32))
    );
    assert_eq!(memo.children, ids);
    assert_eq!(
        memo.child_lane.requested_slots,
        before_requested + 2 * ids.len()
    );
    assert_eq!(memo.child_lane.capacity_growths, before_growths + 1);
}

#[test]
fn growth_samples_reconcile_live_mirrors_and_rollback_retention() {
    let batch = collect(module("my f = 1", "f5c-transaction-growth-ledger"));
    let mut session = InferenceSession::new(batch);
    let child = session.fresh_value_at_level(1).unwrap();
    let sibling = session.fresh_value_at_level(1).unwrap();
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[sibling as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .extend([
            ValueEndpointKey::ValueRow(child),
            ValueEndpointKey::ValueRow(sibling),
        ]);
    let mut memo = F5cComponentExpansionMemo::default();
    memo.fail_reserve_at = Some((F5cTestReserveFailure::RootUndo, 1));
    let (failed, memo, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert_eq!(failed, Err(SolveAvailabilityError::IdentityExhausted));
    assert!(memo.roots.is_empty());
    assert!(
        memo.capacity_samples
            .iter()
            .any(|sample| sample[16] > 0 && sample[17] > 0 && sample[18] > 0)
    );
    let failed_peak = memo.peak_bytes().unwrap();
    let retained_after_failure = memo.retained_bytes().unwrap();
    assert!(retained_after_failure > 0);
    assert!(
        memo.capacity_samples
            .iter()
            .any(|sample| sample[10] == memo.root_undo.capacity())
    );
    let mut ledger = IndependentResourceLedger::default();
    ledger.record_component_expansion_memo(&memo).unwrap();
    assert_eq!(ledger.component_expansion_memo_peak_bytes, failed_peak);

    let (retry, memo_after_retry, _, _) =
        F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert!(retry.is_ok());
    assert!(memo_after_retry.retained_bytes().unwrap() >= retained_after_failure);
    let mut retry_ledger = IndependentResourceLedger::default();
    retry_ledger
        .record_component_expansion_memo(&memo_after_retry)
        .unwrap();
    assert_eq!(
        retry_ledger.component_expansion_memo_peak_bytes,
        memo_after_retry.peak_bytes().unwrap()
    );
    let mut memo = memo_after_retry;

    let retained_node = memo
        .push_node(F5cSummaryNodeKind::PositiveBottom, None)
        .unwrap();
    let count = memo.capacity_samples.len();
    memo.push_children(&[retained_node]).unwrap();
    assert!(memo.capacity_samples.len() >= count);
    memo.push_children(&vec![retained_node; 256]).unwrap();
    let mut later = IndependentResourceLedger::default();
    later.record_component_expansion_memo(&memo).unwrap();
    assert_eq!(
        later.component_expansion_memo_peak_bytes,
        memo.peak_bytes().unwrap()
    );
    assert!(later.component_expansion_memo_peak_bytes >= failed_peak);
    assert!(
        memo.capacity_samples
            .iter()
            .any(|sample| sample[2] >= 256 && sample[16..19] == [0; 3])
    );
}

#[test]
fn f5c_component_expansion_memo_same_key_readmission_failure_restores_prior_root() {
    let mut memo = F5cComponentExpansionMemo::default();
    let key = F5cExpansionKey {
        row: 3,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 5,
    };
    let prior = memo
        .push_node(
            F5cSummaryNodeKind::PositiveInt,
            Some((7, Polarity::Positive)),
        )
        .unwrap();
    memo.admit(key, prior).unwrap();
    let before = persistent_memo_state!(memo);
    let node_checkpoint = memo.nodes.len();
    let child_checkpoint = memo.children.len();
    let reverse_checkpoint = memo.reverse_parents.len();
    let incidence_checkpoint = memo.incidences.len();
    let invalidation_checkpoint = memo.root_undo.len();
    memo.invalidate_row(7).unwrap();
    assert!(!memo.roots.contains_key(&key));

    let replacement = memo
        .push_node(F5cSummaryNodeKind::PositiveBottom, None)
        .unwrap();
    memo.fail_observation_at = Some(F5cTestObservationFailure::Admit);
    memo.admit(key, replacement).unwrap();
    assert_eq!(
        memo.root_undo[invalidation_checkpoint..],
        [F5cRootUndo::Invalidate(0), F5cRootUndo::Admit(1)]
    );
    assert_eq!(
        memo.observe_walker(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    memo.finish_root_transaction(invalidation_checkpoint, false)
        .unwrap();
    memo.reset_active_scratch();
    memo.rollback_nodes(
        node_checkpoint,
        child_checkpoint,
        reverse_checkpoint,
        incidence_checkpoint,
    )
    .unwrap();

    assert_eq!(persistent_memo_state!(memo), before);
    assert_eq!(memo.roots.get(&key), Some(&prior));
    assert!(memo.root_edges[0].live);
    assert_eq!(memo.root_heads[prior.0 as usize], Some(0));
}

#[test]
fn f5c_component_admit_invalidate_failure_replays_stable_edges() {
    let mut memo = F5cComponentExpansionMemo::default();
    let old_key = F5cExpansionKey {
        row: 1,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    };
    let old = memo
        .push_node(F5cSummaryNodeKind::PositiveInt, None)
        .unwrap();
    memo.admit(old_key, old).unwrap();
    let before = persistent_memo_state!(memo);
    let checkpoint = memo.root_undo.len();
    let node_checkpoint = memo.nodes.len();
    let child_checkpoint = memo.children.len();
    let reverse_checkpoint = memo.reverse_parents.len();
    let incidence_checkpoint = memo.incidences.len();
    let key = F5cExpansionKey {
        row: 2,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    };
    let root = memo
        .push_node(
            F5cSummaryNodeKind::PositiveBottom,
            Some((7, Polarity::Positive)),
        )
        .unwrap();
    memo.fail_observation_at = Some(F5cTestObservationFailure::Admit);
    memo.admit(key, root).unwrap();
    memo.invalidate_row(7).unwrap();
    assert_eq!(
        memo.root_undo[checkpoint..],
        [F5cRootUndo::Admit(1), F5cRootUndo::Invalidate(1)]
    );
    assert_eq!(
        memo.observe_walker(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    memo.finish_root_transaction(checkpoint, false).unwrap();
    memo.reset_active_scratch();
    memo.rollback_nodes(
        node_checkpoint,
        child_checkpoint,
        reverse_checkpoint,
        incidence_checkpoint,
    )
    .unwrap();
    assert_eq!(persistent_memo_state!(memo), before);
    assert_eq!(memo.roots.get(&old_key), Some(&old));
    assert!(!memo.conflicts_active(old_key));
    assert!(memo.active_rows.is_empty() && memo.active_conflicts.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty());
    assert!(memo.root_lane.requested_slots >= 2);
    assert!(memo.index_lane.requested_slots >= 4);
    assert_eq!(
        memo.index_lane.peak_bytes,
        memo.index_retained_bytes().unwrap()
    );
}

#[test]
fn f5c_component_conflict_invalidation_failure_does_not_restore_transient_conflict() {
    let mut memo = F5cComponentExpansionMemo::default();
    let key = F5cExpansionKey {
        row: 3,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    };
    let root = memo
        .push_node(
            F5cSummaryNodeKind::PositiveInt,
            Some((7, Polarity::Positive)),
        )
        .unwrap();
    memo.admit(key, root).unwrap();
    let before = persistent_memo_state!(memo);
    let checkpoint = memo.root_undo.len();
    memo.enter_active(7).unwrap();
    assert!(memo.conflicts_active(key));
    memo.invalidate_row(7).unwrap();
    memo.fail_observation_at = Some(F5cTestObservationFailure::Leave);
    memo.leave_active(7).unwrap();
    assert_eq!(
        memo.observe_walker(),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    memo.finish_root_transaction(checkpoint, false).unwrap();
    memo.reset_active_scratch();
    assert_eq!(persistent_memo_state!(memo), before);
    assert_eq!(memo.roots.get(&key), Some(&root));
    assert!(!memo.conflicts_active(key));
    assert!(memo.active_rows.is_empty() && memo.active_conflicts.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty());
    memo.enter_active(7).unwrap();
    assert!(memo.conflicts_active(key));
    memo.leave_active(7).unwrap();
    assert!(!memo.conflicts_active(key));
}

#[test]
fn f5c_walker_active_observation_failures_leave_idle_mirrors_and_retry() {
    let batch = collect(module("my f = 1", "f5c-active-observation"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    for point in [
        F5cTestObservationFailure::Enter,
        F5cTestObservationFailure::Leave,
    ] {
        let mut generalizer = F5cGeneralizer::new(&session);
        generalizer.memo.fail_observation_at = Some(point);
        assert_eq!(
            generalizer.positive_row(row, false).err(),
            Some(SolveAvailabilityError::IdentityExhausted)
        );
        assert!(generalizer.active.is_empty() && generalizer.active_set.is_empty());
        assert!(generalizer.frames.is_empty() && generalizer.path.is_empty());
        assert!(
            generalizer.memo.active_rows.is_empty() && generalizer.memo.active_conflicts.is_empty()
        );
        assert!(generalizer.memo.work.is_empty() && generalizer.memo.conflict_journal.is_empty());
        assert!(matches!(
            generalizer.positive_row(row, false).unwrap(),
            F5cPositive::Shared(_)
        ));
    }
}

#[test]
fn f5c_component_admission_observation_failure_restores_memo_and_retries() {
    let batch = collect(module("my f = 1", "f5c-admission-observation"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    let child = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut memo = F5cComponentExpansionMemo::default();
    let before = persistent_memo_state!(memo);
    memo.fail_observation_at = Some(F5cTestObservationFailure::Admit);
    let (result, returned, _, _) =
        F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert_eq!(
        result.err(),
        Some(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(persistent_memo_state!(returned), before);
    assert!(returned.root_undo.is_empty());
    assert!(returned.active_rows.is_empty() && returned.active_conflicts.is_empty());
    assert!(returned.work.is_empty() && returned.conflict_journal.is_empty());
    assert_eq!(returned.generalizer_scratch_capacities, [0; 3]);
    assert!(returned.root_lane.requested_slots > 0);
    assert!(returned.index_lane.peak_bytes >= returned.index_retained_bytes().unwrap());
    let (retry, memo, _, _) =
        F5cGeneralizer::with_memo(&session, returned, 0).build_component(root);
    assert!(retry.is_ok());
    assert!(!memo.roots.is_empty());
}

#[test]
fn f5c_component_reserve_preparation_failures_roll_back_prior_admission() {
    let batch = collect(module("my f = 1", "f5c-reserve-preparation-rollback"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    let child = session.fresh_value_at_level(1).unwrap();
    let sibling = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(sibling));
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[sibling as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    for point in [
        F5cTestReserveFailure::ActiveMirrors,
        F5cTestReserveFailure::RootUndo,
    ] {
        let mut memo = F5cComponentExpansionMemo::default();
        let before = persistent_memo_state!(memo);
        memo.fail_reserve_at = Some((point, 1));
        let (failed, memo, _, _) =
            F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
        assert_eq!(
            failed.err(),
            Some(SolveAvailabilityError::IdentityExhausted),
            "{point:?}"
        );
        assert_eq!(persistent_memo_state!(memo), before);
        assert!(memo.root_undo.is_empty());
        assert!(memo.active_rows.is_empty() && memo.active_conflicts.is_empty());
        assert!(memo.work.is_empty() && memo.conflict_journal.is_empty());
        assert_eq!(memo.generalizer_scratch_capacities, [0; 3]);
        assert!(memo.root_lane.requested_slots > 0);
        let (retry, memo, _, _) =
            F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
        assert!(retry.is_ok());
        assert!(!memo.roots.is_empty());
    }
}

#[test]
fn f5c_component_peak_samples_live_mirrors_and_later_retained_growth() {
    let batch = collect(module("my f = 1", "f5c-live-mirror-peak"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let (result, mut memo, _, _) = F5cGeneralizer::new(&session).build_component(root);
    assert!(result.is_ok());
    let live_peak = memo.peak_bytes().unwrap();
    assert!(live_peak > memo.retained_bytes().unwrap());
    assert_eq!(memo.generalizer_scratch_capacities, [0; 3]);
    let id = memo
        .push_node(F5cSummaryNodeKind::PositiveBottom, None)
        .unwrap();
    let before_growth = memo.peak_bytes().unwrap();
    memo.push_children(&vec![id; 256]).unwrap();
    let expected = before_growth.max(memo.retained_bytes().unwrap());
    assert_eq!(memo.peak_bytes().unwrap(), expected);
    let mut independent = IndependentResourceLedger::default();
    independent.record_component_expansion_memo(&memo).unwrap();
    session
        .record_component_expansion_memo_resources(&memo)
        .unwrap();
    assert_eq!(independent.component_expansion_memo_peak_bytes, expected);
    assert_eq!(
        session
            .execution_counters
            .component_expansion_memo_peak_bytes,
        expected
    );
}
