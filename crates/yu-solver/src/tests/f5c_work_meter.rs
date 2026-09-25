use super::*;
use crate::f5c_generalization::{
    F5C_BULK_DRAIN_BOUNDARY, F5C_FUNCTION_OUTPUT_CONSTRUCTION, F5C_ORDER_REGISTRATION,
    F5C_TAINT_BOUNDARY, F5cBulkDrainSite, F5cTestReserveFailure, F5cWalkTask,
};

fn assert_bulk_drain_overflow_retries<T>(
    site: F5cBulkDrainSite,
    meter: &F5cDraftWorkMeter,
    mut run: impl FnMut() -> Result<T, SolveAvailabilityError>,
    equal: impl Fn(&T, &T) -> bool,
) -> T {
    F5C_BULK_DRAIN_BOUNDARY.with(|boundary| boundary.set(None));
    meter.set(0);
    let expected = run().unwrap();
    let (actual_site, before_drain, count) =
        F5C_BULK_DRAIN_BOUNDARY.with(|boundary| boundary.take().unwrap());
    assert_eq!(actual_site, site);
    assert!(count > 0);

    let failed_start = usize::MAX - before_drain - (count - 1);
    meter.set(failed_start);
    F5C_BULK_DRAIN_BOUNDARY.with(|boundary| boundary.set(None));
    assert!(matches!(
        run(),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert_eq!(
        F5C_BULK_DRAIN_BOUNDARY.with(|boundary| boundary.take()),
        Some((site, usize::MAX - count + 1, count))
    );

    meter.set(0);
    let retry = run().unwrap();
    assert!(equal(&retry, &expected));
    retry
}

fn walk_values_equal(first: &F5cWalkValue, second: &F5cWalkValue) -> bool {
    match (first, second) {
        (F5cWalkValue::Positive(first, _), F5cWalkValue::Positive(second, _)) => first == second,
        (F5cWalkValue::Negative(first, _), F5cWalkValue::Negative(second, _)) => first == second,
        _ => false,
    }
}

#[test]
fn f5c_work_materialized_incidence_overflow_preserves_order_for_retry() {
    let batch = collect(module("my f = 1", "f5c-incidence-overflow"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    let mut generalizer = F5cGeneralizer::new(&session);
    let id = generalizer
        .memo
        .positive_node(&F5cPositive::Int, Some((row, Polarity::Positive)))
        .unwrap();
    generalizer.memo.work_meter.set(0);
    let expected = generalizer
        .materialize_positive(F5cPositive::Shared(id))
        .unwrap();
    let work = generalizer.memo.work_meter.get();
    let registration = F5C_ORDER_REGISTRATION.with(|marker| marker.take().unwrap());
    assert_eq!(generalizer.order, [row]);
    assert!(registration < work);

    generalizer.order.clear();
    generalizer.order_seen.clear();
    generalizer.memo.work_meter.set(usize::MAX - registration);
    assert_eq!(
        generalizer.materialize_positive(F5cPositive::Shared(id)),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert!(generalizer.order.is_empty() && generalizer.order_seen.is_empty());
    generalizer.memo.work_meter.set(0);
    assert_eq!(
        generalizer.materialize_positive(F5cPositive::Shared(id)),
        Ok(expected)
    );
    assert_eq!(generalizer.order, [row]);
    assert_eq!(generalizer.memo.work_meter.get(), work);
}

#[test]
fn f5c_work_order_registration_charges_first_seen_and_revisit() {
    let meter = F5cDraftWorkMeter::default();
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    F5cGeneralizer::register_order(&meter, &mut seen, &mut order, 7).unwrap();
    assert_eq!(meter.get(), 3);
    F5cGeneralizer::register_order(&meter, &mut seen, &mut order, 7).unwrap();
    assert_eq!(meter.get(), 4);
    assert_eq!(order, [7]);
    meter.set(usize::MAX - 1);
    assert_eq!(
        F5cGeneralizer::register_order(&meter, &mut seen, &mut order, 8),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(order, [7]);
    assert!(!seen.contains(&8));
}

#[test]
fn f5c_work_summary_materialization_bulk_drain_overflow_retries_both_polarities() {
    let mut memo = F5cComponentExpansionMemo::default();
    let positive = F5cPositive::Union(vec![F5cPositive::Int, F5cPositive::Bottom]);
    let negative = F5cNegative::Intersection(vec![F5cNegative::Int, F5cNegative::Bottom]);
    let positive_root = memo.positive_node(&positive, None).unwrap();
    let negative_root = memo.negative_node(&negative, None).unwrap();
    let meter = memo.work_meter.clone();

    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::SummaryPositive,
        &meter,
        || memo.positive_value(positive_root),
        |first, second| first == second,
    );
    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::SummaryNegative,
        &meter,
        || memo.negative_value(negative_root),
        |first, second| first == second,
    );
}

#[test]
fn f5c_work_generalizer_row_drain_overflow_retries_both_polarities() {
    let batch = collect(module("my f = 1", "f5c-row-drain-overflow"));
    let mut session = InferenceSession::new(batch);
    let positive_row = session.fresh_value_at_level(1).unwrap();
    let negative_row = session.fresh_value_at_level(1).unwrap();
    session.bounds[positive_row as usize]
        .exact_non_variable_lowers
        .extend([ValueEndpointKey::IntPositive, ValueEndpointKey::IntPositive]);
    session.bounds[negative_row as usize]
        .exact_non_variable_uppers
        .extend([ValueEndpointKey::IntNegative, ValueEndpointKey::IntNegative]);
    let meter = session.f5c_draft_work.clone();

    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::RowPositive,
        &meter,
        || {
            F5cGeneralizer::new(&session).walk(F5cWalkTask::EnterRow {
                row: positive_row,
                polarity: Polarity::Positive,
                root: true,
            })
        },
        walk_values_equal,
    );
    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::RowNegative,
        &meter,
        || {
            F5cGeneralizer::new(&session).walk(F5cWalkTask::EnterRow {
                row: negative_row,
                polarity: Polarity::Negative,
                root: true,
            })
        },
        walk_values_equal,
    );
}

#[test]
fn f5c_work_replay_bulk_drain_overflow_retries_both_polarities() {
    let mut memo = F5cComponentExpansionMemo::default();
    let positive = F5cPositive::Union(vec![F5cPositive::Int, F5cPositive::Bottom]);
    let negative = F5cNegative::Intersection(vec![F5cNegative::Int, F5cNegative::Bottom]);
    let protected = HashSet::new();
    let positive_only = HashSet::new();
    let negative_only = HashSet::new();
    let meter = memo.work_meter.clone();

    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::ReplayPositive,
        &meter,
        || {
            crate::f5c_replay::replay_positive(
                &mut memo,
                &positive,
                &protected,
                &positive_only,
                &negative_only,
            )
        },
        |first, second| first == second,
    );
    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::ReplayNegative,
        &meter,
        || {
            crate::f5c_replay::replay_negative(
                &mut memo,
                &negative,
                &protected,
                &positive_only,
                &negative_only,
            )
        },
        |first, second| first == second,
    );
}

#[test]
fn f5c_work_substitution_bulk_drain_overflow_retries_both_polarities() {
    let mut memo = F5cComponentExpansionMemo::default();
    let positive = F5cPositive::Union(vec![F5cPositive::Int, F5cPositive::Bottom]);
    let negative = F5cNegative::Intersection(vec![F5cNegative::Int, F5cNegative::Bottom]);
    let q = HashMap::new();
    let r = HashMap::new();
    let positive_eliminated = HashSet::new();
    let negative_eliminated = HashSet::new();
    let meter = memo.work_meter.clone();

    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::SubstitutePositive,
        &meter,
        || {
            crate::f5c_binder_substitution::substitute_positive(
                &mut memo,
                positive.clone(),
                &q,
                &r,
                &positive_eliminated,
                &negative_eliminated,
            )
        },
        |first, second| first == second,
    );
    assert_bulk_drain_overflow_retries(
        F5cBulkDrainSite::SubstituteNegative,
        &meter,
        || {
            crate::f5c_binder_substitution::substitute_negative(
                &mut memo,
                negative.clone(),
                &q,
                &r,
                &positive_eliminated,
                &negative_eliminated,
            )
        },
        |first, second| first == second,
    );
}

#[test]
fn f5c_work_function_output_overflow_precedes_construction_and_rolls_back() {
    let batch = collect(module("my f = 1", "f5c-function-output-overflow"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
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
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(function));
    let (baseline, _, _, _) = F5cGeneralizer::new(&session).build_component(root);
    let baseline = baseline.unwrap();
    let baseline_work = session.f5c_draft_work.get();
    let (at_construction, count) =
        F5C_FUNCTION_OUTPUT_CONSTRUCTION.with(|marker| marker.take().unwrap());
    assert_eq!(count, 1);
    assert!(at_construction < baseline_work);

    session
        .f5c_draft_work
        .set(usize::MAX - (at_construction - 1));
    let (failed, memo, _, _) = F5cGeneralizer::new(&session).build_component(root);
    assert_eq!(failed, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(
        F5C_FUNCTION_OUTPUT_CONSTRUCTION.with(|marker| marker.take()),
        None
    );
    assert!(memo.roots.is_empty() && memo.nodes.is_empty() && memo.children.is_empty());
    assert!(memo.active_rows.is_empty() && memo.root_undo.is_empty());
    session.f5c_draft_work.set(0);
    let (retry, _, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert_eq!(retry, Ok(baseline));
    assert_eq!(session.f5c_draft_work.get(), baseline_work);
}

#[test]
fn f5c_work_taint_frame_overflow_precedes_mutation_and_component_restores_state() {
    let batch = collect(module("my f = 1", "f5c-taint-frame-overflow"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    let mut row = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(row));
    for _ in 0..63 {
        let next = session.fresh_value_at_level(1).unwrap();
        session.bounds[row as usize].direct_lower_rows.push(next);
        row = next;
    }
    let result = session.live_value_term(Polarity::Positive, root).unwrap();
    let argument = session.negative_top_term().unwrap();
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
    let (baseline, _, _, _) = F5cGeneralizer::new(&session).build_component(root);
    let baseline = baseline.unwrap();
    let baseline_work = session.f5c_draft_work.get();
    let (boundary_work, frames) = F5C_TAINT_BOUNDARY.with(|boundary| boundary.take().unwrap());
    assert_eq!(frames, 64);
    assert!(baseline_work > boundary_work);

    session.f5c_draft_work.set(usize::MAX - boundary_work);
    let (result, memo, _, _) = F5cGeneralizer::new(&session).build_component(root);
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.f5c_draft_work.get(), usize::MAX);
    assert_eq!(
        F5C_TAINT_BOUNDARY.with(|boundary| boundary.take()),
        Some((usize::MAX, frames))
    );
    assert!(memo.roots.is_empty() && memo.nodes.is_empty() && memo.children.is_empty());
    assert!(memo.parent_heads.is_empty() && memo.reverse_parents.is_empty());
    assert!(memo.incidence_heads.is_empty() && memo.incidences.is_empty());
    assert!(memo.root_heads.is_empty() && memo.root_edges.is_empty());
    assert!(memo.root_edge_marks.is_empty() && memo.root_undo.is_empty());
    assert!(memo.active_rows.is_empty() && memo.active_conflicts.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty());
    assert!(memo.visit_epochs.is_empty());
    assert_eq!((memo.visit_epoch, memo.root_edge_mark_epoch), (0, 0));
    assert_eq!(memo.generalizer_scratch_capacities, [0; 3]);
    session.f5c_draft_work.set(0);
    let (retry, _, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert_eq!(retry, Ok(baseline));
    assert_eq!(session.f5c_draft_work.get(), baseline_work);
}

#[test]
fn f5c_work_charges_child_inspection_separately_from_scheduling() {
    let mut memo = F5cComponentExpansionMemo::default();
    let mut function = F5cPositive::Int;
    for _ in 0..64 {
        function = F5cPositive::Function {
            argument: Box::new(F5cNegative::Int),
            result: Box::new(function),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
        };
    }
    assert!(
        !crate::f5c_tree_analysis::Walker::new(&mut memo)
            .has_guarded_owner_positive(&function, 0)
            .unwrap()
    );
    assert_eq!(memo.work_meter.get(), 2 * (2 * 64 + 1) + 2 * 64);
}

#[test]
fn f5c_work_charges_emitted_values_and_stored_direct_edges() {
    let batch = collect(module("my f = 1", "f5c-walk-operation-counts"));
    let mut session = InferenceSession::new(batch);
    let leaf = session.fresh_value_at_level(1).unwrap();
    let parent = session.fresh_value_at_level(1).unwrap();
    session.bounds[leaf as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[parent as usize].direct_lower_rows.push(leaf);
    let leaf_walk = F5cGeneralizer::new(&session).positive_row(leaf, false);
    assert!(matches!(leaf_walk, Ok(F5cPositive::Shared(_))));
    let leaf_work = session.f5c_draft_work.get();
    session.f5c_draft_work.set(0);
    let parent_walk = F5cGeneralizer::new(&session).positive_row(parent, false);
    assert!(matches!(parent_walk, Ok(F5cPositive::Shared(_))));
    let parent_work = session.f5c_draft_work.get();
    assert_eq!(leaf_work, 23); // emitted values and first-seen order registration
    assert_eq!(parent_work, 48); // direct edge, nested emissions, and two first-seen registrations
}

#[test]
fn f5c_work_accumulates_across_component_roots() {
    let batch = collect(module("my f = 1", "f5c-work-accumulation"));
    let mut session = InferenceSession::new(batch);
    let first = session.fresh_value_at_level(1).unwrap();
    let second = session.fresh_value_at_level(1).unwrap();
    let child = session.fresh_value_at_level(1).unwrap();
    session.bounds[first as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[second as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    let (result, _, _, _) = F5cGeneralizer::new(&session).build_component(first);
    assert!(result.is_ok());
    let after_first = session.f5c_draft_work.get();
    assert!(after_first > 0);
    let (result, _, _, _) = F5cGeneralizer::new(&session).build_component(second);
    assert!(result.is_ok());
    assert!(session.f5c_draft_work.get() > after_first);
}

#[test]
fn f5c_work_survives_later_component_failure_and_memo_rollback() {
    let batch = collect(module("my f = 1", "f5c-work-failure"));
    let mut session = InferenceSession::new(batch);
    let first = session.fresh_value_at_level(1).unwrap();
    let second = session.fresh_value_at_level(1).unwrap();
    let child = session.fresh_value_at_level(1).unwrap();
    session.bounds[first as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[second as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    let (result, mut memo, _, _) = F5cGeneralizer::new(&session).build_component(first);
    assert!(result.is_ok());
    let after_first = session.f5c_draft_work.get();
    let before_roots = memo.roots.clone();
    let before_nodes = memo.nodes.clone();
    memo.fail_reserve_at = Some((F5cTestReserveFailure::RootUndo, 0));
    let (result, memo, _, _) = F5cGeneralizer::with_memo(&session, memo, 1).build_component(second);
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert!(session.f5c_draft_work.get() > after_first);
    assert_eq!(memo.roots, before_roots);
    assert_eq!(memo.nodes, before_nodes);
    assert!(memo.active_rows.is_empty() && memo.root_undo.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty());
}

#[test]
fn f5c_work_overflow_rolls_back_and_repeats_cleanly() {
    let batch = collect(module("my f = 1", "f5c-work-overflow"));
    let mut session = InferenceSession::new(batch);
    let root = session.fresh_value_at_level(1).unwrap();
    let child = session.fresh_value_at_level(1).unwrap();
    let sibling = session.fresh_value_at_level(1).unwrap();
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    session.bounds[child as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[sibling as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[root as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(sibling));
    let warm = session.fresh_value_at_level(1).unwrap();
    session.bounds[warm as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::ValueRow(child));
    let (success, memo, _, _) = F5cGeneralizer::new(&session).build_component(warm);
    assert!(success.is_ok());
    let warm_work = session.f5c_draft_work.get();
    assert!(!memo.roots.is_empty() && !memo.nodes.is_empty() && !memo.incidences.is_empty());
    let warm_summary = memo.roots[&F5cExpansionKey {
        row: child,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    let (success, _, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert!(success.is_ok());
    let later_work = session.f5c_draft_work.get() - warm_work;
    assert!(later_work > 3);
    session.f5c_draft_work.set(0);
    let (success, memo, _, _) = F5cGeneralizer::new(&session).build_component(warm);
    assert!(success.is_ok());
    let before_state = (
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
    );
    session.f5c_draft_work.arm_overflow_after_root_admission(1);
    let before = session.f5c_draft_work.get();
    let (first, memo, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert_eq!(first, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.f5c_draft_work.get(), usize::MAX);
    let mutation = session
        .f5c_draft_work
        .last_persistent_mutation_work()
        .unwrap();
    assert!(mutation > before && mutation < usize::MAX);
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
            memo.root_edge_marks.clone()
        ),
        before_state
    );
    assert!(memo.active_rows.is_empty() && memo.root_undo.is_empty());
    assert!(memo.work.is_empty() && memo.conflict_journal.is_empty());
    assert!(memo.active_conflicts.is_empty());
    assert!(memo.visit_epochs.iter().all(|epoch| *epoch == 0));
    assert_eq!(memo.visit_epoch, 0);
    assert_eq!(memo.root_edge_mark_epoch, 0);
    assert_eq!(memo.generalizer_scratch_capacities, [0; 3]);
    let (second, memo, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert_eq!(second, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.f5c_draft_work.get(), usize::MAX);
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
            memo.root_edge_marks.clone()
        ),
        before_state
    );
    assert!(memo.active_rows.is_empty() && memo.root_undo.is_empty());
    session.f5c_draft_work.set(0);
    let mut raw = F5cGeneralizer::with_memo(&session, memo, 0);
    assert_eq!(
        raw.positive_row(child, false),
        Ok(F5cPositive::Shared(warm_summary))
    );
    let memo = raw.memo;
    session.f5c_draft_work.set(0);
    let (retry, _, _, _) = F5cGeneralizer::with_memo(&session, memo, 0).build_component(root);
    assert!(retry.is_ok());
    assert_eq!(session.f5c_draft_work.get(), later_work);
}
