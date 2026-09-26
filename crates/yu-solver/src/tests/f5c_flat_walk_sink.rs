use super::*;
use crate::f5c_generalization::{F5cTestObservationFailure, F5cTestReserveFailure, F5cWalkTask};

#[test]
fn flat_one_root_deduplicates_local_values_before_promotion() {
    let batch = collect(module("my f = 1", "f5c-flat-local-dedup"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .extend([ValueEndpointKey::IntPositive, ValueEndpointKey::IntPositive]);

    let mut generalizer = F5cGeneralizer::new(&session);
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
    let mut generalizer = F5cGeneralizer::new(&session);
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
    let (warm_result, memo, _, _) = F5cGeneralizer::new(&session).build_component(holder);
    assert!(warm_result.is_ok());
    let warm_id = memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: warm,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    let mut generalizer = F5cGeneralizer::with_memo(&session, memo, 0);
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
    let (built, memo, _, _) = F5cGeneralizer::new(&session).build_component(holder);
    assert!(built.is_ok());
    let warm_id = memo.roots[&crate::f5c_generalization::F5cExpansionKey {
        row: warm,
        polarity: Polarity::Positive,
        frozen_bound_epoch: 0,
    }];
    let mut generalizer = F5cGeneralizer::with_memo(&session, memo, 0);
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
    let mut generalizer = F5cGeneralizer::new(&session);
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
    let (built, memo, _, _) = F5cGeneralizer::new(&session).build_component(holder);
    assert!(built.is_ok());
    let mut generalizer = F5cGeneralizer::with_memo(&session, memo, 0);
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
    let batch = collect(module("my f = 1", "f5c-flat-after-admit"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    session.bounds[row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let mut generalizer = F5cGeneralizer::new(&session);
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
    let mut retry = F5cGeneralizer::with_memo(&session, memo, 0);
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
    let mut generalizer = F5cGeneralizer::new(&session);
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
    let (built, memo, _, _) = F5cGeneralizer::new(&session).build_component(holder);
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
    let mut generalizer = F5cGeneralizer::with_memo(&session, memo, 0);
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
    let mut generalizer = F5cGeneralizer::new(&session);
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
    let mut generalizer = F5cGeneralizer::new(&session);
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
            let mut generalizer = F5cGeneralizer::new(&session);
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
    let mut generalizer = F5cGeneralizer::new(&session);
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
