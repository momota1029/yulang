use super::*;

#[test]
fn f5c_flat_analysis_traces_repeated_edges_and_recovers_from_bad_indices() {
    use crate::f5c_draft::{
        ChildSpan, FlatDraft, NegativeId, NegativeNode, PositiveId, PositiveNode,
    };
    use crate::f5c_tree_analysis::Task;

    let mut flat = FlatDraft::default();
    let positive = flat.positive(PositiveNode::Variable(7)).unwrap();
    let negative = flat.negative(NegativeNode::Variable(8)).unwrap();
    let function = flat
        .positive(PositiveNode::Function {
            argument: negative,
            result: positive,
        })
        .unwrap();
    flat.positive_children
        .extend([positive, function, positive, function]);
    let positive_root = flat
        .positive(PositiveNode::Union(ChildSpan { start: 0, len: 4 }))
        .unwrap();
    let negative_function = flat
        .negative(NegativeNode::Function {
            argument: positive,
            result: negative,
        })
        .unwrap();
    flat.negative_children
        .extend([negative, negative_function, negative, negative_function]);
    let negative_root = flat
        .negative(NegativeNode::Intersection(ChildSpan { start: 0, len: 4 }))
        .unwrap();
    let boxed_positive = F5cPositive::Union(vec![
        F5cPositive::Variable(7),
        F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(8)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Variable(7)),
        },
        F5cPositive::Variable(7),
        F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(8)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Variable(7)),
        },
    ]);
    let boxed_negative = F5cNegative::Intersection(vec![
        F5cNegative::Variable(8),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(7)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(8)),
        },
        F5cNegative::Variable(8),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(7)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(8)),
        },
    ]);
    let mut memo = F5cComponentExpansionMemo::default();
    let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
    for (lower, upper) in [
        (PositiveId(u32::MAX), negative_root),
        (positive_root, NegativeId(u32::MAX)),
    ] {
        assert!(matches!(
            walker.flat_guarded_bound_survives(&flat, 7, lower, upper),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
    }
    for limit in [usize::MAX, 3] {
        assert_eq!(
            walker
                .trace_values(Some(&flat), Task::FlatPositive(positive_root, false), limit)
                .unwrap(),
            walker
                .trace_values(None, Task::Positive(&boxed_positive, false), limit)
                .unwrap()
        );
        assert_eq!(
            walker
                .trace_values(Some(&flat), Task::FlatNegative(negative_root, false), limit)
                .unwrap(),
            walker
                .trace_values(None, Task::Negative(&boxed_negative, false), limit)
                .unwrap()
        );
    }
    let before = walker.memo.work_meter.get();
    walker
        .trace_values(
            Some(&flat),
            Task::FlatPositive(positive_root, false),
            usize::MAX,
        )
        .unwrap();
    let flat_charge = walker.memo.work_meter.get() - before;
    let before = walker.memo.work_meter.get();
    walker
        .trace_values(None, Task::Positive(&boxed_positive, false), usize::MAX)
        .unwrap();
    assert_eq!(flat_charge, walker.memo.work_meter.get() - before);
    assert_eq!(flat_charge, 26); // 9 visits, 9 scheduled tasks, 8 child edges.

    for task in [
        Task::FlatPositive(PositiveId(u32::MAX), false),
        Task::FlatNegative(NegativeId(u32::MAX), false),
    ] {
        assert!(matches!(
            walker.trace_values(Some(&flat), task, usize::MAX),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
        assert!(walker.tasks_are_clear_for_test());
        assert_eq!(
            walker
                .trace_values(Some(&flat), Task::FlatPositive(positive, false), usize::MAX)
                .unwrap(),
            vec![(7, Polarity::Positive, false)]
        );
    }
    for span in [
        ChildSpan {
            start: u32::MAX,
            len: 2,
        },
        ChildSpan { start: 0, len: 5 },
    ] {
        let bad_positive = flat.positive(PositiveNode::Union(span)).unwrap();
        let bad_negative = flat.negative(NegativeNode::Intersection(span)).unwrap();
        for task in [
            Task::FlatPositive(bad_positive, false),
            Task::FlatNegative(bad_negative, false),
        ] {
            assert!(matches!(
                walker.trace_values(Some(&flat), task, usize::MAX),
                Err(SolveAvailabilityError::IdentityExhausted)
            ));
            assert!(walker.tasks_are_clear_for_test());
            assert_eq!(
                walker
                    .trace_values(Some(&flat), Task::FlatNegative(negative, false), usize::MAX)
                    .unwrap(),
                vec![(8, Polarity::Negative, false)]
            );
        }
    }
    flat.positive_children[0] = PositiveId(u32::MAX);
    assert!(matches!(
        walker.trace_values(
            Some(&flat),
            Task::FlatPositive(positive_root, false),
            usize::MAX
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(walker.tasks_are_clear_for_test());
    flat.positive_children[0] = positive;
    flat.negative_children[0] = NegativeId(u32::MAX);
    assert!(matches!(
        walker.trace_values(
            Some(&flat),
            Task::FlatNegative(negative_root, false),
            usize::MAX
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    ));
    assert!(walker.tasks_are_clear_for_test());
    flat.negative_children[0] = negative;
    assert_eq!(
        walker
            .trace_values(Some(&flat), Task::FlatNegative(negative_root, false), 3)
            .unwrap(),
        walker
            .trace_values(None, Task::Negative(&boxed_negative, false), 3)
            .unwrap()
    );
}

#[test]
fn f5c_flat_tree_analysis_matches_boxed_dfs_and_guarding() {
    use crate::f5c_draft::{ChildSpan, FlatDraft, NegativeNode, NodeRef, PositiveNode};
    let mut flat = FlatDraft::default();
    let first = flat.positive(PositiveNode::Variable(3)).unwrap();
    let argument = flat.negative(NegativeNode::Variable(4)).unwrap();
    let result = flat.positive(PositiveNode::Variable(3)).unwrap();
    let function = flat
        .positive(PositiveNode::Function { argument, result })
        .unwrap();
    let last = flat.positive(PositiveNode::Variable(5)).unwrap();
    flat.positive_children.extend([first, function, last]);
    let span = ChildSpan { start: 0, len: 3 };
    let root = flat.positive(PositiveNode::Union(span)).unwrap();
    let top = flat.negative(NegativeNode::Top).unwrap();
    let boxed = F5cPositive::Union(vec![
        F5cPositive::Variable(3),
        F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(4)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Variable(3)),
        },
        F5cPositive::Variable(5),
    ]);
    let mut memo = F5cComponentExpansionMemo::default();
    let mut flat_order = Vec::new();
    let mut boxed_order = Vec::new();
    let mut flat_seen = HashSet::new();
    let mut boxed_seen = HashSet::new();
    let mut flat_positive = HashSet::new();
    let mut flat_negative = HashSet::new();
    let mut boxed_positive = HashSet::new();
    let mut boxed_negative = HashSet::new();
    let mut flat_references = HashSet::new();
    let mut boxed_references = HashSet::new();
    let owners = HashSet::from([4, 5]);
    let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
    walker
        .flat_occurrences(
            &flat,
            NodeRef::Positive(root),
            &mut flat_order,
            &mut flat_seen,
        )
        .unwrap();
    walker
        .occurrences_positive(&boxed, &mut boxed_order, &mut boxed_seen)
        .unwrap();
    walker
        .flat_incidences(
            &flat,
            NodeRef::Positive(root),
            &mut flat_positive,
            &mut flat_negative,
        )
        .unwrap();
    walker
        .incidences_positive(&boxed, &mut boxed_positive, &mut boxed_negative)
        .unwrap();
    walker
        .flat_references(
            &flat,
            NodeRef::Positive(root),
            &owners,
            &mut flat_references,
        )
        .unwrap();
    walker
        .references_positive(&boxed, &owners, &mut boxed_references)
        .unwrap();
    assert_eq!(flat_order, boxed_order);
    assert_eq!(
        (flat_positive, flat_negative),
        (boxed_positive, boxed_negative)
    );
    assert_eq!(flat_references, boxed_references);
    assert_eq!(
        walker
            .flat_guarded_bound_survives(&flat, 3, root, top)
            .unwrap(),
        walker
            .guarded_bound_survives(3, &boxed, &F5cNegative::Top)
            .unwrap()
    );

    drop(walker);
    let negative_first = flat.negative(NegativeNode::Variable(8)).unwrap();
    let negative_argument = flat.positive(PositiveNode::Variable(6)).unwrap();
    let negative_result = flat.negative(NegativeNode::Variable(8)).unwrap();
    let negative_function = flat
        .negative(NegativeNode::Function {
            argument: negative_argument,
            result: negative_result,
        })
        .unwrap();
    flat.negative_children
        .extend([negative_first, negative_function]);
    let negative_root = flat
        .negative(NegativeNode::Intersection(ChildSpan { start: 0, len: 2 }))
        .unwrap();
    let boxed_negative_root = F5cNegative::Intersection(vec![
        F5cNegative::Variable(8),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(6)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(8)),
        },
    ]);
    let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
    let mut flat_order = Vec::new();
    let mut boxed_order = Vec::new();
    let mut flat_seen = HashSet::new();
    let mut boxed_seen = HashSet::new();
    walker
        .flat_occurrences(
            &flat,
            NodeRef::Negative(negative_root),
            &mut flat_order,
            &mut flat_seen,
        )
        .unwrap();
    walker
        .occurrences_negative(&boxed_negative_root, &mut boxed_order, &mut boxed_seen)
        .unwrap();
    assert_eq!(flat_order, boxed_order);
    assert_eq!(flat_order, [8, 6]);
    assert_eq!(
        walker
            .flat_guarded_bound_survives(&flat, 8, root, negative_root)
            .unwrap(),
        walker
            .guarded_bound_survives(8, &boxed, &boxed_negative_root)
            .unwrap()
    );
}

#[test]
fn f5c_tree_analysis_preserves_depth_first_polarity_and_first_occurrence() {
    let value = F5cPositive::Union(vec![
        F5cPositive::Variable(3),
        F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(4)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Variable(3)),
        },
        F5cPositive::Variable(5),
    ]);
    let mut memo = F5cComponentExpansionMemo::default();
    let mut ordered = Vec::new();
    let mut seen = HashSet::new();
    let mut positive = HashSet::new();
    let mut negative = HashSet::new();
    {
        let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
        walker
            .occurrences_positive(&value, &mut ordered, &mut seen)
            .unwrap();
    }
    {
        let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
        walker
            .incidences_positive(&value, &mut positive, &mut negative)
            .unwrap();
    }
    assert_eq!(ordered, [3, 4, 5]);
    assert_eq!(positive, HashSet::from([3, 5]));
    assert_eq!(negative, HashSet::from([4]));
    let mut references = HashSet::new();
    {
        let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
        walker
            .references_positive(&value, &HashSet::from([4, 5]), &mut references)
            .unwrap();
    }
    assert_eq!(references, HashSet::from([4, 5]));
    {
        let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
        assert!(walker.has_guarded_owner_positive(&value, 3).unwrap());
        assert!(!walker.has_guarded_owner_positive(&value, 5).unwrap());
    }

    let negative_value = F5cNegative::Intersection(vec![
        F5cNegative::Variable(8),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(6)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(8)),
        },
        F5cNegative::Variable(9),
    ]);
    let mut negative_ordered = Vec::new();
    let mut negative_seen = HashSet::new();
    let mut negative_positive = HashSet::new();
    let mut negative_negative = HashSet::new();
    {
        let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
        walker
            .occurrences_negative(&negative_value, &mut negative_ordered, &mut negative_seen)
            .unwrap();
        walker
            .incidences_negative(
                &negative_value,
                &mut negative_positive,
                &mut negative_negative,
            )
            .unwrap();
        assert!(
            walker
                .has_guarded_owner_negative(&negative_value, 8)
                .unwrap()
        );
    }
    assert_eq!(negative_ordered, [8, 6, 9]);
    assert_eq!(negative_positive, HashSet::from([6]));
    assert_eq!(negative_negative, HashSet::from([8, 9]));

    let lane = F5cWalkerLaneKind::AnalysisTasks as usize;
    assert!(memo.walker_resources.lanes[lane].requested_slots > 0);
    assert_eq!(memo.walker_resources.lanes[lane].actual_capacity, 0);
    let mut ledger = IndependentResourceLedger::default();
    ledger.record_component_expansion_memo(&memo).unwrap();
    let physical = memo.walker_resources.independent_lanes[lane];
    let recorded = &ledger.generalization_walker_lanes[lane];
    assert_eq!(recorded.requested_slots, physical.requested_slots);
    assert_eq!(recorded.capacity_growths, physical.capacity_growths);
    assert_eq!(recorded.peak_bytes, physical.peak_bytes);
    assert_eq!(recorded.actual_capacity, 0);
}

#[test]
fn f5c_tree_and_term_analysis_are_stack_safe_on_small_stacks() {
    const DEPTH: usize = 4096;
    let mut value = F5cPositive::Variable(7);
    for _ in 0..DEPTH {
        value = F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(99)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(value),
        };
    }
    let mut negative_value = F5cNegative::Variable(8);
    for _ in 0..DEPTH {
        negative_value = F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(100)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(negative_value),
        };
    }
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut memo = F5cComponentExpansionMemo::default();
            let mut ordered = Vec::new();
            let mut seen = HashSet::new();
            {
                let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
                walker
                    .occurrences_positive(&value, &mut ordered, &mut seen)
                    .unwrap();
            }
            let guarded = {
                let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
                walker.has_guarded_owner_positive(&value, 7).unwrap()
            };
            assert_eq!(ordered, [99, 7]);
            assert!(guarded);
            assert!(
                memo.walker_resources.lanes[F5cWalkerLaneKind::AnalysisTasks as usize]
                    .requested_slots
                    >= DEPTH
            );
            std::mem::forget(value);
            let mut memo = F5cComponentExpansionMemo::default();
            let mut ordered = Vec::new();
            let mut seen = HashSet::new();
            let guarded = {
                let mut walker = crate::f5c_tree_analysis::Walker::new(&mut memo);
                walker
                    .occurrences_negative(&negative_value, &mut ordered, &mut seen)
                    .unwrap();
                walker
                    .has_guarded_owner_negative(&negative_value, 8)
                    .unwrap()
            };
            assert_eq!(ordered, [100, 8]);
            assert!(guarded);
            std::mem::forget(negative_value);
        })
        .unwrap();
    worker.join().unwrap();

    let batch = collect(module("my f = 1", "f5c-deep-term-analysis"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    let live = session.live_value_term(Polarity::Positive, row).unwrap();
    let argument = session.negative_top_term().unwrap();
    let argument_effect = session.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
    let result_effect = session
        .batch
        .collected_leaf_term(Leaf::EffectBottomPositive);
    let mut term = live;
    for _ in 0..DEPTH {
        term = session
            .positive_function_term(argument, argument_effect, result_effect, term)
            .unwrap();
    }
    let store = Box::new(session.store);
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut memo = F5cComponentExpansionMemo::default();
            let mut rows = HashSet::new();
            crate::f5c_tree_analysis::Walker::new(&mut memo)
                .term_rows(&store, term, &mut rows)
                .unwrap();
            assert_eq!(rows, HashSet::from([row]));
            assert_eq!(
                memo.walker_resources.lanes[F5cWalkerLaneKind::AnalysisTasks as usize]
                    .actual_capacity,
                0
            );
        })
        .unwrap();
    worker.join().unwrap();
}
