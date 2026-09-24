use super::*;

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
    let store = session.store;
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
