use super::*;

#[test]
fn f5c_replay_preserves_polarity_elimination_and_product_order() {
    let positive = F5cPositive::Function {
        argument: Box::new(F5cNegative::Intersection(vec![
            F5cNegative::Variable(2),
            F5cNegative::Variable(3),
        ])),
        argument_effect: F5cNegativeEffect::Empty,
        result_effect: F5cPositiveEffect::Bottom,
        result: Box::new(F5cPositive::Union(vec![
            F5cPositive::Variable(1),
            F5cPositive::Function {
                argument: Box::new(F5cNegative::Top),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(F5cPositive::Variable(3)),
            },
        ])),
    };
    let negative = F5cNegative::Intersection(vec![
        F5cNegative::Variable(3),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Union(vec![
                F5cPositive::Variable(2),
                F5cPositive::Variable(3),
            ])),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(1)),
        },
    ]);
    let protected = HashSet::from([3]);
    let positive_only = HashSet::from([1, 2, 3]);
    let negative_only = HashSet::from([1, 2, 3]);
    let mut memo = F5cComponentExpansionMemo::default();

    let positive_replayed = crate::f5c_replay::replay_positive(
        &mut memo,
        &positive,
        &protected,
        &positive_only,
        &negative_only,
    )
    .unwrap();
    let negative_replayed = crate::f5c_replay::replay_negative(
        &mut memo,
        &negative,
        &protected,
        &positive_only,
        &negative_only,
    )
    .unwrap();

    assert_eq!(
        positive_replayed,
        F5cPositive::Function {
            argument: Box::new(F5cNegative::Intersection(vec![
                F5cNegative::Top,
                F5cNegative::Variable(3),
            ])),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Union(vec![
                F5cPositive::Bottom,
                F5cPositive::Function {
                    argument: Box::new(F5cNegative::Top),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Variable(3)),
                },
            ])),
        }
    );
    assert_eq!(
        negative_replayed,
        F5cNegative::Intersection(vec![
            F5cNegative::Variable(3),
            F5cNegative::Function {
                argument: Box::new(F5cPositive::Union(vec![
                    F5cPositive::Bottom,
                    F5cPositive::Variable(3),
                ])),
                argument_effect: F5cPositiveEffect::Bottom,
                result_effect: F5cNegativeEffect::Empty,
                result: Box::new(F5cNegative::Top),
            },
        ])
    );
}

#[test]
fn f5c_replay_handles_deep_positive_and_negative_trees_on_small_stack() {
    const DEPTH: usize = 4096;
    let mut positive = F5cPositive::Variable(7);
    for _ in 0..DEPTH {
        positive = F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(9)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(positive),
        };
    }
    let mut negative = F5cNegative::Variable(8);
    for _ in 0..DEPTH {
        negative = F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(9)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(negative),
        };
    }
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut memo = F5cComponentExpansionMemo::default();
            let empty = HashSet::new();
            let positive_only = HashSet::from([7, 9]);
            let negative_only = HashSet::from([8, 9]);
            let replayed_positive = crate::f5c_replay::replay_positive(
                &mut memo,
                &positive,
                &empty,
                &positive_only,
                &negative_only,
            )
            .unwrap();
            let replayed_negative = crate::f5c_replay::replay_negative(
                &mut memo,
                &negative,
                &empty,
                &positive_only,
                &negative_only,
            )
            .unwrap();

            let mut positive_functions = 0;
            let mut positive_cursor = &replayed_positive;
            loop {
                match positive_cursor {
                    F5cPositive::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert_eq!(argument.as_ref(), &F5cNegative::Top);
                        assert_eq!(*argument_effect, F5cNegativeEffect::Empty);
                        assert_eq!(*result_effect, F5cPositiveEffect::Bottom);
                        positive_functions += 1;
                        positive_cursor = result;
                    }
                    F5cPositive::Bottom => break,
                    _ => panic!("positive replay reaches the eliminated leaf"),
                }
            }
            let mut negative_functions = 0;
            let mut negative_cursor = &replayed_negative;
            loop {
                match negative_cursor {
                    F5cNegative::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert_eq!(argument.as_ref(), &F5cPositive::Bottom);
                        assert_eq!(*argument_effect, F5cPositiveEffect::Bottom);
                        assert_eq!(*result_effect, F5cNegativeEffect::Empty);
                        negative_functions += 1;
                        negative_cursor = result;
                    }
                    F5cNegative::Top => break,
                    _ => panic!("negative replay reaches the eliminated leaf"),
                }
            }
            assert_eq!(positive_functions, DEPTH);
            assert_eq!(negative_functions, DEPTH);
            for kind in [
                F5cWalkerLaneKind::ReplayTasks,
                F5cWalkerLaneKind::ReplayValues,
            ] {
                let lane = memo.walker_resources.lanes[kind as usize];
                assert!(lane.requested_slots >= DEPTH);
                assert_eq!(lane.actual_capacity, 0);
            }
            let mut ledger = IndependentResourceLedger::default();
            ledger.record_component_expansion_memo(&memo).unwrap();
            for kind in [
                F5cWalkerLaneKind::ReplayTasks,
                F5cWalkerLaneKind::ReplayValues,
            ] {
                let index = kind as usize;
                let physical = memo.walker_resources.independent_lanes[index];
                let recorded = &ledger.generalization_walker_lanes[index];
                assert_eq!(recorded.requested_slots, physical.requested_slots);
                assert_eq!(recorded.capacity_growths, physical.capacity_growths);
                assert_eq!(recorded.peak_bytes, physical.peak_bytes);
                assert_eq!(recorded.actual_capacity, 0);
            }
            std::mem::forget(positive);
            std::mem::forget(negative);
            std::mem::forget(replayed_positive);
            std::mem::forget(replayed_negative);
        })
        .unwrap();
    worker.join().unwrap();
}
