use super::*;

fn alternating_function_chain(depth: usize) -> F5cWalkValue {
    let mut value = F5cWalkValue::Positive(F5cPositive::Int, true);
    for _ in 0..depth {
        value = match value {
            F5cWalkValue::Positive(value, _) => F5cWalkValue::Negative(
                F5cNegative::Function {
                    argument: Box::new(value),
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: Box::new(F5cNegative::Int),
                },
                true,
            ),
            F5cWalkValue::Negative(value, _) => F5cWalkValue::Positive(
                F5cPositive::Function {
                    argument: Box::new(value),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Int),
                },
                true,
            ),
        };
    }
    value
}

fn consume_alternating_function_chain(mut value: F5cWalkValue) -> usize {
    let mut functions = 0;
    loop {
        value = match value {
            F5cWalkValue::Positive(
                F5cPositive::Function {
                    argument, result, ..
                },
                _,
            ) => {
                assert!(matches!(*result, F5cPositive::Int));
                functions += 1;
                F5cWalkValue::Negative(*argument, true)
            }
            F5cWalkValue::Negative(
                F5cNegative::Function {
                    argument, result, ..
                },
                _,
            ) => {
                assert!(matches!(*result, F5cNegative::Int));
                functions += 1;
                F5cWalkValue::Positive(*argument, true)
            }
            F5cWalkValue::Positive(F5cPositive::Int, _) => return functions,
            _ => panic!("alternating Function chain remains intact"),
        };
    }
}

#[test]
fn f5c_draft_materialization_handles_deep_alternating_functions_on_small_stack() {
    const DEPTH: usize = 2048;
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            let mut memo = F5cComponentExpansionMemo::default();

            let F5cWalkValue::Positive(positive, _) = alternating_function_chain(DEPTH) else {
                panic!("even-depth chain has positive root");
            };
            let F5cWalkValue::Positive(positive, _) =
                crate::f5c_materialization::materialize_iterative(
                    &mut memo,
                    crate::f5c_materialization::Task::Positive(positive),
                    |_, _, _| Err(SolveAvailabilityError::IdentityExhausted),
                )
                .unwrap()
            else {
                panic!("positive polarity is preserved");
            };
            assert_eq!(
                consume_alternating_function_chain(F5cWalkValue::Positive(positive, true)),
                DEPTH
            );

            let F5cWalkValue::Negative(negative, _) = alternating_function_chain(DEPTH + 1) else {
                panic!("odd-depth chain has negative root");
            };
            let F5cWalkValue::Negative(negative, _) =
                crate::f5c_materialization::materialize_iterative(
                    &mut memo,
                    crate::f5c_materialization::Task::Negative(negative),
                    |_, _, _| Err(SolveAvailabilityError::IdentityExhausted),
                )
                .unwrap()
            else {
                panic!("negative polarity is preserved");
            };
            assert_eq!(
                consume_alternating_function_chain(F5cWalkValue::Negative(negative, true)),
                DEPTH + 1
            );

            let mut ledger = IndependentResourceLedger::default();
            ledger.record_component_expansion_memo(&memo).unwrap();
            for kind in [
                F5cWalkerLaneKind::DraftMaterializeTasks,
                F5cWalkerLaneKind::DraftMaterializeValues,
            ] {
                let lane = memo.walker_resources.lanes[kind as usize];
                let independent = memo.walker_resources.independent_lanes[kind as usize];
                let recorded = &ledger.generalization_walker_lanes[kind as usize];
                assert!(lane.requested_slots >= DEPTH);
                assert!(lane.capacity_growths > 0);
                assert!(lane.peak_bytes > 0);
                assert_eq!(lane.actual_capacity, 0);
                assert_eq!(independent.requested_slots, lane.requested_slots);
                assert_eq!(independent.capacity_growths, lane.capacity_growths);
                assert_eq!(independent.peak_bytes, lane.peak_bytes);
                assert_eq!(independent.actual_capacity, 0);
                assert_eq!(recorded.requested_slots, lane.requested_slots);
                assert_eq!(recorded.capacity_growths, lane.capacity_growths);
                assert_eq!(recorded.peak_bytes, lane.peak_bytes);
                assert_eq!(recorded.actual_capacity, 0);
            }
            assert_eq!(
                ledger.generalization_walker_peak_bytes,
                memo.walker_resources.independent_peak_bytes
            );
        })
        .unwrap();
    worker.join().unwrap();
}

#[test]
fn f5c_recursive_bound_materialization_moves_deep_trees_on_small_stack() {
    const DEPTH: usize = 4096;
    let mut lower = F5cPositive::Int;
    for _ in 0..DEPTH {
        lower = F5cPositive::Function {
            argument: Box::new(F5cNegative::Int),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(lower),
        };
    }
    let mut upper = F5cNegative::Int;
    for _ in 0..DEPTH {
        upper = F5cNegative::Function {
            argument: Box::new(F5cPositive::Int),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(upper),
        };
    }
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut memo = F5cComponentExpansionMemo::default();
            let mut bounds = HashMap::from([(0, (lower, upper))]);
            crate::f5c_materialization::materialize_bound_trees(&mut bounds, |value| {
                let task = match value {
                    F5cWalkValue::Positive(value, _) => {
                        crate::f5c_materialization::Task::Positive(value)
                    }
                    F5cWalkValue::Negative(value, _) => {
                        crate::f5c_materialization::Task::Negative(value)
                    }
                };
                crate::f5c_materialization::materialize_iterative(&mut memo, task, |_, _, _| {
                    Err(SolveAvailabilityError::IdentityExhausted)
                })
            })
            .unwrap();

            let (lower, upper) = bounds.get(&0).unwrap();
            let mut positive_functions = 0;
            let mut positive_cursor = lower;
            loop {
                match positive_cursor {
                    F5cPositive::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert_eq!(argument.as_ref(), &F5cNegative::Int);
                        assert_eq!(*argument_effect, F5cNegativeEffect::Empty);
                        assert_eq!(*result_effect, F5cPositiveEffect::Bottom);
                        positive_functions += 1;
                        positive_cursor = result;
                    }
                    F5cPositive::Int => break,
                    _ => panic!("positive bound remains an ordered Function chain"),
                }
            }
            let mut negative_functions = 0;
            let mut negative_cursor = upper;
            loop {
                match negative_cursor {
                    F5cNegative::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert_eq!(argument.as_ref(), &F5cPositive::Int);
                        assert_eq!(*argument_effect, F5cPositiveEffect::Bottom);
                        assert_eq!(*result_effect, F5cNegativeEffect::Empty);
                        negative_functions += 1;
                        negative_cursor = result;
                    }
                    F5cNegative::Int => break,
                    _ => panic!("negative bound remains an ordered Function chain"),
                }
            }
            assert_eq!(positive_functions, DEPTH);
            assert_eq!(negative_functions, DEPTH);

            let mut ledger = IndependentResourceLedger::default();
            ledger.record_component_expansion_memo(&memo).unwrap();
            for kind in [
                F5cWalkerLaneKind::DraftMaterializeTasks,
                F5cWalkerLaneKind::DraftMaterializeValues,
            ] {
                let lane = memo.walker_resources.lanes[kind as usize];
                let recorded = &ledger.generalization_walker_lanes[kind as usize];
                assert!(lane.requested_slots >= DEPTH);
                assert!(lane.peak_bytes > 0);
                assert_eq!(lane.actual_capacity, 0);
                assert_eq!(recorded.requested_slots, lane.requested_slots);
                assert_eq!(recorded.capacity_growths, lane.capacity_growths);
                assert_eq!(recorded.peak_bytes, lane.peak_bytes);
                assert_eq!(recorded.actual_capacity, 0);
            }
            std::mem::forget(bounds);
        })
        .unwrap();
    worker.join().unwrap();
}
