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
