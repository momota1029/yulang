use super::*;

#[test]
fn f5c_binder_substitution_preserves_polarity_qr_and_member_order() {
    let positive = F5cPositive::Function {
        argument: Box::new(F5cNegative::Intersection(vec![
            F5cNegative::Variable(3),
            F5cNegative::Variable(4),
            F5cNegative::Variable(6),
        ])),
        argument_effect: F5cNegativeEffect::Empty,
        result_effect: F5cPositiveEffect::Bottom,
        result: Box::new(F5cPositive::Union(vec![
            F5cPositive::Variable(5),
            F5cPositive::Function {
                argument: Box::new(F5cNegative::Bottom),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(F5cPositive::Variable(1)),
            },
        ])),
    };
    let negative = F5cNegative::Intersection(vec![
        F5cNegative::Variable(6),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Union(vec![
                F5cPositive::Variable(2),
                F5cPositive::Variable(4),
                F5cPositive::Variable(5),
                F5cPositive::Int,
            ])),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(7)),
        },
        F5cNegative::Bottom,
    ]);
    let q = HashMap::from([(1, 0), (2, 1), (3, 2)]);
    let r = HashMap::from([(4, 3)]);
    let positive_eliminated = HashSet::from([5]);
    let negative_eliminated = HashSet::from([6, 7]);
    let mut memo = F5cComponentExpansionMemo::default();

    let substituted_positive = crate::f5c_binder_substitution::substitute_positive(
        &mut memo,
        positive,
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();
    let substituted_negative = crate::f5c_binder_substitution::substitute_negative(
        &mut memo,
        negative,
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();

    assert_eq!(
        substituted_positive,
        F5cPositive::Function {
            argument: Box::new(F5cNegative::Intersection(vec![
                F5cNegative::Quantified(2),
                F5cNegative::Recursive(3),
                F5cNegative::Top,
            ])),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(F5cPositive::Union(vec![
                F5cPositive::Bottom,
                F5cPositive::Function {
                    argument: Box::new(F5cNegative::Bottom),
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: Box::new(F5cPositive::Quantified(0)),
                },
            ])),
        }
    );
    assert_eq!(
        substituted_negative,
        F5cNegative::Intersection(vec![
            F5cNegative::Top,
            F5cNegative::Function {
                argument: Box::new(F5cPositive::Union(vec![
                    F5cPositive::Quantified(1),
                    F5cPositive::Recursive(3),
                    F5cPositive::Bottom,
                    F5cPositive::Int,
                ])),
                argument_effect: F5cPositiveEffect::Bottom,
                result_effect: F5cNegativeEffect::Empty,
                result: Box::new(F5cNegative::Top),
            },
            F5cNegative::Bottom,
        ])
    );
}

#[test]
fn f5c_binder_substitution_rejects_unmapped_variables_and_releases_lanes() {
    let mut memo = F5cComponentExpansionMemo::default();
    let empty_map = HashMap::new();
    let empty_set = HashSet::new();

    assert_eq!(
        crate::f5c_binder_substitution::substitute_positive(
            &mut memo,
            F5cPositive::Variable(90),
            &empty_map,
            &empty_map,
            &empty_set,
            &empty_set,
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    for kind in [
        F5cWalkerLaneKind::BinderTasks,
        F5cWalkerLaneKind::BinderValues,
    ] {
        assert_eq!(
            memo.walker_resources.lanes[kind as usize].actual_capacity,
            0
        );
    }
}

#[test]
fn f5c_binder_substitution_handles_deep_trees_on_small_stack() {
    const DEPTH: usize = 4096;
    let mut positive = F5cPositive::Variable(1);
    for _ in 0..DEPTH {
        positive = F5cPositive::Function {
            argument: Box::new(F5cNegative::Variable(3)),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(positive),
        };
    }
    let mut negative = F5cNegative::Variable(2);
    for _ in 0..DEPTH {
        negative = F5cNegative::Function {
            argument: Box::new(F5cPositive::Variable(4)),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(negative),
        };
    }

    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut memo = F5cComponentExpansionMemo::default();
            let q = HashMap::from([(1, 0), (2, 1), (4, 2)]);
            let r = HashMap::from([(3, 3)]);
            let empty = HashSet::new();
            let substituted_positive = crate::f5c_binder_substitution::substitute_positive(
                &mut memo, positive, &q, &r, &empty, &empty,
            )
            .unwrap();
            let substituted_negative = crate::f5c_binder_substitution::substitute_negative(
                &mut memo, negative, &q, &r, &empty, &empty,
            )
            .unwrap();

            let mut positive_functions = 0;
            let mut positive_cursor = &substituted_positive;
            loop {
                match positive_cursor {
                    F5cPositive::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert_eq!(argument.as_ref(), &F5cNegative::Recursive(3));
                        assert_eq!(*argument_effect, F5cNegativeEffect::Empty);
                        assert_eq!(*result_effect, F5cPositiveEffect::Bottom);
                        positive_functions += 1;
                        positive_cursor = result;
                    }
                    F5cPositive::Quantified(0) => break,
                    _ => panic!("positive substitution reaches its Q leaf"),
                }
            }
            let mut negative_functions = 0;
            let mut negative_cursor = &substituted_negative;
            loop {
                match negative_cursor {
                    F5cNegative::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        assert_eq!(argument.as_ref(), &F5cPositive::Quantified(2));
                        assert_eq!(*argument_effect, F5cPositiveEffect::Bottom);
                        assert_eq!(*result_effect, F5cNegativeEffect::Empty);
                        negative_functions += 1;
                        negative_cursor = result;
                    }
                    F5cNegative::Quantified(1) => break,
                    _ => panic!("negative substitution reaches its Q leaf"),
                }
            }
            assert_eq!(positive_functions, DEPTH);
            assert_eq!(negative_functions, DEPTH);

            for kind in [
                F5cWalkerLaneKind::BinderTasks,
                F5cWalkerLaneKind::BinderValues,
            ] {
                let lane = memo.walker_resources.lanes[kind as usize];
                assert!(lane.requested_slots >= DEPTH);
                assert_eq!(lane.actual_capacity, 0);
            }
            let mut ledger = IndependentResourceLedger::default();
            ledger.record_component_expansion_memo(&memo).unwrap();
            for kind in [
                F5cWalkerLaneKind::BinderTasks,
                F5cWalkerLaneKind::BinderValues,
            ] {
                let index = kind as usize;
                let physical = memo.walker_resources.independent_lanes[index];
                let recorded = &ledger.generalization_walker_lanes[index];
                assert_eq!(recorded.requested_slots, physical.requested_slots);
                assert_eq!(recorded.capacity_growths, physical.capacity_growths);
                assert_eq!(recorded.peak_bytes, physical.peak_bytes);
                assert_eq!(recorded.actual_capacity, 0);
            }
            std::mem::forget(substituted_positive);
            std::mem::forget(substituted_negative);
        })
        .unwrap();
    worker.join().unwrap();
}
