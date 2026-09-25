use super::*;
use crate::f5c_draft::{FlatDraft, NegativeNode, PositiveNode, RecursiveBound};

#[test]
fn f5c_flat_substitution_matches_boxed_roots_and_preserves_layout() {
    let mut flat = FlatDraft::default();
    let p_r = flat.positive(PositiveNode::Variable(4)).unwrap();
    let p_q = flat.positive(PositiveNode::Variable(1)).unwrap();
    let p_gone = flat.positive(PositiveNode::Variable(5)).unwrap();
    let p_int = flat.positive(PositiveNode::Int).unwrap();
    let n_q = flat.negative(NegativeNode::Variable(2)).unwrap();
    let n_r = flat.negative(NegativeNode::Variable(4)).unwrap();
    let n_gone = flat.negative(NegativeNode::Variable(6)).unwrap();
    let n_span = flat.negative_span(&[n_q, n_r, n_gone]).unwrap();
    let n_intersection = flat.negative(NegativeNode::Intersection(n_span)).unwrap();
    let p_span = flat.positive_span(&[p_r, p_q, p_gone, p_int]).unwrap();
    let p_union = flat.positive(PositiveNode::Union(p_span)).unwrap();
    let predicate = flat
        .positive(PositiveNode::Function {
            argument: n_intersection,
            result: p_union,
        })
        .unwrap();
    let upper = flat
        .negative(NegativeNode::Function {
            argument: p_union,
            result: n_intersection,
        })
        .unwrap();
    flat.predicate = Some(predicate);
    flat.quantifier_count = 2;
    flat.bound(RecursiveBound {
        ordinal: 3,
        lower: p_union,
        upper,
    })
    .unwrap();

    let before_positive = flat.positive_nodes.clone();
    let before_negative = flat.negative_nodes.clone();
    let before_positive_children = flat.positive_children.clone();
    let before_negative_children = flat.negative_children.clone();
    let before_bounds = flat.recursive_bounds.clone();
    let before_order = flat.insertion_order.clone();
    let q = HashMap::from([(1, 0), (2, 1), (4, 99)]);
    let r = HashMap::from([(4, 3)]);
    let positive_eliminated = HashSet::from([5]);
    let negative_eliminated = HashSet::from([6]);

    crate::f5c_binder_substitution::substitute_flat(
        &mut flat,
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();

    let positive_input = F5cPositive::Union(vec![
        F5cPositive::Variable(4),
        F5cPositive::Variable(1),
        F5cPositive::Variable(5),
        F5cPositive::Int,
    ]);
    let negative_input = F5cNegative::Intersection(vec![
        F5cNegative::Variable(2),
        F5cNegative::Variable(4),
        F5cNegative::Variable(6),
    ]);
    let mut memo = F5cComponentExpansionMemo::default();
    let oracle_positive = crate::f5c_binder_substitution::substitute_positive(
        &mut memo,
        F5cPositive::Function {
            argument: Box::new(negative_input.clone()),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(positive_input.clone()),
        },
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();
    let oracle_negative = crate::f5c_binder_substitution::substitute_negative(
        &mut memo,
        F5cNegative::Function {
            argument: Box::new(positive_input),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(negative_input),
        },
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();

    let substituted_positive = F5cPositive::Union(vec![
        F5cPositive::Recursive(3),
        F5cPositive::Quantified(0),
        F5cPositive::Bottom,
        F5cPositive::Int,
    ]);
    let substituted_negative = F5cNegative::Intersection(vec![
        F5cNegative::Quantified(1),
        F5cNegative::Recursive(3),
        F5cNegative::Top,
    ]);
    assert_eq!(
        oracle_positive,
        F5cPositive::Function {
            argument: Box::new(substituted_negative.clone()),
            argument_effect: F5cNegativeEffect::Empty,
            result_effect: F5cPositiveEffect::Bottom,
            result: Box::new(substituted_positive.clone()),
        }
    );
    assert_eq!(
        oracle_negative,
        F5cNegative::Function {
            argument: Box::new(substituted_positive),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(substituted_negative),
        }
    );
    assert_eq!(
        flat.positive_nodes,
        vec![
            PositiveNode::Recursive(3),
            PositiveNode::Quantified(0),
            PositiveNode::Bottom,
            PositiveNode::Int,
            PositiveNode::Union(p_span),
            PositiveNode::Function {
                argument: n_intersection,
                result: p_union
            },
        ]
    );
    assert_eq!(
        flat.negative_nodes,
        vec![
            NegativeNode::Quantified(1),
            NegativeNode::Recursive(3),
            NegativeNode::Top,
            NegativeNode::Intersection(n_span),
            NegativeNode::Function {
                argument: p_union,
                result: n_intersection
            },
        ]
    );
    assert_eq!(&flat.positive_nodes[4..], &before_positive[4..]);
    assert_eq!(&flat.negative_nodes[3..], &before_negative[3..]);
    assert_eq!(flat.predicate, Some(predicate));
    assert_eq!(flat.quantifier_count, 2);
    assert_eq!(flat.recursive_bounds, before_bounds);
    assert_eq!(flat.positive_children, before_positive_children);
    assert_eq!(flat.negative_children, before_negative_children);
    assert_eq!(flat.insertion_order, before_order);
}

#[test]
fn f5c_flat_substitution_unmapped_variable_is_failure_atomic() {
    let mut flat = FlatDraft::default();
    let mapped = flat.positive(PositiveNode::Variable(1)).unwrap();
    let missing = flat.negative(NegativeNode::Variable(90)).unwrap();
    flat.predicate = Some(mapped);
    flat.quantifier_count = 1;
    flat.bound(RecursiveBound {
        ordinal: 2,
        lower: mapped,
        upper: missing,
    })
    .unwrap();
    let snapshot = (
        flat.quantifier_count,
        flat.predicate,
        flat.positive_nodes.clone(),
        flat.negative_nodes.clone(),
        flat.positive_children.clone(),
        flat.negative_children.clone(),
        flat.recursive_bounds.clone(),
        flat.insertion_order.clone(),
    );
    assert_eq!(
        crate::f5c_binder_substitution::substitute_flat(
            &mut flat,
            &HashMap::from([(1, 0)]),
            &HashMap::new(),
            &HashSet::new(),
            &HashSet::new(),
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        (
            flat.quantifier_count,
            flat.predicate,
            flat.positive_nodes,
            flat.negative_nodes,
            flat.positive_children,
            flat.negative_children,
            flat.recursive_bounds,
            flat.insertion_order
        ),
        snapshot
    );
}

#[test]
fn f5c_flat_substitution_visits_bound_only_roots_and_leaves_orphans() {
    let mut flat = FlatDraft::default();
    let orphan = flat.positive(PositiveNode::Variable(90)).unwrap();
    let predicate = flat.positive(PositiveNode::Int).unwrap();
    let lower = flat.positive(PositiveNode::Variable(5)).unwrap();
    let upper = flat.negative(NegativeNode::Variable(6)).unwrap();
    flat.predicate = Some(predicate);
    flat.bound(RecursiveBound {
        ordinal: 0,
        lower,
        upper,
    })
    .unwrap();
    let before_order = flat.insertion_order.clone();
    let q = HashMap::from([(5, 1), (6, 2)]);
    let r = HashMap::new();
    let positive_eliminated = HashSet::from([5]);
    let negative_eliminated = HashSet::from([6]);
    let mut memo = F5cComponentExpansionMemo::default();
    let expected_lower = crate::f5c_binder_substitution::substitute_positive(
        &mut memo,
        F5cPositive::Variable(5),
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();
    let expected_upper = crate::f5c_binder_substitution::substitute_negative(
        &mut memo,
        F5cNegative::Variable(6),
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();
    crate::f5c_binder_substitution::substitute_flat(
        &mut flat,
        &q,
        &r,
        &positive_eliminated,
        &negative_eliminated,
    )
    .unwrap();
    assert_eq!(expected_lower, F5cPositive::Quantified(1));
    assert_eq!(expected_upper, F5cNegative::Quantified(2));
    assert_eq!(
        flat.positive_nodes[orphan.0 as usize],
        PositiveNode::Variable(90)
    );
    assert_eq!(
        flat.positive_nodes[lower.0 as usize],
        PositiveNode::Quantified(1)
    );
    assert_eq!(
        flat.negative_nodes[upper.0 as usize],
        NegativeNode::Quantified(2)
    );
    assert_eq!(flat.predicate, Some(predicate));
    assert_eq!(flat.insertion_order, before_order);
}

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
