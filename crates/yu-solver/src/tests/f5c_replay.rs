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
fn f5c_flat_replay_matches_boxed_polarity_and_occurrence_order() {
    use crate::f5c_draft::{
        ChildSpan, FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveId, PositiveNode,
    };

    let mut source = FlatDraft::default();
    let n0 = source.negative(NegativeNode::Variable(2)).unwrap();
    let n1 = source.negative(NegativeNode::Variable(3)).unwrap();
    let p0 = source.positive(PositiveNode::Variable(1)).unwrap();
    let p1 = source.positive(PositiveNode::Variable(3)).unwrap();
    let n2 = source.negative(NegativeNode::Top).unwrap();
    let intersection = source
        .negative_span(&[n0, n1])
        .and_then(|span| source.negative(NegativeNode::Intersection(span)))
        .unwrap();
    let p2 = source
        .positive(PositiveNode::Function {
            argument: n2,
            result: p1,
        })
        .unwrap();
    let p3 = source
        .positive_span(&[p0, p2])
        .and_then(|span| source.positive(PositiveNode::Union(span)))
        .unwrap();
    let p4 = source
        .positive(PositiveNode::Function {
            argument: intersection,
            result: p3,
        })
        .unwrap();
    let p5 = source
        .positive_span(&[p0, p1])
        .and_then(|span| source.positive(PositiveNode::Union(span)))
        .unwrap();
    let n4 = source
        .negative(NegativeNode::Function {
            argument: p5,
            result: n0,
        })
        .unwrap();
    let n5 = source
        .negative_span(&[n1, n4])
        .and_then(|span| source.negative(NegativeNode::Intersection(span)))
        .unwrap();

    let protected = HashSet::from([3]);
    let positive_only = HashSet::from([1, 2, 3]);
    let negative_only = HashSet::from([2, 3]);
    let boxed_positive = F5cPositive::Function {
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
    let boxed_negative = F5cNegative::Intersection(vec![
        F5cNegative::Variable(3),
        F5cNegative::Function {
            argument: Box::new(F5cPositive::Union(vec![
                F5cPositive::Variable(1),
                F5cPositive::Variable(3),
            ])),
            argument_effect: F5cPositiveEffect::Bottom,
            result_effect: F5cNegativeEffect::Empty,
            result: Box::new(F5cNegative::Variable(2)),
        },
    ]);
    let mut boxed_memo = F5cComponentExpansionMemo::default();
    let expected_positive = crate::f5c_replay::replay_positive(
        &mut boxed_memo,
        &boxed_positive,
        &protected,
        &positive_only,
        &negative_only,
    )
    .unwrap();
    let expected_negative = crate::f5c_replay::replay_negative(
        &mut boxed_memo,
        &boxed_negative,
        &protected,
        &positive_only,
        &negative_only,
    )
    .unwrap();

    fn expand_positive(
        flat: &crate::f5c_draft::FlatDraft,
        id: crate::f5c_draft::PositiveId,
    ) -> F5cPositive {
        use crate::f5c_draft::PositiveNode;
        match flat.positive_nodes[id.0 as usize] {
            PositiveNode::Bottom => F5cPositive::Bottom,
            PositiveNode::Int => F5cPositive::Int,
            PositiveNode::Variable(owner) => F5cPositive::Variable(owner),
            PositiveNode::Union(span) => {
                let start = span.start as usize;
                let end = start + span.len as usize;
                F5cPositive::Union(
                    flat.positive_children[start..end]
                        .iter()
                        .copied()
                        .map(|child| expand_positive(flat, child))
                        .collect(),
                )
            }
            PositiveNode::Function { argument, result } => F5cPositive::Function {
                argument: Box::new(expand_negative(flat, argument)),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(expand_positive(flat, result)),
            },
            _ => panic!("fixture uses only replay-supported positive nodes"),
        }
    }
    fn expand_negative(
        flat: &crate::f5c_draft::FlatDraft,
        id: crate::f5c_draft::NegativeId,
    ) -> F5cNegative {
        use crate::f5c_draft::NegativeNode;
        match flat.negative_nodes[id.0 as usize] {
            NegativeNode::Top => F5cNegative::Top,
            NegativeNode::Bottom => F5cNegative::Bottom,
            NegativeNode::Int => F5cNegative::Int,
            NegativeNode::Variable(owner) => F5cNegative::Variable(owner),
            NegativeNode::Intersection(span) => {
                let start = span.start as usize;
                let end = start + span.len as usize;
                F5cNegative::Intersection(
                    flat.negative_children[start..end]
                        .iter()
                        .copied()
                        .map(|child| expand_negative(flat, child))
                        .collect(),
                )
            }
            NegativeNode::Function { argument, result } => F5cNegative::Function {
                argument: Box::new(expand_positive(flat, argument)),
                argument_effect: F5cPositiveEffect::Bottom,
                result_effect: F5cNegativeEffect::Empty,
                result: Box::new(expand_negative(flat, result)),
            },
            _ => panic!("fixture uses only replay-supported negative nodes"),
        }
    }

    let mut memo = F5cComponentExpansionMemo::default();
    let mut output = FlatDraft::default();
    assert_eq!(
        crate::f5c_replay::replay_flat(
            &mut memo,
            &source,
            NodeRef::Positive(p4),
            &mut output,
            &protected,
            &positive_only,
            &negative_only,
        )
        .unwrap(),
        NodeRef::Positive(PositiveId(4))
    );
    assert_eq!(expand_positive(&output, PositiveId(4)), expected_positive);
    assert_eq!(
        output.positive_nodes,
        vec![
            PositiveNode::Bottom,
            PositiveNode::Variable(3),
            PositiveNode::Function {
                argument: NegativeId(3),
                result: PositiveId(1),
            },
            PositiveNode::Union(ChildSpan { start: 0, len: 2 }),
            PositiveNode::Function {
                argument: NegativeId(2),
                result: PositiveId(3),
            },
        ]
    );
    assert_eq!(
        output.negative_nodes,
        vec![
            NegativeNode::Top,
            NegativeNode::Variable(3),
            NegativeNode::Intersection(ChildSpan { start: 0, len: 2 }),
            NegativeNode::Top,
        ]
    );
    assert_eq!(output.positive_children, vec![PositiveId(0), PositiveId(2)]);
    assert_eq!(output.negative_children, vec![NegativeId(0), NegativeId(1)]);

    assert_eq!(
        crate::f5c_replay::replay_flat(
            &mut memo,
            &source,
            NodeRef::Negative(n5),
            &mut output,
            &protected,
            &positive_only,
            &negative_only,
        )
        .unwrap(),
        NodeRef::Negative(NegativeId(7))
    );
    assert_eq!(expand_negative(&output, NegativeId(7)), expected_negative);
    assert_eq!(
        &output.positive_nodes[5..],
        &[
            PositiveNode::Bottom,
            PositiveNode::Variable(3),
            PositiveNode::Union(ChildSpan { start: 2, len: 2 }),
        ]
    );
    assert_eq!(
        &output.negative_nodes[4..],
        &[
            NegativeNode::Variable(3),
            NegativeNode::Top,
            NegativeNode::Function {
                argument: PositiveId(7),
                result: NegativeId(5),
            },
            NegativeNode::Intersection(ChildSpan { start: 2, len: 2 }),
        ]
    );
    assert_eq!(
        &output.positive_children[2..],
        &[PositiveId(5), PositiveId(6)]
    );
    assert_eq!(
        &output.negative_children[2..],
        &[NegativeId(4), NegativeId(6)]
    );
    crate::f5c_replay::release_flat_output(&mut memo, output);
}

#[test]
fn f5c_flat_replay_preserves_repeated_edge_occurrences() {
    use crate::f5c_draft::{ChildSpan, FlatDraft, NodeRef, PositiveId, PositiveNode};

    let mut source = FlatDraft::default();
    let shared = source.positive(PositiveNode::Int).unwrap();
    let root = source
        .positive_span(&[shared, shared])
        .and_then(|span| source.positive(PositiveNode::Union(span)))
        .unwrap();
    let boxed = F5cPositive::Union(vec![F5cPositive::Int, F5cPositive::Int]);
    let mut boxed_memo = F5cComponentExpansionMemo::default();
    let expected = crate::f5c_replay::replay_positive(
        &mut boxed_memo,
        &boxed,
        &HashSet::new(),
        &HashSet::new(),
        &HashSet::new(),
    )
    .unwrap();

    let mut memo = F5cComponentExpansionMemo::default();
    let mut output = FlatDraft::default();
    let replayed = crate::f5c_replay::replay_flat(
        &mut memo,
        &source,
        NodeRef::Positive(root),
        &mut output,
        &HashSet::new(),
        &HashSet::new(),
        &HashSet::new(),
    )
    .unwrap();
    assert_eq!(replayed, NodeRef::Positive(PositiveId(2)));
    assert_eq!(
        output.positive_nodes,
        vec![
            PositiveNode::Int,
            PositiveNode::Int,
            PositiveNode::Union(ChildSpan { start: 0, len: 2 }),
        ]
    );
    assert_eq!(output.positive_children, vec![PositiveId(0), PositiveId(1)]);
    let expanded = F5cPositive::Union(vec![F5cPositive::Int, F5cPositive::Int]);
    assert_eq!(expanded, expected);
    crate::f5c_replay::release_flat_output(&mut memo, output);
}

#[test]
fn f5c_flat_replay_restores_output_after_a_late_cycle() {
    use crate::f5c_draft::{
        FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveNode, RecursiveBound,
    };

    let mut source = FlatDraft::default();
    let p0 = source.positive(PositiveNode::Int).unwrap();
    let first_union = source
        .positive_span(&[p0, p0])
        .and_then(|span| source.positive(PositiveNode::Union(span)))
        .unwrap();
    let n0 = source.negative(NegativeNode::Top).unwrap();
    let p2 = source
        .positive(PositiveNode::Function {
            argument: NegativeId(1),
            result: p0,
        })
        .unwrap();
    source
        .negative(NegativeNode::Function {
            argument: p2,
            result: n0,
        })
        .unwrap();
    let root = source
        .positive_span(&[first_union, p2])
        .and_then(|span| source.positive(PositiveNode::Union(span)))
        .unwrap();

    let mut output = FlatDraft::default();
    output.quantifier_count = 4;
    let base_positive = output.positive(PositiveNode::Int).unwrap();
    let base_negative = output.negative(NegativeNode::Bottom).unwrap();
    output.positive_span(&[base_positive]).unwrap();
    output.negative_span(&[base_negative]).unwrap();
    output.predicate = Some(base_positive);
    output
        .bound(RecursiveBound {
            ordinal: 1,
            lower: base_positive,
            upper: base_negative,
        })
        .unwrap();
    let before = (
        output.quantifier_count,
        output.predicate,
        output.positive_nodes.clone(),
        output.negative_nodes.clone(),
        output.positive_children.clone(),
        output.negative_children.clone(),
        output.recursive_bounds.clone(),
        output.insertion_order.clone(),
    );

    let mut memo = F5cComponentExpansionMemo::default();
    let result = crate::f5c_replay::replay_flat(
        &mut memo,
        &source,
        NodeRef::Positive(root),
        &mut output,
        &HashSet::new(),
        &HashSet::new(),
        &HashSet::new(),
    );
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(
        (
            output.quantifier_count,
            output.predicate,
            output.positive_nodes.clone(),
            output.negative_nodes.clone(),
            output.positive_children.clone(),
            output.negative_children.clone(),
            output.recursive_bounds.clone(),
            output.insertion_order.clone(),
        ),
        before
    );
    crate::f5c_replay::release_flat_output(&mut memo, output);
}

#[test]
fn f5c_flat_replay_handles_deep_drafts_on_a_small_stack() {
    use crate::f5c_draft::{FlatDraft, NegativeNode, NodeRef, PositiveNode};

    const DEPTH: usize = 4096;
    let mut source = FlatDraft::default();
    let argument = source.negative(NegativeNode::Variable(9)).unwrap();
    let mut root = source.positive(PositiveNode::Variable(7)).unwrap();
    for _ in 0..DEPTH {
        root = source
            .positive(PositiveNode::Function {
                argument,
                result: root,
            })
            .unwrap();
    }
    let worker = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            let mut memo = F5cComponentExpansionMemo::default();
            let mut output = FlatDraft::default();
            let replayed = crate::f5c_replay::replay_flat(
                &mut memo,
                &source,
                NodeRef::Positive(root),
                &mut output,
                &HashSet::new(),
                &HashSet::from([7]),
                &HashSet::from([9]),
            )
            .unwrap();
            let NodeRef::Positive(mut current) = replayed else {
                panic!("positive root keeps its polarity");
            };
            let mut functions = 0;
            loop {
                match output.positive_nodes[current.0 as usize] {
                    PositiveNode::Function { argument, result } => {
                        assert_eq!(
                            output.negative_nodes[argument.0 as usize],
                            NegativeNode::Top
                        );
                        functions += 1;
                        current = result;
                    }
                    PositiveNode::Bottom => break,
                    _ => panic!("the eliminated positive leaf becomes bottom"),
                }
            }
            assert_eq!(functions, DEPTH);
            assert_eq!(output.negative_nodes.len(), DEPTH);
            for (lane, minimum) in [
                (F5cWalkerLaneKind::ReplayTasks, DEPTH),
                (F5cWalkerLaneKind::ReplayValues, DEPTH),
            ] {
                assert!(memo.walker_resources.lanes[lane as usize].requested_slots >= minimum);
                assert_eq!(
                    memo.walker_resources.lanes[lane as usize].actual_capacity,
                    0
                );
            }
            crate::f5c_replay::release_flat_output(&mut memo, output);
        })
        .unwrap();
    worker.join().unwrap();
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
