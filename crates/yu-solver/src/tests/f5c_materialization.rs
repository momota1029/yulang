use super::*;

enum FlatBoxedStep<'a> {
    Positive(crate::f5c_draft::PositiveId, &'a F5cPositive),
    Negative(crate::f5c_draft::NegativeId, &'a F5cNegative),
}

enum BoxedSummaryStep<'a> {
    Positive(&'a F5cPositive),
    Negative(&'a F5cNegative),
}

fn count_summary_references(root: &F5cWalkValue, target: F5cSummaryNodeId) -> usize {
    let mut pending = match root {
        F5cWalkValue::Positive(value, _) => vec![BoxedSummaryStep::Positive(value)],
        F5cWalkValue::Negative(value, _) => vec![BoxedSummaryStep::Negative(value)],
    };
    let mut count = 0;
    while let Some(step) = pending.pop() {
        match step {
            BoxedSummaryStep::Positive(F5cPositive::Shared(id)) => {
                if *id == target {
                    count += 1;
                }
            }
            BoxedSummaryStep::Positive(F5cPositive::Union(children)) => {
                pending.extend(children.iter().map(BoxedSummaryStep::Positive));
            }
            BoxedSummaryStep::Positive(F5cPositive::Function {
                argument, result, ..
            }) => {
                pending.push(BoxedSummaryStep::Positive(result));
                pending.push(BoxedSummaryStep::Negative(argument));
            }
            BoxedSummaryStep::Negative(F5cNegative::Shared(id)) => {
                if *id == target {
                    count += 1;
                }
            }
            BoxedSummaryStep::Negative(F5cNegative::Intersection(children)) => {
                pending.extend(children.iter().map(BoxedSummaryStep::Negative));
            }
            BoxedSummaryStep::Negative(F5cNegative::Function {
                argument, result, ..
            }) => {
                pending.push(BoxedSummaryStep::Negative(result));
                pending.push(BoxedSummaryStep::Positive(argument));
            }
            BoxedSummaryStep::Positive(_) | BoxedSummaryStep::Negative(_) => {}
        }
    }
    count
}

// Shallow fixtures only: deep boxed values need an iterative consumer or safe destruction.
fn assert_flat_summary_matches_boxed(
    flat: &crate::f5c_draft::FlatDraft,
    root: crate::f5c_draft::NodeRef,
    boxed: &F5cWalkValue,
) {
    use crate::f5c_draft::{NegativeNode, PositiveNode};

    let mut pending = match (root, boxed) {
        (crate::f5c_draft::NodeRef::Positive(id), F5cWalkValue::Positive(value, _)) => {
            vec![FlatBoxedStep::Positive(id, value)]
        }
        (crate::f5c_draft::NodeRef::Negative(id), F5cWalkValue::Negative(value, _)) => {
            vec![FlatBoxedStep::Negative(id, value)]
        }
        _ => panic!("flat and boxed summary roots keep their polarity"),
    };

    while let Some(step) = pending.pop() {
        match step {
            FlatBoxedStep::Positive(id, boxed) => {
                match (flat.positive_nodes[id.0 as usize], boxed) {
                    (PositiveNode::Bottom, F5cPositive::Bottom)
                    | (PositiveNode::Int, F5cPositive::Int) => {}
                    (PositiveNode::Variable(flat), F5cPositive::Variable(boxed)) => {
                        assert_eq!(flat, *boxed)
                    }
                    (PositiveNode::Quantified(flat), F5cPositive::Quantified(boxed))
                    | (PositiveNode::Recursive(flat), F5cPositive::Recursive(boxed)) => {
                        assert_eq!(flat, *boxed)
                    }
                    (PositiveNode::Union(span), F5cPositive::Union(children)) => {
                        let start = span.start as usize;
                        let end = start + span.len as usize;
                        let flat_children = &flat.positive_children[start..end];
                        assert_eq!(flat_children.len(), children.len());
                        pending.extend(
                            flat_children
                                .iter()
                                .copied()
                                .zip(children)
                                .map(|(flat, boxed)| FlatBoxedStep::Positive(flat, boxed)),
                        );
                    }
                    (
                        PositiveNode::Function { argument, result },
                        F5cPositive::Function {
                            argument: boxed_argument,
                            argument_effect,
                            result_effect,
                            result: boxed_result,
                        },
                    ) => {
                        assert_eq!(*argument_effect, F5cNegativeEffect::Empty);
                        assert_eq!(*result_effect, F5cPositiveEffect::Bottom);
                        pending.push(FlatBoxedStep::Positive(result, boxed_result));
                        pending.push(FlatBoxedStep::Negative(argument, boxed_argument));
                    }
                    _ => panic!("flat positive node matches boxed summary"),
                }
            }
            FlatBoxedStep::Negative(id, boxed) => {
                match (flat.negative_nodes[id.0 as usize], boxed) {
                    (NegativeNode::Top, F5cNegative::Top)
                    | (NegativeNode::Bottom, F5cNegative::Bottom)
                    | (NegativeNode::Int, F5cNegative::Int) => {}
                    (NegativeNode::Variable(flat), F5cNegative::Variable(boxed)) => {
                        assert_eq!(flat, *boxed)
                    }
                    (NegativeNode::Quantified(flat), F5cNegative::Quantified(boxed))
                    | (NegativeNode::Recursive(flat), F5cNegative::Recursive(boxed)) => {
                        assert_eq!(flat, *boxed)
                    }
                    (NegativeNode::Intersection(span), F5cNegative::Intersection(children)) => {
                        let start = span.start as usize;
                        let end = start + span.len as usize;
                        let flat_children = &flat.negative_children[start..end];
                        assert_eq!(flat_children.len(), children.len());
                        pending.extend(
                            flat_children
                                .iter()
                                .copied()
                                .zip(children)
                                .map(|(flat, boxed)| FlatBoxedStep::Negative(flat, boxed)),
                        );
                    }
                    (
                        NegativeNode::Function { argument, result },
                        F5cNegative::Function {
                            argument: boxed_argument,
                            argument_effect,
                            result_effect,
                            result: boxed_result,
                        },
                    ) => {
                        assert_eq!(*argument_effect, F5cPositiveEffect::Bottom);
                        assert_eq!(*result_effect, F5cNegativeEffect::Empty);
                        pending.push(FlatBoxedStep::Negative(result, boxed_result));
                        pending.push(FlatBoxedStep::Positive(argument, boxed_argument));
                    }
                    _ => panic!("flat negative node matches boxed summary"),
                }
            }
        }
    }
}

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

#[test]
fn f5c_generalizer_summary_roots_materialize_flat_with_boxed_parity() {
    let batch = collect(module("my f = 1", "f5c-summary-to-flat-producer"));
    let mut session = InferenceSession::new(batch);
    let inner = session.fresh_value_at_level(1).unwrap();
    let outer = session.fresh_value_at_level(1).unwrap();
    session.bounds[inner as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    session.bounds[inner as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::IntNegative);

    let negative_inner = session.live_value_term(Polarity::Negative, inner).unwrap();
    let positive_inner = session.live_value_term(Polarity::Positive, inner).unwrap();
    let empty_effect = session.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
    let bottom_effect = session
        .batch
        .collected_leaf_term(Leaf::EffectBottomPositive);
    let positive_function = session
        .positive_function_term(negative_inner, empty_effect, bottom_effect, positive_inner)
        .unwrap();

    let positive_inner = session.live_value_term(Polarity::Positive, inner).unwrap();
    let negative_inner = session.live_value_term(Polarity::Negative, inner).unwrap();
    let negative_function = session
        .negative_function_term(positive_inner, bottom_effect, empty_effect, negative_inner)
        .unwrap();
    session.bounds[outer as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(positive_function));
    session.bounds[outer as usize]
        .exact_non_variable_uppers
        .push(ValueEndpointKey::NegativeFunction(negative_function));

    let mut generalizer = F5cGeneralizer::new(&session);
    let F5cPositive::Shared(positive_root) = generalizer.positive_row(outer, false).unwrap() else {
        panic!("non-root positive expansion is represented by a summary ID");
    };
    let F5cNegative::Shared(negative_root) = generalizer.negative_row(outer).unwrap() else {
        panic!("negative expansion is represented by a summary ID");
    };
    assert_eq!(
        generalizer.memo.roots.get(&F5cExpansionKey {
            row: outer,
            polarity: Polarity::Positive,
            frozen_bound_epoch: 0,
        }),
        Some(&positive_root)
    );
    assert_eq!(
        generalizer.memo.roots.get(&F5cExpansionKey {
            row: outer,
            polarity: Polarity::Negative,
            frozen_bound_epoch: 0,
        }),
        Some(&negative_root)
    );

    let mut boxed_positive_marks = Vec::new();
    let boxed_positive = generalizer
        .memo
        .positive_value_with(positive_root, &mut |row, polarity| {
            boxed_positive_marks.push((row, polarity));
            Ok(())
        })
        .unwrap();
    let mut flat_positive = crate::f5c_draft::FlatDraft::default();
    let mut positive_marks = Vec::new();
    let flat_positive_root = crate::f5c_materialization::materialize_summary_flat(
        &generalizer.memo,
        &mut flat_positive,
        positive_root,
        Polarity::Positive,
        |row, polarity| positive_marks.push((row, polarity)),
    )
    .unwrap();
    assert_eq!(positive_marks, boxed_positive_marks);
    let boxed_positive = F5cWalkValue::Positive(boxed_positive, true);
    assert_flat_summary_matches_boxed(&flat_positive, flat_positive_root, &boxed_positive);

    let mut boxed_negative_marks = Vec::new();
    let boxed_negative = generalizer
        .memo
        .negative_value_with(negative_root, &mut |row, polarity| {
            boxed_negative_marks.push((row, polarity));
            Ok(())
        })
        .unwrap();
    let mut flat_negative = crate::f5c_draft::FlatDraft::default();
    let mut negative_marks = Vec::new();
    let flat_negative_root = crate::f5c_materialization::materialize_summary_flat(
        &generalizer.memo,
        &mut flat_negative,
        negative_root,
        Polarity::Negative,
        |row, polarity| negative_marks.push((row, polarity)),
    )
    .unwrap();
    assert_eq!(negative_marks, boxed_negative_marks);
    let boxed_negative = F5cWalkValue::Negative(boxed_negative, true);
    assert_flat_summary_matches_boxed(&flat_negative, flat_negative_root, &boxed_negative);
}

#[test]
fn f5c_generalizer_guarded_self_source_roots_materialize_flat_with_boxed_parity() {
    let batch = collect(module("my f = 1", "f5c-guarded-source-roots"));
    let mut session = InferenceSession::new(batch);
    let root = session.batch.definitions[0].root.clone();
    let root_row =
        session.live_components[session.batch.root_component_positions[&root].component].ordinal;
    let nested = session.fresh_value_at_level(1).unwrap();
    session.bounds[nested as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::IntPositive);
    let argument = session.negative_top_term().unwrap();
    let argument_effect = session.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
    let result_effect = session
        .batch
        .collected_leaf_term(Leaf::EffectBottomPositive);
    let nested_result = session.live_value_term(Polarity::Positive, nested).unwrap();
    let nested_function = session
        .positive_function_term(argument, argument_effect, result_effect, nested_result)
        .unwrap();
    session.bounds[root_row as usize]
        .exact_non_variable_lowers
        .push(ValueEndpointKey::PositiveFunction(nested_function));
    let self_result = session
        .live_value_term(Polarity::Positive, root_row)
        .unwrap();
    let self_function = session
        .positive_function_term(argument, argument_effect, result_effect, self_result)
        .unwrap();
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 202);
    let cause = CauseId::for_occurrence(occurrence.clone());
    session
        .constrain_live_value(
            CanonicalValuePairKey {
                lower: ValueEndpointKey::PositiveFunction(self_function),
                upper: ValueEndpointKey::ValueRow(root_row),
            },
            &occurrence,
            &cause,
        )
        .unwrap();

    let mut generalizer = F5cGeneralizer::new(&session);
    let predicate = generalizer.positive_row(root_row, true).unwrap();
    let mut bounds = HashMap::new();
    let mut owners = Vec::new();
    let mut completed = HashSet::new();
    let mut next_owner = 0;
    while next_owner < generalizer.reentries.len() {
        let owner = generalizer.reentries[next_owner].owner;
        next_owner += 1;
        if !completed.insert(owner) {
            continue;
        }
        owners.push(owner);
        let source = generalizer
            .session
            .bounds
            .get(owner as usize)
            .cloned()
            .unwrap();
        let expanded_lower = generalizer.positive_row(owner, false).unwrap();
        let expanded_upper = generalizer.negative_row(owner).unwrap();
        let lower =
            if source.exact_non_variable_lowers.is_empty() && source.direct_lower_rows.is_empty() {
                F5cPositive::Bottom
            } else {
                expanded_lower
            };
        let upper =
            if source.exact_non_variable_uppers.is_empty() && source.direct_upper_rows.is_empty() {
                F5cNegative::Top
            } else {
                expanded_upper
            };
        bounds.insert(owner, (lower, upper));
    }
    assert_eq!(owners, vec![root_row]);
    assert!(!generalizer.invalid_effects);
    let nested_summary = *generalizer
        .memo
        .roots
        .get(&F5cExpansionKey {
            row: nested,
            polarity: Polarity::Positive,
            frozen_bound_epoch: 0,
        })
        .expect("nested positive row is admitted as a shared summary");

    let mut roots = vec![F5cWalkValue::Positive(predicate.clone(), true)];
    for owner in &owners {
        let (lower, upper) = &bounds[owner];
        assert!(matches!(upper, F5cNegative::Top));
        roots.push(F5cWalkValue::Positive(lower.clone(), true));
        roots.push(F5cWalkValue::Negative(upper.clone(), true));
    }
    assert_eq!(count_summary_references(&roots[0], nested_summary), 1);
    assert_eq!(count_summary_references(&roots[1], nested_summary), 1);
    let boxed_predicate = generalizer.materialize_positive(predicate).unwrap();
    generalizer
        .materialize_recursive_bounds(&mut bounds)
        .unwrap();
    let mut boxed_roots = vec![F5cWalkValue::Positive(boxed_predicate, true)];
    for owner in &owners {
        let (lower, upper) = bounds.remove(owner).unwrap();
        boxed_roots.push(F5cWalkValue::Positive(lower, true));
        boxed_roots.push(F5cWalkValue::Negative(upper, true));
    }

    let mut flat = crate::f5c_draft::FlatDraft::default();
    let mut flat_roots = Vec::with_capacity(roots.len());
    for (root_index, (raw, boxed)) in roots.iter().zip(&boxed_roots).enumerate() {
        let (id, polarity) = match raw {
            F5cWalkValue::Positive(value, _) => (
                generalizer.memo.positive_node(value, None).unwrap(),
                Polarity::Positive,
            ),
            F5cWalkValue::Negative(value, _) => (
                generalizer.memo.negative_node(value, None).unwrap(),
                Polarity::Negative,
            ),
        };
        let mut boxed_marks = Vec::new();
        let summary_boxed = match polarity {
            Polarity::Positive => F5cWalkValue::Positive(
                generalizer
                    .memo
                    .positive_value_with(id, &mut |row, side| {
                        boxed_marks.push((row, side));
                        Ok(())
                    })
                    .unwrap(),
                true,
            ),
            Polarity::Negative => F5cWalkValue::Negative(
                generalizer
                    .memo
                    .negative_value_with(id, &mut |row, side| {
                        boxed_marks.push((row, side));
                        Ok(())
                    })
                    .unwrap(),
                true,
            ),
        };
        if root_index < 2 {
            assert_eq!(
                boxed_marks
                    .iter()
                    .filter(|mark| **mark == (nested, Polarity::Positive))
                    .count(),
                1
            );
        }
        let mut flat_marks = Vec::new();
        let flat_root = crate::f5c_materialization::materialize_summary_flat(
            &generalizer.memo,
            &mut flat,
            id,
            polarity,
            |row, side| flat_marks.push((row, side)),
        )
        .unwrap();
        assert_eq!(flat_marks, boxed_marks);
        assert_flat_summary_matches_boxed(&flat, flat_root, &summary_boxed);
        assert_flat_summary_matches_boxed(&flat, flat_root, boxed);
        flat_roots.push(flat_root);
    }
    let Some(crate::f5c_draft::NodeRef::Positive(predicate)) = flat_roots.first().copied() else {
        panic!("flat source draft retains its positive predicate root");
    };
    flat.predicate = Some(predicate);
    let bound_roots = &flat_roots[1..];
    assert_eq!(bound_roots.len(), owners.len() * 2);
    for (&owner, roots) in owners.iter().zip(bound_roots.chunks_exact(2)) {
        let crate::f5c_draft::NodeRef::Positive(lower) = roots[0] else {
            panic!("flat recursive bound keeps a positive lower root");
        };
        let crate::f5c_draft::NodeRef::Negative(upper) = roots[1] else {
            panic!("flat recursive bound keeps a negative upper root");
        };
        flat.bound(crate::f5c_draft::RecursiveBound {
            ordinal: owner,
            lower,
            upper,
        })
        .unwrap();
    }
    assert_eq!(
        flat.recursive_bounds
            .iter()
            .map(|bound| bound.ordinal)
            .collect::<Vec<_>>(),
        owners
    );
}
