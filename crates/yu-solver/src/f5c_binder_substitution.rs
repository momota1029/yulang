use super::f5c_draft::{FlatDraft, NegativeNode, NodeRef, PositiveNode};
#[cfg(test)]
use super::f5c_generalization::{F5cBulkDrainSite, record_bulk_drain_boundary};
use super::{
    F5cComponentExpansionMemo, F5cNegative, F5cNegativeEffect, F5cPositive, F5cPositiveEffect,
    F5cWalkValue, F5cWalkerLaneKind, SolveAvailabilityError,
};
use std::collections::{HashMap, HashSet};

pub(super) enum Task {
    Positive(F5cPositive),
    Negative(F5cNegative),
    FinishPositiveUnion(usize),
    FinishNegativeIntersection(usize),
    FinishPositiveFunction,
    FinishNegativeFunction,
}

/// Substitutes producer-graph nodes reachable from the scheme roots; scratch nodes remain untouched.
/// `normalize_flat` owns insertion-order and topology validation. Isolate root-unreachable
/// Variable scratch before normalization, which scans all inserted nodes and rejects Variables.
#[allow(dead_code)]
pub(super) fn substitute_flat(
    draft: &mut FlatDraft,
    q: &HashMap<u32, u32>,
    r: &HashMap<u32, u32>,
    positive_eliminated: &HashSet<u32>,
    negative_eliminated: &HashSet<u32>,
) -> Result<(), SolveAvailabilityError> {
    let exhausted = SolveAvailabilityError::IdentityExhausted;
    let mut positive_seen = Vec::new();
    positive_seen
        .try_reserve(draft.positive_nodes.len())
        .map_err(|_| exhausted)?;
    positive_seen.resize(draft.positive_nodes.len(), false);
    let mut negative_seen = Vec::new();
    negative_seen
        .try_reserve(draft.negative_nodes.len())
        .map_err(|_| exhausted)?;
    negative_seen.resize(draft.negative_nodes.len(), false);
    let mut stack = Vec::new();
    macro_rules! enqueue {
        ($node:expr) => {{
            let node = $node;
            let seen = match node {
                NodeRef::Positive(id) => {
                    positive_seen.get_mut(usize::try_from(id.0).map_err(|_| exhausted)?)
                }
                NodeRef::Negative(id) => {
                    negative_seen.get_mut(usize::try_from(id.0).map_err(|_| exhausted)?)
                }
            }
            .ok_or(exhausted)?;
            if !*seen {
                stack.try_reserve(1).map_err(|_| exhausted)?;
                stack.push(node);
                *seen = true;
            }
        }};
    }
    // Preflight all reachable edges and variables before touching the draft.
    let predicate = draft.predicate.ok_or(exhausted)?;
    for bound in draft.recursive_bounds.iter().rev() {
        enqueue!(NodeRef::Negative(bound.upper));
        enqueue!(NodeRef::Positive(bound.lower));
    }
    enqueue!(NodeRef::Positive(predicate));
    while let Some(node) = stack.pop() {
        match node {
            NodeRef::Positive(id) => {
                let index = usize::try_from(id.0).map_err(|_| exhausted)?;
                let value = *draft.positive_nodes.get(index).ok_or(exhausted)?;
                match value {
                    PositiveNode::Variable(ordinal)
                        if !r.contains_key(&ordinal)
                            && !q.contains_key(&ordinal)
                            && !positive_eliminated.contains(&ordinal) =>
                    {
                        return Err(exhausted);
                    }
                    PositiveNode::Union(span) => {
                        let start = usize::try_from(span.start).map_err(|_| exhausted)?;
                        let end = span.start.checked_add(span.len).ok_or(exhausted)?;
                        let end = usize::try_from(end).map_err(|_| exhausted)?;
                        let children = draft.positive_children.get(start..end).ok_or(exhausted)?;
                        for &child in children.iter().rev() {
                            enqueue!(NodeRef::Positive(child));
                        }
                    }
                    PositiveNode::Function { argument, result } => {
                        enqueue!(NodeRef::Positive(result));
                        enqueue!(NodeRef::Negative(argument));
                    }
                    _ => {}
                }
            }
            NodeRef::Negative(id) => {
                let index = usize::try_from(id.0).map_err(|_| exhausted)?;
                let value = *draft.negative_nodes.get(index).ok_or(exhausted)?;
                match value {
                    NegativeNode::Variable(ordinal)
                        if !r.contains_key(&ordinal)
                            && !q.contains_key(&ordinal)
                            && !negative_eliminated.contains(&ordinal) =>
                    {
                        return Err(exhausted);
                    }
                    NegativeNode::Intersection(span) => {
                        let start = usize::try_from(span.start).map_err(|_| exhausted)?;
                        let end = span.start.checked_add(span.len).ok_or(exhausted)?;
                        let end = usize::try_from(end).map_err(|_| exhausted)?;
                        let children = draft.negative_children.get(start..end).ok_or(exhausted)?;
                        for &child in children.iter().rev() {
                            enqueue!(NodeRef::Negative(child));
                        }
                    }
                    NegativeNode::Function { argument, result } => {
                        enqueue!(NodeRef::Negative(result));
                        enqueue!(NodeRef::Positive(argument));
                    }
                    _ => {}
                }
            }
        }
    }

    for (node, seen) in draft.positive_nodes.iter_mut().zip(positive_seen) {
        if let (true, PositiveNode::Variable(ordinal)) = (seen, *node) {
            *node = if let Some(&mapped) = r.get(&ordinal) {
                PositiveNode::Recursive(mapped)
            } else if let Some(&mapped) = q.get(&ordinal) {
                PositiveNode::Quantified(mapped)
            } else {
                PositiveNode::Bottom
            };
        }
    }
    for (node, seen) in draft.negative_nodes.iter_mut().zip(negative_seen) {
        if let (true, NegativeNode::Variable(ordinal)) = (seen, *node) {
            *node = if let Some(&mapped) = r.get(&ordinal) {
                NegativeNode::Recursive(mapped)
            } else if let Some(&mapped) = q.get(&ordinal) {
                NegativeNode::Quantified(mapped)
            } else {
                NegativeNode::Top
            };
        }
    }
    Ok(())
}

pub(super) fn substitute_positive(
    memo: &mut F5cComponentExpansionMemo,
    value: F5cPositive,
    q: &HashMap<u32, u32>,
    r: &HashMap<u32, u32>,
    positive_eliminated: &HashSet<u32>,
    negative_eliminated: &HashSet<u32>,
) -> Result<F5cPositive, SolveAvailabilityError> {
    match substitute(
        memo,
        Task::Positive(value),
        q,
        r,
        positive_eliminated,
        negative_eliminated,
    )? {
        F5cWalkValue::Positive(value, _) => Ok(value),
        F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
    }
}

pub(super) fn substitute_negative(
    memo: &mut F5cComponentExpansionMemo,
    value: F5cNegative,
    q: &HashMap<u32, u32>,
    r: &HashMap<u32, u32>,
    positive_eliminated: &HashSet<u32>,
    negative_eliminated: &HashSet<u32>,
) -> Result<F5cNegative, SolveAvailabilityError> {
    match substitute(
        memo,
        Task::Negative(value),
        q,
        r,
        positive_eliminated,
        negative_eliminated,
    )? {
        F5cWalkValue::Negative(value, _) => Ok(value),
        F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
    }
}

fn substitute(
    memo: &mut F5cComponentExpansionMemo,
    first: Task,
    q: &HashMap<u32, u32>,
    r: &HashMap<u32, u32>,
    positive_eliminated: &HashSet<u32>,
    negative_eliminated: &HashSet<u32>,
) -> Result<F5cWalkValue, SolveAvailabilityError> {
    let mut tasks = Vec::new();
    let mut values = Vec::new();
    macro_rules! push_task {
        ($task:expr) => {{
            memo.work_meter.charge(1)?;
            memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::BinderTasks)?;
            tasks.push($task);
        }};
    }
    macro_rules! push_value {
        ($value:expr) => {{
            memo.work_meter.charge(1)?;
            memo.reserve_walker(&mut values, F5cWalkerLaneKind::BinderValues)?;
            values.push($value);
        }};
    }

    let result = (|| {
        push_task!(first);
        while !tasks.is_empty() {
            memo.work_meter.charge(1)?;
            let task = tasks
                .pop()
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            match task {
                Task::Positive(value) => match value {
                    F5cPositive::Variable(ordinal) => {
                        let replacement = r
                            .get(&ordinal)
                            .copied()
                            .map(F5cPositive::Recursive)
                            .or_else(|| q.get(&ordinal).copied().map(F5cPositive::Quantified))
                            .or_else(|| {
                                positive_eliminated
                                    .contains(&ordinal)
                                    .then_some(F5cPositive::Bottom)
                            })
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        push_value!(F5cWalkValue::Positive(replacement, true));
                    }
                    F5cPositive::Function {
                        argument, result, ..
                    } => {
                        push_task!(Task::FinishPositiveFunction);
                        memo.work_meter.charge(1)?; // result child edge
                        push_task!(Task::Positive(*result));
                        memo.work_meter.charge(1)?; // argument child edge
                        push_task!(Task::Negative(*argument));
                    }
                    F5cPositive::Union(children) => {
                        let start = values.len();
                        push_task!(Task::FinishPositiveUnion(start));
                        memo.work_meter.charge(children.len())?;
                        for child in children.into_iter().rev() {
                            push_task!(Task::Positive(child));
                        }
                    }
                    other => push_value!(F5cWalkValue::Positive(other, true)),
                },
                Task::Negative(value) => match value {
                    F5cNegative::Variable(ordinal) => {
                        let replacement = r
                            .get(&ordinal)
                            .copied()
                            .map(F5cNegative::Recursive)
                            .or_else(|| q.get(&ordinal).copied().map(F5cNegative::Quantified))
                            .or_else(|| {
                                negative_eliminated
                                    .contains(&ordinal)
                                    .then_some(F5cNegative::Top)
                            })
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        push_value!(F5cWalkValue::Negative(replacement, true));
                    }
                    F5cNegative::Function {
                        argument, result, ..
                    } => {
                        push_task!(Task::FinishNegativeFunction);
                        memo.work_meter.charge(1)?; // result child edge
                        push_task!(Task::Negative(*result));
                        memo.work_meter.charge(1)?; // argument child edge
                        push_task!(Task::Positive(*argument));
                    }
                    F5cNegative::Intersection(children) => {
                        let start = values.len();
                        push_task!(Task::FinishNegativeIntersection(start));
                        memo.work_meter.charge(children.len())?;
                        for child in children.into_iter().rev() {
                            push_task!(Task::Negative(child));
                        }
                    }
                    other => push_value!(F5cWalkValue::Negative(other, true)),
                },
                Task::FinishPositiveUnion(start) => {
                    // Scheduled positive children each leave one value in this suffix;
                    // precharge before draining boxed values.
                    let count = values
                        .len()
                        .checked_sub(start)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(test)]
                    record_bulk_drain_boundary(
                        F5cBulkDrainSite::SubstitutePositive,
                        &memo.work_meter,
                        count,
                    );
                    let mut children = Vec::new();
                    memo.work_meter.charge(count)?;
                    for value in values.drain(start..) {
                        let F5cWalkValue::Positive(value, _) = value else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        children.push(value);
                    }
                    push_value!(F5cWalkValue::Positive(F5cPositive::Union(children), true));
                }
                Task::FinishNegativeIntersection(start) => {
                    // Scheduled negative children each leave one value in this suffix;
                    // precharge before draining boxed values.
                    let count = values
                        .len()
                        .checked_sub(start)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(test)]
                    record_bulk_drain_boundary(
                        F5cBulkDrainSite::SubstituteNegative,
                        &memo.work_meter,
                        count,
                    );
                    let mut children = Vec::new();
                    memo.work_meter.charge(count)?;
                    for value in values.drain(start..) {
                        let F5cWalkValue::Negative(value, _) = value else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        children.push(value);
                    }
                    push_value!(F5cWalkValue::Negative(
                        F5cNegative::Intersection(children),
                        true,
                    ));
                }
                Task::FinishPositiveFunction => {
                    memo.work_meter.charge(2)?;
                    let F5cWalkValue::Positive(result, _) = values
                        .pop()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let F5cWalkValue::Negative(argument, _) = values
                        .pop()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    push_value!(F5cWalkValue::Positive(
                        F5cPositive::Function {
                            argument: Box::new(argument),
                            argument_effect: F5cNegativeEffect::Empty,
                            result_effect: F5cPositiveEffect::Bottom,
                            result: Box::new(result),
                        },
                        true,
                    ));
                }
                Task::FinishNegativeFunction => {
                    memo.work_meter.charge(2)?;
                    let F5cWalkValue::Negative(result, _) = values
                        .pop()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let F5cWalkValue::Positive(argument, _) = values
                        .pop()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    push_value!(F5cWalkValue::Negative(
                        F5cNegative::Function {
                            argument: Box::new(argument),
                            argument_effect: F5cPositiveEffect::Bottom,
                            result_effect: F5cNegativeEffect::Empty,
                            result: Box::new(result),
                        },
                        true,
                    ));
                }
            }
        }
        if values.len() != 1 {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        values
            .pop()
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    })();
    memo.walker_resources
        .release(F5cWalkerLaneKind::BinderTasks);
    memo.walker_resources
        .release(F5cWalkerLaneKind::BinderValues);
    result
}
