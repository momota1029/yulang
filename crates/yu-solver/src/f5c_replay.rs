use super::f5c_draft::{
    ChildSpan, FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveId, PositiveNode,
};
use super::{
    F5cComponentExpansionMemo, F5cNegative, F5cNegativeEffect, F5cPositive, F5cPositiveEffect,
    F5cWalkValue, F5cWalkerLaneKind, SolveAvailabilityError,
};
use std::collections::HashSet;

pub(super) enum Task<'tree> {
    Positive(&'tree F5cPositive),
    Negative(&'tree F5cNegative),
    FinishPositiveUnion(usize),
    FinishNegativeIntersection(usize),
    FinishPositiveFunction,
    FinishNegativeFunction,
}

#[derive(Clone, Copy)]
enum FlatTask {
    Positive(PositiveId),
    Negative(NegativeId),
    LeavePositive(usize),
    LeaveNegative(usize),
    FinishPositiveUnion(usize),
    FinishNegativeIntersection(usize),
    FinishPositiveFunction,
    FinishNegativeFunction,
}

fn flat_children<T: Copy>(children: &[T], span: ChildSpan) -> Result<&[T], SolveAvailabilityError> {
    let start =
        usize::try_from(span.start).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    let end = span
        .start
        .checked_add(span.len)
        .and_then(|end| usize::try_from(end).ok())
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    children
        .get(start..end)
        .ok_or(SolveAvailabilityError::IdentityExhausted)
}

/// Fixture-only, occurrence-preserving replay over a flat source draft.
/// The source stays immutable because generalization replays it under multiple
/// candidate masks; each call appends an independently expanded root.
#[allow(dead_code)]
pub(super) fn replay_flat(
    memo: &mut F5cComponentExpansionMemo,
    source: &FlatDraft,
    root: NodeRef,
    output: &mut FlatDraft,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<NodeRef, SolveAvailabilityError> {
    let checkpoint = (
        output.positive_nodes.len(),
        output.negative_nodes.len(),
        output.positive_children.len(),
        output.negative_children.len(),
        output.insertion_order.len(),
    );
    let result = (|| {
        let exhausted = SolveAvailabilityError::IdentityExhausted;
        let mut active_positive = Vec::new();
        active_positive
            .try_reserve_exact(source.positive_nodes.len())
            .map_err(|_| exhausted)?;
        active_positive.resize(source.positive_nodes.len(), false);
        let mut active_negative = Vec::new();
        active_negative
            .try_reserve_exact(source.negative_nodes.len())
            .map_err(|_| exhausted)?;
        active_negative.resize(source.negative_nodes.len(), false);

        let mut tasks = Vec::new();
        let mut values = Vec::new();
        macro_rules! push_task {
            ($task:expr) => {{
                memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::ReplayTasks)?;
                tasks.push($task);
            }};
        }
        macro_rules! push_value {
            ($value:expr) => {{
                memo.reserve_walker(&mut values, F5cWalkerLaneKind::ReplayValues)?;
                values.push($value);
            }};
        }
        macro_rules! push_positive {
            ($node:expr) => {{
                push_value!(NodeRef::Positive(output.positive($node)?));
            }};
        }
        macro_rules! push_negative {
            ($node:expr) => {{
                push_value!(NodeRef::Negative(output.negative($node)?));
            }};
        }

        let replayed = (|| {
            match root {
                NodeRef::Positive(id) => push_task!(FlatTask::Positive(id)),
                NodeRef::Negative(id) => push_task!(FlatTask::Negative(id)),
            }
            while let Some(task) = tasks.pop() {
                match task {
                    FlatTask::Positive(id) => {
                        let index = usize::try_from(id.0).map_err(|_| exhausted)?;
                        match *source.positive_nodes.get(index).ok_or(exhausted)? {
                            PositiveNode::Bottom => push_positive!(PositiveNode::Bottom),
                            PositiveNode::Int => push_positive!(PositiveNode::Int),
                            PositiveNode::Variable(owner)
                                if !protected.contains(&owner)
                                    && positive_only.contains(&owner) =>
                            {
                                push_positive!(PositiveNode::Bottom);
                            }
                            PositiveNode::Variable(owner) => {
                                push_positive!(PositiveNode::Variable(owner));
                            }
                            PositiveNode::Quantified(owner) => {
                                push_positive!(PositiveNode::Quantified(owner));
                            }
                            PositiveNode::Recursive(owner) => {
                                push_positive!(PositiveNode::Recursive(owner));
                            }
                            PositiveNode::Union(span) => {
                                let children = flat_children(&source.positive_children, span)?;
                                if children.iter().any(|child| child.0 >= id.0) {
                                    return Err(exhausted);
                                }
                                if *active_positive.get(index).ok_or(exhausted)? {
                                    return Err(exhausted);
                                }
                                active_positive[index] = true;
                                let start = values.len();
                                push_task!(FlatTask::LeavePositive(index));
                                push_task!(FlatTask::FinishPositiveUnion(start));
                                for &child in children.iter().rev() {
                                    push_task!(FlatTask::Positive(child));
                                }
                            }
                            PositiveNode::Function { argument, result } => {
                                let argument_index =
                                    usize::try_from(argument.0).map_err(|_| exhausted)?;
                                let result_index =
                                    usize::try_from(result.0).map_err(|_| exhausted)?;
                                if source.negative_nodes.get(argument_index).is_none()
                                    || source.positive_nodes.get(result_index).is_none()
                                {
                                    return Err(exhausted);
                                }
                                if *active_positive.get(index).ok_or(exhausted)? {
                                    return Err(exhausted);
                                }
                                active_positive[index] = true;
                                push_task!(FlatTask::LeavePositive(index));
                                push_task!(FlatTask::FinishPositiveFunction);
                                push_task!(FlatTask::Positive(result));
                                push_task!(FlatTask::Negative(argument));
                            }
                        }
                    }
                    FlatTask::Negative(id) => {
                        let index = usize::try_from(id.0).map_err(|_| exhausted)?;
                        match *source.negative_nodes.get(index).ok_or(exhausted)? {
                            NegativeNode::Top => push_negative!(NegativeNode::Top),
                            NegativeNode::Bottom => push_negative!(NegativeNode::Bottom),
                            NegativeNode::Int => push_negative!(NegativeNode::Int),
                            NegativeNode::Variable(owner)
                                if !protected.contains(&owner)
                                    && negative_only.contains(&owner) =>
                            {
                                push_negative!(NegativeNode::Top);
                            }
                            NegativeNode::Variable(owner) => {
                                push_negative!(NegativeNode::Variable(owner));
                            }
                            NegativeNode::Quantified(owner) => {
                                push_negative!(NegativeNode::Quantified(owner));
                            }
                            NegativeNode::Recursive(owner) => {
                                push_negative!(NegativeNode::Recursive(owner));
                            }
                            NegativeNode::Intersection(span) => {
                                let children = flat_children(&source.negative_children, span)?;
                                if children.iter().any(|child| child.0 >= id.0) {
                                    return Err(exhausted);
                                }
                                if *active_negative.get(index).ok_or(exhausted)? {
                                    return Err(exhausted);
                                }
                                active_negative[index] = true;
                                let start = values.len();
                                push_task!(FlatTask::LeaveNegative(index));
                                push_task!(FlatTask::FinishNegativeIntersection(start));
                                for &child in children.iter().rev() {
                                    push_task!(FlatTask::Negative(child));
                                }
                            }
                            NegativeNode::Function { argument, result } => {
                                let argument_index =
                                    usize::try_from(argument.0).map_err(|_| exhausted)?;
                                let result_index =
                                    usize::try_from(result.0).map_err(|_| exhausted)?;
                                if source.positive_nodes.get(argument_index).is_none()
                                    || source.negative_nodes.get(result_index).is_none()
                                {
                                    return Err(exhausted);
                                }
                                if *active_negative.get(index).ok_or(exhausted)? {
                                    return Err(exhausted);
                                }
                                active_negative[index] = true;
                                push_task!(FlatTask::LeaveNegative(index));
                                push_task!(FlatTask::FinishNegativeFunction);
                                push_task!(FlatTask::Negative(result));
                                push_task!(FlatTask::Positive(argument));
                            }
                        }
                    }
                    FlatTask::LeavePositive(index) => {
                        *active_positive.get_mut(index).ok_or(exhausted)? = false;
                    }
                    FlatTask::LeaveNegative(index) => {
                        *active_negative.get_mut(index).ok_or(exhausted)? = false;
                    }
                    FlatTask::FinishPositiveUnion(start) => {
                        let count = values.len().checked_sub(start).ok_or(exhausted)?;
                        let child_start =
                            u32::try_from(output.positive_children.len()).map_err(|_| exhausted)?;
                        let child_len = u32::try_from(count).map_err(|_| exhausted)?;
                        child_start.checked_add(child_len).ok_or(exhausted)?;
                        output
                            .positive_children
                            .try_reserve(count)
                            .map_err(|_| exhausted)?;
                        for value in values.drain(start..) {
                            let NodeRef::Positive(child) = value else {
                                return Err(exhausted);
                            };
                            output.positive_children.push(child);
                        }
                        push_positive!(PositiveNode::Union(ChildSpan {
                            start: child_start,
                            len: child_len,
                        }));
                    }
                    FlatTask::FinishNegativeIntersection(start) => {
                        let count = values.len().checked_sub(start).ok_or(exhausted)?;
                        let child_start =
                            u32::try_from(output.negative_children.len()).map_err(|_| exhausted)?;
                        let child_len = u32::try_from(count).map_err(|_| exhausted)?;
                        child_start.checked_add(child_len).ok_or(exhausted)?;
                        output
                            .negative_children
                            .try_reserve(count)
                            .map_err(|_| exhausted)?;
                        for value in values.drain(start..) {
                            let NodeRef::Negative(child) = value else {
                                return Err(exhausted);
                            };
                            output.negative_children.push(child);
                        }
                        push_negative!(NegativeNode::Intersection(ChildSpan {
                            start: child_start,
                            len: child_len,
                        }));
                    }
                    FlatTask::FinishPositiveFunction => {
                        let NodeRef::Positive(result) = values.pop().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        let NodeRef::Negative(argument) = values.pop().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        push_positive!(PositiveNode::Function { argument, result });
                    }
                    FlatTask::FinishNegativeFunction => {
                        let NodeRef::Negative(result) = values.pop().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        let NodeRef::Positive(argument) = values.pop().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        push_negative!(NegativeNode::Function { argument, result });
                    }
                }
            }
            if values.len() != 1 {
                return Err(exhausted);
            }
            values.pop().ok_or(exhausted)
        })();
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayTasks);
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayValues);
        replayed
    })();
    if result.is_err() {
        output.positive_nodes.truncate(checkpoint.0);
        output.negative_nodes.truncate(checkpoint.1);
        output.positive_children.truncate(checkpoint.2);
        output.negative_children.truncate(checkpoint.3);
        output.insertion_order.truncate(checkpoint.4);
    }
    result
}

pub(super) fn replay_positive(
    memo: &mut F5cComponentExpansionMemo,
    value: &F5cPositive,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<F5cPositive, SolveAvailabilityError> {
    match replay(
        memo,
        Task::Positive(value),
        protected,
        positive_only,
        negative_only,
    )? {
        F5cWalkValue::Positive(value, _) => Ok(value),
        F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
    }
}

pub(super) fn replay_negative(
    memo: &mut F5cComponentExpansionMemo,
    value: &F5cNegative,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<F5cNegative, SolveAvailabilityError> {
    match replay(
        memo,
        Task::Negative(value),
        protected,
        positive_only,
        negative_only,
    )? {
        F5cWalkValue::Negative(value, _) => Ok(value),
        F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
    }
}

fn replay(
    memo: &mut F5cComponentExpansionMemo,
    first: Task<'_>,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<F5cWalkValue, SolveAvailabilityError> {
    let mut tasks = Vec::new();
    let mut values = Vec::new();
    macro_rules! push_task {
        ($task:expr) => {{
            memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::ReplayTasks)?;
            tasks.push($task);
        }};
    }
    macro_rules! push_value {
        ($value:expr) => {{
            memo.reserve_walker(&mut values, F5cWalkerLaneKind::ReplayValues)?;
            values.push($value);
        }};
    }

    let result = (|| {
        push_task!(first);
        while let Some(task) = tasks.pop() {
            match task {
                Task::Positive(value) => match value {
                    F5cPositive::Variable(owner)
                        if !protected.contains(owner) && positive_only.contains(owner) =>
                    {
                        push_value!(F5cWalkValue::Positive(F5cPositive::Bottom, true));
                    }
                    F5cPositive::Function {
                        argument, result, ..
                    } => {
                        push_task!(Task::FinishPositiveFunction);
                        push_task!(Task::Positive(result));
                        push_task!(Task::Negative(argument));
                    }
                    F5cPositive::Union(children) => {
                        let start = values.len();
                        push_task!(Task::FinishPositiveUnion(start));
                        for child in children.iter().rev() {
                            push_task!(Task::Positive(child));
                        }
                    }
                    other => {
                        push_value!(F5cWalkValue::Positive(other.clone(), true));
                    }
                },
                Task::Negative(value) => match value {
                    F5cNegative::Variable(owner)
                        if !protected.contains(owner) && negative_only.contains(owner) =>
                    {
                        push_value!(F5cWalkValue::Negative(F5cNegative::Top, true));
                    }
                    F5cNegative::Function {
                        argument, result, ..
                    } => {
                        push_task!(Task::FinishNegativeFunction);
                        push_task!(Task::Negative(result));
                        push_task!(Task::Positive(argument));
                    }
                    F5cNegative::Intersection(children) => {
                        let start = values.len();
                        push_task!(Task::FinishNegativeIntersection(start));
                        for child in children.iter().rev() {
                            push_task!(Task::Negative(child));
                        }
                    }
                    other => {
                        push_value!(F5cWalkValue::Negative(other.clone(), true));
                    }
                },
                Task::FinishPositiveUnion(start) => {
                    let mut children = Vec::new();
                    for value in values.drain(start..) {
                        let F5cWalkValue::Positive(value, _) = value else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        children.push(value);
                    }
                    push_value!(F5cWalkValue::Positive(F5cPositive::Union(children), true));
                }
                Task::FinishNegativeIntersection(start) => {
                    let mut children = Vec::new();
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
        .release(F5cWalkerLaneKind::ReplayTasks);
    memo.walker_resources
        .release(F5cWalkerLaneKind::ReplayValues);
    result
}
