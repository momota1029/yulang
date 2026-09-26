use super::f5c_draft::{
    ChildSpan, FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveId, PositiveNode,
};
#[cfg(test)]
use super::f5c_generalization::{F5cBulkDrainSite, record_bulk_drain_boundary};
use super::{
    F5cComponentExpansionMemo, F5cNegative, F5cNegativeEffect, F5cPositive, F5cPositiveEffect,
    F5cWalkValue, F5cWalkerLaneKind, SolveAvailabilityError,
};
use std::collections::HashSet;

#[cfg(test)]
thread_local! {
    static FAIL_AFTER_FLAT_OUTPUT: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    static FAILED_AFTER_OUTPUT_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn inject_failure_after_flat_output() {
    FAIL_AFTER_FLAT_OUTPUT.with(|flag| flag.set(1));
    FAILED_AFTER_OUTPUT_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub(super) fn failed_after_flat_output_count() -> usize {
    FAILED_AFTER_OUTPUT_COUNT.with(std::cell::Cell::get)
}

pub(super) enum Task<'tree> {
    Positive(&'tree F5cPositive),
    Negative(&'tree F5cNegative),
    FinishPositiveUnion(usize),
    FinishNegativeIntersection(usize),
    FinishPositiveFunction,
    FinishNegativeFunction,
}

#[cfg(test)]
pub(super) fn observe_flat_output(
    memo: &mut F5cComponentExpansionMemo,
    output: &mut FlatDraft,
) -> Result<(), SolveAvailabilityError> {
    let memo_bytes = memo.retained_bytes()?;
    let resources = &mut memo.walker_resources;
    resources.reserve(
        &mut output.positive_nodes,
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        0,
        memo_bytes,
    )?;
    resources.reserve(
        &mut output.negative_nodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        0,
        memo_bytes,
    )?;
    resources.reserve(
        &mut output.positive_children,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        0,
        memo_bytes,
    )?;
    resources.reserve(
        &mut output.negative_children,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        0,
        memo_bytes,
    )?;
    resources.reserve(
        &mut output.insertion_order,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        0,
        memo_bytes,
    )
}

#[cfg(test)]
pub(super) fn release_flat_output(memo: &mut F5cComponentExpansionMemo, output: FlatDraft) {
    drop(output);
    for lane in [
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
    ] {
        memo.walker_resources.release(lane);
    }
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
        let active_len = source
            .positive_nodes
            .len()
            .checked_add(source.negative_nodes.len())
            .ok_or(exhausted)?;
        memo.work_meter.charge(active_len)?; // initialized replay-active slots
        let mut active_positive = Vec::new();
        let memo_bytes = memo.retained_bytes()?;
        let allocation = memo.walker_resources.reserve(
            &mut active_positive,
            F5cWalkerLaneKind::ReplayActivePositive,
            source.positive_nodes.len(),
            memo_bytes,
        );
        if let Err(error) = allocation {
            drop(active_positive);
            memo.walker_resources
                .release(F5cWalkerLaneKind::ReplayActivePositive);
            return Err(error);
        }
        active_positive.resize(source.positive_nodes.len(), false);
        let mut active_negative = Vec::new();
        let allocation = memo.walker_resources.reserve(
            &mut active_negative,
            F5cWalkerLaneKind::ReplayActiveNegative,
            source.negative_nodes.len(),
            memo_bytes,
        );
        if let Err(error) = allocation {
            drop(active_positive);
            drop(active_negative);
            memo.walker_resources
                .release(F5cWalkerLaneKind::ReplayActivePositive);
            memo.walker_resources
                .release(F5cWalkerLaneKind::ReplayActiveNegative);
            return Err(error);
        }
        active_negative.resize(source.negative_nodes.len(), false);

        let mut tasks = Vec::new();
        let mut values = Vec::new();
        macro_rules! push_task {
            ($task:expr) => {{
                memo.work_meter.charge(1)?; // scheduled flat replay task
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
            while !tasks.is_empty() {
                memo.work_meter.charge(1)?; // visited flat replay task
                #[cfg(test)]
                if FAIL_AFTER_FLAT_OUTPUT.with(|flag| flag.get()) == 2 {
                    FAIL_AFTER_FLAT_OUTPUT.with(|flag| flag.set(0));
                    return Err(exhausted);
                }
                let task = tasks.pop().expect("nonempty flat replay tasks");
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
                                for child in children {
                                    memo.work_meter.charge(1)?; // inspected union edge
                                    if child.0 >= id.0 {
                                        return Err(exhausted);
                                    }
                                }
                                if *active_positive.get(index).ok_or(exhausted)? {
                                    return Err(exhausted);
                                }
                                active_positive[index] = true;
                                let start = values.len();
                                push_task!(FlatTask::LeavePositive(index));
                                push_task!(FlatTask::FinishPositiveUnion(start));
                                for &child in children.iter().rev() {
                                    memo.work_meter.charge(1)?; // union incidence
                                    push_task!(FlatTask::Positive(child));
                                }
                            }
                            PositiveNode::Function { argument, result } => {
                                memo.work_meter.charge(2)?; // inspected Function edges
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
                                memo.work_meter.charge(1)?; // result edge
                                push_task!(FlatTask::Positive(result));
                                memo.work_meter.charge(1)?; // argument edge
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
                                for child in children {
                                    memo.work_meter.charge(1)?; // inspected intersection edge
                                    if child.0 >= id.0 {
                                        return Err(exhausted);
                                    }
                                }
                                if *active_negative.get(index).ok_or(exhausted)? {
                                    return Err(exhausted);
                                }
                                active_negative[index] = true;
                                let start = values.len();
                                push_task!(FlatTask::LeaveNegative(index));
                                push_task!(FlatTask::FinishNegativeIntersection(start));
                                for &child in children.iter().rev() {
                                    memo.work_meter.charge(1)?; // intersection incidence
                                    push_task!(FlatTask::Negative(child));
                                }
                            }
                            NegativeNode::Function { argument, result } => {
                                memo.work_meter.charge(2)?; // inspected Function edges
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
                                memo.work_meter.charge(1)?; // result edge
                                push_task!(FlatTask::Negative(result));
                                memo.work_meter.charge(1)?; // argument edge
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
        #[cfg(test)]
        if replayed.is_ok() && FAIL_AFTER_FLAT_OUTPUT.with(|flag| flag.get()) == 1 {
            let emitted = output.positive_nodes.len() - checkpoint.0 + output.negative_nodes.len()
                - checkpoint.1;
            if emitted > 0 {
                FAILED_AFTER_OUTPUT_COUNT.with(|count| count.set(emitted));
                FAIL_AFTER_FLAT_OUTPUT.with(|flag| flag.set(2));
            }
        }
        #[cfg(test)]
        let observed = observe_flat_output(memo, output);
        #[cfg(test)]
        let replayed = match observed {
            Ok(()) => replayed,
            Err(error) => Err(error),
        };
        drop(active_positive);
        drop(active_negative);
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayActivePositive);
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayActiveNegative);
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
            memo.work_meter.charge(1)?; // scheduled replay task
            memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::ReplayTasks)?;
            tasks.push($task);
        }};
    }
    macro_rules! push_value {
        ($value:expr) => {{
            memo.work_meter.charge(1)?; // emitted replay value
            memo.reserve_walker(&mut values, F5cWalkerLaneKind::ReplayValues)?;
            values.push($value);
        }};
    }

    let result = (|| {
        push_task!(first);
        while !tasks.is_empty() {
            memo.work_meter.charge(1)?; // visited source or finish task
            let task = tasks.pop().expect("nonempty replay tasks");
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
                        memo.work_meter.charge(1)?; // result edge
                        push_task!(Task::Positive(result));
                        memo.work_meter.charge(1)?; // argument edge
                        push_task!(Task::Negative(argument));
                    }
                    F5cPositive::Union(children) => {
                        let start = values.len();
                        push_task!(Task::FinishPositiveUnion(start));
                        for child in children.iter().rev() {
                            memo.work_meter.charge(1)?; // union incidence
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
                        memo.work_meter.charge(1)?; // result edge
                        push_task!(Task::Negative(result));
                        memo.work_meter.charge(1)?; // argument edge
                        push_task!(Task::Positive(argument));
                    }
                    F5cNegative::Intersection(children) => {
                        let start = values.len();
                        push_task!(Task::FinishNegativeIntersection(start));
                        for child in children.iter().rev() {
                            memo.work_meter.charge(1)?; // intersection incidence
                            push_task!(Task::Negative(child));
                        }
                    }
                    other => {
                        push_value!(F5cWalkValue::Negative(other.clone(), true));
                    }
                },
                Task::FinishPositiveUnion(start) => {
                    // Scheduled positive children each leave one value in this suffix;
                    // the batch charge precedes the drain and output mutation.
                    let count = values
                        .len()
                        .checked_sub(start)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(test)]
                    record_bulk_drain_boundary(
                        F5cBulkDrainSite::ReplayPositive,
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
                    // the batch charge precedes the drain and output mutation.
                    let count = values
                        .len()
                        .checked_sub(start)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(test)]
                    record_bulk_drain_boundary(
                        F5cBulkDrainSite::ReplayNegative,
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
