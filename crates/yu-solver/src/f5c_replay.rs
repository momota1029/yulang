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
