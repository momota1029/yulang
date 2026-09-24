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
            memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::BinderTasks)?;
            tasks.push($task);
        }};
    }
    macro_rules! push_value {
        ($value:expr) => {{
            memo.reserve_walker(&mut values, F5cWalkerLaneKind::BinderValues)?;
            values.push($value);
        }};
    }

    let result = (|| {
        push_task!(first);
        while let Some(task) = tasks.pop() {
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
                        push_task!(Task::Positive(*result));
                        push_task!(Task::Negative(*argument));
                    }
                    F5cPositive::Union(children) => {
                        let start = values.len();
                        push_task!(Task::FinishPositiveUnion(start));
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
                        push_task!(Task::Negative(*result));
                        push_task!(Task::Positive(*argument));
                    }
                    F5cNegative::Intersection(children) => {
                        let start = values.len();
                        push_task!(Task::FinishNegativeIntersection(start));
                        for child in children.into_iter().rev() {
                            push_task!(Task::Negative(child));
                        }
                    }
                    other => push_value!(F5cWalkValue::Negative(other, true)),
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
        .release(F5cWalkerLaneKind::BinderTasks);
    memo.walker_resources
        .release(F5cWalkerLaneKind::BinderValues);
    result
}
