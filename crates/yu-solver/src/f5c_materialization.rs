use super::{
    F5cComponentExpansionMemo, F5cGeneralizer, F5cNegative, F5cNegativeEffect, F5cPositive,
    F5cPositiveEffect, F5cSummaryNodeId, F5cWalkValue, F5cWalkerLaneKind, Polarity,
    SolveAvailabilityError,
};

pub(super) enum Task {
    Positive(F5cPositive),
    Negative(F5cNegative),
    FinishPositiveUnion(usize),
    FinishNegativeIntersection(usize),
    FinishPositiveFunction {
        argument_effect: F5cNegativeEffect,
        result_effect: F5cPositiveEffect,
    },
    FinishNegativeFunction {
        argument_effect: F5cPositiveEffect,
        result_effect: F5cNegativeEffect,
    },
}

pub(super) fn materialize_iterative(
    memo: &mut F5cComponentExpansionMemo,
    first: Task,
    mut shared: impl FnMut(
        &mut F5cComponentExpansionMemo,
        F5cSummaryNodeId,
        Polarity,
    ) -> Result<F5cWalkValue, SolveAvailabilityError>,
) -> Result<F5cWalkValue, SolveAvailabilityError> {
    let mut tasks = Vec::new();
    let mut values = Vec::new();
    macro_rules! push_task {
        ($task:expr) => {{
            memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::DraftMaterializeTasks)?;
            tasks.push($task);
        }};
    }
    macro_rules! push_value {
        ($value:expr) => {{
            memo.reserve_walker(&mut values, F5cWalkerLaneKind::DraftMaterializeValues)?;
            values.push($value);
        }};
    }

    let result = (|| {
        push_task!(first);
        while let Some(task) = tasks.pop() {
            match task {
                Task::Positive(value) => match value {
                    F5cPositive::Shared(id) => {
                        push_value!(shared(memo, id, Polarity::Positive)?);
                    }
                    F5cPositive::Union(children) => {
                        let start = values.len();
                        push_task!(Task::FinishPositiveUnion(start));
                        for child in children.into_iter().rev() {
                            push_task!(Task::Positive(child));
                        }
                    }
                    F5cPositive::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        push_task!(Task::FinishPositiveFunction {
                            argument_effect,
                            result_effect,
                        });
                        push_task!(Task::Positive(*result));
                        push_task!(Task::Negative(*argument));
                    }
                    value => push_value!(F5cWalkValue::Positive(value, true)),
                },
                Task::Negative(value) => match value {
                    F5cNegative::Shared(id) => {
                        push_value!(shared(memo, id, Polarity::Negative)?);
                    }
                    F5cNegative::Intersection(children) => {
                        let start = values.len();
                        push_task!(Task::FinishNegativeIntersection(start));
                        for child in children.into_iter().rev() {
                            push_task!(Task::Negative(child));
                        }
                    }
                    F5cNegative::Function {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => {
                        push_task!(Task::FinishNegativeFunction {
                            argument_effect,
                            result_effect,
                        });
                        push_task!(Task::Negative(*result));
                        push_task!(Task::Positive(*argument));
                    }
                    value => push_value!(F5cWalkValue::Negative(value, true)),
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
                Task::FinishPositiveFunction {
                    argument_effect,
                    result_effect,
                } => {
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
                            argument_effect,
                            result_effect,
                            result: Box::new(result),
                        },
                        true,
                    ));
                }
                Task::FinishNegativeFunction {
                    argument_effect,
                    result_effect,
                } => {
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
                            argument_effect,
                            result_effect,
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
        .release(F5cWalkerLaneKind::DraftMaterializeTasks);
    memo.walker_resources
        .release(F5cWalkerLaneKind::DraftMaterializeValues);
    result
}

impl F5cGeneralizer<'_> {
    fn materialize(&mut self, first: Task) -> Result<F5cWalkValue, SolveAvailabilityError> {
        let session = self.session;
        let frames = &mut self.frames;
        let active_set = &self.active_set;
        let provisional = &self.provisional_recursive_rows;
        let order = &mut self.order;
        let order_seen = &mut self.order_seen;
        let mut active_conflict = false;
        let result = materialize_iterative(&mut self.memo, first, |memo, id, polarity| {
            let mut mark = |row, _polarity| {
                active_conflict |= active_set.contains(&(row, Polarity::Positive))
                    || active_set.contains(&(row, Polarity::Negative));
                if order_seen.insert(row) {
                    order.push(row);
                }
                if provisional.contains(&row)
                    || session
                        .value_metadata
                        .get(row as usize)
                        .is_none_or(|metadata| metadata.non_generic)
                    || session
                        .value_levels
                        .get(row as usize)
                        .is_none_or(|level| *level == 0)
                {
                    if let Some(frame) = frames.last_mut() {
                        frame.tainted = true;
                    }
                }
            };
            match polarity {
                Polarity::Positive => Ok(F5cWalkValue::Positive(
                    memo.positive_value_with(id, &mut mark)?,
                    true,
                )),
                Polarity::Negative => Ok(F5cWalkValue::Negative(
                    memo.negative_value_with(id, &mut mark)?,
                    true,
                )),
            }
        });
        if active_conflict {
            self.taint_active_states();
        }
        result
    }

    pub(super) fn materialize_positive(
        &mut self,
        value: F5cPositive,
    ) -> Result<F5cPositive, SolveAvailabilityError> {
        match self.materialize(Task::Positive(value))? {
            F5cWalkValue::Positive(value, _) => Ok(value),
            F5cWalkValue::Negative(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    pub(super) fn materialize_negative(
        &mut self,
        value: F5cNegative,
    ) -> Result<F5cNegative, SolveAvailabilityError> {
        match self.materialize(Task::Negative(value))? {
            F5cWalkValue::Negative(value, _) => Ok(value),
            F5cWalkValue::Positive(_, _) => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }
}
