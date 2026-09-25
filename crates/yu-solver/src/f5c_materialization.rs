use super::F5cSummaryNodeKind;
use super::f5c_draft::{FlatDraft, NegativeNode, NodeRef, PositiveNode};
use super::{
    F5cComponentExpansionMemo, F5cGeneralizer, F5cNegative, F5cNegativeEffect, F5cPositive,
    F5cPositiveEffect, F5cSummaryNodeId, F5cWalkValue, F5cWalkerLaneKind, Polarity,
    SolveAvailabilityError,
};
use std::collections::HashMap;

#[derive(Clone, Copy)]
enum FlatTask {
    Enter(F5cSummaryNodeId, Polarity),
    Union(usize),
    Intersection(usize),
    PositiveFunction,
    NegativeFunction,
}

fn push_flat_task(tasks: &mut Vec<FlatTask>, task: FlatTask) -> Result<(), SolveAvailabilityError> {
    tasks
        .try_reserve(1)
        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
    tasks.push(task);
    Ok(())
}

/// Expand one summary occurrence. The draft append transaction is restored on error.
/// Callback state is caller-owned; on Err the caller must discard its candidate
/// mark, order, and conflict state.
#[allow(dead_code)]
pub(super) fn materialize_summary_flat(
    memo: &F5cComponentExpansionMemo,
    draft: &mut FlatDraft,
    root: F5cSummaryNodeId,
    polarity: Polarity,
    mut mark: impl FnMut(u32, Polarity),
) -> Result<NodeRef, SolveAvailabilityError> {
    let checkpoint = (
        draft.positive_nodes.len(),
        draft.negative_nodes.len(),
        draft.positive_children.len(),
        draft.negative_children.len(),
        draft.recursive_bounds.len(),
        draft.insertion_order.len(),
    );
    let result = (|| {
        let bad = SolveAvailabilityError::IdentityExhausted;
        let mut tasks = Vec::new();
        let mut values = Vec::new();
        push_flat_task(&mut tasks, FlatTask::Enter(root, polarity))?;
        while let Some(task) = tasks.pop() {
            match task {
                FlatTask::Enter(id, expected) => {
                    let index = usize::try_from(id.0).map_err(|_| bad)?;
                    let node = *memo.nodes.get(index).ok_or(bad)?;
                    if let Some((row, polarity)) = node.incidence {
                        mark(row, polarity);
                    }
                    let output = match (expected, node.kind) {
                        (Polarity::Positive, F5cSummaryNodeKind::PositiveBottom) => {
                            Some(NodeRef::Positive(draft.positive(PositiveNode::Bottom)?))
                        }
                        (Polarity::Positive, F5cSummaryNodeKind::PositiveInt) => {
                            Some(NodeRef::Positive(draft.positive(PositiveNode::Int)?))
                        }
                        (Polarity::Positive, F5cSummaryNodeKind::PositiveRow(row)) => Some(
                            NodeRef::Positive(draft.positive(PositiveNode::Variable(row))?),
                        ),
                        (Polarity::Negative, F5cSummaryNodeKind::NegativeTop) => {
                            Some(NodeRef::Negative(draft.negative(NegativeNode::Top)?))
                        }
                        (Polarity::Negative, F5cSummaryNodeKind::NegativeBottom) => {
                            Some(NodeRef::Negative(draft.negative(NegativeNode::Bottom)?))
                        }
                        (Polarity::Negative, F5cSummaryNodeKind::NegativeInt) => {
                            Some(NodeRef::Negative(draft.negative(NegativeNode::Int)?))
                        }
                        (Polarity::Negative, F5cSummaryNodeKind::NegativeRow(row)) => Some(
                            NodeRef::Negative(draft.negative(NegativeNode::Variable(row))?),
                        ),
                        (polarity, F5cSummaryNodeKind::PositiveAlias { start })
                            if polarity == Polarity::Positive =>
                        {
                            let child = memo.child_slice(start, 1)?[0];
                            if child.0 >= id.0 {
                                return Err(bad);
                            }
                            push_flat_task(&mut tasks, FlatTask::Enter(child, polarity))?;
                            None
                        }
                        (polarity, F5cSummaryNodeKind::NegativeAlias { start })
                            if polarity == Polarity::Negative =>
                        {
                            let child = memo.child_slice(start, 1)?[0];
                            if child.0 >= id.0 {
                                return Err(bad);
                            }
                            push_flat_task(&mut tasks, FlatTask::Enter(child, polarity))?;
                            None
                        }
                        (Polarity::Positive, F5cSummaryNodeKind::PositiveUnion { start, len }) => {
                            let children = memo.child_slice(start, len)?;
                            if children.iter().any(|child| child.0 >= id.0) {
                                return Err(bad);
                            }
                            push_flat_task(&mut tasks, FlatTask::Union(values.len()))?;
                            for &child in children.iter().rev() {
                                push_flat_task(
                                    &mut tasks,
                                    FlatTask::Enter(child, Polarity::Positive),
                                )?;
                            }
                            None
                        }
                        (
                            Polarity::Negative,
                            F5cSummaryNodeKind::NegativeIntersection { start, len },
                        ) => {
                            let children = memo.child_slice(start, len)?;
                            if children.iter().any(|child| child.0 >= id.0) {
                                return Err(bad);
                            }
                            push_flat_task(&mut tasks, FlatTask::Intersection(values.len()))?;
                            for &child in children.iter().rev() {
                                push_flat_task(
                                    &mut tasks,
                                    FlatTask::Enter(child, Polarity::Negative),
                                )?;
                            }
                            None
                        }
                        (
                            Polarity::Positive,
                            F5cSummaryNodeKind::PositiveFunction { argument, result },
                        ) => {
                            if argument.0 >= id.0 || result.0 >= id.0 {
                                return Err(bad);
                            }
                            push_flat_task(&mut tasks, FlatTask::PositiveFunction)?;
                            push_flat_task(
                                &mut tasks,
                                FlatTask::Enter(result, Polarity::Positive),
                            )?;
                            push_flat_task(
                                &mut tasks,
                                FlatTask::Enter(argument, Polarity::Negative),
                            )?;
                            None
                        }
                        (
                            Polarity::Negative,
                            F5cSummaryNodeKind::NegativeFunction { argument, result },
                        ) => {
                            if argument.0 >= id.0 || result.0 >= id.0 {
                                return Err(bad);
                            }
                            push_flat_task(&mut tasks, FlatTask::NegativeFunction)?;
                            push_flat_task(
                                &mut tasks,
                                FlatTask::Enter(result, Polarity::Negative),
                            )?;
                            push_flat_task(
                                &mut tasks,
                                FlatTask::Enter(argument, Polarity::Positive),
                            )?;
                            None
                        }
                        _ => return Err(bad),
                    };
                    if let Some(output) = output {
                        values.try_reserve(1).map_err(|_| bad)?;
                        values.push(output);
                    }
                }
                FlatTask::Union(start) => {
                    let mut children = Vec::new();
                    children
                        .try_reserve(values.len().checked_sub(start).ok_or(bad)?)
                        .map_err(|_| bad)?;
                    for value in values.drain(start..) {
                        let NodeRef::Positive(id) = value else {
                            return Err(bad);
                        };
                        children.push(id);
                    }
                    let span = draft.positive_span(&children)?;
                    values.try_reserve(1).map_err(|_| bad)?;
                    values.push(NodeRef::Positive(
                        draft.positive(PositiveNode::Union(span))?,
                    ));
                }
                FlatTask::Intersection(start) => {
                    let mut children = Vec::new();
                    children
                        .try_reserve(values.len().checked_sub(start).ok_or(bad)?)
                        .map_err(|_| bad)?;
                    for value in values.drain(start..) {
                        let NodeRef::Negative(id) = value else {
                            return Err(bad);
                        };
                        children.push(id);
                    }
                    let span = draft.negative_span(&children)?;
                    values.try_reserve(1).map_err(|_| bad)?;
                    values.push(NodeRef::Negative(
                        draft.negative(NegativeNode::Intersection(span))?,
                    ));
                }
                FlatTask::PositiveFunction => {
                    let NodeRef::Positive(result) = values.pop().ok_or(bad)? else {
                        return Err(bad);
                    };
                    let NodeRef::Negative(argument) = values.pop().ok_or(bad)? else {
                        return Err(bad);
                    };
                    values.try_reserve(1).map_err(|_| bad)?;
                    values.push(NodeRef::Positive(
                        draft.positive(PositiveNode::Function { argument, result })?,
                    ));
                }
                FlatTask::NegativeFunction => {
                    let NodeRef::Negative(result) = values.pop().ok_or(bad)? else {
                        return Err(bad);
                    };
                    let NodeRef::Positive(argument) = values.pop().ok_or(bad)? else {
                        return Err(bad);
                    };
                    values.try_reserve(1).map_err(|_| bad)?;
                    values.push(NodeRef::Negative(
                        draft.negative(NegativeNode::Function { argument, result })?,
                    ));
                }
            }
        }
        if values.len() != 1 {
            return Err(bad);
        }
        values.pop().ok_or(bad)
    })();
    if result.is_err() {
        draft.positive_nodes.truncate(checkpoint.0);
        draft.negative_nodes.truncate(checkpoint.1);
        draft.positive_children.truncate(checkpoint.2);
        draft.negative_children.truncate(checkpoint.3);
        draft.recursive_bounds.truncate(checkpoint.4);
        draft.insertion_order.truncate(checkpoint.5);
    }
    result
}

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

pub(super) fn materialize_bound_trees(
    bounds: &mut HashMap<u32, (F5cPositive, F5cNegative)>,
    mut transform: impl FnMut(F5cWalkValue) -> Result<F5cWalkValue, SolveAvailabilityError>,
) -> Result<(), SolveAvailabilityError> {
    for (lower, upper) in bounds.values_mut() {
        let raw_lower = std::mem::replace(lower, F5cPositive::Bottom);
        let F5cWalkValue::Positive(mapped_lower, _) =
            transform(F5cWalkValue::Positive(raw_lower, true))?
        else {
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        *lower = mapped_lower;

        let raw_upper = std::mem::replace(upper, F5cNegative::Top);
        let F5cWalkValue::Negative(mapped_upper, _) =
            transform(F5cWalkValue::Negative(raw_upper, true))?
        else {
            return Err(SolveAvailabilityError::IdentityExhausted);
        };
        *upper = mapped_upper;
    }
    Ok(())
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

    pub(super) fn materialize_recursive_bounds(
        &mut self,
        bounds: &mut HashMap<u32, (F5cPositive, F5cNegative)>,
    ) -> Result<(), SolveAvailabilityError> {
        materialize_bound_trees(bounds, |value| match value {
            F5cWalkValue::Positive(value, _) => self
                .materialize_positive(value)
                .map(|value| F5cWalkValue::Positive(value, true)),
            F5cWalkValue::Negative(value, _) => self
                .materialize_negative(value)
                .map(|value| F5cWalkValue::Negative(value, true)),
        })
    }
}

#[cfg(test)]
mod flat_tests {
    use super::super::F5cSummaryNode;
    use super::*;

    fn expand_positive(flat: &FlatDraft, id: super::super::f5c_draft::PositiveId) -> F5cPositive {
        use PositiveNode::*;
        match flat.positive_nodes[id.0 as usize] {
            Bottom => F5cPositive::Bottom,
            Int => F5cPositive::Int,
            Variable(row) => F5cPositive::Variable(row),
            Union(span) => F5cPositive::Union(
                flat.positive_children[span.start as usize..(span.start + span.len) as usize]
                    .iter()
                    .map(|&child| expand_positive(flat, child))
                    .collect(),
            ),
            Function { argument, result } => F5cPositive::Function {
                argument: Box::new(expand_negative(flat, argument)),
                argument_effect: F5cNegativeEffect::Empty,
                result_effect: F5cPositiveEffect::Bottom,
                result: Box::new(expand_positive(flat, result)),
            },
            _ => panic!("unexpected flat positive node"),
        }
    }

    fn expand_negative(flat: &FlatDraft, id: super::super::f5c_draft::NegativeId) -> F5cNegative {
        use NegativeNode::*;
        match flat.negative_nodes[id.0 as usize] {
            Top => F5cNegative::Top,
            Bottom => F5cNegative::Bottom,
            Int => F5cNegative::Int,
            Variable(row) => F5cNegative::Variable(row),
            Intersection(span) => F5cNegative::Intersection(
                flat.negative_children[span.start as usize..(span.start + span.len) as usize]
                    .iter()
                    .map(|&child| expand_negative(flat, child))
                    .collect(),
            ),
            Function { argument, result } => F5cNegative::Function {
                argument: Box::new(expand_positive(flat, argument)),
                argument_effect: F5cPositiveEffect::Bottom,
                result_effect: F5cNegativeEffect::Empty,
                result: Box::new(expand_negative(flat, result)),
            },
            _ => panic!("unexpected flat negative node"),
        }
    }

    #[test]
    fn summary_flat_matches_boxed_mixed_shared_fixture() {
        let mut memo = F5cComponentExpansionMemo::default();
        let ids = (0..8).map(F5cSummaryNodeId).collect::<Vec<_>>();
        let kinds = [
            F5cSummaryNodeKind::PositiveRow(11),
            F5cSummaryNodeKind::NegativeRow(12),
            F5cSummaryNodeKind::NegativeIntersection { start: 0, len: 2 },
            F5cSummaryNodeKind::NegativeFunction {
                argument: ids[0],
                result: ids[2],
            },
            F5cSummaryNodeKind::PositiveFunction {
                argument: ids[3],
                result: ids[0],
            },
            F5cSummaryNodeKind::PositiveFunction {
                argument: ids[2],
                result: ids[4],
            },
            F5cSummaryNodeKind::PositiveAlias { start: 2 },
            F5cSummaryNodeKind::PositiveUnion { start: 3, len: 4 },
        ];
        memo.nodes = kinds
            .into_iter()
            .enumerate()
            .map(|(index, kind)| F5cSummaryNode {
                incidence: Some((
                    index as u32,
                    if matches!(index, 1 | 2 | 3) {
                        Polarity::Negative
                    } else {
                        Polarity::Positive
                    },
                )),
                transitive_incidence_count: 0,
                kind,
            })
            .collect();
        memo.children = vec![ids[1], ids[1], ids[4], ids[5], ids[6], ids[4], ids[5]];
        let mut boxed_marks = Vec::new();
        let boxed = memo
            .positive_value_with(ids[7], &mut |row, polarity| {
                boxed_marks.push((row, polarity))
            })
            .unwrap();
        let mut flat = FlatDraft::default();
        let mut flat_marks = Vec::new();
        let root = materialize_summary_flat(
            &memo,
            &mut flat,
            ids[7],
            Polarity::Positive,
            |row, polarity| flat_marks.push((row, polarity)),
        )
        .unwrap();
        assert_eq!(flat_marks, boxed_marks);
        let NodeRef::Positive(root_id) = root else {
            panic!("wrong root polarity")
        };
        assert_eq!(expand_positive(&flat, root_id), boxed);
        let PositiveNode::Union(span) = flat.positive_nodes[root_id.0 as usize] else {
            panic!("wrong root kind")
        };
        let children =
            &flat.positive_children[span.start as usize..(span.start + span.len) as usize];
        assert_ne!(children[0], children[3]);
        assert_ne!(children[1], children[2]);
        let mut boxed_negative_marks = Vec::new();
        let boxed_negative = memo
            .negative_value_with(ids[3], &mut |row, polarity| {
                boxed_negative_marks.push((row, polarity))
            })
            .unwrap();
        let mut flat_negative_marks = Vec::new();
        let NodeRef::Negative(negative_root) = materialize_summary_flat(
            &memo,
            &mut flat,
            ids[3],
            Polarity::Negative,
            |row, polarity| flat_negative_marks.push((row, polarity)),
        )
        .unwrap() else {
            panic!("wrong negative root polarity");
        };
        assert_eq!(flat_negative_marks, boxed_negative_marks);
        assert_eq!(expand_negative(&flat, negative_root), boxed_negative);
    }

    #[test]
    fn summary_flat_replays_incidence_and_rolls_back() {
        let mut memo = F5cComponentExpansionMemo::default();
        let row = F5cSummaryNodeId(0);
        let alias = F5cSummaryNodeId(1);
        let union = F5cSummaryNodeId(4);
        memo.nodes = vec![
            F5cSummaryNode {
                incidence: Some((7, Polarity::Positive)),
                transitive_incidence_count: 1,
                kind: F5cSummaryNodeKind::PositiveRow(7),
            },
            F5cSummaryNode {
                incidence: Some((8, Polarity::Positive)),
                transitive_incidence_count: 2,
                kind: F5cSummaryNodeKind::PositiveAlias { start: 0 },
            },
            F5cSummaryNode {
                incidence: None,
                transitive_incidence_count: 4,
                kind: F5cSummaryNodeKind::PositiveUnion { start: 1, len: 2 },
            },
            F5cSummaryNode {
                incidence: None,
                transitive_incidence_count: 0,
                kind: F5cSummaryNodeKind::PositiveAlias { start: 3 },
            },
            F5cSummaryNode {
                incidence: None,
                transitive_incidence_count: 4,
                kind: F5cSummaryNodeKind::PositiveUnion { start: 1, len: 2 },
            },
        ];
        memo.children = vec![row, alias, alias, F5cSummaryNodeId(3)];
        let mut flat = FlatDraft::default();
        let mut marks = Vec::new();
        let root = materialize_summary_flat(&memo, &mut flat, union, Polarity::Positive, |r, p| {
            marks.push((r, p))
        })
        .unwrap();
        assert_eq!(
            marks,
            vec![
                (8, Polarity::Positive),
                (7, Polarity::Positive),
                (8, Polarity::Positive),
                (7, Polarity::Positive)
            ]
        );
        assert_eq!(
            flat.positive_nodes,
            vec![
                PositiveNode::Variable(7),
                PositiveNode::Variable(7),
                PositiveNode::Union(super::super::f5c_draft::ChildSpan { start: 0, len: 2 })
            ]
        );
        assert_eq!(
            flat.positive_children,
            vec![
                super::super::f5c_draft::PositiveId(0),
                super::super::f5c_draft::PositiveId(1)
            ]
        );
        assert_eq!(
            root,
            NodeRef::Positive(super::super::f5c_draft::PositiveId(2))
        );
        let prior_nodes = flat.positive_nodes.clone();
        let prior_negative_nodes = flat.negative_nodes.clone();
        let prior_children = flat.positive_children.clone();
        let prior_negative_children = flat.negative_children.clone();
        let prior_bounds = flat.recursive_bounds.clone();
        let prior_order = flat.insertion_order.clone();
        memo.children[2] = F5cSummaryNodeId(3);
        let mut failed_marks = Vec::new();
        assert!(
            materialize_summary_flat(&memo, &mut flat, union, Polarity::Positive, |r, p| {
                failed_marks.push((r, p))
            })
            .is_err()
        );
        assert_eq!(
            failed_marks,
            vec![(8, Polarity::Positive), (7, Polarity::Positive)]
        );
        // The caller discards failed_marks on Err; only the draft append is rolled back here.
        assert_eq!(flat.positive_nodes, prior_nodes);
        assert_eq!(flat.negative_nodes, prior_negative_nodes);
        assert_eq!(flat.positive_children, prior_children);
        assert_eq!(flat.negative_children, prior_negative_children);
        assert_eq!(flat.recursive_bounds, prior_bounds);
        assert_eq!(flat.insertion_order, prior_order);
    }

    #[test]
    fn summary_flat_rejects_alias_cycles() {
        let mut memo = F5cComponentExpansionMemo::default();
        memo.nodes = vec![F5cSummaryNode {
            incidence: None,
            transitive_incidence_count: 0,
            kind: F5cSummaryNodeKind::PositiveAlias { start: 0 },
        }];
        memo.children = vec![F5cSummaryNodeId(0)];
        let mut flat = FlatDraft::default();
        assert!(matches!(
            materialize_summary_flat(
                &memo,
                &mut flat,
                F5cSummaryNodeId(0),
                Polarity::Positive,
                |_, _| {}
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
        memo.nodes.push(F5cSummaryNode {
            incidence: None,
            transitive_incidence_count: 0,
            kind: F5cSummaryNodeKind::PositiveAlias { start: 1 },
        });
        memo.children = vec![F5cSummaryNodeId(1), F5cSummaryNodeId(0)];
        assert!(matches!(
            materialize_summary_flat(
                &memo,
                &mut flat,
                F5cSummaryNodeId(1),
                Polarity::Positive,
                |_, _| {}
            ),
            Err(SolveAvailabilityError::IdentityExhausted)
        ));
        assert!(flat.positive_nodes.is_empty());
    }

    #[test]
    fn summary_flat_preserves_both_functions_and_intersection() {
        use super::super::f5c_draft::{ChildSpan, NegativeId, PositiveId};
        let mut memo = F5cComponentExpansionMemo::default();
        let kinds = [
            F5cSummaryNodeKind::PositiveInt,
            F5cSummaryNodeKind::NegativeRow(9),
            F5cSummaryNodeKind::NegativeInt,
            F5cSummaryNodeKind::NegativeIntersection { start: 0, len: 2 },
            F5cSummaryNodeKind::PositiveFunction {
                argument: F5cSummaryNodeId(3),
                result: F5cSummaryNodeId(0),
            },
            F5cSummaryNodeKind::NegativeFunction {
                argument: F5cSummaryNodeId(0),
                result: F5cSummaryNodeId(3),
            },
        ];
        memo.nodes = kinds
            .into_iter()
            .map(|kind| F5cSummaryNode {
                incidence: None,
                transitive_incidence_count: 0,
                kind,
            })
            .collect();
        memo.children = vec![F5cSummaryNodeId(1), F5cSummaryNodeId(2)];
        let mut flat = FlatDraft::default();
        let positive = materialize_summary_flat(
            &memo,
            &mut flat,
            F5cSummaryNodeId(4),
            Polarity::Positive,
            |_, _| {},
        )
        .unwrap();
        let negative = materialize_summary_flat(
            &memo,
            &mut flat,
            F5cSummaryNodeId(5),
            Polarity::Negative,
            |_, _| {},
        )
        .unwrap();
        assert_eq!(positive, NodeRef::Positive(PositiveId(1)));
        assert_eq!(negative, NodeRef::Negative(NegativeId(6)));
        assert_eq!(
            flat.negative_nodes,
            vec![
                NegativeNode::Variable(9),
                NegativeNode::Int,
                NegativeNode::Intersection(ChildSpan { start: 0, len: 2 }),
                NegativeNode::Variable(9),
                NegativeNode::Int,
                NegativeNode::Intersection(ChildSpan { start: 2, len: 2 }),
                NegativeNode::Function {
                    argument: PositiveId(2),
                    result: NegativeId(5)
                },
            ]
        );
        assert_eq!(
            flat.positive_nodes,
            vec![
                PositiveNode::Int,
                PositiveNode::Function {
                    argument: NegativeId(2),
                    result: PositiveId(0)
                },
                PositiveNode::Int,
            ]
        );
        assert_eq!(
            flat.negative_children,
            vec![NegativeId(0), NegativeId(1), NegativeId(3), NegativeId(4)]
        );
        let boxed_positive = memo.positive_value(F5cSummaryNodeId(4)).unwrap();
        let boxed_negative = memo.negative_value(F5cSummaryNodeId(5)).unwrap();
        assert!(
            matches!(boxed_positive, F5cPositive::Function { argument, result, .. }
            if matches!(*argument, F5cNegative::Intersection(_)) && matches!(*result, F5cPositive::Int))
        );
        assert!(
            matches!(boxed_negative, F5cNegative::Function { argument, result, .. }
            if matches!(*argument, F5cPositive::Int) && matches!(*result, F5cNegative::Intersection(_)))
        );
    }
}
