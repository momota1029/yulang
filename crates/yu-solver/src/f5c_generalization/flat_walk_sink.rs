//! Indexed candidate values for the shared F5c producer interpreter.

use super::flat_source_arena::{
    Checkpoint, FlatSourceArena, NegativeNode, NegativeRef, PositiveNode, PositiveRef,
};
use super::*;
use crate::f5c_draft::{
    ChildSpan as DraftSpan, FlatDraft, NegativeNode as DraftNegativeNode, NodeRef,
    PositiveNode as DraftPositiveNode,
};
use crate::f5c_materialization::materialize_summary_flat_checked;

#[derive(Clone, Copy)]
pub(super) enum SourceMaterializeTask {
    Enter(FlatWalkRef),
    Union(usize),
    Intersection(usize),
    PositiveFunction,
    NegativeFunction,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FlatWalkRef {
    Positive(PositiveRef),
    Negative(NegativeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct FlatWalkValue {
    pub(super) reference: FlatWalkRef,
    pub(crate) cacheable: bool,
}

#[cfg(test)]
impl FlatWalkValue {
    pub(crate) fn positive_shared_id(self) -> Option<F5cSummaryNodeId> {
        match self.reference {
            FlatWalkRef::Positive(PositiveRef::Shared(id)) => Some(id),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum CompareTask {
    Positive(PositiveRef, PositiveRef),
    Negative(NegativeRef, NegativeRef),
}

#[derive(Clone, Copy)]
pub(super) enum PromotionTask {
    Positive(PositiveRef, Option<(u32, Polarity)>),
    Negative(NegativeRef, Option<(u32, Polarity)>),
    PositiveUnion(usize, Option<(u32, Polarity)>),
    NegativeIntersection(usize, Option<(u32, Polarity)>),
    PositiveFunction(Option<(u32, Polarity)>),
    NegativeFunction(Option<(u32, Polarity)>),
}

#[derive(Default)]
pub(crate) struct F5cFlatWalkSink {
    pub(super) arena: FlatSourceArena,
    pub(super) component_checkpoint: Option<Checkpoint>,
    pub(super) counter_checkpoint: Option<(usize, usize)>,
    #[cfg(test)]
    pub(crate) promotion_observation: Option<[usize; 10]>,
}

impl F5cFlatWalkSink {
    /// Append every raw occurrence in caller order. The source arena stays live for
    /// subsequent producer work; a failed batch restores all draft append lanes.
    /// The caller owns `outputs` after return and must release its resource lane
    /// only after dropping that vector, via `release_materialized_roots`.
    pub(super) fn materialize_roots(
        &self,
        memo: &mut F5cComponentExpansionMemo,
        draft: &mut FlatDraft,
        roots: &[FlatWalkValue],
        outputs: &mut Vec<NodeRef>,
        mut mark: impl FnMut(
            &mut F5cWalkerResources,
            usize,
            u32,
            Polarity,
        ) -> Result<(), SolveAvailabilityError>,
    ) -> Result<(), SolveAvailabilityError> {
        let checkpoint = (
            draft.positive_nodes.len(),
            draft.negative_nodes.len(),
            draft.positive_children.len(),
            draft.negative_children.len(),
            draft.recursive_bounds.len(),
            draft.insertion_order.len(),
        );
        let output_checkpoint = outputs.len();
        let mut tasks = Vec::new();
        let mut values: Vec<NodeRef> = Vec::new();
        let result = (|| {
            let bad = SolveAvailabilityError::IdentityExhausted;
            macro_rules! reserve {
                ($buffer:expr, $lane:expr, $count:expr) => {{
                    let bytes = memo.retained_bytes()?;
                    memo.walker_resources
                        .reserve($buffer, $lane, $count, bytes)?;
                }};
            }
            macro_rules! task {
                ($task:expr) => {{
                    memo.work_meter.charge(1)?;
                    reserve!(&mut tasks, F5cWalkerLaneKind::FlatSourceMaterializeTasks, 1);
                    tasks.push($task);
                }};
            }
            macro_rules! value {
                ($value:expr) => {{
                    reserve!(
                        &mut values,
                        F5cWalkerLaneKind::FlatSourceMaterializeValues,
                        1
                    );
                    values.push($value);
                }};
            }
            macro_rules! positive {
                ($node:expr) => {{
                    reserve!(
                        &mut draft.positive_nodes,
                        F5cWalkerLaneKind::DraftPositiveNodes,
                        1
                    );
                    reserve!(
                        &mut draft.insertion_order,
                        F5cWalkerLaneKind::DraftInsertionOrder,
                        1
                    );
                    memo.work_meter.charge(1)?;
                    value!(NodeRef::Positive(draft.positive($node)?));
                }};
            }
            macro_rules! negative {
                ($node:expr) => {{
                    reserve!(
                        &mut draft.negative_nodes,
                        F5cWalkerLaneKind::DraftNegativeNodes,
                        1
                    );
                    reserve!(
                        &mut draft.insertion_order,
                        F5cWalkerLaneKind::DraftInsertionOrder,
                        1
                    );
                    memo.work_meter.charge(1)?;
                    value!(NodeRef::Negative(draft.negative($node)?));
                }};
            }
            // Account for an already-reserved output vector, including an empty
            // root batch where the append path would otherwise never observe it.
            reserve!(outputs, F5cWalkerLaneKind::FlatSourceMaterializeRoots, 0);
            for root in roots {
                match root.reference {
                    FlatWalkRef::Positive(PositiveRef::Shared(id)) => {
                        reserve!(outputs, F5cWalkerLaneKind::FlatSourceMaterializeRoots, 1);
                        outputs.push(materialize_summary_flat_checked(
                            memo,
                            draft,
                            id,
                            Polarity::Positive,
                            &mut mark,
                        )?);
                    }
                    FlatWalkRef::Negative(NegativeRef::Shared(id)) => {
                        reserve!(outputs, F5cWalkerLaneKind::FlatSourceMaterializeRoots, 1);
                        outputs.push(materialize_summary_flat_checked(
                            memo,
                            draft,
                            id,
                            Polarity::Negative,
                            &mut mark,
                        )?);
                    }
                    reference => {
                        task!(SourceMaterializeTask::Enter(reference));
                        while let Some(task) = tasks.pop() {
                            memo.work_meter.charge(1)?;
                            match task {
                                SourceMaterializeTask::Enter(FlatWalkRef::Positive(
                                    PositiveRef::Shared(id),
                                )) => {
                                    value!(materialize_summary_flat_checked(
                                        memo,
                                        draft,
                                        id,
                                        Polarity::Positive,
                                        &mut mark
                                    )?);
                                }
                                SourceMaterializeTask::Enter(FlatWalkRef::Negative(
                                    NegativeRef::Shared(id),
                                )) => {
                                    value!(materialize_summary_flat_checked(
                                        memo,
                                        draft,
                                        id,
                                        Polarity::Negative,
                                        &mut mark
                                    )?);
                                }
                                SourceMaterializeTask::Enter(FlatWalkRef::Positive(
                                    PositiveRef::Local(id),
                                )) => match *self.arena.positive_node(id).ok_or(bad)? {
                                    PositiveNode::Bottom => positive!(DraftPositiveNode::Bottom),
                                    PositiveNode::Int => positive!(DraftPositiveNode::Int),
                                    PositiveNode::Variable(row) => {
                                        positive!(DraftPositiveNode::Variable(row))
                                    }
                                    PositiveNode::Quantified(row) => {
                                        positive!(DraftPositiveNode::Quantified(row))
                                    }
                                    PositiveNode::Recursive(row) => {
                                        positive!(DraftPositiveNode::Recursive(row))
                                    }
                                    PositiveNode::Union(span) => {
                                        let children =
                                            self.arena.positive_children(span).ok_or(bad)?;
                                        task!(SourceMaterializeTask::Union(values.len()));
                                        for &child in children.iter().rev() {
                                            memo.work_meter.charge(1)?;
                                            task!(SourceMaterializeTask::Enter(
                                                FlatWalkRef::Positive(child)
                                            ));
                                        }
                                    }
                                    PositiveNode::Function {
                                        argument,
                                        argument_effect: F5cNegativeEffect::Empty,
                                        result_effect: F5cPositiveEffect::Bottom,
                                        result,
                                    } => {
                                        task!(SourceMaterializeTask::PositiveFunction);
                                        memo.work_meter.charge(2)?;
                                        task!(SourceMaterializeTask::Enter(FlatWalkRef::Positive(
                                            result
                                        )));
                                        task!(SourceMaterializeTask::Enter(FlatWalkRef::Negative(
                                            argument
                                        )));
                                    }
                                },
                                SourceMaterializeTask::Enter(FlatWalkRef::Negative(
                                    NegativeRef::Local(id),
                                )) => match *self.arena.negative_node(id).ok_or(bad)? {
                                    NegativeNode::Top => negative!(DraftNegativeNode::Top),
                                    NegativeNode::Bottom => negative!(DraftNegativeNode::Bottom),
                                    NegativeNode::Int => negative!(DraftNegativeNode::Int),
                                    NegativeNode::Variable(row) => {
                                        negative!(DraftNegativeNode::Variable(row))
                                    }
                                    NegativeNode::Quantified(row) => {
                                        negative!(DraftNegativeNode::Quantified(row))
                                    }
                                    NegativeNode::Recursive(row) => {
                                        negative!(DraftNegativeNode::Recursive(row))
                                    }
                                    NegativeNode::Intersection(span) => {
                                        let children =
                                            self.arena.negative_children(span).ok_or(bad)?;
                                        task!(SourceMaterializeTask::Intersection(values.len()));
                                        for &child in children.iter().rev() {
                                            memo.work_meter.charge(1)?;
                                            task!(SourceMaterializeTask::Enter(
                                                FlatWalkRef::Negative(child)
                                            ));
                                        }
                                    }
                                    NegativeNode::Function {
                                        argument,
                                        argument_effect: F5cPositiveEffect::Bottom,
                                        result_effect: F5cNegativeEffect::Empty,
                                        result,
                                    } => {
                                        task!(SourceMaterializeTask::NegativeFunction);
                                        memo.work_meter.charge(2)?;
                                        task!(SourceMaterializeTask::Enter(FlatWalkRef::Negative(
                                            result
                                        )));
                                        task!(SourceMaterializeTask::Enter(FlatWalkRef::Positive(
                                            argument
                                        )));
                                    }
                                },
                                SourceMaterializeTask::Union(start) => {
                                    let count = values.len().checked_sub(start).ok_or(bad)?;
                                    let span = DraftSpan {
                                        start: u32::try_from(draft.positive_children.len())
                                            .map_err(|_| bad)?,
                                        len: u32::try_from(count).map_err(|_| bad)?,
                                    };
                                    span.start.checked_add(span.len).ok_or(bad)?;
                                    reserve!(
                                        &mut draft.positive_children,
                                        F5cWalkerLaneKind::DraftPositiveChildren,
                                        count
                                    );
                                    memo.work_meter.charge(count)?;
                                    for item in values.drain(start..) {
                                        let NodeRef::Positive(id) = item else {
                                            return Err(bad);
                                        };
                                        draft.positive_children.push(id);
                                    }
                                    positive!(DraftPositiveNode::Union(span));
                                }
                                SourceMaterializeTask::Intersection(start) => {
                                    let count = values.len().checked_sub(start).ok_or(bad)?;
                                    let span = DraftSpan {
                                        start: u32::try_from(draft.negative_children.len())
                                            .map_err(|_| bad)?,
                                        len: u32::try_from(count).map_err(|_| bad)?,
                                    };
                                    span.start.checked_add(span.len).ok_or(bad)?;
                                    reserve!(
                                        &mut draft.negative_children,
                                        F5cWalkerLaneKind::DraftNegativeChildren,
                                        count
                                    );
                                    memo.work_meter.charge(count)?;
                                    for item in values.drain(start..) {
                                        let NodeRef::Negative(id) = item else {
                                            return Err(bad);
                                        };
                                        draft.negative_children.push(id);
                                    }
                                    negative!(DraftNegativeNode::Intersection(span));
                                }
                                SourceMaterializeTask::PositiveFunction => {
                                    let NodeRef::Positive(result) = values.pop().ok_or(bad)? else {
                                        return Err(bad);
                                    };
                                    let NodeRef::Negative(argument) = values.pop().ok_or(bad)?
                                    else {
                                        return Err(bad);
                                    };
                                    positive!(DraftPositiveNode::Function { argument, result });
                                }
                                SourceMaterializeTask::NegativeFunction => {
                                    let NodeRef::Negative(result) = values.pop().ok_or(bad)? else {
                                        return Err(bad);
                                    };
                                    let NodeRef::Positive(argument) = values.pop().ok_or(bad)?
                                    else {
                                        return Err(bad);
                                    };
                                    negative!(DraftNegativeNode::Function { argument, result });
                                }
                            }
                        }
                        if values.len() != 1 {
                            return Err(bad);
                        }
                        reserve!(outputs, F5cWalkerLaneKind::FlatSourceMaterializeRoots, 1);
                        outputs.push(values.pop().ok_or(bad)?);
                    }
                }
            }
            Ok(())
        })();
        memo.walker_resources
            .release(F5cWalkerLaneKind::FlatSourceMaterializeTasks);
        memo.walker_resources
            .release(F5cWalkerLaneKind::FlatSourceMaterializeValues);
        if result.is_err() {
            outputs.truncate(output_checkpoint);
            draft.positive_nodes.truncate(checkpoint.0);
            draft.negative_nodes.truncate(checkpoint.1);
            draft.positive_children.truncate(checkpoint.2);
            draft.negative_children.truncate(checkpoint.3);
            draft.recursive_bounds.truncate(checkpoint.4);
            draft.insertion_order.truncate(checkpoint.5);
        }
        result
    }

    /// Call after the caller drops the vector passed to `materialize_roots`.
    pub(super) fn release_materialized_roots(&self, memo: &mut F5cComponentExpansionMemo) {
        memo.walker_resources
            .release(F5cWalkerLaneKind::FlatSourceMaterializeRoots);
    }
}

#[cfg(test)]
mod materialization_tests {
    use super::*;

    #[test]
    fn mixed_occurrences_keep_order_and_batch_failure_restores_draft() {
        let mut sink = F5cFlatWalkSink::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let shared = memo
            .push_node(
                F5cSummaryNodeKind::PositiveInt,
                Some((7, Polarity::Positive)),
            )
            .unwrap();
        let memo_bytes = memo.retained_bytes().unwrap();
        let local = sink
            .arena
            .positive(
                PositiveNode::Bottom,
                &mut memo.walker_resources,
                &memo.work_meter,
                memo_bytes,
            )
            .unwrap();
        let union = sink
            .arena
            .union(
                &[
                    PositiveRef::Shared(shared),
                    local,
                    PositiveRef::Shared(shared),
                ],
                &mut memo.walker_resources,
                &memo.work_meter,
                memo_bytes,
            )
            .unwrap();
        let root = FlatWalkValue {
            reference: FlatWalkRef::Positive(union),
            cacheable: false,
        };
        let mut draft = FlatDraft::default();
        let mut outputs = Vec::new();
        let mut marks = Vec::new();
        assert!(
            sink.materialize_roots(
                &mut memo,
                &mut draft,
                &[root, root],
                &mut outputs,
                |_, _, row, p| {
                    marks.push((row, p));
                    if marks.len() == 4 {
                        Err(SolveAvailabilityError::IdentityExhausted)
                    } else {
                        Ok(())
                    }
                }
            )
            .is_err()
        );
        assert!(draft.positive_nodes.is_empty() && draft.positive_children.is_empty());
        assert!(draft.insertion_order.is_empty() && outputs.is_empty());
        marks.clear();
        sink.materialize_roots(
            &mut memo,
            &mut draft,
            &[root, root],
            &mut outputs,
            |_, _, row, p| {
                marks.push((row, p));
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(marks, vec![(7, Polarity::Positive); 4]);
        assert_ne!(outputs[0], outputs[1]);
        assert_eq!(draft.positive_children.len(), 6);
        assert!(
            sink.arena
                .positive_children(
                    match sink
                        .arena
                        .positive_node(match union {
                            PositiveRef::Local(id) => id,
                            _ => unreachable!(),
                        })
                        .unwrap()
                    {
                        PositiveNode::Union(span) => *span,
                        _ => unreachable!(),
                    }
                )
                .is_some()
        );
    }

    #[test]
    fn local_functions_preserve_both_polarities_and_source() {
        let mut sink = F5cFlatWalkSink::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let meter = &memo.work_meter;
        let resources = &mut memo.walker_resources;
        let p = sink
            .arena
            .positive(PositiveNode::Int, resources, meter, 0)
            .unwrap();
        let n = sink
            .arena
            .negative(NegativeNode::Top, resources, meter, 0)
            .unwrap();
        let p = sink.arena.union(&[p, p], resources, meter, 0).unwrap();
        let n = sink
            .arena
            .intersection(&[n, n], resources, meter, 0)
            .unwrap();
        let pf = sink
            .arena
            .positive(
                PositiveNode::Function {
                    argument: n,
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: p,
                },
                resources,
                meter,
                0,
            )
            .unwrap();
        let nf = sink
            .arena
            .negative(
                NegativeNode::Function {
                    argument: p,
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: n,
                },
                resources,
                meter,
                0,
            )
            .unwrap();
        let source_checkpoint = sink.arena.checkpoint();
        let roots = [
            FlatWalkValue {
                reference: FlatWalkRef::Positive(pf),
                cacheable: false,
            },
            FlatWalkValue {
                reference: FlatWalkRef::Negative(nf),
                cacheable: false,
            },
        ];
        let mut draft = FlatDraft::default();
        let mut outputs = Vec::new();
        sink.materialize_roots(&mut memo, &mut draft, &roots, &mut outputs, |_, _, _, _| {
            Ok(())
        })
        .unwrap();
        assert!(sink.arena.checkpoint() == source_checkpoint);
        let NodeRef::Positive(pid) = outputs[0] else {
            panic!("positive root")
        };
        let NodeRef::Negative(nid) = outputs[1] else {
            panic!("negative root")
        };
        assert!(matches!(
            draft.positive_nodes[pid.0 as usize],
            DraftPositiveNode::Function { .. }
        ));
        assert!(matches!(
            draft.negative_nodes[nid.0 as usize],
            DraftNegativeNode::Function { .. }
        ));
        assert_eq!(draft.positive_children.len(), 4);
        assert_eq!(draft.negative_children.len(), 4);
        let retained = memo.retained_bytes().unwrap();
        let source_bytes = sink.arena.positive_nodes.capacity()
            * std::mem::size_of::<PositiveNode>()
            + sink.arena.negative_nodes.capacity() * std::mem::size_of::<NegativeNode>()
            + sink.arena.positive_children.capacity() * std::mem::size_of::<PositiveRef>()
            + sink.arena.negative_children.capacity() * std::mem::size_of::<NegativeRef>();
        let draft_bytes = draft.positive_nodes.capacity()
            * std::mem::size_of::<DraftPositiveNode>()
            + draft.negative_nodes.capacity() * std::mem::size_of::<DraftNegativeNode>()
            + draft.positive_children.capacity()
                * std::mem::size_of::<crate::f5c_draft::PositiveId>()
            + draft.negative_children.capacity()
                * std::mem::size_of::<crate::f5c_draft::NegativeId>()
            + draft.insertion_order.capacity() * std::mem::size_of::<NodeRef>();
        assert!(
            memo.walker_resources.simultaneous_memo_peak_bytes
                >= retained + source_bytes + draft_bytes
        );
    }

    #[test]
    fn empty_batch_accounts_existing_output_capacity_until_release() {
        let sink = F5cFlatWalkSink::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let mut draft = FlatDraft::default();
        let mut outputs = Vec::new();
        outputs.try_reserve(8).unwrap();
        let capacity = outputs.capacity();
        sink.materialize_roots(
            &mut memo,
            &mut draft,
            &[],
            &mut outputs,
            |_, _, _, _| Ok(()),
        )
        .unwrap();
        assert_eq!(
            memo.walker_resources.lanes[F5cWalkerLaneKind::FlatSourceMaterializeRoots as usize]
                .actual_capacity,
            capacity
        );
        drop(outputs);
        sink.release_materialized_roots(&mut memo);
        assert_eq!(
            memo.walker_resources.lanes[F5cWalkerLaneKind::FlatSourceMaterializeRoots as usize]
                .actual_capacity,
            0
        );
    }
}

#[cfg(test)]
impl F5cFlatWalkSink {
    pub(crate) fn source_capacities(&self) -> [usize; 4] {
        [
            self.arena.positive_nodes.capacity(),
            self.arena.negative_nodes.capacity(),
            self.arena.positive_children.capacity(),
            self.arena.negative_children.capacity(),
        ]
    }

    pub(crate) fn arena_is_empty(&self) -> bool {
        let checkpoint = self.arena.checkpoint();
        let empty = FlatSourceArena::default().checkpoint();
        checkpoint == empty
    }

    pub(crate) fn local_positive_is(&self, value: FlatWalkValue, int: bool) -> bool {
        let FlatWalkRef::Positive(PositiveRef::Local(id)) = value.reference else {
            return false;
        };
        matches!(
            self.arena.positive_node(id),
            Some(PositiveNode::Int) if int
        ) || matches!(
            self.arena.positive_node(id),
            Some(PositiveNode::Bottom) if !int
        )
    }
}

impl F5cFlatWalkSink {
    fn positive(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        node: PositiveNode,
        cacheable: bool,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        let memo_bytes = generalizer.memo.retained_bytes()?;
        let reference = self.arena.positive(
            node,
            &mut generalizer.memo.walker_resources,
            &generalizer.memo.work_meter,
            memo_bytes,
        )?;
        Ok(FlatWalkValue {
            reference: FlatWalkRef::Positive(reference),
            cacheable,
        })
    }

    fn negative(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        node: NegativeNode,
        cacheable: bool,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        let memo_bytes = generalizer.memo.retained_bytes()?;
        let reference = self.arena.negative(
            node,
            &mut generalizer.memo.walker_resources,
            &generalizer.memo.work_meter,
            memo_bytes,
        )?;
        Ok(FlatWalkValue {
            reference: FlatWalkRef::Negative(reference),
            cacheable,
        })
    }

    fn equal(
        &self,
        generalizer: &mut F5cGeneralizer<'_>,
        first: CompareTask,
        tasks: &mut Vec<CompareTask>,
    ) -> Result<bool, SolveAvailabilityError> {
        tasks.clear();
        macro_rules! push {
            ($task:expr) => {{
                generalizer.memo.work_meter.charge(1)?;
                generalizer
                    .memo
                    .reserve_walker(tasks, F5cWalkerLaneKind::FlatComparison)?;
                tasks.push($task);
            }};
        }
        push!(first);
        while let Some(task) = tasks.pop() {
            generalizer.memo.work_meter.charge(1)?;
            match task {
                CompareTask::Positive(left, right) => match (left, right) {
                    (PositiveRef::Shared(a), PositiveRef::Shared(b)) if a == b => {}
                    (PositiveRef::Local(a), PositiveRef::Local(b)) => {
                        let a = *self
                            .arena
                            .positive_node(a)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let b = *self
                            .arena
                            .positive_node(b)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        match (a, b) {
                            (PositiveNode::Bottom, PositiveNode::Bottom)
                            | (PositiveNode::Int, PositiveNode::Int) => {}
                            (PositiveNode::Variable(a), PositiveNode::Variable(b))
                            | (PositiveNode::Quantified(a), PositiveNode::Quantified(b))
                            | (PositiveNode::Recursive(a), PositiveNode::Recursive(b))
                                if a == b => {}
                            (PositiveNode::Union(a), PositiveNode::Union(b)) => {
                                let a = self
                                    .arena
                                    .positive_children(a)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                let b = self
                                    .arena
                                    .positive_children(b)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                if a.len() != b.len() {
                                    return Ok(false);
                                }
                                for (&a, &b) in a.iter().zip(b).rev() {
                                    generalizer.memo.work_meter.charge(1)?;
                                    push!(CompareTask::Positive(a, b));
                                }
                            }
                            (
                                PositiveNode::Function {
                                    argument: aa,
                                    argument_effect: ae,
                                    result_effect: ar,
                                    result: av,
                                },
                                PositiveNode::Function {
                                    argument: ba,
                                    argument_effect: be,
                                    result_effect: br,
                                    result: bv,
                                },
                            ) if ae == be && ar == br => {
                                generalizer.memo.work_meter.charge(2)?;
                                push!(CompareTask::Positive(av, bv));
                                push!(CompareTask::Negative(aa, ba));
                            }
                            _ => return Ok(false),
                        }
                    }
                    _ => return Ok(false),
                },
                CompareTask::Negative(left, right) => match (left, right) {
                    (NegativeRef::Shared(a), NegativeRef::Shared(b)) if a == b => {}
                    (NegativeRef::Local(a), NegativeRef::Local(b)) => {
                        let a = *self
                            .arena
                            .negative_node(a)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let b = *self
                            .arena
                            .negative_node(b)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        match (a, b) {
                            (NegativeNode::Top, NegativeNode::Top)
                            | (NegativeNode::Bottom, NegativeNode::Bottom)
                            | (NegativeNode::Int, NegativeNode::Int) => {}
                            (NegativeNode::Variable(a), NegativeNode::Variable(b))
                            | (NegativeNode::Quantified(a), NegativeNode::Quantified(b))
                            | (NegativeNode::Recursive(a), NegativeNode::Recursive(b))
                                if a == b => {}
                            (NegativeNode::Intersection(a), NegativeNode::Intersection(b)) => {
                                let a = self
                                    .arena
                                    .negative_children(a)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                let b = self
                                    .arena
                                    .negative_children(b)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                if a.len() != b.len() {
                                    return Ok(false);
                                }
                                for (&a, &b) in a.iter().zip(b).rev() {
                                    generalizer.memo.work_meter.charge(1)?;
                                    push!(CompareTask::Negative(a, b));
                                }
                            }
                            (
                                NegativeNode::Function {
                                    argument: aa,
                                    argument_effect: ae,
                                    result_effect: ar,
                                    result: av,
                                },
                                NegativeNode::Function {
                                    argument: ba,
                                    argument_effect: be,
                                    result_effect: br,
                                    result: bv,
                                },
                            ) if ae == be && ar == br => {
                                generalizer.memo.work_meter.charge(2)?;
                                push!(CompareTask::Negative(av, bv));
                                push!(CompareTask::Positive(aa, ba));
                            }
                            _ => return Ok(false),
                        }
                    }
                    _ => return Ok(false),
                },
            }
        }
        Ok(true)
    }

    fn promote_value(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        value: FlatWalkRef,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        let mut tasks = Vec::new();
        let mut ids = Vec::new();
        macro_rules! push_task {
            ($task:expr) => {{
                generalizer.memo.work_meter.charge(1)?;
                generalizer
                    .memo
                    .reserve_walker(&mut tasks, F5cWalkerLaneKind::FlatPromotionTasks)?;
                tasks.push($task);
            }};
        }
        macro_rules! push_id {
            ($id:expr) => {{
                generalizer.memo.work_meter.charge(1)?;
                generalizer
                    .memo
                    .reserve_walker(&mut ids, F5cWalkerLaneKind::FlatPromotionIds)?;
                ids.push($id);
            }};
        }
        let incidence = Some((row, polarity));
        let result = (|| {
            push_task!(match value {
                FlatWalkRef::Positive(reference) => PromotionTask::Positive(reference, incidence),
                FlatWalkRef::Negative(reference) => PromotionTask::Negative(reference, incidence),
            });
            while let Some(task) = tasks.pop() {
                generalizer.memo.work_meter.charge(1)?;
                match task {
                    PromotionTask::Positive(PositiveRef::Shared(id), incidence) => {
                        if let Some(incidence) = incidence {
                            let (start, _) = generalizer.memo.push_children(&[id])?;
                            push_id!(generalizer.memo.push_node(
                                F5cSummaryNodeKind::PositiveAlias { start },
                                Some(incidence)
                            )?);
                        } else {
                            push_id!(id);
                        }
                    }
                    PromotionTask::Negative(NegativeRef::Shared(id), incidence) => {
                        if let Some(incidence) = incidence {
                            let (start, _) = generalizer.memo.push_children(&[id])?;
                            push_id!(generalizer.memo.push_node(
                                F5cSummaryNodeKind::NegativeAlias { start },
                                Some(incidence)
                            )?);
                        } else {
                            push_id!(id);
                        }
                    }
                    PromotionTask::Positive(PositiveRef::Local(id), incidence) => {
                        let node = *self
                            .arena
                            .positive_node(id)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        match node {
                            PositiveNode::Bottom => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::PositiveBottom, incidence)?
                            ),
                            PositiveNode::Int => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::PositiveInt, incidence)?
                            ),
                            PositiveNode::Variable(row) => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::PositiveRow(row), incidence)?
                            ),
                            PositiveNode::Union(span) => {
                                let children = self
                                    .arena
                                    .positive_children(span)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                push_task!(PromotionTask::PositiveUnion(ids.len(), incidence));
                                for &child in children.iter().rev() {
                                    generalizer.memo.work_meter.charge(1)?;
                                    push_task!(PromotionTask::Positive(child, None));
                                }
                            }
                            PositiveNode::Function {
                                argument,
                                argument_effect: F5cNegativeEffect::Empty,
                                result_effect: F5cPositiveEffect::Bottom,
                                result,
                            } => {
                                push_task!(PromotionTask::PositiveFunction(incidence));
                                generalizer.memo.work_meter.charge(2)?;
                                push_task!(PromotionTask::Positive(result, None));
                                push_task!(PromotionTask::Negative(argument, None));
                            }
                            _ => return Err(SolveAvailabilityError::IdentityExhausted),
                        }
                    }
                    PromotionTask::Negative(NegativeRef::Local(id), incidence) => {
                        let node = *self
                            .arena
                            .negative_node(id)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        match node {
                            NegativeNode::Top => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::NegativeTop, incidence)?
                            ),
                            NegativeNode::Bottom => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::NegativeBottom, incidence)?
                            ),
                            NegativeNode::Int => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::NegativeInt, incidence)?
                            ),
                            NegativeNode::Variable(row) => push_id!(
                                generalizer
                                    .memo
                                    .push_node(F5cSummaryNodeKind::NegativeRow(row), incidence)?
                            ),
                            NegativeNode::Intersection(span) => {
                                let children = self
                                    .arena
                                    .negative_children(span)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                push_task!(PromotionTask::NegativeIntersection(
                                    ids.len(),
                                    incidence
                                ));
                                for &child in children.iter().rev() {
                                    generalizer.memo.work_meter.charge(1)?;
                                    push_task!(PromotionTask::Negative(child, None));
                                }
                            }
                            NegativeNode::Function {
                                argument,
                                argument_effect: F5cPositiveEffect::Bottom,
                                result_effect: F5cNegativeEffect::Empty,
                                result,
                            } => {
                                push_task!(PromotionTask::NegativeFunction(incidence));
                                generalizer.memo.work_meter.charge(2)?;
                                push_task!(PromotionTask::Negative(result, None));
                                push_task!(PromotionTask::Positive(argument, None));
                            }
                            _ => return Err(SolveAvailabilityError::IdentityExhausted),
                        }
                    }
                    PromotionTask::PositiveUnion(start, incidence) => {
                        let (child_start, len) = generalizer.memo.push_children(&ids[start..])?;
                        ids.truncate(start);
                        push_id!(generalizer.memo.push_node(
                            F5cSummaryNodeKind::PositiveUnion {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    PromotionTask::NegativeIntersection(start, incidence) => {
                        let (child_start, len) = generalizer.memo.push_children(&ids[start..])?;
                        ids.truncate(start);
                        push_id!(generalizer.memo.push_node(
                            F5cSummaryNodeKind::NegativeIntersection {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    PromotionTask::PositiveFunction(incidence) => {
                        let result = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let argument =
                            ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        push_id!(generalizer.memo.push_node(
                            F5cSummaryNodeKind::PositiveFunction { argument, result },
                            incidence
                        )?);
                    }
                    PromotionTask::NegativeFunction(incidence) => {
                        let result = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let argument =
                            ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        push_id!(generalizer.memo.push_node(
                            F5cSummaryNodeKind::NegativeFunction { argument, result },
                            incidence
                        )?);
                    }
                }
            }
            if ids.len() != 1 {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)
        })();
        // Memo nodes may grow while both promotion work lanes are still live.
        let observation = generalizer.memo.observe_walker();
        #[cfg(test)]
        {
            self.record_promotion_observation(generalizer, &tasks, &ids);
        }
        drop(tasks);
        drop(ids);
        generalizer
            .memo
            .walker_resources
            .release(F5cWalkerLaneKind::FlatPromotionTasks);
        generalizer
            .memo
            .walker_resources
            .release(F5cWalkerLaneKind::FlatPromotionIds);
        match result {
            Ok(id) => observation.map(|()| id),
            Err(error) => Err(error),
        }
    }
}

#[cfg(test)]
impl F5cFlatWalkSink {
    fn record_promotion_observation(
        &mut self,
        generalizer: &F5cGeneralizer<'_>,
        tasks: &Vec<PromotionTask>,
        ids: &Vec<F5cSummaryNodeId>,
    ) {
        let memo = &generalizer.memo;
        let capacities = [
            memo.nodes.capacity() * std::mem::size_of::<F5cSummaryNode>(),
            memo.children.capacity() * std::mem::size_of::<F5cSummaryNodeId>(),
            memo.reverse_parents.capacity() * std::mem::size_of::<F5cReverseParentEdge>(),
            memo.incidences.capacity() * std::mem::size_of::<F5cIncidenceEdge>(),
            self.arena.positive_nodes.capacity() * std::mem::size_of::<PositiveNode>(),
            self.arena.negative_nodes.capacity() * std::mem::size_of::<NegativeNode>(),
            self.arena.positive_children.capacity() * std::mem::size_of::<PositiveRef>(),
            self.arena.negative_children.capacity() * std::mem::size_of::<NegativeRef>(),
            tasks.capacity() * std::mem::size_of::<PromotionTask>(),
            ids.capacity() * std::mem::size_of::<F5cSummaryNodeId>(),
        ];
        if self
            .promotion_observation
            .is_none_or(|old| old.iter().sum::<usize>() < capacities.iter().sum())
        {
            self.promotion_observation = Some(capacities);
        }
    }
}

impl F5cWalkSink for F5cFlatWalkSink {
    type Value = FlatWalkValue;

    fn variable(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
        row: u32,
        cacheable: bool,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        match polarity {
            Polarity::Positive => {
                self.positive(generalizer, PositiveNode::Variable(row), cacheable)
            }
            Polarity::Negative => {
                self.negative(generalizer, NegativeNode::Variable(row), cacheable)
            }
        }
    }

    fn shared(
        &mut self,
        _generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
        id: F5cSummaryNodeId,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        Ok(FlatWalkValue {
            reference: match polarity {
                Polarity::Positive => FlatWalkRef::Positive(PositiveRef::Shared(id)),
                Polarity::Negative => FlatWalkRef::Negative(NegativeRef::Shared(id)),
            },
            cacheable: true,
        })
    }

    fn int(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        match polarity {
            Polarity::Positive => self.positive(generalizer, PositiveNode::Int, true),
            Polarity::Negative => self.negative(generalizer, NegativeNode::Int, true),
        }
    }

    fn bottom(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        match polarity {
            Polarity::Positive => self.positive(generalizer, PositiveNode::Bottom, true),
            Polarity::Negative => self.negative(generalizer, NegativeNode::Bottom, true),
        }
    }

    fn top(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        self.negative(generalizer, NegativeNode::Top, true)
    }

    fn cacheable(&self, value: &Self::Value) -> bool {
        value.cacheable
    }

    fn finish_row(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        values: &mut Vec<Self::Value>,
        start: usize,
        row: u32,
        polarity: Polarity,
        root: bool,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        let result = match polarity {
            Polarity::Positive => {
                let mut parts = Vec::new();
                let mut comparisons = Vec::new();
                let mut cacheable = true;
                let result = (|| {
                    for child in values.drain(start..) {
                        let FlatWalkRef::Positive(reference) = child.reference else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let mut duplicate = false;
                        for &previous in &parts {
                            generalizer.memo.work_meter.charge(1)?;
                            let equal = self.equal(
                                generalizer,
                                CompareTask::Positive(previous, reference),
                                &mut comparisons,
                            )?;
                            if equal {
                                duplicate = true;
                                break;
                            }
                        }
                        if !duplicate {
                            cacheable &= child.cacheable;
                            generalizer
                                .memo
                                .reserve_walker(&mut parts, F5cWalkerLaneKind::FlatPositiveParts)?;
                            parts.push(reference);
                        }
                    }
                    let nonempty = !parts.is_empty();
                    match parts.len() {
                        0 if root => self.positive(generalizer, PositiveNode::Bottom, true),
                        0 => self.positive(generalizer, PositiveNode::Variable(row), false),
                        1 => Ok(FlatWalkValue {
                            reference: FlatWalkRef::Positive(parts[0]),
                            cacheable: cacheable && nonempty,
                        }),
                        _ => {
                            let memo_bytes = generalizer.memo.retained_bytes()?;
                            let reference = self.arena.union(
                                &parts,
                                &mut generalizer.memo.walker_resources,
                                &generalizer.memo.work_meter,
                                memo_bytes,
                            )?;
                            Ok(FlatWalkValue {
                                reference: FlatWalkRef::Positive(reference),
                                cacheable,
                            })
                        }
                    }
                })();
                drop(comparisons);
                drop(parts);
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatComparison);
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatPositiveParts);
                result
            }
            Polarity::Negative => {
                let mut parts = Vec::new();
                let mut comparisons = Vec::new();
                let mut cacheable = true;
                let result = (|| {
                    for child in values.drain(start..) {
                        let FlatWalkRef::Negative(reference) = child.reference else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let mut duplicate = false;
                        for &previous in &parts {
                            generalizer.memo.work_meter.charge(1)?;
                            let equal = self.equal(
                                generalizer,
                                CompareTask::Negative(previous, reference),
                                &mut comparisons,
                            )?;
                            if equal {
                                duplicate = true;
                                break;
                            }
                        }
                        if !duplicate {
                            cacheable &= child.cacheable;
                            generalizer
                                .memo
                                .reserve_walker(&mut parts, F5cWalkerLaneKind::FlatNegativeParts)?;
                            parts.push(reference);
                        }
                    }
                    let nonempty = !parts.is_empty();
                    match parts.len() {
                        0 => self.negative(generalizer, NegativeNode::Variable(row), false),
                        1 => Ok(FlatWalkValue {
                            reference: FlatWalkRef::Negative(parts[0]),
                            cacheable: cacheable && nonempty,
                        }),
                        _ => {
                            let memo_bytes = generalizer.memo.retained_bytes()?;
                            let reference = self.arena.intersection(
                                &parts,
                                &mut generalizer.memo.walker_resources,
                                &generalizer.memo.work_meter,
                                memo_bytes,
                            )?;
                            Ok(FlatWalkValue {
                                reference: FlatWalkRef::Negative(reference),
                                cacheable,
                            })
                        }
                    }
                })();
                drop(comparisons);
                drop(parts);
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatComparison);
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatNegativeParts);
                result
            }
        };
        result
    }

    fn function(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        polarity: Polarity,
        argument: Self::Value,
        result: Self::Value,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        let cacheable = argument.cacheable && result.cacheable;
        match (polarity, argument.reference, result.reference) {
            (
                Polarity::Positive,
                FlatWalkRef::Negative(argument),
                FlatWalkRef::Positive(result),
            ) => self.positive(
                generalizer,
                PositiveNode::Function {
                    argument,
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result,
                },
                cacheable,
            ),
            (
                Polarity::Negative,
                FlatWalkRef::Positive(argument),
                FlatWalkRef::Negative(result),
            ) => self.negative(
                generalizer,
                NegativeNode::Function {
                    argument,
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result,
                },
                cacheable,
            ),
            _ => Err(SolveAvailabilityError::IdentityExhausted),
        }
    }

    fn promote(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_>,
        value: &Self::Value,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.promote_value(generalizer, value.reference, row, polarity)
    }
}
