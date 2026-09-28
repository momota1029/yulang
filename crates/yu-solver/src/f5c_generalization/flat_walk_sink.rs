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

fn checked_output_root_count(
    existing: usize,
    additional: usize,
) -> Result<u32, SolveAvailabilityError> {
    let count = existing
        .checked_add(additional)
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    u32::try_from(count).map_err(|_| SolveAvailabilityError::IdentityExhausted)
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
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        mut outputs_owner: Option<&mut RawWalkerOwner<'_>>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        source_meter: Option<&DraftHeapMeter>,
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
            draft.structural_census()?.1,
        );
        let output_checkpoint = outputs.len();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut tasks_owner = source_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::FlatSourceMaterializeTasks as usize,
            F5cWalkerLaneKind::FlatSourceMaterializeTasks.slot_size()));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut values_owner = source_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::FlatSourceMaterializeValues as usize,
            F5cWalkerLaneKind::FlatSourceMaterializeValues.slot_size()));
        let mut tasks = Vec::new();
        let mut values: Vec<NodeRef> = Vec::new();
        let result = (|| {
            let bad = SolveAvailabilityError::IdentityExhausted;
            checked_output_root_count(outputs.len(), roots.len())?;
            macro_rules! reserve {
                ($buffer:expr, $lane:expr, $count:expr) => {{
                    let count = $count;
                    let bytes = memo.retained_bytes()?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let old_capacity = ($buffer).capacity();
                    let reservation = memo.walker_resources
                        .reserve($buffer, $lane, count, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    {
                        let lane = $lane as usize;
                        let index = match lane {
                            x if x == F5cWalkerLaneKind::DraftPositiveNodes as usize => 0,
                            x if x == F5cWalkerLaneKind::DraftNegativeNodes as usize => 1,
                            x if x == F5cWalkerLaneKind::DraftPositiveChildren as usize => 2,
                            x if x == F5cWalkerLaneKind::DraftNegativeChildren as usize => 3,
                            x if x == F5cWalkerLaneKind::DraftRecursiveBounds as usize => 4,
                            _ => 5,
                        };
                        let requested = match index {
                            0 => draft.positive_nodes.len(), 1 => draft.negative_nodes.len(),
                            2 => draft.positive_children.len(), 3 => draft.negative_children.len(),
                            4 => draft.recursive_bounds.len(), _ => draft.insertion_order.len(),
                        }.saturating_add(count);
                        draft.observe_owner(index, requested);
                    }
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    memo.observe_walker_capacity_change_with_source(
                        source_meter, old_capacity, ($buffer).capacity())?;
                    reservation?;
                }};
            }
            macro_rules! reserve_output {
                ($count:expr) => {{
                    let count = $count;
                    let bytes = memo.retained_bytes()?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let old_capacity = outputs.capacity();
                    let reservation = memo.walker_resources.reserve(
                        outputs, F5cWalkerLaneKind::FlatSourceMaterializeRoots, count, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = outputs_owner.as_deref_mut() {
                        owner.observe(outputs.len(), outputs.capacity());
                    }
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    memo.observe_walker_capacity_change_with_source(
                        source_meter, old_capacity, outputs.capacity())?;
                    reservation?;
                }};
            }
            macro_rules! task {
                ($task:expr) => {{
                    memo.work_meter.charge(1)?;
                    let bytes = memo.retained_bytes()?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let old_capacity = tasks.capacity();
                    let reservation = memo.walker_resources.reserve(
                        &mut tasks, F5cWalkerLaneKind::FlatSourceMaterializeTasks, 1, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = tasks_owner.as_mut() {
                        owner.observe(tasks.len(), tasks.capacity());
                    }
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    memo.observe_walker_capacity_change_with_source(
                        source_meter, old_capacity, tasks.capacity())?;
                    reservation?;
                    tasks.push($task);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = tasks_owner.as_mut() {
                        owner.observe(tasks.len(), tasks.capacity());
                    }
                }};
            }
            macro_rules! value {
                ($value:expr) => {{
                    let bytes = memo.retained_bytes()?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let old_capacity = values.capacity();
                    let reservation = memo.walker_resources.reserve(
                        &mut values, F5cWalkerLaneKind::FlatSourceMaterializeValues, 1, bytes);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = values_owner.as_mut() {
                        owner.observe(values.len(), values.capacity());
                    }
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    memo.observe_walker_capacity_change_with_source(
                        source_meter, old_capacity, values.capacity())?;
                    reservation?;
                    values.push($value);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = values_owner.as_mut() { owner.observe(values.len(), values.capacity()); }
                }};
            }
            macro_rules! positive {
                ($node:expr) => {{
                    let node = $node;
                    draft.admit_positive_node(node)?;
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
                    value!(NodeRef::Positive(draft.positive(node)?));
                }};
            }
            macro_rules! negative {
                ($node:expr) => {{
                    let node = $node;
                    draft.admit_negative_node(node)?;
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
                    value!(NodeRef::Negative(draft.negative(node)?));
                }};
            }
            macro_rules! pop_value {
                () => {{
                    let value = values.pop().ok_or(bad)?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    if let Some(owner) = values_owner.as_mut() { owner.observe(values.len(), values.capacity()); }
                    value
                }};
            }
            // Account for an already-reserved output vector, including an empty
            // root batch where the append path would otherwise never observe it.
            reserve_output!(0);
            for root in roots {
                match root.reference {
                    FlatWalkRef::Positive(PositiveRef::Shared(id)) => {
                        reserve_output!(1);
                        outputs.push(materialize_summary_flat_checked(
                            memo,
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            source_meter,
                            draft,
                            id,
                            Polarity::Positive,
                            &mut mark,
                        )?);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = outputs_owner.as_deref_mut() { owner.observe(outputs.len(), outputs.capacity()); }
                    }
                    FlatWalkRef::Negative(NegativeRef::Shared(id)) => {
                        reserve_output!(1);
                        outputs.push(materialize_summary_flat_checked(
                            memo,
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            source_meter,
                            draft,
                            id,
                            Polarity::Negative,
                            &mut mark,
                        )?);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = outputs_owner.as_deref_mut() { owner.observe(outputs.len(), outputs.capacity()); }
                    }
                    reference => {
                        task!(SourceMaterializeTask::Enter(reference));
                        while let Some(task) = tasks.pop() {
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            if let Some(owner) = tasks_owner.as_mut() { owner.observe(tasks.len(), tasks.capacity()); }
                            memo.work_meter.charge(1)?;
                            match task {
                                SourceMaterializeTask::Enter(FlatWalkRef::Positive(
                                    PositiveRef::Shared(id),
                                )) => {
                                    value!(materialize_summary_flat_checked(
                                        memo,
                                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                                        source_meter,
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
                                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                                        source_meter,
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
                                    draft.admit_child_entries(count)?;
                                    draft.admit_logical_incidences(count)?;
                                    reserve!(
                                        &mut draft.positive_children,
                                        F5cWalkerLaneKind::DraftPositiveChildren,
                                        count
                                    );
                                    memo.work_meter.charge(count)?;
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    let capacity = values.capacity();
                                    let drained = values.drain(start..);
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    if let Some(owner) = values_owner.as_mut() { owner.observe(start, capacity); }
                                    for item in drained {
                                        let NodeRef::Positive(id) = item else {
                                            return Err(bad);
                                        };
                                        draft.push_reserved_positive_child(id);
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
                                    draft.admit_child_entries(count)?;
                                    draft.admit_logical_incidences(count)?;
                                    reserve!(
                                        &mut draft.negative_children,
                                        F5cWalkerLaneKind::DraftNegativeChildren,
                                        count
                                    );
                                    memo.work_meter.charge(count)?;
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    let capacity = values.capacity();
                                    let drained = values.drain(start..);
                                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                                    if let Some(owner) = values_owner.as_mut() { owner.observe(start, capacity); }
                                    for item in drained {
                                        let NodeRef::Negative(id) = item else {
                                            return Err(bad);
                                        };
                                        draft.push_reserved_negative_child(id);
                                    }
                                    negative!(DraftNegativeNode::Intersection(span));
                                }
                                SourceMaterializeTask::PositiveFunction => {
                                    let NodeRef::Positive(result) = pop_value!() else {
                                        return Err(bad);
                                    };
                                    let NodeRef::Negative(argument) = pop_value!()
                                    else {
                                        return Err(bad);
                                    };
                                    positive!(DraftPositiveNode::Function { argument, result });
                                }
                                SourceMaterializeTask::NegativeFunction => {
                                    let NodeRef::Negative(result) = pop_value!() else {
                                        return Err(bad);
                                    };
                                    let NodeRef::Positive(argument) = pop_value!()
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
                        reserve_output!(1);
                        outputs.push(pop_value!());
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = outputs_owner.as_deref_mut() { owner.observe(outputs.len(), outputs.capacity()); }
                    }
                }
            }
            Ok(())
        })();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let had_scratch_capacity = tasks.capacity() != 0 || values.capacity() != 0;
        drop(tasks);
        drop(values);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            drop(tasks_owner);
            drop(values_owner);
        }
        memo.walker_resources
            .release(F5cWalkerLaneKind::FlatSourceMaterializeTasks);
        memo.walker_resources
            .release(F5cWalkerLaneKind::FlatSourceMaterializeValues);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let release_sample = if had_scratch_capacity {
            source_meter.map(|meter| memo.observe_walker_with_source(meter))
                .transpose().map(|_| ())
        } else {
            Ok(())
        };
        if result.is_err() {
            outputs.truncate(output_checkpoint);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if let Some(owner) = outputs_owner.as_deref_mut() { owner.observe(outputs.len(), outputs.capacity()); }
            draft.positive_nodes.truncate(checkpoint.0);
            draft.negative_nodes.truncate(checkpoint.1);
            draft.positive_children.truncate(checkpoint.2);
            draft.negative_children.truncate(checkpoint.3);
            draft.recursive_bounds.truncate(checkpoint.4);
            draft.insertion_order.truncate(checkpoint.5);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            draft.sync_owners();
            draft.restore_structural_census(checkpoint.6);
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        release_sample?;
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

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn local_materialization_scratch_events_use_run_component() {
        let path = std::env::temp_dir().join(format!(
            "f5c-local-materialize-{}-{:?}.bin",
            std::process::id(), std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        meter.set_event_component(19);
        let mut sink = F5cFlatWalkSink::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let node = sink.arena.positive(PositiveNode::Int, None,
            &mut memo.walker_resources, &memo.work_meter, 0).unwrap();
        let root = FlatWalkValue {
            reference: FlatWalkRef::Positive(node), cacheable: true,
        };
        let mut draft = FlatDraft::default();
        let mut outputs = Vec::new();
        sink.materialize_roots(&mut memo, &mut draft, &[root], &mut outputs,
            None, Some(&meter), |_, _, _, _| Ok(())).unwrap();
        drop(outputs);
        sink.release_materialized_roots(&mut memo);
        crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        for lane in [F5cWalkerLaneKind::FlatSourceMaterializeTasks,
            F5cWalkerLaneKind::FlatSourceMaterializeValues]
        {
            let lane_events: Vec<_> = events.iter()
                .filter(|event| event[3] == 32 + lane as u64).collect();
            assert!(!lane_events.is_empty());
            assert!(lane_events.iter().all(|event| event[0] == 19));
            assert_eq!(lane_events.first().unwrap()[2], 1);
            assert_eq!(lane_events.last().unwrap()[2], 5);
            assert!(lane_events.iter().any(|event| event[2] == 3));
            assert!(lane_events.iter().any(|event| event[2] == 2));
        }
    }

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn output_owner_records_each_growth_and_releases_after_drop() {
        let path = std::env::temp_dir().join(format!(
            "f5c-materialize-output-{}-{:?}.bin",
            std::process::id(), std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        meter.set_event_component(19);
        let sink = F5cFlatWalkSink::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let shared = memo.push_node(F5cSummaryNodeKind::PositiveInt, None).unwrap();
        let root = FlatWalkValue {
            reference: FlatWalkRef::Positive(PositiveRef::Shared(shared)),
            cacheable: true,
        };
        let mut draft = FlatDraft::default();
        let mut owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::FlatSourceMaterializeRoots as usize,
            F5cWalkerLaneKind::FlatSourceMaterializeRoots.slot_size());
        let mut outputs = Vec::new();
        sink.materialize_roots(&mut memo, &mut draft, &[root; 5], &mut outputs,
            Some(&mut owner), Some(&meter), |_, _, _, _| Ok(())).unwrap();
        assert_eq!(outputs.len(), 5);
        drop(outputs);
        drop(owner);
        sink.release_materialized_roots(&mut memo);
        let _ = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let role = 32 + F5cWalkerLaneKind::FlatSourceMaterializeRoots as u64;
        let all_events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).collect();
        let events: Vec<_> = all_events.iter().filter(|event| event[3] == role).collect();
        assert_eq!(events.iter().filter(|event| event[2] != 2)
            .map(|event| event[2]).collect::<Vec<_>>(), [1, 3, 3, 5]);
        assert!(events.iter().all(|event| event[1] == events[0][1]));
        assert!(events.iter().filter(|event| event[2] == 3).map(|event| event[5])
            .collect::<Vec<_>>().windows(2).all(|pair| pair[1] > pair[0]));
        for lane in [F5cWalkerLaneKind::FlatMaterializeTasks,
            F5cWalkerLaneKind::FlatMaterializeValues]
        {
            let lane_events: Vec<_> = all_events.iter()
                .filter(|event| event[3] == 32 + lane as u64).collect();
            assert!(!lane_events.is_empty());
            assert!(lane_events.iter().all(|event| event[0] == 19));
            assert_eq!(lane_events.first().unwrap()[2], 1);
            assert_eq!(lane_events.last().unwrap()[2], 5);
        }
    }

    #[cfg(feature = "f5c_resource_probe")]
    #[test]
    fn output_owner_releases_capacity_after_failed_batch() {
        let path = std::env::temp_dir().join(format!(
            "f5c-materialize-failure-{}-{:?}.bin",
            std::process::id(), std::thread::current().id()));
        crate::f5c_draft_heap::open_f5c_resource_events(&path).unwrap();
        let meter = DraftHeapMeter::default();
        let sink = F5cFlatWalkSink::default();
        let mut memo = F5cComponentExpansionMemo::default();
        let shared = memo.push_node(
            F5cSummaryNodeKind::PositiveInt, Some((7, Polarity::Positive))).unwrap();
        let root = FlatWalkValue {
            reference: FlatWalkRef::Positive(PositiveRef::Shared(shared)),
            cacheable: true,
        };
        let mut draft = FlatDraft::default();
        let mut owner = RawWalkerOwner::new(&meter,
            F5cWalkerLaneKind::FlatSourceMaterializeRoots as usize,
            F5cWalkerLaneKind::FlatSourceMaterializeRoots.slot_size());
        let mut outputs = Vec::new();
        let mut marks = 0;
        let result = sink.materialize_roots(&mut memo, &mut draft, &[root; 5],
            &mut outputs, Some(&mut owner), Some(&meter), |_, _, _, _| {
                marks += 1;
                if marks == 5 { Err(SolveAvailabilityError::IdentityExhausted) }
                else { Ok(()) }
            });
        assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
        assert!(outputs.is_empty());
        drop(outputs);
        drop(owner);
        sink.release_materialized_roots(&mut memo);
        let _ = crate::f5c_draft_heap::close_f5c_resource_events().unwrap();
        let bytes = std::fs::read(&path).unwrap();
        std::fs::remove_file(path).unwrap();
        let role = 32 + F5cWalkerLaneKind::FlatSourceMaterializeRoots as u64;
        let events: Vec<[u64; 8]> = bytes[8..].chunks_exact(64).map(|event| {
            std::array::from_fn(|index| u64::from_le_bytes(
                event[index * 8..(index + 1) * 8].try_into().unwrap()))
        }).filter(|event| event[3] == role).collect();
        assert_eq!(events.iter().map(|event| event[2]).collect::<Vec<_>>(),
            [1, 3, 3, 5]);
        assert!(events.iter().all(|event| event[1] == events[0][1]));
        assert!(events[1][5] > 0);
    }

    #[test]
    fn output_root_count_rejects_unrepresentable_sum() {
        assert_eq!(checked_output_root_count(0, 0), Ok(0));
        assert_eq!(checked_output_root_count(1, 2), Ok(3));
        assert_eq!(
            checked_output_root_count(0, u32::MAX as usize),
            Ok(u32::MAX)
        );
        assert_eq!(
            checked_output_root_count(1, u32::MAX as usize),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
        assert_eq!(
            checked_output_root_count(usize::MAX, 1),
            Err(SolveAvailabilityError::IdentityExhausted)
        );
    }

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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
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
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
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
            .positive(PositiveNode::Int,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None, resources, meter, 0)
            .unwrap();
        let n = sink
            .arena
            .negative(NegativeNode::Top,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None, resources, meter, 0)
            .unwrap();
        let p = sink.arena.union(&[p, p],
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None, resources, meter, 0).unwrap();
        let n = sink
            .arena
            .intersection(&[n, n],
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None, resources, meter, 0)
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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                None,
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
        sink.materialize_roots(
            &mut memo,
            &mut draft,
            &roots,
            &mut outputs,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            |_, _, _, _| {
                Ok(())
            },
        )
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
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            None,
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
        generalizer: &mut F5cGeneralizer<'_, '_>,
        node: PositiveNode,
        cacheable: bool,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        let memo_bytes = generalizer.memo.retained_bytes()?;
        let reference = self.arena.positive(
            node,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(&mut generalizer.source_arena_owners[0]),
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
        generalizer: &mut F5cGeneralizer<'_, '_>,
        node: NegativeNode,
        cacheable: bool,
    ) -> Result<FlatWalkValue, SolveAvailabilityError> {
        let memo_bytes = generalizer.memo.retained_bytes()?;
        let reference = self.arena.negative(
            node,
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            Some(&mut generalizer.source_arena_owners[1]),
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
        generalizer: &mut F5cGeneralizer<'_, '_>,
        first: CompareTask,
        tasks: &mut Vec<CompareTask>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        owner: &mut RawWalkerOwner<'_>,
    ) -> Result<bool, SolveAvailabilityError> {
        tasks.clear();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        owner.observe(tasks.len(), tasks.capacity());
        macro_rules! push {
            ($task:expr) => {{
                generalizer.memo.work_meter.charge(1)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let old_capacity = tasks.capacity();
                let reservation = generalizer
                    .memo
                    .reserve_walker(tasks, F5cWalkerLaneKind::FlatComparison);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                owner.observe(tasks.len(), tasks.capacity());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                generalizer.memo.observe_walker_capacity_change_with_source(
                    Some(generalizer.source_meter), old_capacity, tasks.capacity())?;
                reservation?;
                tasks.push($task);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                owner.observe(tasks.len(), tasks.capacity());
            }};
        }
        push!(first);
        while let Some(task) = tasks.pop() {
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            owner.observe(tasks.len(), tasks.capacity());
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
        generalizer: &mut F5cGeneralizer<'_, '_>,
        value: FlatWalkRef,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut tasks_owner = RawWalkerOwner::new(generalizer.source_meter,
            F5cWalkerLaneKind::FlatPromotionTasks as usize,
            F5cWalkerLaneKind::FlatPromotionTasks.slot_size());
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut ids_owner = RawWalkerOwner::new(generalizer.source_meter,
            F5cWalkerLaneKind::FlatPromotionIds as usize,
            F5cWalkerLaneKind::FlatPromotionIds.slot_size());
        let mut tasks = Vec::new();
        let mut ids = Vec::new();
        macro_rules! push_task {
            ($task:expr) => {{
                generalizer.memo.work_meter.charge(1)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let old_capacity = tasks.capacity();
                let reservation = generalizer
                    .memo
                    .reserve_walker(&mut tasks, F5cWalkerLaneKind::FlatPromotionTasks);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                generalizer.memo.observe_walker_capacity_change_with_source(
                    Some(generalizer.source_meter), old_capacity, tasks.capacity())?;
                reservation?;
                tasks.push($task);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
            }};
        }
        macro_rules! push_id {
            ($id:expr) => {{
                generalizer.memo.work_meter.charge(1)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let old_capacity = ids.capacity();
                let reservation = generalizer
                    .memo
                    .reserve_walker(&mut ids, F5cWalkerLaneKind::FlatPromotionIds);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                ids_owner.observe(ids.len(), ids.capacity());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                generalizer.memo.observe_walker_capacity_change_with_source(
                    Some(generalizer.source_meter), old_capacity, ids.capacity())?;
                reservation?;
                ids.push($id);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                ids_owner.observe(ids.len(), ids.capacity());
            }};
        }
        macro_rules! pop_id {
            () => {{
                let value = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                ids_owner.observe(ids.len(), ids.capacity());
                value
            }};
        }
        let incidence = Some((row, polarity));
        let result = (|| {
            push_task!(match value {
                FlatWalkRef::Positive(reference) => PromotionTask::Positive(reference, incidence),
                FlatWalkRef::Negative(reference) => PromotionTask::Negative(reference, incidence),
            });
            while let Some(task) = tasks.pop() {
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                tasks_owner.observe(tasks.len(), tasks.capacity());
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
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        ids_owner.observe(ids.len(), ids.capacity());
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
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        ids_owner.observe(ids.len(), ids.capacity());
                        push_id!(generalizer.memo.push_node(
                            F5cSummaryNodeKind::NegativeIntersection {
                                start: child_start,
                                len
                            },
                            incidence
                        )?);
                    }
                    PromotionTask::PositiveFunction(incidence) => {
                        let result = pop_id!();
                        let argument =
                            pop_id!();
                        push_id!(generalizer.memo.push_node(
                            F5cSummaryNodeKind::PositiveFunction { argument, result },
                            incidence
                        )?);
                    }
                    PromotionTask::NegativeFunction(incidence) => {
                        let result = pop_id!();
                        let argument =
                            pop_id!();
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
            let result = ids.pop().ok_or(SolveAvailabilityError::IdentityExhausted);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            ids_owner.observe(ids.len(), ids.capacity());
            result
        })();
        // Memo nodes may grow while both promotion work lanes are still live.
        let observation = generalizer.memo.observe_walker();
        #[cfg(test)]
        {
            self.record_promotion_observation(generalizer, &tasks, &ids);
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let had_capacity = tasks.capacity() != 0 || ids.capacity() != 0;
        drop(tasks);
        drop(ids);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            drop(tasks_owner);
            drop(ids_owner);
        }
        generalizer
            .memo
            .walker_resources
            .release(F5cWalkerLaneKind::FlatPromotionTasks);
        generalizer
            .memo
            .walker_resources
            .release(F5cWalkerLaneKind::FlatPromotionIds);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if had_capacity {
            generalizer.memo.observe_walker_with_source(generalizer.source_meter)?;
        }
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
        generalizer: &F5cGeneralizer<'_, '_>,
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

impl<'meter> F5cWalkSink<'meter> for F5cFlatWalkSink {
    type Value = FlatWalkValue;

    fn variable(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
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
        _generalizer: &mut F5cGeneralizer<'_, 'meter>,
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
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        match polarity {
            Polarity::Positive => self.positive(generalizer, PositiveNode::Int, true),
            Polarity::Negative => self.negative(generalizer, NegativeNode::Int, true),
        }
    }

    fn bottom(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        polarity: Polarity,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        match polarity {
            Polarity::Positive => self.positive(generalizer, PositiveNode::Bottom, true),
            Polarity::Negative => self.negative(generalizer, NegativeNode::Bottom, true),
        }
    }

    fn top(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        self.negative(generalizer, NegativeNode::Top, true)
    }

    fn cacheable(&self, value: &Self::Value) -> bool {
        value.cacheable
    }

    fn finish_row(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        values: &mut Vec<Self::Value>,
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        values_owner: &mut RawWalkerOwner<'meter>,
        start: usize,
        row: u32,
        polarity: Polarity,
        root: bool,
    ) -> Result<Self::Value, SolveAvailabilityError> {
        let result = match polarity {
            Polarity::Positive => {
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut parts_owner = RawWalkerOwner::new(generalizer.source_meter,
                    F5cWalkerLaneKind::FlatPositiveParts as usize,
                    F5cWalkerLaneKind::FlatPositiveParts.slot_size());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut comparisons_owner = RawWalkerOwner::new(generalizer.source_meter,
                    F5cWalkerLaneKind::FlatComparison as usize,
                    F5cWalkerLaneKind::FlatComparison.slot_size());
                let mut parts = Vec::new();
                let mut comparisons = Vec::new();
                let mut cacheable = true;
                let result = (|| {
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let capacity = values.capacity();
                    let drained = values.drain(start..);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    values_owner.observe(start, capacity);
                    for child in drained {
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
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                &mut comparisons_owner,
                            )?;
                            if equal {
                                duplicate = true;
                                break;
                            }
                        }
                        if !duplicate {
                            cacheable &= child.cacheable;
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            let old_capacity = parts.capacity();
                            let reservation = generalizer
                                .memo
                                .reserve_walker(&mut parts, F5cWalkerLaneKind::FlatPositiveParts);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            parts_owner.observe(parts.len(), parts.capacity());
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            generalizer.memo.observe_walker_capacity_change_with_source(
                                Some(generalizer.source_meter), old_capacity, parts.capacity())?;
                            reservation?;
                            parts.push(reference);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            parts_owner.observe(parts.len(), parts.capacity());
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
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            let (node_owners, child_owners) =
                                generalizer.source_arena_owners.split_at_mut(2);
                            let reference = self.arena.union(
                                &parts,
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                Some(&mut node_owners[0]),
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                Some(&mut child_owners[0]),
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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let had_capacity = comparisons.capacity() != 0 || parts.capacity() != 0;
                drop(comparisons);
                drop(parts);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    drop(comparisons_owner);
                    drop(parts_owner);
                }
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatComparison);
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatPositiveParts);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if had_capacity {
                    generalizer.memo.observe_walker_with_source(generalizer.source_meter)?;
                }
                result
            }
            Polarity::Negative => {
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut parts_owner = RawWalkerOwner::new(generalizer.source_meter,
                    F5cWalkerLaneKind::FlatNegativeParts as usize,
                    F5cWalkerLaneKind::FlatNegativeParts.slot_size());
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let mut comparisons_owner = RawWalkerOwner::new(generalizer.source_meter,
                    F5cWalkerLaneKind::FlatComparison as usize,
                    F5cWalkerLaneKind::FlatComparison.slot_size());
                let mut parts = Vec::new();
                let mut comparisons = Vec::new();
                let mut cacheable = true;
                let result = (|| {
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let capacity = values.capacity();
                    let drained = values.drain(start..);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    values_owner.observe(start, capacity);
                    for child in drained {
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
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                &mut comparisons_owner,
                            )?;
                            if equal {
                                duplicate = true;
                                break;
                            }
                        }
                        if !duplicate {
                            cacheable &= child.cacheable;
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            let old_capacity = parts.capacity();
                            let reservation = generalizer
                                .memo
                                .reserve_walker(&mut parts, F5cWalkerLaneKind::FlatNegativeParts);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            parts_owner.observe(parts.len(), parts.capacity());
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            generalizer.memo.observe_walker_capacity_change_with_source(
                                Some(generalizer.source_meter), old_capacity, parts.capacity())?;
                            reservation?;
                            parts.push(reference);
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            parts_owner.observe(parts.len(), parts.capacity());
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
                            #[cfg(all(test, feature = "f5c_resource_probe"))]
                            let (node_owners, child_owners) =
                                generalizer.source_arena_owners.split_at_mut(2);
                            let reference = self.arena.intersection(
                                &parts,
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                Some(&mut node_owners[1]),
                                #[cfg(all(test, feature = "f5c_resource_probe"))]
                                Some(&mut child_owners[1]),
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
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let had_capacity = comparisons.capacity() != 0 || parts.capacity() != 0;
                drop(comparisons);
                drop(parts);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                {
                    drop(comparisons_owner);
                    drop(parts_owner);
                }
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatComparison);
                generalizer
                    .memo
                    .walker_resources
                    .release(F5cWalkerLaneKind::FlatNegativeParts);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if had_capacity {
                    generalizer.memo.observe_walker_with_source(generalizer.source_meter)?;
                }
                result
            }
        };
        result
    }

    fn function(
        &mut self,
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
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
        generalizer: &mut F5cGeneralizer<'_, 'meter>,
        value: &Self::Value,
        row: u32,
        polarity: Polarity,
    ) -> Result<F5cSummaryNodeId, SolveAvailabilityError> {
        self.promote_value(generalizer, value.reference, row, polarity)
    }
}
