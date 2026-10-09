use super::f5c_draft::{
    ChildSpan, FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveId, PositiveNode,
};
#[cfg(test)]
use super::f5c_generalization::{F5cBulkDrainSite, record_bulk_drain_boundary};
use super::{
    DraftHeapMeter, F5cComponentExpansionMemo, F5cNegative, F5cNegativeEffect, F5cPositive,
    F5cPositiveEffect, F5cWalkValue, F5cWalkerLaneKind, PhysicalOwnerKind,
    SolveAvailabilityError, TrackedOne,
    TrackedVec,
};
use std::collections::HashSet;
#[cfg(all(test, feature = "f5c_resource_probe"))]
use super::f5c_draft_heap::RawWalkerOwner;

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

pub(super) enum Task<'tree, 'meter> {
    Positive(&'tree F5cPositive<'meter>),
    Negative(&'tree F5cNegative<'meter>),
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
    let reservation = resources.reserve(
        &mut output.positive_nodes,
        F5cWalkerLaneKind::ReplayOutputPositiveNodes,
        0,
        memo_bytes,
    );
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    output.observe_owner(0, output.positive_nodes.len());
    reservation?;
    let reservation = resources.reserve(
        &mut output.negative_nodes,
        F5cWalkerLaneKind::ReplayOutputNegativeNodes,
        0,
        memo_bytes,
    );
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    output.observe_owner(1, output.negative_nodes.len());
    reservation?;
    let reservation = resources.reserve(
        &mut output.positive_children,
        F5cWalkerLaneKind::ReplayOutputPositiveChildren,
        0,
        memo_bytes,
    );
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    output.observe_owner(2, output.positive_children.len());
    reservation?;
    let reservation = resources.reserve(
        &mut output.negative_children,
        F5cWalkerLaneKind::ReplayOutputNegativeChildren,
        0,
        memo_bytes,
    );
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    output.observe_owner(3, output.negative_children.len());
    reservation?;
    let reservation = resources.reserve(
        &mut output.insertion_order,
        F5cWalkerLaneKind::ReplayOutputInsertionOrder,
        0,
        memo_bytes,
    );
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    output.observe_owner(5, output.insertion_order.len());
    reservation
}

pub(super) fn release_flat_output(
    memo: &mut F5cComponentExpansionMemo,
    output: FlatDraft,
    #[cfg(all(test, feature = "f5c_resource_probe"))] source_meter: Option<&DraftHeapMeter>,
) {
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
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    if let Some(source_meter) = source_meter {
        let _ = memo.observe_component_external(source_meter);
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
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    probe_meter: Option<&DraftHeapMeter>,
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
        output.structural_census()?.1,
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
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut active_positive_owner = probe_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::ReplayActivePositive as usize,
            F5cWalkerLaneKind::ReplayActivePositive.slot_size()));
        let memo_bytes = memo.retained_bytes()?;
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let old_capacity = active_positive.capacity();
        let allocation = memo.walker_resources.reserve(
            &mut active_positive,
            F5cWalkerLaneKind::ReplayActivePositive,
            source.positive_nodes.len(),
            memo_bytes,
        );
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = active_positive_owner.as_mut() {
            owner.observe(active_positive.len(), active_positive.capacity());
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let allocation = memo.observe_walker_capacity_change_with_source(
            probe_meter, old_capacity, active_positive.capacity()).and(allocation);
        if let Err(error) = allocation {
            drop(active_positive);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            drop(active_positive_owner);
            memo.walker_resources
                .release(F5cWalkerLaneKind::ReplayActivePositive);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if let Some(meter) = probe_meter {
                memo.observe_walker_with_source(meter)?;
            }
            return Err(error);
        }
        active_positive.resize(source.positive_nodes.len(), false);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = active_positive_owner.as_mut() {
            owner.observe(active_positive.len(), active_positive.capacity());
        }
        let mut active_negative = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut active_negative_owner = probe_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::ReplayActiveNegative as usize,
            F5cWalkerLaneKind::ReplayActiveNegative.slot_size()));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let old_capacity = active_negative.capacity();
        let allocation = memo.walker_resources.reserve(
            &mut active_negative,
            F5cWalkerLaneKind::ReplayActiveNegative,
            source.negative_nodes.len(),
            memo_bytes,
        );
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = active_negative_owner.as_mut() {
            owner.observe(active_negative.len(), active_negative.capacity());
        }
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let allocation = memo.observe_walker_capacity_change_with_source(
            probe_meter, old_capacity, active_negative.capacity()).and(allocation);
        if let Err(error) = allocation {
            drop(active_positive);
            drop(active_negative);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            {
                drop(active_positive_owner);
                drop(active_negative_owner);
            }
            memo.walker_resources
                .release(F5cWalkerLaneKind::ReplayActivePositive);
            memo.walker_resources
                .release(F5cWalkerLaneKind::ReplayActiveNegative);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            if let Some(meter) = probe_meter {
                memo.observe_walker_with_source(meter)?;
            }
            return Err(error);
        }
        active_negative.resize(source.negative_nodes.len(), false);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if let Some(owner) = active_negative_owner.as_mut() {
            owner.observe(active_negative.len(), active_negative.capacity());
        }

        let mut tasks = Vec::new();
        let mut values = Vec::new();
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut tasks_owner = probe_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::ReplayTasks as usize,
            F5cWalkerLaneKind::ReplayTasks.slot_size()));
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let mut values_owner = probe_meter.map(|meter| RawWalkerOwner::new(meter,
            F5cWalkerLaneKind::ReplayValues as usize,
            F5cWalkerLaneKind::ReplayValues.slot_size()));
        macro_rules! push_task {
            ($task:expr) => {{
                memo.work_meter.charge(1)?; // scheduled flat replay task
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let old_capacity = tasks.capacity();
                let reservation = memo.reserve_walker(&mut tasks, F5cWalkerLaneKind::ReplayTasks);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = tasks_owner.as_mut() {
                    owner.observe(tasks.len(), tasks.capacity());
                }
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                memo.observe_walker_capacity_change_with_source(
                    probe_meter, old_capacity, tasks.capacity())?;
                reservation?;
                tasks.push($task);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = tasks_owner.as_mut() {
                    owner.observe(tasks.len(), tasks.capacity());
                }
            }};
        }
        macro_rules! push_value {
            ($value:expr) => {{
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                let old_capacity = values.capacity();
                let reservation = memo.reserve_walker(&mut values, F5cWalkerLaneKind::ReplayValues);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = values_owner.as_mut() {
                    owner.observe(values.len(), values.capacity());
                }
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                memo.observe_walker_capacity_change_with_source(
                    probe_meter, old_capacity, values.capacity())?;
                reservation?;
                values.push($value);
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = values_owner.as_mut() {
                    owner.observe(values.len(), values.capacity());
                }
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
        macro_rules! pop_task {
            () => {{
                let popped = tasks.pop();
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = tasks_owner.as_mut() {
                    owner.observe(tasks.len(), tasks.capacity());
                }
                popped
            }};
        }
        macro_rules! pop_value {
            () => {{
                let popped = values.pop();
                #[cfg(all(test, feature = "f5c_resource_probe"))]
                if let Some(owner) = values_owner.as_mut() {
                    owner.observe(values.len(), values.capacity());
                }
                popped
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
                let task = pop_task!().expect("nonempty flat replay tasks");
                match task {
                    FlatTask::Positive(id) => {
                        let index = usize::try_from(id.0).map_err(|_| exhausted)?;
                        match *source.positive_nodes.get(index).ok_or(exhausted)? {
                            PositiveNode::Bottom => push_positive!(PositiveNode::Bottom),
                            PositiveNode::Int => push_positive!(PositiveNode::Int),
                            PositiveNode::Unit => push_positive!(PositiveNode::Unit),
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
                            NegativeNode::Unit => push_negative!(NegativeNode::Unit),
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
                        output.admit_child_entries(count)?;
                        output.admit_logical_incidences(count)?;
                        let reservation = output.positive_children.try_reserve(count)
                            .map_err(|_| exhausted);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        output.observe_owner(2, output.positive_children.len() + count);
                        reservation?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let values_capacity = values.capacity();
                        let drained = values.drain(start..);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = values_owner.as_mut() {
                            owner.observe(start, values_capacity);
                        }
                        for value in drained {
                            let NodeRef::Positive(child) = value else {
                                return Err(exhausted);
                            };
                            output.push_reserved_positive_child(child);
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
                        output.admit_child_entries(count)?;
                        output.admit_logical_incidences(count)?;
                        let reservation = output.negative_children.try_reserve(count)
                            .map_err(|_| exhausted);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        output.observe_owner(3, output.negative_children.len() + count);
                        reservation?;
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        let values_capacity = values.capacity();
                        let drained = values.drain(start..);
                        #[cfg(all(test, feature = "f5c_resource_probe"))]
                        if let Some(owner) = values_owner.as_mut() {
                            owner.observe(start, values_capacity);
                        }
                        for value in drained {
                            let NodeRef::Negative(child) = value else {
                                return Err(exhausted);
                            };
                            output.push_reserved_negative_child(child);
                        }
                        push_negative!(NegativeNode::Intersection(ChildSpan {
                            start: child_start,
                            len: child_len,
                        }));
                    }
                    FlatTask::FinishPositiveFunction => {
                        let NodeRef::Positive(result) = pop_value!().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        let NodeRef::Negative(argument) = pop_value!().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        push_positive!(PositiveNode::Function { argument, result });
                    }
                    FlatTask::FinishNegativeFunction => {
                        let NodeRef::Negative(result) = pop_value!().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        let NodeRef::Positive(argument) = pop_value!().ok_or(exhausted)? else {
                            return Err(exhausted);
                        };
                        push_negative!(NegativeNode::Function { argument, result });
                    }
                }
            }
            if values.len() != 1 {
                return Err(exhausted);
            }
            pop_value!().ok_or(exhausted)
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
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let observed = observed.and_then(|()| match probe_meter {
            Some(meter) => memo.observe_walker_with_source(meter),
            None => Ok(()),
        });
        #[cfg(test)]
        let replayed = match observed {
            Ok(()) => replayed,
            Err(error) => Err(error),
        };
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        let had_scratch_capacity = active_positive.capacity() != 0
            || active_negative.capacity() != 0 || tasks.capacity() != 0 || values.capacity() != 0;
        drop(active_positive);
        drop(active_negative);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        {
            drop(tasks);
            drop(values);
            drop(active_positive_owner);
            drop(active_negative_owner);
            drop(tasks_owner);
            drop(values_owner);
        }
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayActivePositive);
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayActiveNegative);
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayTasks);
        memo.walker_resources
            .release(F5cWalkerLaneKind::ReplayValues);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        if had_scratch_capacity && let Some(meter) = probe_meter {
            memo.observe_walker_with_source(meter)?;
        }
        replayed
    })();
    if result.is_err() {
        output.positive_nodes.truncate(checkpoint.0);
        output.negative_nodes.truncate(checkpoint.1);
        output.positive_children.truncate(checkpoint.2);
        output.negative_children.truncate(checkpoint.3);
        output.insertion_order.truncate(checkpoint.4);
        #[cfg(all(test, feature = "f5c_resource_probe"))]
        output.sync_owners();
        output.restore_structural_census(checkpoint.5);
    }
    result
}

pub(super) fn replay_positive<'meter>(
    source_meter: &'meter DraftHeapMeter,
    memo: &mut F5cComponentExpansionMemo,
    value: &F5cPositive<'meter>,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<F5cPositive<'meter>, SolveAvailabilityError> {
    match replay(
        source_meter,
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

pub(super) fn replay_negative<'meter>(
    source_meter: &'meter DraftHeapMeter,
    memo: &mut F5cComponentExpansionMemo,
    value: &F5cNegative<'meter>,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<F5cNegative<'meter>, SolveAvailabilityError> {
    match replay(
        source_meter,
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

fn replay<'meter>(
    source_meter: &'meter DraftHeapMeter,
    memo: &mut F5cComponentExpansionMemo,
    first: Task<'_, 'meter>,
    protected: &HashSet<u32>,
    positive_only: &HashSet<u32>,
    negative_only: &HashSet<u32>,
) -> Result<F5cWalkValue<'meter>, SolveAvailabilityError> {
    let mut tasks = Vec::new();
    let mut values = Vec::new();
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    let mut tasks_owner = RawWalkerOwner::new(source_meter,
        F5cWalkerLaneKind::ReplayTasks as usize,
        F5cWalkerLaneKind::ReplayTasks.slot_size());
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    let mut values_owner = RawWalkerOwner::new(source_meter,
        F5cWalkerLaneKind::ReplayValues as usize,
        F5cWalkerLaneKind::ReplayValues.slot_size());
    macro_rules! push_task {
        ($task:expr) => {{
            memo.work_meter.charge(1)?; // scheduled replay task
            let reservation = memo.reserve_walker_with_source(
                &mut tasks,
                F5cWalkerLaneKind::ReplayTasks,
                source_meter,
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            tasks_owner.observe(tasks.len(), tasks.capacity());
            reservation?;
            tasks.push($task);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            tasks_owner.observe(tasks.len(), tasks.capacity());
        }};
    }
    macro_rules! push_value {
        ($value:expr) => {{
            memo.work_meter.charge(1)?; // emitted replay value
            let reservation = memo.reserve_walker_with_source(
                &mut values,
                F5cWalkerLaneKind::ReplayValues,
                source_meter,
            );
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            values_owner.observe(values.len(), values.capacity());
            reservation?;
            values.push($value);
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            values_owner.observe(values.len(), values.capacity());
        }};
    }

    macro_rules! pop_task {
        () => {{
            let popped = tasks.pop();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            tasks_owner.observe(tasks.len(), tasks.capacity());
            popped
        }};
    }
    macro_rules! pop_value {
        () => {{
            let popped = values.pop();
            #[cfg(all(test, feature = "f5c_resource_probe"))]
            values_owner.observe(values.len(), values.capacity());
            popped
        }};
    }

    let result = (|| {
        push_task!(first);
        while !tasks.is_empty() {
            memo.work_meter.charge(1)?; // visited source or finish task
            let task = pop_task!().expect("nonempty replay tasks");
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
                    F5cPositive::Bottom => {
                        push_value!(F5cWalkValue::Positive(F5cPositive::Bottom, true))
                    }
                    F5cPositive::Int => push_value!(F5cWalkValue::Positive(F5cPositive::Int, true)),
                    F5cPositive::Unit => push_value!(F5cWalkValue::Positive(F5cPositive::Unit, true)),
                    F5cPositive::Variable(row) => {
                        push_value!(F5cWalkValue::Positive(F5cPositive::Variable(*row), true))
                    }
                    F5cPositive::Quantified(row) => {
                        push_value!(F5cWalkValue::Positive(F5cPositive::Quantified(*row), true))
                    }
                    F5cPositive::Recursive(row) => {
                        push_value!(F5cWalkValue::Positive(F5cPositive::Recursive(*row), true))
                    }
                    F5cPositive::Shared(id) => {
                        push_value!(F5cWalkValue::Positive(F5cPositive::Shared(*id), true))
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
                    F5cNegative::Top => push_value!(F5cWalkValue::Negative(F5cNegative::Top, true)),
                    F5cNegative::Bottom => {
                        push_value!(F5cWalkValue::Negative(F5cNegative::Bottom, true))
                    }
                    F5cNegative::Int => push_value!(F5cWalkValue::Negative(F5cNegative::Int, true)),
                    F5cNegative::Unit => push_value!(F5cWalkValue::Negative(F5cNegative::Unit, true)),
                    F5cNegative::Variable(row) => {
                        push_value!(F5cWalkValue::Negative(F5cNegative::Variable(*row), true))
                    }
                    F5cNegative::Quantified(row) => {
                        push_value!(F5cWalkValue::Negative(F5cNegative::Quantified(*row), true))
                    }
                    F5cNegative::Recursive(row) => {
                        push_value!(F5cWalkValue::Negative(F5cNegative::Recursive(*row), true))
                    }
                    F5cNegative::Shared(id) => {
                        push_value!(F5cWalkValue::Negative(F5cNegative::Shared(*id), true))
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
                    let mut children = TrackedVec::new_with_kind(
                        source_meter, PhysicalOwnerKind::UnionChildren);
                    memo.work_meter.charge(count)?;
                    memo.observe_component_external(source_meter)?;
                    children
                        .try_reserve_exact(count)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let values_capacity = values.capacity();
                    let drained = values.drain(start..);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    values_owner.observe(start, values_capacity);
                    for value in drained {
                        let F5cWalkValue::Positive(value, _) = value else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        children.push_reserved(value);
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
                    let mut children = TrackedVec::new_with_kind(
                        source_meter, PhysicalOwnerKind::IntersectionChildren);
                    memo.work_meter.charge(count)?;
                    memo.observe_component_external(source_meter)?;
                    children
                        .try_reserve_exact(count)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    let values_capacity = values.capacity();
                    let drained = values.drain(start..);
                    #[cfg(all(test, feature = "f5c_resource_probe"))]
                    values_owner.observe(start, values_capacity);
                    for value in drained {
                        let F5cWalkValue::Negative(value, _) = value else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        children.push_reserved(value);
                    }
                    push_value!(F5cWalkValue::Negative(
                        F5cNegative::Intersection(children),
                        true,
                    ));
                }
                Task::FinishPositiveFunction => {
                    let F5cWalkValue::Positive(result, _) = pop_value!()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let F5cWalkValue::Negative(argument, _) = pop_value!()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    push_value!(F5cWalkValue::Positive(
                        F5cPositive::Function {
                            argument: TrackedOne::try_new_with_kind(source_meter, argument,
                                PhysicalOwnerKind::PositiveFunctionArgument)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                            argument_effect: F5cNegativeEffect::Empty,
                            result_effect: F5cPositiveEffect::Bottom,
                            result: TrackedOne::try_new_with_kind(source_meter, result,
                                PhysicalOwnerKind::PositiveFunctionResult)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                        },
                        true,
                    ));
                }
                Task::FinishNegativeFunction => {
                    let F5cWalkValue::Negative(result, _) = pop_value!()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    let F5cWalkValue::Positive(argument, _) = pop_value!()
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?
                    else {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    };
                    push_value!(F5cWalkValue::Negative(
                        F5cNegative::Function {
                            argument: TrackedOne::try_new_with_kind(source_meter, argument,
                                PhysicalOwnerKind::NegativeFunctionArgument)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                            argument_effect: F5cPositiveEffect::Bottom,
                            result_effect: F5cNegativeEffect::Empty,
                            result: TrackedOne::try_new_with_kind(source_meter, result,
                                PhysicalOwnerKind::NegativeFunctionResult)
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                        },
                        true,
                    ));
                }
            }
        }
        if values.len() != 1 {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        pop_value!()
            .ok_or(SolveAvailabilityError::IdentityExhausted)
    })();
    #[cfg(all(test, feature = "f5c_resource_probe"))]
    {
        drop(tasks);
        drop(values);
        drop(tasks_owner);
        drop(values_owner);
    }
    memo.release_walker_with_source(F5cWalkerLaneKind::ReplayTasks, source_meter)?;
    memo.release_walker_with_source(F5cWalkerLaneKind::ReplayValues, source_meter)?;
    result
}
