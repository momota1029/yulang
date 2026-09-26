//! Indexed candidate values for the shared F5c producer interpreter.

use super::flat_source_arena::{
    Checkpoint, FlatSourceArena, NegativeNode, NegativeRef, PositiveNode, PositiveRef,
};
use super::*;

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

#[cfg(test)]
impl F5cFlatWalkSink {
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
