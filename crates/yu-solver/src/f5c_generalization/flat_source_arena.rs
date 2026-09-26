//! Temporary, indexed source values for the candidate F5c walker sink.

use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PositiveId(u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct NegativeId(u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PositiveRef {
    Local(PositiveId),
    Shared(F5cSummaryNodeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NegativeRef {
    Local(NegativeId),
    Shared(F5cSummaryNodeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ChildSpan {
    start: u32,
    len: u32,
}

impl ChildSpan {
    fn checked(start: usize, len: usize) -> Result<Self, SolveAvailabilityError> {
        let end = start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        u32::try_from(end).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        Ok(Self {
            start: u32::try_from(start).map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
            len: u32::try_from(len).map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PositiveNode {
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Union(ChildSpan),
    Function {
        argument: NegativeRef,
        argument_effect: F5cNegativeEffect,
        result_effect: F5cPositiveEffect,
        result: PositiveRef,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NegativeNode {
    Top,
    Bottom,
    Int,
    Variable(u32),
    Quantified(u32),
    Recursive(u32),
    Intersection(ChildSpan),
    Function {
        argument: PositiveRef,
        argument_effect: F5cPositiveEffect,
        result_effect: F5cNegativeEffect,
        result: NegativeRef,
    },
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) struct Checkpoint {
    positive_nodes: usize,
    negative_nodes: usize,
    positive_children: usize,
    negative_children: usize,
}

#[derive(Default)]
pub(super) struct FlatSourceArena {
    pub(super) positive_nodes: Vec<PositiveNode>,
    pub(super) negative_nodes: Vec<NegativeNode>,
    pub(super) positive_children: Vec<PositiveRef>,
    pub(super) negative_children: Vec<NegativeRef>,
}

impl FlatSourceArena {
    pub(super) fn positive_node(&self, id: PositiveId) -> Option<&PositiveNode> {
        self.positive_nodes.get(id.0 as usize)
    }

    pub(super) fn negative_node(&self, id: NegativeId) -> Option<&NegativeNode> {
        self.negative_nodes.get(id.0 as usize)
    }

    pub(super) fn positive_children(&self, span: ChildSpan) -> Option<&[PositiveRef]> {
        let start = span.start as usize;
        let end = start.checked_add(span.len as usize)?;
        self.positive_children.get(start..end)
    }

    pub(super) fn negative_children(&self, span: ChildSpan) -> Option<&[NegativeRef]> {
        let start = span.start as usize;
        let end = start.checked_add(span.len as usize)?;
        self.negative_children.get(start..end)
    }

    pub(super) fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            positive_nodes: self.positive_nodes.len(),
            negative_nodes: self.negative_nodes.len(),
            positive_children: self.positive_children.len(),
            negative_children: self.negative_children.len(),
        }
    }

    pub(super) fn rollback(&mut self, checkpoint: Checkpoint) {
        self.positive_nodes.truncate(checkpoint.positive_nodes);
        self.negative_nodes.truncate(checkpoint.negative_nodes);
        self.positive_children
            .truncate(checkpoint.positive_children);
        self.negative_children
            .truncate(checkpoint.negative_children);
    }

    fn positive_id(&self) -> Result<PositiveId, SolveAvailabilityError> {
        Ok(PositiveId(
            u32::try_from(self.positive_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        ))
    }

    fn negative_id(&self) -> Result<NegativeId, SolveAvailabilityError> {
        Ok(NegativeId(
            u32::try_from(self.negative_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        ))
    }

    pub(super) fn positive(
        &mut self,
        node: PositiveNode,
        resources: &mut F5cWalkerResources,
        meter: &F5cDraftWorkMeter,
        memo_bytes: usize,
    ) -> Result<PositiveRef, SolveAvailabilityError> {
        if matches!(node, PositiveNode::Union(_)) {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let id = self.positive_id()?;
        resources.reserve(
            &mut self.positive_nodes,
            F5cWalkerLaneKind::SourcePositiveNodes,
            1,
            memo_bytes,
        )?;
        meter.charge(1)?;
        self.positive_nodes.push(node);
        Ok(PositiveRef::Local(id))
    }

    pub(super) fn negative(
        &mut self,
        node: NegativeNode,
        resources: &mut F5cWalkerResources,
        meter: &F5cDraftWorkMeter,
        memo_bytes: usize,
    ) -> Result<NegativeRef, SolveAvailabilityError> {
        if matches!(node, NegativeNode::Intersection(_)) {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        let id = self.negative_id()?;
        resources.reserve(
            &mut self.negative_nodes,
            F5cWalkerLaneKind::SourceNegativeNodes,
            1,
            memo_bytes,
        )?;
        meter.charge(1)?;
        self.negative_nodes.push(node);
        Ok(NegativeRef::Local(id))
    }

    pub(super) fn union(
        &mut self,
        children: &[PositiveRef],
        resources: &mut F5cWalkerResources,
        meter: &F5cDraftWorkMeter,
        memo_bytes: usize,
    ) -> Result<PositiveRef, SolveAvailabilityError> {
        let id = self.positive_id()?;
        let span = ChildSpan::checked(self.positive_children.len(), children.len())?;
        resources.reserve(
            &mut self.positive_nodes,
            F5cWalkerLaneKind::SourcePositiveNodes,
            1,
            memo_bytes,
        )?;
        resources.reserve(
            &mut self.positive_children,
            F5cWalkerLaneKind::SourcePositiveChildren,
            children.len(),
            memo_bytes,
        )?;
        meter.charge(
            children
                .len()
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        )?;
        self.positive_children.extend_from_slice(children);
        self.positive_nodes.push(PositiveNode::Union(span));
        Ok(PositiveRef::Local(id))
    }

    pub(super) fn intersection(
        &mut self,
        children: &[NegativeRef],
        resources: &mut F5cWalkerResources,
        meter: &F5cDraftWorkMeter,
        memo_bytes: usize,
    ) -> Result<NegativeRef, SolveAvailabilityError> {
        let id = self.negative_id()?;
        let span = ChildSpan::checked(self.negative_children.len(), children.len())?;
        resources.reserve(
            &mut self.negative_nodes,
            F5cWalkerLaneKind::SourceNegativeNodes,
            1,
            memo_bytes,
        )?;
        resources.reserve(
            &mut self.negative_children,
            F5cWalkerLaneKind::SourceNegativeChildren,
            children.len(),
            memo_bytes,
        )?;
        meter.charge(
            children
                .len()
                .checked_add(1)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        )?;
        self.negative_children.extend_from_slice(children);
        self.negative_nodes.push(NegativeNode::Intersection(span));
        Ok(NegativeRef::Local(id))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tagged_children_and_functions_keep_polarity_and_order() {
        let mut arena = FlatSourceArena::default();
        let mut resources = F5cWalkerResources::default();
        let meter = F5cDraftWorkMeter::default();
        let positive = arena
            .positive(PositiveNode::Int, &mut resources, &meter, 0)
            .unwrap();
        let negative = arena
            .negative(NegativeNode::Top, &mut resources, &meter, 0)
            .unwrap();
        let shared_positive = PositiveRef::Shared(F5cSummaryNodeId(7));
        let shared_negative = NegativeRef::Shared(F5cSummaryNodeId(8));
        let union = arena
            .union(&[shared_positive, positive], &mut resources, &meter, 0)
            .unwrap();
        let intersection = arena
            .intersection(&[negative, shared_negative], &mut resources, &meter, 0)
            .unwrap();
        let positive_function = arena
            .positive(
                PositiveNode::Function {
                    argument: intersection,
                    argument_effect: F5cNegativeEffect::Empty,
                    result_effect: F5cPositiveEffect::Bottom,
                    result: union,
                },
                &mut resources,
                &meter,
                0,
            )
            .unwrap();
        let negative_function = arena
            .negative(
                NegativeNode::Function {
                    argument: union,
                    argument_effect: F5cPositiveEffect::Bottom,
                    result_effect: F5cNegativeEffect::Empty,
                    result: intersection,
                },
                &mut resources,
                &meter,
                0,
            )
            .unwrap();
        assert_eq!(arena.positive_children, [shared_positive, positive]);
        assert_eq!(arena.negative_children, [negative, shared_negative]);
        assert!(matches!(
            positive_function,
            PositiveRef::Local(PositiveId(2))
        ));
        assert!(matches!(
            negative_function,
            NegativeRef::Local(NegativeId(2))
        ));
        assert_eq!(meter.get(), 10);
    }

    #[test]
    fn checked_span_and_failed_charge_publish_nothing_but_retain_capacity() {
        assert!(ChildSpan::checked(usize::MAX, 1).is_err());
        assert!(ChildSpan::checked(u32::MAX as usize, 1).is_err());
        let mut arena = FlatSourceArena::default();
        let mut resources = F5cWalkerResources::default();
        let meter = F5cDraftWorkMeter::default();
        meter.set(usize::MAX);
        assert!(
            arena
                .union(
                    &[PositiveRef::Shared(F5cSummaryNodeId(1))],
                    &mut resources,
                    &meter,
                    19
                )
                .is_err()
        );
        assert!(arena.positive_nodes.is_empty());
        assert!(arena.positive_children.is_empty());
        assert_eq!(
            resources.lanes[F5cWalkerLaneKind::SourcePositiveNodes as usize].actual_capacity,
            arena.positive_nodes.capacity()
        );
        assert_eq!(
            resources.lanes[F5cWalkerLaneKind::SourcePositiveChildren as usize].actual_capacity,
            arena.positive_children.capacity()
        );
        assert!(resources.simultaneous_memo_peak_bytes >= resources.retained_bytes().unwrap() + 19);
    }

    #[test]
    fn rollback_truncates_every_lane() {
        let mut arena = FlatSourceArena::default();
        let mut resources = F5cWalkerResources::default();
        let meter = F5cDraftWorkMeter::default();
        let checkpoint = arena.checkpoint();
        let positive = arena
            .positive(PositiveNode::Bottom, &mut resources, &meter, 0)
            .unwrap();
        let negative = arena
            .negative(NegativeNode::Bottom, &mut resources, &meter, 0)
            .unwrap();
        arena.union(&[positive], &mut resources, &meter, 0).unwrap();
        arena
            .intersection(&[negative], &mut resources, &meter, 0)
            .unwrap();
        arena.rollback(checkpoint);
        assert!(arena.positive_nodes.is_empty() && arena.negative_nodes.is_empty());
        assert!(arena.positive_children.is_empty() && arena.negative_children.is_empty());
        assert_eq!(meter.get(), 6);
        assert!(resources.retained_bytes().unwrap() > 0);
    }

    #[test]
    fn second_lane_reserve_failure_does_not_append_first_lane() {
        let mut arena = FlatSourceArena::default();
        let mut resources = F5cWalkerResources::default();
        let meter = F5cDraftWorkMeter::default();
        resources.lanes[F5cWalkerLaneKind::SourcePositiveChildren as usize].requested_slots =
            usize::MAX;
        assert!(
            arena
                .union(
                    &[PositiveRef::Shared(F5cSummaryNodeId(1))],
                    &mut resources,
                    &meter,
                    0,
                )
                .is_err()
        );
        assert!(arena.positive_nodes.is_empty());
        assert!(arena.positive_children.is_empty());
        assert_eq!(meter.get(), 0);
        assert_eq!(
            resources.lanes[F5cWalkerLaneKind::SourcePositiveNodes as usize].actual_capacity,
            arena.positive_nodes.capacity()
        );
    }
}
