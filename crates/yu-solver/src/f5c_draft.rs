use super::SolveAvailabilityError;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PositiveId(pub(super) u32);
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct NegativeId(pub(super) u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ChildSpan {
    pub(super) start: u32,
    pub(super) len: u32,
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
        argument: NegativeId,
        result: PositiveId,
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
        argument: PositiveId,
        result: NegativeId,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct RecursiveBound {
    pub(super) ordinal: u32,
    pub(super) lower: PositiveId,
    pub(super) upper: NegativeId,
}

#[derive(Default)]
pub(super) struct FlatDraft {
    pub(super) quantifier_count: u32,
    pub(super) predicate: Option<PositiveId>,
    pub(super) positive_nodes: Vec<PositiveNode>,
    pub(super) negative_nodes: Vec<NegativeNode>,
    pub(super) positive_children: Vec<PositiveId>,
    pub(super) negative_children: Vec<NegativeId>,
    pub(super) recursive_bounds: Vec<RecursiveBound>,
    pub(super) insertion_order: Vec<NodeRef>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum NodeRef {
    Positive(PositiveId),
    Negative(NegativeId),
}

impl FlatDraft {
    pub(super) fn positive(
        &mut self,
        node: PositiveNode,
    ) -> Result<PositiveId, SolveAvailabilityError> {
        let id = PositiveId(
            u32::try_from(self.positive_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
        self.positive_nodes
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.insertion_order
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.positive_nodes.push(node);
        self.insertion_order.push(NodeRef::Positive(id));
        Ok(id)
    }

    pub(super) fn negative(
        &mut self,
        node: NegativeNode,
    ) -> Result<NegativeId, SolveAvailabilityError> {
        let id = NegativeId(
            u32::try_from(self.negative_nodes.len())
                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
        );
        self.negative_nodes
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.insertion_order
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.negative_nodes.push(node);
        self.insertion_order.push(NodeRef::Negative(id));
        Ok(id)
    }

    pub(super) fn positive_span(
        &mut self,
        children: &[PositiveId],
    ) -> Result<ChildSpan, SolveAvailabilityError> {
        let start = u32::try_from(self.positive_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(children.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.positive_children
            .try_reserve(children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.positive_children.extend_from_slice(children);
        Ok(ChildSpan { start, len })
    }

    pub(super) fn negative_span(
        &mut self,
        children: &[NegativeId],
    ) -> Result<ChildSpan, SolveAvailabilityError> {
        let start = u32::try_from(self.negative_children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let len =
            u32::try_from(children.len()).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        start
            .checked_add(len)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.negative_children
            .try_reserve(children.len())
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.negative_children.extend_from_slice(children);
        Ok(ChildSpan { start, len })
    }

    pub(super) fn bound(&mut self, bound: RecursiveBound) -> Result<(), SolveAvailabilityError> {
        self.recursive_bounds
            .try_reserve(1)
            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        self.recursive_bounds.push(bound);
        Ok(())
    }
}
