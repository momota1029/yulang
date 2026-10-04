//! Test-only executable model of finite SCC parent/use identity transport.
//!
//! This is deliberately not connected to `InferenceSession`.  It exercises
//! the conditional graph-renaming operation with caller-supplied partitions;
//! production classification and source adequacy remain separate gates.

use std::{
    collections::{HashMap, HashSet},
    ops::Range,
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct Identity(pub(super) u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct TermId(pub(super) usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Atom {
    Int,
    Bool,
    String,
    EffectRead,
    EffectWrite,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Term {
    Variable(Identity),
    Atom(Atom),
    Bottom,
    Top,
    Function {
        argument: TermId,
        argument_effect: TermId,
        result_effect: TermId,
        result: TermId,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Bound {
    pub(super) lower: TermId,
    pub(super) upper: TermId,
    pub(super) evidence: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Graph {
    pub(super) terms: Vec<Term>,
    pub(super) bounds: Vec<Bound>,
    pub(super) evidence: Vec<u32>,
    pub(super) identities: Vec<Identity>,
    pub(super) root: TermId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AllocationLane {
    Identities,
    Terms,
    Bounds,
    Evidence,
    UseViews,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TransportError {
    InvalidRoot,
    InvalidTermReference,
    InvalidEvidenceRange,
    DuplicateIdentity,
    IncompletePartition,
    UnknownIdentity,
    IdentityExhausted,
    AllocationFailed(AllocationLane),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParentView {
    pub(super) graph: Graph,
    pub(super) local: Vec<Identity>,
    pub(super) anchors: Vec<Identity>,
    /// Source identity to parent identity, including identity mappings for
    /// anchors. Kept as evidence for differential checks, not as a type rule.
    pub(super) identity_map: Vec<(Identity, Identity)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct UseOverlay {
    pub(super) graph: Graph,
    pub(super) identity_map: Vec<(Identity, Identity)>,
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct FaultInjection(Option<(AllocationLane, usize)>);

impl FaultInjection {
    pub(super) const fn fail_at(lane: AllocationLane) -> Self {
        Self(Some((lane, 0)))
    }

    pub(super) const fn fail_after(lane: AllocationLane, successful_checks: usize) -> Self {
        Self(Some((lane, successful_checks)))
    }

    fn check(&mut self, lane: AllocationLane) -> Result<(), TransportError> {
        if let Some((target, skip)) = self.0
            && target == lane
        {
            if skip == 0 {
                self.0 = None;
                return Err(TransportError::AllocationFailed(lane));
            }
            self.0 = Some((target, skip - 1));
        }
        Ok(())
    }
}

impl Graph {
    fn validate(&self) -> Result<HashSet<Identity>, TransportError> {
        if self.root.0 >= self.terms.len() {
            return Err(TransportError::InvalidRoot);
        }

        let mut identities = HashSet::new();
        identities
            .try_reserve(self.identities.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
        for identity in &self.identities {
            if !identities.insert(*identity) {
                return Err(TransportError::DuplicateIdentity);
            }
        }

        for term in &self.terms {
            match term {
                Term::Variable(identity) if !identities.contains(identity) => {
                    return Err(TransportError::UnknownIdentity);
                }
                Term::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } if [*argument, *argument_effect, *result_effect, *result]
                    .into_iter()
                    .any(|child| child.0 >= self.terms.len()) =>
                {
                    return Err(TransportError::InvalidTermReference);
                }
                _ => {}
            }
        }

        for bound in &self.bounds {
            if bound.lower.0 >= self.terms.len() || bound.upper.0 >= self.terms.len() {
                return Err(TransportError::InvalidTermReference);
            }
            if bound.evidence.start > bound.evidence.end || bound.evidence.end > self.evidence.len()
            {
                return Err(TransportError::InvalidEvidenceRange);
            }
        }
        Ok(identities)
    }

    fn renamed(
        &self,
        mapping: &HashMap<Identity, Identity>,
        new_identities: Vec<Identity>,
        fault: &mut FaultInjection,
    ) -> Result<Self, TransportError> {
        fault.check(AllocationLane::Terms)?;
        let mut terms = Vec::new();
        terms
            .try_reserve_exact(self.terms.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Terms))?;
        terms.extend(self.terms.iter().map(|term| match *term {
            Term::Variable(identity) => {
                Term::Variable(mapping.get(&identity).copied().unwrap_or(identity))
            }
            other => other,
        }));

        fault.check(AllocationLane::Bounds)?;
        let mut bounds = Vec::new();
        bounds
            .try_reserve_exact(self.bounds.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Bounds))?;
        bounds.extend(self.bounds.iter().cloned());

        fault.check(AllocationLane::Evidence)?;
        let mut evidence = Vec::new();
        evidence
            .try_reserve_exact(self.evidence.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Evidence))?;
        evidence.extend_from_slice(&self.evidence);

        fault.check(AllocationLane::Identities)?;
        let mut identities = Vec::new();
        identities
            .try_reserve_exact(new_identities.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
        identities.extend(new_identities);

        Ok(Self {
            terms,
            bounds,
            evidence,
            identities,
            root: self.root,
        })
    }
}

pub(super) fn make_parent(
    graph: &Graph,
    local: &[Identity],
    anchors: &[Identity],
    receiving_namespace: &[Identity],
    mut fault: FaultInjection,
) -> Result<ParentView, TransportError> {
    let graph_identities = graph.validate()?;
    validate_partition(&graph_identities, local, anchors)?;
    let mut occupied = validate_namespace(receiving_namespace)?;
    occupied
        .try_reserve(graph_identities.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    occupied.extend(graph_identities.iter().copied());

    let (fresh, _occupied) = fresh_identities(local.len(), occupied)?;
    let mapping_capacity = local
        .len()
        .checked_add(anchors.len())
        .ok_or(TransportError::IdentityExhausted)?;
    let mut identity_map = HashMap::new();
    identity_map
        .try_reserve(mapping_capacity)
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    let mut public_map = Vec::new();
    fault.check(AllocationLane::Identities)?;
    public_map
        .try_reserve_exact(mapping_capacity)
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;

    for (&old, &new) in local.iter().zip(&fresh) {
        identity_map.insert(old, new);
        public_map.push((old, new));
    }
    for &anchor in anchors {
        identity_map.insert(anchor, anchor);
        public_map.push((anchor, anchor));
    }

    // Keep the local list in caller-supplied order; every identity was checked
    // against the complete graph partition above.
    let mut parent_local = Vec::new();
    fault.check(AllocationLane::Identities)?;
    parent_local
        .try_reserve_exact(fresh.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    parent_local.extend(fresh.iter().copied());

    let mut parent_identities = Vec::new();
    fault.check(AllocationLane::Identities)?;
    parent_identities
        .try_reserve_exact(graph.identities.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    parent_identities.extend(
        graph
            .identities
            .iter()
            .map(|identity| identity_map.get(identity).copied().unwrap_or(*identity)),
    );

    fault.check(AllocationLane::Identities)?;
    let mut parent_anchors = Vec::new();
    parent_anchors
        .try_reserve_exact(anchors.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    parent_anchors.extend_from_slice(anchors);

    Ok(ParentView {
        graph: graph.renamed(&identity_map, parent_identities, &mut fault)?,
        local: parent_local,
        anchors: parent_anchors,
        identity_map: public_map,
    })
}

pub(super) fn make_uses(
    parent: &ParentView,
    receiving_namespaces: &[Vec<Identity>],
    mut fault: FaultInjection,
) -> Result<Vec<UseOverlay>, TransportError> {
    let parent_identities = parent.graph.validate()?;
    validate_partition(&parent_identities, &parent.local, &parent.anchors)?;

    let mut occupied = parent_identities;
    let source_and_parent_count = parent
        .identity_map
        .len()
        .checked_mul(2)
        .ok_or(TransportError::IdentityExhausted)?;
    occupied
        .try_reserve(source_and_parent_count)
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    for (source, parent) in &parent.identity_map {
        occupied.insert(*source);
        occupied.insert(*parent);
    }
    for namespace in receiving_namespaces {
        let namespace_identities = validate_namespace(namespace)?;
        occupied
            .try_reserve(namespace_identities.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
        occupied.extend(namespace_identities);
    }

    fault.check(AllocationLane::UseViews)?;
    let mut overlays = Vec::new();
    overlays
        .try_reserve_exact(receiving_namespaces.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::UseViews))?;

    for _ in receiving_namespaces {
        let (fresh, next_occupied) = fresh_identities(parent.local.len(), occupied)?;
        occupied = next_occupied;

        let mut mapping = HashMap::new();
        mapping
            .try_reserve(parent.local.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
        let mut public_map = Vec::new();
        fault.check(AllocationLane::Identities)?;
        public_map
            .try_reserve_exact(parent.local.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
        for (&old, &new) in parent.local.iter().zip(&fresh) {
            mapping.insert(old, new);
            public_map.push((old, new));
        }

        let mut identities = Vec::new();
        fault.check(AllocationLane::Identities)?;
        identities
            .try_reserve_exact(parent.graph.identities.len())
            .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
        identities.extend(
            parent
                .graph
                .identities
                .iter()
                .map(|identity| mapping.get(identity).copied().unwrap_or(*identity)),
        );
        let graph = parent.graph.renamed(&mapping, identities, &mut fault)?;
        overlays.push(UseOverlay {
            graph,
            identity_map: public_map,
        });
    }
    Ok(overlays)
}

fn validate_partition(
    graph: &HashSet<Identity>,
    local: &[Identity],
    anchors: &[Identity],
) -> Result<(), TransportError> {
    let mut seen = HashSet::new();
    seen.try_reserve(local.len() + anchors.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    for identity in local.iter().chain(anchors) {
        if !graph.contains(identity) {
            return Err(TransportError::UnknownIdentity);
        }
        if !seen.insert(*identity) {
            return Err(TransportError::DuplicateIdentity);
        }
    }
    if &seen != graph {
        return Err(TransportError::IncompletePartition);
    }
    Ok(())
}

fn validate_namespace(namespace: &[Identity]) -> Result<HashSet<Identity>, TransportError> {
    let mut result = HashSet::new();
    result
        .try_reserve(namespace.len())
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    for identity in namespace {
        if !result.insert(*identity) {
            return Err(TransportError::DuplicateIdentity);
        }
    }
    Ok(result)
}

fn fresh_identities(
    count: usize,
    mut occupied: HashSet<Identity>,
) -> Result<(Vec<Identity>, HashSet<Identity>), TransportError> {
    occupied
        .try_reserve(count)
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(count)
        .map_err(|_| TransportError::AllocationFailed(AllocationLane::Identities))?;

    let mut candidate = 0u32;
    while result.len() < count {
        while occupied.contains(&Identity(candidate)) {
            candidate = candidate
                .checked_add(1)
                .ok_or(TransportError::IdentityExhausted)?;
        }
        let fresh = Identity(candidate);
        occupied.insert(fresh);
        result.push(fresh);
        if result.len() < count {
            candidate = candidate
                .checked_add(1)
                .ok_or(TransportError::IdentityExhausted)?;
        }
    }
    Ok((result, occupied))
}
