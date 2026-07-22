//! Shadow-only ordinary-cast eligibility classification over bounded explanations.

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use super::explain::{
    ExplanationBudget, ExplanationCompleteness, ExplanationEdge, ExplanationEdgeKind,
    ExplanationNode, ExplanationNodeId, ExplanationQueryError, ExplanationQueryResult,
    ExplanationTruncationReason,
};
use super::{
    BinaryReplayDerivation, BoundDerivation, ConstraintMachine, ConstraintOriginKind,
    ConstraintRecordId, OriginId, SourceBoundaryId, SubtractFactDerivation,
};
use crate::time::Duration;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OcastEligibilityState {
    EligibleSourceBoundary,
    InternalOnly,
    Incomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OcastEligibilityClassification {
    pub(crate) producer: ConstraintRecordId,
    pub(crate) outcome: OcastEligibilityOutcome,
    pub(crate) visited_nodes: usize,
    pub(crate) visited_edges: usize,
}

impl OcastEligibilityClassification {
    pub(crate) fn state(&self) -> OcastEligibilityState {
        match self.outcome {
            OcastEligibilityOutcome::EligibleSourceBoundary { .. } => {
                OcastEligibilityState::EligibleSourceBoundary
            }
            OcastEligibilityOutcome::InternalOnly { .. } => OcastEligibilityState::InternalOnly,
            OcastEligibilityOutcome::Incomplete { .. } => OcastEligibilityState::Incomplete,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OcastEligibilityOutcome {
    EligibleSourceBoundary {
        boundary: SourceBoundaryId,
        origin: OriginId,
        kind: ConstraintOriginKind,
        evidence: EligibleBoundaryEvidence,
    },
    InternalOnly {
        evidence: InternalOnlyEvidence,
    },
    Incomplete {
        reason: OcastIncompleteReason,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EligibleBoundaryEvidence {
    RootRelation {
        path: Vec<ExplanationNodeId>,
    },
    SharedReplayPair {
        replay: BinaryReplayDerivation,
        path_to_pair: Vec<ExplanationNodeId>,
    },
    OneSidedReplayPair {
        replay: BinaryReplayDerivation,
        source_parent: ReplaySourceParent,
        path_to_pair: Vec<ExplanationNodeId>,
    },
}

impl EligibleBoundaryEvidence {
    /// Preserve the classifier's already-bounded witness shape without exposing graph identities.
    pub(crate) fn diagnostic_kind(&self) -> EligibleBoundaryDiagnosticKind {
        match self {
            Self::RootRelation { .. } => EligibleBoundaryDiagnosticKind::RootRelation,
            Self::SharedReplayPair { .. } => EligibleBoundaryDiagnosticKind::SharedReplayPair,
            Self::OneSidedReplayPair { .. } => EligibleBoundaryDiagnosticKind::OneSidedReplayPair,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EligibleBoundaryDiagnosticKind {
    RootRelation,
    SharedReplayPair,
    OneSidedReplayPair,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplaySourceParent {
    Lower,
    Upper,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InternalOnlyEvidence {
    DisjointReplayParents {
        replay: BinaryReplayDerivation,
        lower_boundaries: Vec<SourceBoundaryEvidence>,
        upper_boundaries: Vec<SourceBoundaryEvidence>,
        disjoint_pair_count: usize,
    },
    NoEligibleSourceBoundary,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct SourceBoundaryEvidence {
    pub(crate) boundary: SourceBoundaryId,
    pub(crate) origin: OriginId,
    pub(crate) kind: ConstraintOriginKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OcastIncompleteReason {
    Query {
        completeness: ExplanationCompleteness,
        truncation: Option<ExplanationTruncationReason>,
    },
    QueryError(ExplanationQueryError),
    UnknownOrigin(OriginId),
    ImportedFact(OriginId),
    MissingOwnershipWitness(SourceBoundaryId),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct OcastEligibilityMetrics {
    pub classified: usize,
    pub eligible_source_boundary: usize,
    pub internal_only: usize,
    pub incomplete: usize,
    pub visited_nodes: usize,
    pub visited_edges: usize,
    pub elapsed: Duration,
}

impl OcastEligibilityMetrics {
    pub(crate) fn record(&mut self, classification: &OcastEligibilityClassification) {
        self.classified += 1;
        self.visited_nodes += classification.visited_nodes;
        self.visited_edges += classification.visited_edges;
        match classification.state() {
            OcastEligibilityState::EligibleSourceBoundary => self.eligible_source_boundary += 1,
            OcastEligibilityState::InternalOnly => self.internal_only += 1,
            OcastEligibilityState::Incomplete => self.incomplete += 1,
        }
    }
}

impl ConstraintMachine {
    pub(crate) fn classify_ocast_eligibility(
        &self,
        producer: ConstraintRecordId,
        budget: ExplanationBudget,
    ) -> OcastEligibilityClassification {
        // Body-use provenance explains a callee definition; it does not own the call-site cast
        // boundary. Including it here would let unrelated definition-internal unknown roots change
        // CPROV-I's already-approved eligibility decision.
        match self.why_constraint_without_scheme_instantiation(producer, budget) {
            Ok(explanation) => classify_explanation(producer, explanation),
            Err(error) => OcastEligibilityClassification {
                producer,
                outcome: OcastEligibilityOutcome::Incomplete {
                    reason: OcastIncompleteReason::QueryError(error),
                },
                visited_nodes: 0,
                visited_edges: 0,
            },
        }
    }
}

fn classify_explanation(
    producer: ConstraintRecordId,
    explanation: ExplanationQueryResult,
) -> OcastEligibilityClassification {
    let visited_nodes = explanation.nodes.len();
    let visited_edges = explanation.edges.len();
    if explanation.completeness != ExplanationCompleteness::Complete {
        return incomplete(
            producer,
            visited_nodes,
            visited_edges,
            OcastIncompleteReason::Query {
                completeness: explanation.completeness,
                truncation: explanation.truncation,
            },
        );
    }
    let unknown_origin = explanation.nodes.iter().find_map(|node| match node {
        ExplanationNode::Origin {
            id,
            kind: ConstraintOriginKind::UnknownInternal,
            ..
        } => Some(*id),
        _ => None,
    });
    let imported_origin = explanation.edges.iter().find_map(|edge| match edge.kind {
        ExplanationEdgeKind::SubtractFact(SubtractFactDerivation::Import(origin)) => Some(origin),
        _ => None,
    });
    if let Some(origin) = unknown_origin {
        return incomplete(
            producer,
            visited_nodes,
            visited_edges,
            OcastIncompleteReason::UnknownOrigin(origin),
        );
    }
    if let Some(origin) = imported_origin {
        return incomplete(
            producer,
            visited_nodes,
            visited_edges,
            OcastIncompleteReason::ImportedFact(origin),
        );
    }

    let boundary_evidence = explanation
        .source_leaves
        .iter()
        .map(|leaf| {
            (
                leaf.boundary,
                SourceBoundaryEvidence {
                    boundary: leaf.boundary,
                    origin: leaf.origin,
                    kind: leaf.kind,
                },
            )
        })
        .collect::<FxHashMap<_, _>>();
    let contributors = boundary_contributors(&explanation);
    let internal_ancestry = internal_ancestry(&explanation);
    let owners = coherent_boundary_owners(&explanation, &contributors, &internal_ancestry);
    let producer_node = ExplanationNodeId::Constraint(producer);
    let producer_owners = owners.get(&producer_node).cloned().unwrap_or_default();
    // A one-sided replay is source-owned only when alternate exact derivations do not bring a
    // second, independent source obligation into the same canonical producer.
    let producer_boundaries = explanation
        .source_leaves
        .iter()
        .filter(|leaf| is_eligible_source_kind(leaf.kind))
        .map(|leaf| leaf.boundary)
        .collect::<FxHashSet<_>>();

    if let Some(source) = explanation.source_leaves.iter().find(|leaf| {
        is_eligible_source_kind(leaf.kind)
            && producer_boundaries.len() == 1
            && producer_owners.contains(&leaf.boundary)
    }) {
        let Some(evidence) = find_eligible_evidence(
            producer_node,
            source.boundary,
            &owners,
            &contributors,
            &internal_ancestry,
            &explanation.edges,
        ) else {
            return incomplete(
                producer,
                visited_nodes,
                visited_edges,
                OcastIncompleteReason::MissingOwnershipWitness(source.boundary),
            );
        };
        return OcastEligibilityClassification {
            producer,
            outcome: OcastEligibilityOutcome::EligibleSourceBoundary {
                boundary: source.boundary,
                origin: source.origin,
                kind: source.kind,
                evidence,
            },
            visited_nodes,
            visited_edges,
        };
    }

    let disjoint = disjoint_replay_evidence(&explanation.edges, &contributors, &boundary_evidence);
    if let Some((replay, lower_boundaries, upper_boundaries)) = disjoint.first {
        return OcastEligibilityClassification {
            producer,
            outcome: OcastEligibilityOutcome::InternalOnly {
                evidence: InternalOnlyEvidence::DisjointReplayParents {
                    replay,
                    lower_boundaries,
                    upper_boundaries,
                    disjoint_pair_count: disjoint.count,
                },
            },
            visited_nodes,
            visited_edges,
        };
    }
    OcastEligibilityClassification {
        producer,
        outcome: OcastEligibilityOutcome::InternalOnly {
            evidence: InternalOnlyEvidence::NoEligibleSourceBoundary,
        },
        visited_nodes,
        visited_edges,
    }
}

fn incomplete(
    producer: ConstraintRecordId,
    visited_nodes: usize,
    visited_edges: usize,
    reason: OcastIncompleteReason,
) -> OcastEligibilityClassification {
    OcastEligibilityClassification {
        producer,
        outcome: OcastEligibilityOutcome::Incomplete { reason },
        visited_nodes,
        visited_edges,
    }
}

fn coherent_boundary_owners(
    explanation: &ExplanationQueryResult,
    contributors: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    internal_ancestry: &FxHashSet<ExplanationNodeId>,
) -> FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>> {
    let mut owners = FxHashMap::<ExplanationNodeId, FxHashSet<SourceBoundaryId>>::default();
    let mut dependents = FxHashMap::<ExplanationNodeId, Vec<usize>>::default();
    for (index, edge) in explanation.edges.iter().enumerate() {
        for parent in &edge.parents {
            dependents.entry(*parent).or_default().push(index);
        }
    }
    let mut changed = VecDeque::new();
    for leaf in &explanation.source_leaves {
        if !is_eligible_source_kind(leaf.kind) {
            continue;
        }
        let node = ExplanationNodeId::Origin(leaf.origin);
        if owners.entry(node).or_default().insert(leaf.boundary) {
            changed.push_back(node);
        }
    }
    while let Some(parent) = changed.pop_front() {
        for index in dependents.get(&parent).into_iter().flatten() {
            let edge = &explanation.edges[*index];
            let contribution =
                edge_boundary_contribution(edge, &owners, contributors, internal_ancestry);
            let child_owners = owners.entry(edge.child).or_default();
            let before = child_owners.len();
            child_owners.extend(contribution);
            if child_owners.len() != before {
                changed.push_back(edge.child);
            }
        }
    }
    owners
}

fn internal_ancestry(explanation: &ExplanationQueryResult) -> FxHashSet<ExplanationNodeId> {
    let mut internal = FxHashSet::default();
    let mut dependents = FxHashMap::<ExplanationNodeId, Vec<usize>>::default();
    for (index, edge) in explanation.edges.iter().enumerate() {
        for parent in &edge.parents {
            dependents.entry(*parent).or_default().push(index);
        }
    }
    let mut changed = VecDeque::new();
    for node in &explanation.nodes {
        let ExplanationNode::Origin {
            id,
            kind: ConstraintOriginKind::Internal,
            ..
        } = node
        else {
            continue;
        };
        let node = ExplanationNodeId::Origin(*id);
        if internal.insert(node) {
            changed.push_back(node);
        }
    }
    while let Some(parent) = changed.pop_front() {
        for index in dependents.get(&parent).into_iter().flatten() {
            let child = explanation.edges[*index].child;
            if internal.insert(child) {
                changed.push_back(child);
            }
        }
    }
    internal
}

fn boundary_contributors(
    explanation: &ExplanationQueryResult,
) -> FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>> {
    let mut contributors = FxHashMap::<ExplanationNodeId, FxHashSet<SourceBoundaryId>>::default();
    let mut dependents = FxHashMap::<ExplanationNodeId, Vec<usize>>::default();
    for (index, edge) in explanation.edges.iter().enumerate() {
        for parent in &edge.parents {
            dependents.entry(*parent).or_default().push(index);
        }
    }
    let mut changed = VecDeque::new();
    for leaf in &explanation.source_leaves {
        // Located body requirements are explanation leaves, not cast-boundary obligations.
        // Keep them out of ownership/contributor propagation so they neither become eligible nor
        // make an otherwise confidently-internal replay parent look like a competing source side.
        if !is_eligible_source_kind(leaf.kind) {
            continue;
        }
        let node = ExplanationNodeId::Origin(leaf.origin);
        if contributors.entry(node).or_default().insert(leaf.boundary) {
            changed.push_back(node);
        }
    }
    while let Some(parent) = changed.pop_front() {
        for index in dependents.get(&parent).into_iter().flatten() {
            let edge = &explanation.edges[*index];
            let contribution = edge
                .parents
                .iter()
                .flat_map(|parent| contributors.get(parent).into_iter().flatten().copied())
                .collect::<Vec<_>>();
            let child = contributors.entry(edge.child).or_default();
            let before = child.len();
            child.extend(contribution);
            if child.len() != before {
                changed.push_back(edge.child);
            }
        }
    }
    contributors
}

fn edge_boundary_contribution(
    edge: &ExplanationEdge,
    owners: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    contributors: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    internal_ancestry: &FxHashSet<ExplanationNodeId>,
) -> FxHashSet<SourceBoundaryId> {
    if let Some(boundaries) = eligible_replay_boundaries(edge, contributors, internal_ancestry) {
        return boundaries;
    }
    edge.parents
        .iter()
        .flat_map(|parent| owners.get(parent).into_iter().flatten().copied())
        .collect()
}

fn eligible_replay_boundaries(
    edge: &ExplanationEdge,
    contributors: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    internal_ancestry: &FxHashSet<ExplanationNodeId>,
) -> Option<FxHashSet<SourceBoundaryId>> {
    replay_pair(&edge.kind)?;
    let [lower, upper] = edge.parents.as_slice() else {
        return Some(FxHashSet::default());
    };
    let lower_boundaries = contributors.get(lower).cloned().unwrap_or_default();
    let upper_boundaries = contributors.get(upper).cloned().unwrap_or_default();
    let mut eligible = lower_boundaries
        .intersection(&upper_boundaries)
        .copied()
        .collect::<FxHashSet<_>>();
    if confidently_internal_only(*upper, contributors, internal_ancestry) {
        eligible.extend(lower_boundaries);
    }
    if confidently_internal_only(*lower, contributors, internal_ancestry) {
        eligible.extend(upper_boundaries);
    }
    Some(eligible)
}

fn confidently_internal_only(
    node: ExplanationNodeId,
    contributors: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    internal_ancestry: &FxHashSet<ExplanationNodeId>,
) -> bool {
    internal_ancestry.contains(&node) && contributors.get(&node).is_none_or(FxHashSet::is_empty)
}

fn find_eligible_evidence(
    start: ExplanationNodeId,
    boundary: SourceBoundaryId,
    owners: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    contributors: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    internal_ancestry: &FxHashSet<ExplanationNodeId>,
    edges: &[ExplanationEdge],
) -> Option<EligibleBoundaryEvidence> {
    let mut current = start;
    let mut path = vec![start];
    let mut visited = FxHashSet::default();
    while visited.insert(current) {
        if matches!(current, ExplanationNodeId::Origin(_)) {
            return Some(EligibleBoundaryEvidence::RootRelation { path });
        }
        let edge = edges.iter().find(|edge| {
            edge.child == current
                && edge_boundary_contribution(edge, owners, contributors, internal_ancestry)
                    .contains(&boundary)
        })?;
        if let Some(replay) = replay_pair(&edge.kind) {
            let [lower, upper] = edge.parents.as_slice() else {
                return None;
            };
            let lower_has_boundary = contributors
                .get(lower)
                .is_some_and(|set| set.contains(&boundary));
            let upper_has_boundary = contributors
                .get(upper)
                .is_some_and(|set| set.contains(&boundary));
            if lower_has_boundary && upper_has_boundary {
                return Some(EligibleBoundaryEvidence::SharedReplayPair {
                    replay,
                    path_to_pair: path,
                });
            }
            let source_parent = match (lower_has_boundary, upper_has_boundary) {
                (true, false) => ReplaySourceParent::Lower,
                (false, true) => ReplaySourceParent::Upper,
                _ => return None,
            };
            return Some(EligibleBoundaryEvidence::OneSidedReplayPair {
                replay,
                source_parent,
                path_to_pair: path,
            });
        }
        current = edge.parents.iter().copied().find(|parent| {
            owners
                .get(parent)
                .is_some_and(|set| set.contains(&boundary))
        })?;
        path.push(current);
    }
    None
}

struct DisjointReplayEvidence {
    first: Option<(
        BinaryReplayDerivation,
        Vec<SourceBoundaryEvidence>,
        Vec<SourceBoundaryEvidence>,
    )>,
    count: usize,
}

fn disjoint_replay_evidence(
    edges: &[ExplanationEdge],
    owners: &FxHashMap<ExplanationNodeId, FxHashSet<SourceBoundaryId>>,
    evidence: &FxHashMap<SourceBoundaryId, SourceBoundaryEvidence>,
) -> DisjointReplayEvidence {
    let mut result = DisjointReplayEvidence {
        first: None,
        count: 0,
    };
    for edge in edges {
        let Some(replay) = replay_pair(&edge.kind) else {
            continue;
        };
        let [lower, upper] = edge.parents.as_slice() else {
            continue;
        };
        let lower = owners.get(lower).cloned().unwrap_or_default();
        let upper = owners.get(upper).cloned().unwrap_or_default();
        if lower.is_empty()
            || upper.is_empty()
            || lower.iter().any(|boundary| upper.contains(boundary))
        {
            continue;
        }
        result.count += 1;
        if result.first.is_none() {
            result.first = Some((
                replay,
                sorted_boundary_evidence(&lower, evidence),
                sorted_boundary_evidence(&upper, evidence),
            ));
        }
    }
    result
}

fn sorted_boundary_evidence(
    boundaries: &FxHashSet<SourceBoundaryId>,
    evidence: &FxHashMap<SourceBoundaryId, SourceBoundaryEvidence>,
) -> Vec<SourceBoundaryEvidence> {
    let mut result = boundaries
        .iter()
        .filter_map(|boundary| evidence.get(boundary).copied())
        .collect::<Vec<_>>();
    result.sort_by_key(|item| item.boundary.0);
    result
}

fn replay_pair(kind: &ExplanationEdgeKind) -> Option<BinaryReplayDerivation> {
    match kind {
        ExplanationEdgeKind::BinaryReplay(replay)
        | ExplanationEdgeKind::Bound(BoundDerivation::ReplayEvidence(replay)) => Some(*replay),
        _ => None,
    }
}

fn is_eligible_source_kind(kind: ConstraintOriginKind) -> bool {
    matches!(
        kind,
        ConstraintOriginKind::ApplicationArgument
            | ConstraintOriginKind::Annotation
            | ConstraintOriginKind::Return
            | ConstraintOriginKind::Field
            | ConstraintOriginKind::Assignment
    )
}
