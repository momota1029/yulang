//! Bounded, deterministic traversal of the canonical constraint derivation graph.
//!
//! Each record's derivation categories are visited in the order encoded by
//! `visit_*_edges`; records within a category and parents within a hyperedge keep
//! their append-only insertion order. Traversal is depth-first pre-order, and a
//! record is expanded only on its first visit. These rules make a truncated
//! result stable without sorting or enumerating combinations of proof paths.

use super::*;

const DEFAULT_EXPLANATION_NODES: usize = 512;
const DEFAULT_EXPLANATION_EDGES: usize = 1_024;
const DEFAULT_EXPLANATION_DEPTH: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExplanationBudget {
    pub(crate) max_nodes: usize,
    pub(crate) max_edges: usize,
    pub(crate) max_depth: usize,
}

impl Default for ExplanationBudget {
    fn default() -> Self {
        Self {
            max_nodes: DEFAULT_EXPLANATION_NODES,
            max_edges: DEFAULT_EXPLANATION_EDGES,
            max_depth: DEFAULT_EXPLANATION_DEPTH,
        }
    }
}

impl ExplanationBudget {
    pub(crate) fn ocast_classifier() -> Self {
        Self {
            max_nodes: 4_096,
            max_edges: 8_192,
            max_depth: 128,
        }
    }

    pub(crate) fn parameter_body_diagnostic() -> Self {
        Self {
            max_nodes: 4_096,
            max_edges: 8_192,
            max_depth: 512,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ExplanationNodeId {
    Constraint(ConstraintRecordId),
    Bound(BoundRecordId),
    Origin(OriginId),
    RowDerivation(RowDerivationId),
    SubtractFact(SubtractFactRecordId),
    LowerFilter(LowerFilterRecordId),
    BoundDisposition(BoundDispositionRecordId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExplanationNode {
    Constraint {
        id: ConstraintRecordId,
        key: SubtypeConstraintKey,
        replay_provenance: ProvenanceCompleteness,
    },
    Bound {
        id: BoundRecordId,
        direction: BoundDirection,
        owner: TypeVar,
        endpoint: BoundEndpoint,
        weights: ConstraintWeights,
        state: BoundRecordState,
    },
    Origin {
        id: OriginId,
        kind: ConstraintOriginKind,
        source_boundary: Option<SourceBoundaryId>,
    },
    RowDerivation {
        id: RowDerivationId,
        rule: RowDerivationRule,
        retained_items: Vec<NegId>,
    },
    SubtractFact {
        id: SubtractFactRecordId,
        effect: TypeVar,
        fact: SubtractFact,
        active: bool,
    },
    LowerFilter {
        id: LowerFilterRecordId,
        var: TypeVar,
        filter: Subtractability,
    },
    BoundDisposition {
        id: BoundDispositionRecordId,
        direction: BoundDirection,
        owner: TypeVar,
        endpoint: BoundEndpoint,
        weights: ConstraintWeights,
        disposition: BoundDisposition,
    },
    GeneralizedWitness {
        id: GeneralizedSchemeWitnessId,
        scheme: GeneralizedSchemeRecordId,
        path: GeneralizedTypePath,
        role: GeneralizedWitnessRole,
        completeness: ProvenanceCompleteness,
    },
}

impl ExplanationNode {
    pub(crate) fn id(&self) -> ExplanationNodeId {
        match self {
            Self::Constraint { id, .. } => ExplanationNodeId::Constraint(*id),
            Self::Bound { id, .. } => ExplanationNodeId::Bound(*id),
            Self::Origin { id, .. } => ExplanationNodeId::Origin(*id),
            Self::RowDerivation { id, .. } => ExplanationNodeId::RowDerivation(*id),
            Self::SubtractFact { id, .. } => ExplanationNodeId::SubtractFact(*id),
            Self::LowerFilter { id, .. } => ExplanationNodeId::LowerFilter(*id),
            Self::BoundDisposition { id, .. } => ExplanationNodeId::BoundDisposition(*id),
            Self::GeneralizedWitness { id, .. } => ExplanationNodeId::GeneralizedWitness(*id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExplanationEdge {
    pub(crate) child: ExplanationNodeId,
    pub(crate) kind: ExplanationEdgeKind,
    pub(crate) parents: Vec<ExplanationNodeId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExplanationEdgeKind {
    RootOrigin,
    Structural(StructuralDerivationRule),
    BinaryReplay(BinaryReplayDerivation),
    RowResult(RowDerivationId),
    Canonicalization(ConstraintCanonicalizationDisposition),
    Bound(BoundDerivation),
    Row(RowDerivationRule),
    LowerFilter,
    SubtractFact(SubtractFactDerivation),
    BoundDisposition(BoundDisposition),
    Generalization(GeneralizationDerivationRule),
    SchemeInstantiation(SchemeInstantiationDerivation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ExplanationSourceLeaf {
    pub(crate) origin: OriginId,
    pub(crate) boundary: SourceBoundaryId,
    pub(crate) kind: ConstraintOriginKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExplanationCompleteness {
    Complete,
    TruncatedByBudget,
    IncompleteProvenance,
    TruncatedAndIncompleteProvenance,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExplanationTruncationReason {
    NodeBudget { limit: usize },
    EdgeBudget { limit: usize },
    DepthBudget { limit: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExplanationQueryResult {
    pub(crate) nodes: Vec<ExplanationNode>,
    pub(crate) edges: Vec<ExplanationEdge>,
    pub(crate) source_leaves: Vec<ExplanationSourceLeaf>,
    pub(crate) completeness: ExplanationCompleteness,
    pub(crate) truncation: Option<ExplanationTruncationReason>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ParameterBodyRequirementProjectionState {
    MatchedSchemePath,
    NoSchemeInstantiationBridge,
    AnchorUnavailable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParameterBodyRequirementProjection {
    pub(crate) producer: ConstraintRecordId,
    pub(crate) parameter_bound: BoundRecordId,
    pub(crate) state: ParameterBodyRequirementProjectionState,
    pub(crate) requirements: Vec<ParameterBodyRequirementWitness>,
    pub(crate) completeness: ExplanationCompleteness,
    pub(crate) truncation: Option<ExplanationTruncationReason>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParameterBodyRequirementWitness {
    pub(crate) instantiation: SchemeInstantiationId,
    pub(crate) generalized_witness: GeneralizedSchemeWitnessId,
    pub(crate) path: GeneralizedTypePath,
    pub(crate) role: GeneralizedWitnessRole,
    pub(crate) origin: OriginId,
    pub(crate) boundary: SourceBoundaryId,
    pub(crate) kind: BodyRequirementKind,
    pub(crate) graph_path: Vec<ExplanationNodeId>,
}

/// Project body-owned requirements from an already-bounded explanation.
///
/// `parameter_bound` is the exact replay parent selected by the caller as the callee parameter
/// side. The projection follows scheme-instantiation bridges reachable below that canonical bound,
/// then follows each bridge's exact generalized witness path without crossing a nested bridge. It
/// never scans the query's global source-leaf list for an arbitrary body requirement.
pub(crate) fn project_parameter_body_requirements(
    producer: ConstraintRecordId,
    parameter_bound: BoundRecordId,
    explanation: &ExplanationQueryResult,
) -> ParameterBodyRequirementProjection {
    let root = ExplanationNodeId::Constraint(producer);
    let anchor = ExplanationNodeId::Bound(parameter_bound);
    let root_present = explanation.nodes.iter().any(|node| node.id() == root);
    let anchor_present = explanation.nodes.iter().any(|node| node.id() == anchor);
    if !root_present || !anchor_present || !is_reachable(explanation, root, anchor) {
        return ParameterBodyRequirementProjection {
            producer,
            parameter_bound,
            state: ParameterBodyRequirementProjectionState::AnchorUnavailable,
            requirements: Vec::new(),
            completeness: explanation.completeness,
            truncation: explanation.truncation,
        };
    }

    let bridges = reachable_scheme_instantiation_bridges(explanation, anchor);
    let mut requirements = Vec::new();
    let mut seen = FxHashSet::default();
    for bridge in &bridges {
        let Some((derivation, witness_node)) =
            scheme_instantiation_bridge(explanation, bridge.edge)
        else {
            continue;
        };
        let ExplanationNode::GeneralizedWitness {
            id,
            path,
            role,
            completeness: _,
            scheme: _,
        } = witness_node
        else {
            continue;
        };
        // The path on the realized instantiation mapping and the source witness are one identity.
        // A mismatch here is incomplete provenance, never a reason to select another leaf.
        if *id != derivation.source_witness || *path != derivation.path {
            continue;
        }
        collect_body_requirements(
            explanation,
            derivation,
            *role,
            &bridge.path,
            &mut seen,
            &mut requirements,
        );
    }

    ParameterBodyRequirementProjection {
        producer,
        parameter_bound,
        state: if bridges.is_empty() {
            ParameterBodyRequirementProjectionState::NoSchemeInstantiationBridge
        } else {
            ParameterBodyRequirementProjectionState::MatchedSchemePath
        },
        requirements,
        completeness: explanation.completeness,
        truncation: explanation.truncation,
    }
}

pub(crate) fn generalized_scheme_path_reaches_origin_kind(
    explanation: &ExplanationQueryResult,
    witness: GeneralizedSchemeWitnessId,
    expected: ConstraintOriginKind,
) -> bool {
    let Some(ExplanationNode::GeneralizedWitness { scheme, path, .. }) = explanation
        .nodes
        .iter()
        .find(|node| node.id() == ExplanationNodeId::GeneralizedWitness(witness))
    else {
        return false;
    };
    let mut pending = explanation
        .nodes
        .iter()
        .filter_map(|node| match node {
            ExplanationNode::GeneralizedWitness {
                id,
                scheme: candidate_scheme,
                path: candidate_path,
                ..
            } if candidate_scheme == scheme && candidate_path == path => {
                Some(ExplanationNodeId::GeneralizedWitness(*id))
            }
            _ => None,
        })
        .collect::<VecDeque<_>>();
    let mut visited = FxHashSet::default();
    while let Some(node) = pending.pop_front() {
        if !visited.insert(node) {
            continue;
        }
        if explanation.nodes.iter().any(|candidate| {
            matches!(candidate, ExplanationNode::Origin { kind, .. } if candidate.id() == node && *kind == expected)
        }) {
            return true;
        }
        for parent in explanation
            .edges
            .iter()
            .filter(|edge| edge.child == node && !is_scheme_instantiation_edge(edge))
            .flat_map(|edge| edge.parents.iter().copied())
        {
            pending.push_back(parent);
        }
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExplanationQueryError {
    UnknownConstraint(ConstraintRecordId),
    UnknownBound(BoundRecordId),
    UnknownBoundDisposition(BoundDispositionRecordId),
    UnknownGeneralizedWitness(GeneralizedSchemeWitnessId),
    BoundOwner {
        expected: TypeVar,
        actual: TypeVar,
    },
    BoundDirection {
        expected: BoundDirection,
        actual: BoundDirection,
    },
}

impl ConstraintMachine {
    pub(crate) fn why_constraint(
        &self,
        record: ConstraintRecordId,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        if self.constraint_records.get(record.0 as usize).is_none() {
            return Err(ExplanationQueryError::UnknownConstraint(record));
        }
        Ok(ExplanationQuery::new(self, budget).run(ExplanationNodeId::Constraint(record)))
    }

    pub(super) fn why_constraint_without_scheme_instantiation(
        &self,
        record: ConstraintRecordId,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        if self.constraint_records.get(record.0 as usize).is_none() {
            return Err(ExplanationQueryError::UnknownConstraint(record));
        }
        Ok(
            ExplanationQuery::new_without_scheme_instantiation(self, budget)
                .run(ExplanationNodeId::Constraint(record)),
        )
    }

    pub(crate) fn why_lower_bound(
        &self,
        var: TypeVar,
        record: BoundRecordId,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        self.why_bound(var, record, BoundDirection::Lower, budget)
    }

    pub(crate) fn why_upper_bound(
        &self,
        var: TypeVar,
        record: BoundRecordId,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        self.why_bound(var, record, BoundDirection::Upper, budget)
    }

    pub(crate) fn why_bound_disposition(
        &self,
        record: BoundDispositionRecordId,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        if self.bound_dispositions.get(record.0 as usize).is_none() {
            return Err(ExplanationQueryError::UnknownBoundDisposition(record));
        }
        Ok(ExplanationQuery::new(self, budget).run(ExplanationNodeId::BoundDisposition(record)))
    }

    pub(crate) fn why_generalized_witness(
        &self,
        witness: GeneralizedSchemeWitnessId,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        if self.generalized_scheme_witness(witness).is_none() {
            return Err(ExplanationQueryError::UnknownGeneralizedWitness(witness));
        }
        Ok(ExplanationQuery::new(self, budget).run(ExplanationNodeId::GeneralizedWitness(witness)))
    }

    fn why_bound(
        &self,
        var: TypeVar,
        record: BoundRecordId,
        direction: BoundDirection,
        budget: ExplanationBudget,
    ) -> Result<ExplanationQueryResult, ExplanationQueryError> {
        let Some(bound) = self.bounds.record(record) else {
            return Err(ExplanationQueryError::UnknownBound(record));
        };
        if bound.owner != var {
            return Err(ExplanationQueryError::BoundOwner {
                expected: var,
                actual: bound.owner,
            });
        }
        if bound.direction != direction {
            return Err(ExplanationQueryError::BoundDirection {
                expected: direction,
                actual: bound.direction,
            });
        }
        Ok(ExplanationQuery::new(self, budget).run(ExplanationNodeId::Bound(record)))
    }
}

struct ExplanationQuery<'a> {
    machine: &'a ConstraintMachine,
    budget: ExplanationBudget,
    nodes: Vec<ExplanationNode>,
    edges: Vec<ExplanationEdge>,
    source_leaves: Vec<ExplanationSourceLeaf>,
    visited: FxHashSet<ExplanationNodeId>,
    truncation: Option<ExplanationTruncationReason>,
    underlying_incomplete: bool,
    include_scheme_instantiation: bool,
}

impl<'a> ExplanationQuery<'a> {
    fn new(machine: &'a ConstraintMachine, budget: ExplanationBudget) -> Self {
        Self {
            machine,
            budget,
            nodes: Vec::new(),
            edges: Vec::new(),
            source_leaves: Vec::new(),
            visited: FxHashSet::default(),
            truncation: None,
            underlying_incomplete: false,
            include_scheme_instantiation: true,
        }
    }

    fn new_without_scheme_instantiation(
        machine: &'a ConstraintMachine,
        budget: ExplanationBudget,
    ) -> Self {
        let mut query = Self::new(machine, budget);
        query.include_scheme_instantiation = false;
        query
    }

    fn run(mut self, root: ExplanationNodeId) -> ExplanationQueryResult {
        self.visit(root, 0);
        let completeness = match (self.truncation.is_some(), self.underlying_incomplete) {
            (false, false) => ExplanationCompleteness::Complete,
            (true, false) => ExplanationCompleteness::TruncatedByBudget,
            (false, true) => ExplanationCompleteness::IncompleteProvenance,
            (true, true) => ExplanationCompleteness::TruncatedAndIncompleteProvenance,
        };
        ExplanationQueryResult {
            nodes: self.nodes,
            edges: self.edges,
            source_leaves: self.source_leaves,
            completeness,
            truncation: self.truncation,
        }
    }

    fn visit(&mut self, id: ExplanationNodeId, depth: usize) {
        if self.truncation.is_some() || self.visited.contains(&id) {
            return;
        }
        if self.nodes.len() >= self.budget.max_nodes {
            self.truncation = Some(ExplanationTruncationReason::NodeBudget {
                limit: self.budget.max_nodes,
            });
            return;
        }
        let Some(node) = self.node(id) else {
            self.underlying_incomplete = true;
            return;
        };
        self.visited.insert(id);
        self.record_source_leaf(&node);
        self.nodes.push(node);

        if depth >= self.budget.max_depth && self.has_incoming_edges(id) {
            self.truncation = Some(ExplanationTruncationReason::DepthBudget {
                limit: self.budget.max_depth,
            });
            return;
        }
        self.visit_incoming_edges(id, depth);
    }

    fn push_edge(&mut self, edge: ExplanationEdge, depth: usize) {
        if self.truncation.is_some() {
            return;
        }
        if self.edges.len() >= self.budget.max_edges {
            self.truncation = Some(ExplanationTruncationReason::EdgeBudget {
                limit: self.budget.max_edges,
            });
            return;
        }
        let parents = edge.parents.clone();
        self.edges.push(edge);
        for parent in parents {
            self.visit(parent, depth + 1);
            if self.truncation.is_some() {
                break;
            }
        }
    }

    fn node(&mut self, id: ExplanationNodeId) -> Option<ExplanationNode> {
        match id {
            ExplanationNodeId::Constraint(id) => {
                let record = self.machine.constraint_records.get(id.0 as usize)?;
                if record.replay_provenance == ProvenanceCompleteness::Incomplete {
                    self.underlying_incomplete = true;
                }
                Some(ExplanationNode::Constraint {
                    id,
                    key: record.key.clone(),
                    replay_provenance: record.replay_provenance,
                })
            }
            ExplanationNodeId::Bound(id) => {
                let record = self.machine.bounds.record(id)?;
                Some(ExplanationNode::Bound {
                    id,
                    direction: record.direction,
                    owner: record.owner,
                    endpoint: record.endpoint,
                    weights: record.weights.clone(),
                    state: record.state,
                })
            }
            ExplanationNodeId::Origin(id) => {
                let record = self.machine.origins.get(id.0 as usize)?;
                Some(ExplanationNode::Origin {
                    id,
                    kind: record.kind,
                    source_boundary: record.source_boundary,
                })
            }
            ExplanationNodeId::RowDerivation(id) => {
                let record = self.machine.row_derivations.get(id.0 as usize)?;
                Some(ExplanationNode::RowDerivation {
                    id,
                    rule: record.rule,
                    retained_items: record.retained_items.clone(),
                })
            }
            ExplanationNodeId::SubtractFact(id) => {
                let record = self.machine.subtracts.record(id)?;
                Some(ExplanationNode::SubtractFact {
                    id,
                    effect: record.key.effect,
                    fact: record.key.fact.clone(),
                    active: record.active,
                })
            }
            ExplanationNodeId::LowerFilter(id) => {
                let record = self.machine.lower_filter_records.get(id.0 as usize)?;
                Some(ExplanationNode::LowerFilter {
                    id,
                    var: record.var,
                    filter: record.filter.clone(),
                })
            }
            ExplanationNodeId::BoundDisposition(id) => {
                let record = self.machine.bound_dispositions.get(id.0 as usize)?;
                Some(ExplanationNode::BoundDisposition {
                    id,
                    direction: record.direction,
                    owner: record.owner,
                    endpoint: record.endpoint,
                    weights: record.weights.clone(),
                    disposition: record.disposition,
                })
            }
            ExplanationNodeId::GeneralizedWitness(id) => {
                let record = self.machine.generalized_scheme_witness(id)?;
                if record.completeness == ProvenanceCompleteness::Incomplete {
                    self.underlying_incomplete = true;
                }
                Some(ExplanationNode::GeneralizedWitness {
                    id,
                    scheme: record.scheme,
                    path: record.path.clone(),
                    role: record.role,
                    completeness: record.completeness,
                })
            }
        }
    }

    fn record_source_leaf(&mut self, node: &ExplanationNode) {
        let ExplanationNode::Origin {
            id,
            kind,
            source_boundary: Some(boundary),
        } = *node
        else {
            return;
        };
        if kind.is_source()
            && self
                .machine
                .source_boundaries
                .get(boundary.0 as usize)
                .is_some_and(|record| record.origin == id)
        {
            self.source_leaves.push(ExplanationSourceLeaf {
                origin: id,
                boundary,
                kind,
            });
        }
    }

    fn has_incoming_edges(&self, id: ExplanationNodeId) -> bool {
        match id {
            ExplanationNodeId::Constraint(id) => self
                .machine
                .constraint_records
                .get(id.0 as usize)
                .is_some_and(|record| {
                    !record.root_origins.is_empty()
                        || !record.structural_derivations.is_empty()
                        || !record.row_derivations.is_empty()
                        || !record.replay_derivations.is_empty()
                        || !record.canonicalization_dispositions.is_empty()
                }),
            ExplanationNodeId::Bound(id) => self.machine.bounds.record(id).is_some_and(|record| {
                !record.derivations.is_empty() || record.disposition.is_some()
            }),
            ExplanationNodeId::Origin(_) => false,
            ExplanationNodeId::RowDerivation(id) => self
                .machine
                .row_derivations
                .get(id.0 as usize)
                .is_some_and(|record| !record.parents.is_empty()),
            ExplanationNodeId::SubtractFact(id) => self
                .machine
                .subtracts
                .record(id)
                .is_some_and(|record| !record.derivations.is_empty()),
            ExplanationNodeId::LowerFilter(id) => self
                .machine
                .lower_filter_records
                .get(id.0 as usize)
                .is_some_and(|record| !record.derivations.is_empty()),
            ExplanationNodeId::BoundDisposition(id) => self
                .machine
                .bound_dispositions
                .get(id.0 as usize)
                .is_some_and(|record| {
                    record.derivation.is_some()
                        || !matches!(record.disposition, BoundDisposition::Trivial(_))
                }),
            ExplanationNodeId::GeneralizedWitness(id) => self
                .machine
                .generalized_scheme_witness(id)
                .is_some_and(|record| !record.incoming.is_empty()),
        }
    }

    fn visit_incoming_edges(&mut self, id: ExplanationNodeId, depth: usize) {
        match id {
            ExplanationNodeId::Constraint(id) => self.visit_constraint_edges(id, depth),
            ExplanationNodeId::Bound(id) => self.visit_bound_edges(id, depth),
            ExplanationNodeId::Origin(_) => {}
            ExplanationNodeId::RowDerivation(id) => self.visit_row_edges(id, depth),
            ExplanationNodeId::SubtractFact(id) => self.visit_subtract_edges(id, depth),
            ExplanationNodeId::LowerFilter(id) => self.visit_filter_edges(id, depth),
            ExplanationNodeId::BoundDisposition(id) => self.visit_disposition_edges(id, depth),
            ExplanationNodeId::GeneralizedWitness(id) => {
                self.visit_generalized_witness_edges(id, depth)
            }
        }
    }

    fn visit_constraint_edges(&mut self, id: ConstraintRecordId, depth: usize) {
        let record = self.machine.constraint_records[id.0 as usize].clone();
        for origin in record.root_origins {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Constraint(id),
                    kind: ExplanationEdgeKind::RootOrigin,
                    parents: vec![ExplanationNodeId::Origin(origin)],
                },
                depth,
            );
        }
        for derivation in record.structural_derivations {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Constraint(id),
                    kind: ExplanationEdgeKind::Structural(derivation.rule),
                    parents: vec![ExplanationNodeId::Constraint(derivation.parent)],
                },
                depth,
            );
        }
        for derivation in record.row_derivations {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Constraint(id),
                    kind: ExplanationEdgeKind::RowResult(derivation),
                    parents: vec![ExplanationNodeId::RowDerivation(derivation)],
                },
                depth,
            );
        }
        for derivation in record.replay_derivations {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Constraint(id),
                    kind: ExplanationEdgeKind::BinaryReplay(derivation),
                    parents: vec![
                        ExplanationNodeId::Bound(derivation.lower),
                        ExplanationNodeId::Bound(derivation.upper),
                    ],
                },
                depth,
            );
        }
        if self.include_scheme_instantiation {
            for derivation in record.scheme_instantiation_derivations {
                self.push_edge(
                    ExplanationEdge {
                        child: ExplanationNodeId::Constraint(id),
                        kind: ExplanationEdgeKind::SchemeInstantiation(derivation.clone()),
                        parents: vec![ExplanationNodeId::GeneralizedWitness(
                            derivation.source_witness,
                        )],
                    },
                    depth,
                );
            }
        }
        for disposition in record.canonicalization_dispositions {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Constraint(id),
                    kind: ExplanationEdgeKind::Canonicalization(disposition),
                    parents: Vec::new(),
                },
                depth,
            );
        }
    }

    fn visit_bound_edges(&mut self, id: BoundRecordId, depth: usize) {
        let record = self
            .machine
            .bounds
            .record(id)
            .expect("visited bound")
            .clone();
        for derivation in record.derivations {
            if !self.include_scheme_instantiation
                && matches!(derivation, BoundDerivation::SchemeInstantiation(_))
            {
                continue;
            }
            let parents = self.bound_derivation_parents(&derivation);
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Bound(id),
                    kind: ExplanationEdgeKind::Bound(derivation),
                    parents,
                },
                depth,
            );
        }
        if let Some(disposition) = record.disposition {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::Bound(id),
                    kind: ExplanationEdgeKind::BoundDisposition(
                        self.machine.bound_dispositions[disposition.0 as usize].disposition,
                    ),
                    parents: vec![ExplanationNodeId::BoundDisposition(disposition)],
                },
                depth,
            );
        }
    }

    fn visit_row_edges(&mut self, id: RowDerivationId, depth: usize) {
        let record = self.machine.row_derivations[id.0 as usize].clone();
        self.push_edge(
            ExplanationEdge {
                child: ExplanationNodeId::RowDerivation(id),
                kind: ExplanationEdgeKind::Row(record.rule),
                parents: record.parents.into_iter().map(row_parent_node).collect(),
            },
            depth,
        );
    }

    fn visit_subtract_edges(&mut self, id: SubtractFactRecordId, depth: usize) {
        let derivations = self.machine.subtracts.records[id.0 as usize]
            .derivations
            .clone();
        for derivation in derivations {
            let origin = match derivation {
                SubtractFactDerivation::Declaration(origin)
                | SubtractFactDerivation::Import(origin)
                | SubtractFactDerivation::Internal(origin) => origin,
            };
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::SubtractFact(id),
                    kind: ExplanationEdgeKind::SubtractFact(derivation),
                    parents: vec![ExplanationNodeId::Origin(origin)],
                },
                depth,
            );
        }
    }

    fn visit_filter_edges(&mut self, id: LowerFilterRecordId, depth: usize) {
        let derivations = self.machine.lower_filter_records[id.0 as usize]
            .derivations
            .clone();
        for derivation in derivations {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::LowerFilter(id),
                    kind: ExplanationEdgeKind::LowerFilter,
                    parents: derivation
                        .parents
                        .into_iter()
                        .map(row_parent_node)
                        .collect(),
                },
                depth,
            );
        }
    }

    fn visit_disposition_edges(&mut self, id: BoundDispositionRecordId, depth: usize) {
        let record = self.machine.bound_dispositions[id.0 as usize].clone();
        let mut parents = record
            .derivation
            .into_iter()
            .flat_map(|derivation| self.bound_derivation_parents(&derivation))
            .collect::<Vec<_>>();
        match record.disposition {
            BoundDisposition::Inserted(bound)
            | BoundDisposition::EquivalentTo(bound)
            | BoundDisposition::SubsumedBy(bound) => {
                parents.push(ExplanationNodeId::Bound(bound));
            }
            BoundDisposition::Trivial(_) => {}
        }
        self.push_edge(
            ExplanationEdge {
                child: ExplanationNodeId::BoundDisposition(id),
                kind: ExplanationEdgeKind::BoundDisposition(record.disposition),
                parents,
            },
            depth,
        );
    }

    fn visit_generalized_witness_edges(&mut self, id: GeneralizedSchemeWitnessId, depth: usize) {
        let incoming = self
            .machine
            .generalized_scheme_witness(id)
            .expect("visited generalized witness")
            .incoming
            .clone();
        for derivation in incoming {
            self.push_edge(
                ExplanationEdge {
                    child: ExplanationNodeId::GeneralizedWitness(id),
                    kind: ExplanationEdgeKind::Generalization(derivation.rule),
                    parents: derivation
                        .parents
                        .into_iter()
                        .map(|parent| match parent {
                            GeneralizationParent::Constraint(id) => {
                                ExplanationNodeId::Constraint(id)
                            }
                            GeneralizationParent::Bound(id) => ExplanationNodeId::Bound(id),
                        })
                        .collect(),
                },
                depth,
            );
        }
    }

    fn bound_derivation_parents(&mut self, derivation: &BoundDerivation) -> Vec<ExplanationNodeId> {
        match derivation {
            BoundDerivation::Constraint(parent) => vec![ExplanationNodeId::Constraint(*parent)],
            BoundDerivation::Origin(origin) => vec![ExplanationNodeId::Origin(*origin)],
            BoundDerivation::ReplayEvidence(replay) => vec![
                ExplanationNodeId::Bound(replay.lower),
                ExplanationNodeId::Bound(replay.upper),
            ],
            BoundDerivation::Row(row) => vec![ExplanationNodeId::RowDerivation(*row)],
            BoundDerivation::SchemeInstantiation(derivation) => {
                vec![ExplanationNodeId::GeneralizedWitness(
                    derivation.source_witness,
                )]
            }
            BoundDerivation::IncompleteReplay => {
                self.underlying_incomplete = true;
                Vec::new()
            }
        }
    }
}

fn row_parent_node(parent: RowDerivationParent) -> ExplanationNodeId {
    match parent {
        RowDerivationParent::Constraint(id) => ExplanationNodeId::Constraint(id),
        RowDerivationParent::Bound(id) => ExplanationNodeId::Bound(id),
        RowDerivationParent::SubtractFact(id) => ExplanationNodeId::SubtractFact(id),
        RowDerivationParent::RowDerivation(id) => ExplanationNodeId::RowDerivation(id),
        RowDerivationParent::LowerFilter(id) => ExplanationNodeId::LowerFilter(id),
        RowDerivationParent::Origin(id) => ExplanationNodeId::Origin(id),
    }
}

#[derive(Debug)]
struct NearestSchemeBridge {
    edge: usize,
    path: Vec<ExplanationNodeId>,
}

fn is_reachable(
    explanation: &ExplanationQueryResult,
    root: ExplanationNodeId,
    target: ExplanationNodeId,
) -> bool {
    let mut pending = VecDeque::from([root]);
    let mut visited = FxHashSet::default();
    while let Some(node) = pending.pop_front() {
        if !visited.insert(node) {
            continue;
        }
        if node == target {
            return true;
        }
        for parent in explanation
            .edges
            .iter()
            .filter(|edge| edge.child == node)
            .flat_map(|edge| edge.parents.iter().copied())
        {
            pending.push_back(parent);
        }
    }
    false
}

fn reachable_scheme_instantiation_bridges(
    explanation: &ExplanationQueryResult,
    anchor: ExplanationNodeId,
) -> Vec<NearestSchemeBridge> {
    let mut pending = VecDeque::from([(anchor, vec![anchor])]);
    let mut visited = FxHashSet::from_iter([anchor]);
    let mut bridges = Vec::new();
    while let Some((node, path)) = pending.pop_front() {
        for (index, edge) in explanation
            .edges
            .iter()
            .enumerate()
            .filter(|(_, edge)| edge.child == node)
        {
            if is_scheme_instantiation_edge(edge) {
                bridges.push(NearestSchemeBridge {
                    edge: index,
                    path: path.clone(),
                });
                continue;
            }
            for parent in &edge.parents {
                if visited.insert(*parent) {
                    let mut parent_path = path.clone();
                    parent_path.push(*parent);
                    pending.push_back((*parent, parent_path));
                }
            }
        }
    }
    bridges
}

fn is_scheme_instantiation_edge(edge: &ExplanationEdge) -> bool {
    matches!(
        edge.kind,
        ExplanationEdgeKind::SchemeInstantiation(_)
            | ExplanationEdgeKind::Bound(BoundDerivation::SchemeInstantiation(_))
    )
}

fn scheme_instantiation_bridge<'a>(
    explanation: &'a ExplanationQueryResult,
    edge: usize,
) -> Option<(&'a SchemeInstantiationDerivation, &'a ExplanationNode)> {
    let edge = explanation.edges.get(edge)?;
    let derivation = match &edge.kind {
        ExplanationEdgeKind::SchemeInstantiation(derivation)
        | ExplanationEdgeKind::Bound(BoundDerivation::SchemeInstantiation(derivation)) => {
            derivation
        }
        _ => return None,
    };
    let witness = explanation.nodes.iter().find(|node| {
        node.id() == ExplanationNodeId::GeneralizedWitness(derivation.source_witness)
    })?;
    Some((derivation, witness))
}

fn collect_body_requirements(
    explanation: &ExplanationQueryResult,
    derivation: &SchemeInstantiationDerivation,
    role: GeneralizedWitnessRole,
    prefix: &[ExplanationNodeId],
    seen: &mut FxHashSet<(SchemeInstantiationId, OriginId)>,
    requirements: &mut Vec<ParameterBodyRequirementWitness>,
) {
    fn visit(
        explanation: &ExplanationQueryResult,
        derivation: &SchemeInstantiationDerivation,
        role: GeneralizedWitnessRole,
        node: ExplanationNodeId,
        path: &mut Vec<ExplanationNodeId>,
        visited: &mut FxHashSet<ExplanationNodeId>,
        seen: &mut FxHashSet<(SchemeInstantiationId, OriginId)>,
        requirements: &mut Vec<ParameterBodyRequirementWitness>,
    ) {
        if !visited.insert(node) {
            return;
        }
        if let Some(ExplanationNode::Origin {
            id,
            kind: ConstraintOriginKind::BodyRequirement(kind),
            source_boundary: Some(boundary),
        }) = explanation
            .nodes
            .iter()
            .find(|candidate| candidate.id() == node)
        {
            if seen.insert((derivation.instantiation, *id)) {
                requirements.push(ParameterBodyRequirementWitness {
                    instantiation: derivation.instantiation,
                    generalized_witness: derivation.source_witness,
                    path: derivation.path.clone(),
                    role,
                    origin: *id,
                    boundary: *boundary,
                    kind: *kind,
                    graph_path: path.clone(),
                });
            }
            return;
        }
        for edge in explanation
            .edges
            .iter()
            .filter(|edge| edge.child == node && !is_scheme_instantiation_edge(edge))
        {
            for parent in &edge.parents {
                path.push(*parent);
                visit(
                    explanation,
                    derivation,
                    role,
                    *parent,
                    path,
                    visited,
                    seen,
                    requirements,
                );
                path.pop();
            }
        }
    }

    let witness = ExplanationNodeId::GeneralizedWitness(derivation.source_witness);
    let mut path = prefix.to_vec();
    path.push(witness);
    visit(
        explanation,
        derivation,
        role,
        witness,
        &mut path,
        &mut FxHashSet::default(),
        seen,
        requirements,
    );
}
