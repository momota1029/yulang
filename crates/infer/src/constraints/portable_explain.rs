//! Bounded diagnostic projection from the portable constraint-provenance snapshot.
//!
//! The snapshot has already discarded infer's session-local record identities. This query therefore
//! traverses only portable nodes and edges, while retaining CPROV-H's deterministic visited-once DFS
//! and hard node, edge, and depth budgets. No graph identity crosses the public result boundary.

use poly::provenance::{
    PortableBodyRequirementKind, PortableBoundDerivationKind, PortableProvenanceEdge,
    PortableProvenanceEdgeKind, PortableProvenanceNodeId, PortableProvenanceNodeKind,
    PortableProvenanceSnapshot, PortableSourceLocation, PortableSourceRole, ProvenanceAnchor,
    ProvenanceCompleteness,
};
use rustc_hash::FxHashSet;

use crate::SourceSpan;
use crate::analysis::BodyRequirementDiagnosticKind;

const DEFAULT_EXPLANATION_NODES: usize = 512;
const DEFAULT_EXPLANATION_EDGES: usize = 1_024;
const DEFAULT_EXPLANATION_DEPTH: usize = 32;

/// Source-facing explanation of the two endpoint groups of one subtype mismatch.
///
/// Portable anchors and node/edge identities intentionally do not cross this boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticSubtypeExplanation {
    pub lower_sites: Vec<DiagnosticTypeCause>,
    pub upper_sites: Vec<DiagnosticTypeCause>,
    pub completeness: DiagnosticExplanationCompleteness,
    pub truncation: Option<DiagnosticExplanationTruncationReason>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticTypeCause {
    pub role: DiagnosticTypeCauseRole,
    pub source_span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticTypeCauseRole {
    InferredFromExpression,
    RequiredByAnnotation,
    RequiredByPattern,
    RequiredByBodyUse(BodyRequirementDiagnosticKind),
    RequiredByApplication,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticExplanationCompleteness {
    Complete,
    TruncatedByBudget,
    IncompleteProvenance,
    TruncatedAndIncompleteProvenance,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticExplanationTruncationReason {
    NodeBudget { limit: usize },
    EdgeBudget { limit: usize },
    DepthBudget { limit: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PortableExplanationBudget {
    pub max_nodes: usize,
    pub max_edges: usize,
    pub max_depth: usize,
}

impl Default for PortableExplanationBudget {
    fn default() -> Self {
        Self {
            max_nodes: DEFAULT_EXPLANATION_NODES,
            max_edges: DEFAULT_EXPLANATION_EDGES,
            max_depth: DEFAULT_EXPLANATION_DEPTH,
        }
    }
}

/// Explain lower and upper portable endpoint roots without consulting a live infer session.
///
/// Each endpoint group has one bounded traversal and one visited set. Roots, incoming edges, and
/// parents are consumed in caller/snapshot insertion order, so truncation returns a stable prefix.
pub fn explain_portable_subtype(
    snapshot: &PortableProvenanceSnapshot,
    lower_roots: &[ProvenanceAnchor],
    upper_roots: &[ProvenanceAnchor],
    budget: PortableExplanationBudget,
) -> DiagnosticSubtypeExplanation {
    let incoming = PortableIncomingEdges::new(snapshot);
    let lower = PortableExplanationQuery::new(snapshot, &incoming, budget).run(lower_roots);
    let upper = PortableExplanationQuery::new(snapshot, &incoming, budget).run(upper_roots);
    let truncated = lower.truncation.is_some() || upper.truncation.is_some();
    let incomplete = lower.underlying_incomplete || upper.underlying_incomplete;

    DiagnosticSubtypeExplanation {
        lower_sites: lower.causes,
        upper_sites: upper.causes,
        completeness: match (truncated, incomplete) {
            (false, false) => DiagnosticExplanationCompleteness::Complete,
            (true, false) => DiagnosticExplanationCompleteness::TruncatedByBudget,
            (false, true) => DiagnosticExplanationCompleteness::IncompleteProvenance,
            (true, true) => DiagnosticExplanationCompleteness::TruncatedAndIncompleteProvenance,
        },
        truncation: lower.truncation.or(upper.truncation),
    }
}

struct PortableIncomingEdges<'a> {
    edges: Vec<Vec<&'a PortableProvenanceEdge>>,
    malformed: bool,
}

impl<'a> PortableIncomingEdges<'a> {
    fn new(snapshot: &'a PortableProvenanceSnapshot) -> Self {
        let mut edges = vec![Vec::new(); snapshot.nodes().len()];
        let mut malformed = false;
        for edge in snapshot.edges() {
            if let Some(incoming) = edges.get_mut(edge.child.index()) {
                incoming.push(edge);
            } else {
                malformed = true;
            }
        }
        Self { edges, malformed }
    }

    fn get(&self, node: PortableProvenanceNodeId) -> &[&'a PortableProvenanceEdge] {
        self.edges
            .get(node.index())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

struct PortableExplanationQuery<'a> {
    snapshot: &'a PortableProvenanceSnapshot,
    incoming: &'a PortableIncomingEdges<'a>,
    budget: PortableExplanationBudget,
    visited: FxHashSet<PortableProvenanceNodeId>,
    visited_nodes: usize,
    visited_edges: usize,
    causes: Vec<DiagnosticTypeCause>,
    truncation: Option<DiagnosticExplanationTruncationReason>,
    underlying_incomplete: bool,
}

impl<'a> PortableExplanationQuery<'a> {
    fn new(
        snapshot: &'a PortableProvenanceSnapshot,
        incoming: &'a PortableIncomingEdges<'a>,
        budget: PortableExplanationBudget,
    ) -> Self {
        Self {
            snapshot,
            incoming,
            budget,
            visited: FxHashSet::default(),
            visited_nodes: 0,
            visited_edges: 0,
            causes: Vec::new(),
            truncation: None,
            underlying_incomplete: incoming.malformed,
        }
    }

    fn run(mut self, roots: &[ProvenanceAnchor]) -> PortableExplanationResult {
        if roots.is_empty() {
            self.underlying_incomplete = true;
        }
        for root in roots {
            if self.truncation.is_some() {
                break;
            }
            let Some(anchor) = self.snapshot.anchor(*root) else {
                self.underlying_incomplete = true;
                continue;
            };
            if anchor.completeness == ProvenanceCompleteness::Incomplete {
                self.underlying_incomplete = true;
            }
            self.visit(anchor.node, 0);
        }
        PortableExplanationResult {
            causes: self.causes,
            truncation: self.truncation,
            underlying_incomplete: self.underlying_incomplete,
        }
    }

    fn visit(&mut self, id: PortableProvenanceNodeId, depth: usize) {
        if self.truncation.is_some() || self.visited.contains(&id) {
            return;
        }
        if self.visited_nodes >= self.budget.max_nodes {
            self.truncation = Some(DiagnosticExplanationTruncationReason::NodeBudget {
                limit: self.budget.max_nodes,
            });
            return;
        }
        let Some(node) = self.snapshot.node(id).filter(|node| node.id == id) else {
            self.underlying_incomplete = true;
            return;
        };
        self.visited.insert(id);
        self.visited_nodes += 1;
        self.record_cause(node.kind);

        let incoming = self.incoming.get(id);
        if depth >= self.budget.max_depth && !incoming.is_empty() {
            self.truncation = Some(DiagnosticExplanationTruncationReason::DepthBudget {
                limit: self.budget.max_depth,
            });
            return;
        }
        for edge in incoming {
            self.push_edge(edge, depth);
            if self.truncation.is_some() {
                break;
            }
        }
    }

    fn push_edge(&mut self, edge: &PortableProvenanceEdge, depth: usize) {
        if self.truncation.is_some() {
            return;
        }
        if self.visited_edges >= self.budget.max_edges {
            self.truncation = Some(DiagnosticExplanationTruncationReason::EdgeBudget {
                limit: self.budget.max_edges,
            });
            return;
        }
        self.visited_edges += 1;
        if matches!(
            edge.kind,
            PortableProvenanceEdgeKind::Bound(PortableBoundDerivationKind::IncompleteReplay)
        ) {
            self.underlying_incomplete = true;
        }
        for parent in &edge.parents {
            self.visit(*parent, depth + 1);
            if self.truncation.is_some() {
                break;
            }
        }
    }

    fn record_cause(&mut self, kind: PortableProvenanceNodeKind) {
        match kind {
            PortableProvenanceNodeKind::Constraint {
                replay_complete: false,
            }
            | PortableProvenanceNodeKind::GeneralizedWitness {
                complete: false, ..
            } => self.underlying_incomplete = true,
            PortableProvenanceNodeKind::Origin {
                source_site: Some(site),
                ..
            } => {
                let Some(site) = self.snapshot.source_site(site) else {
                    self.underlying_incomplete = true;
                    return;
                };
                let Some(source_span) = site.location.as_ref().map(source_span) else {
                    return;
                };
                self.causes.push(DiagnosticTypeCause {
                    role: diagnostic_role(site.role),
                    source_span,
                });
            }
            _ => {}
        }
    }
}

struct PortableExplanationResult {
    causes: Vec<DiagnosticTypeCause>,
    truncation: Option<DiagnosticExplanationTruncationReason>,
    underlying_incomplete: bool,
}

fn diagnostic_role(role: PortableSourceRole) -> DiagnosticTypeCauseRole {
    match role {
        PortableSourceRole::ApplicationArgument => DiagnosticTypeCauseRole::RequiredByApplication,
        PortableSourceRole::Pattern => DiagnosticTypeCauseRole::RequiredByPattern,
        PortableSourceRole::Annotation => DiagnosticTypeCauseRole::RequiredByAnnotation,
        PortableSourceRole::Return | PortableSourceRole::Field | PortableSourceRole::Assignment => {
            DiagnosticTypeCauseRole::InferredFromExpression
        }
        PortableSourceRole::BodyRequirement(kind) => {
            DiagnosticTypeCauseRole::RequiredByBodyUse(match kind {
                PortableBodyRequirementKind::BooleanCondition => {
                    BodyRequirementDiagnosticKind::BooleanCondition
                }
                PortableBodyRequirementKind::OperatorOperand { .. } => {
                    BodyRequirementDiagnosticKind::OperatorOperand
                }
                PortableBodyRequirementKind::PatternGuard => {
                    BodyRequirementDiagnosticKind::PatternGuard
                }
                PortableBodyRequirementKind::CalleeArgument { .. } => {
                    BodyRequirementDiagnosticKind::CalleeArgument
                }
            })
        }
    }
}

fn source_span(location: &PortableSourceLocation) -> SourceSpan {
    SourceSpan {
        file: sources::Path {
            segments: location.module.iter().cloned().map(sources::Name).collect(),
        },
        range: sources::SourceRange {
            start: location.range.start as usize,
            end: location.range.end as usize,
        },
    }
}
