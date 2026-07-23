//! Portable, semantically inert constraint-provenance vocabulary.
//!
//! These records are adjacent metadata. They never participate in poly type
//! equality, interning, serialization, cache identity, or specialize work keys.

use std::mem::size_of;

use crate::expr::{DefId, ExprId, PatId};
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypePositionIndex(u32);

impl TypePositionIndex {
    pub fn from_usize(index: usize) -> Self {
        Self(u32::try_from(index).expect("type-position index fits in u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct TypePositionPath(pub Vec<TypePositionStep>);

impl TypePositionPath {
    pub fn push(&mut self, step: TypePositionStep) {
        self.0.push(step);
    }

    pub fn depth(&self) -> usize {
        self.0.len()
    }

    pub fn without_first(&self) -> Self {
        Self(self.0.iter().skip(1).copied().collect())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypePositionStep {
    FunctionArgument,
    FunctionArgumentEffect,
    FunctionReturnEffect,
    FunctionReturn,
    ConstructorArgument {
        alternative: TypePositionIndex,
        argument: TypePositionIndex,
    },
    TupleElement(TypePositionIndex),
    RecordField {
        alternative: TypePositionIndex,
        field: TypePositionIndex,
    },
    VariantPayload {
        alternative: TypePositionIndex,
        item: TypePositionIndex,
        payload: TypePositionIndex,
    },
    RowItemArgument {
        item: TypePositionIndex,
        argument: TypePositionIndex,
    },
    RowTail,
    RecursiveBound(TypePositionIndex),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeOccurrenceKey {
    pub owner: TypeOccurrenceOwner,
    pub role: TypeOccurrenceRole,
    pub path: TypePositionPath,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeOccurrenceOwner {
    Definition(DefId),
    Expression(ExprId),
    Pattern(PatId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeOccurrenceRole {
    DefinitionPredicate,
    DefinitionRecursiveLower(TypePositionIndex),
    DefinitionRecursiveUpper(TypePositionIndex),
    ExpressionActual,
    ExpressionExpected,
    PatternInput,
    PatternRequirement,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OccurrenceProvenance {
    pub anchors: Vec<ProvenanceAnchor>,
    pub completeness: ProvenanceCompleteness,
}

/// Sparse occurrence ownership kept adjacent to, but outside, semantic poly IR.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TypeOccurrenceProvenanceTable {
    entries: Vec<(TypeOccurrenceKey, OccurrenceProvenance)>,
    index: FxHashMap<TypeOccurrenceKey, usize>,
}

impl TypeOccurrenceProvenanceTable {
    pub fn get(&self, key: &TypeOccurrenceKey) -> Option<&OccurrenceProvenance> {
        self.index
            .get(key)
            .and_then(|index| self.entries.get(*index))
            .map(|(_, provenance)| provenance)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&TypeOccurrenceKey, &OccurrenceProvenance)> {
        self.entries.iter().map(|(key, value)| (key, value))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn insert(&mut self, key: TypeOccurrenceKey, provenance: OccurrenceProvenance) {
        if let Some(index) = self.index.get(&key).copied() {
            self.entries[index].1 = provenance;
            return;
        }
        let index = self.entries.len();
        self.entries.push((key.clone(), provenance));
        self.index.insert(key, index);
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SubtypeProvenanceMetrics {
    pub occurrence_count: usize,
    pub anchor_count: usize,
    pub complete_occurrences: usize,
    pub incomplete_occurrences: usize,
    pub snapshot_nodes: usize,
    pub snapshot_edges: usize,
    pub snapshot_logical_bytes: usize,
}

/// Cold-build provenance payload. It is intentionally not serializable and never enters caches.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SubtypeProvenanceSidecar {
    pub snapshot: PortableProvenanceSnapshot,
    pub occurrences: TypeOccurrenceProvenanceTable,
    pub metrics: SubtypeProvenanceMetrics,
}

impl SubtypeProvenanceSidecar {
    pub fn empty() -> Self {
        Self::default()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProvenanceAnchor(u32);

impl ProvenanceAnchor {
    pub fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("portable provenance anchor fits in u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PortableProvenanceNodeId(u32);

impl PortableProvenanceNodeId {
    pub fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("portable provenance node fits in u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PortableProvenanceEdgeId(u32);

impl PortableProvenanceEdgeId {
    pub fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("portable provenance edge fits in u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PortableSourceSiteId(u32);

impl PortableSourceSiteId {
    pub fn from_index(index: usize) -> Self {
        Self(u32::try_from(index).expect("portable source site fits in u32"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProvenanceCompleteness {
    Complete,
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableProvenanceTruncation {
    AnchorBudget { limit: usize },
    NodeBudget { limit: usize },
    EdgeBudget { limit: usize },
    DepthBudget { limit: usize },
    ParentFanInBudget { limit: usize },
    SourceSiteBudget { limit: usize },
    LogicalBytesBudget { limit: usize },
    UnderlyingIncomplete,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortableProvenanceSnapshot {
    anchors: Vec<PortableAnchorRecord>,
    nodes: Vec<PortableProvenanceNode>,
    edges: Vec<PortableProvenanceEdge>,
    source_sites: Vec<PortableSourceSite>,
    completeness: ProvenanceCompleteness,
    truncation: Option<PortableProvenanceTruncation>,
}

impl PortableProvenanceSnapshot {
    pub fn empty() -> Self {
        Self {
            anchors: Vec::new(),
            nodes: Vec::new(),
            edges: Vec::new(),
            source_sites: Vec::new(),
            completeness: ProvenanceCompleteness::Complete,
            truncation: None,
        }
    }

    pub fn anchors(&self) -> &[PortableAnchorRecord] {
        &self.anchors
    }

    pub fn nodes(&self) -> &[PortableProvenanceNode] {
        &self.nodes
    }

    pub fn edges(&self) -> &[PortableProvenanceEdge] {
        &self.edges
    }

    pub fn source_sites(&self) -> &[PortableSourceSite] {
        &self.source_sites
    }

    pub fn completeness(&self) -> ProvenanceCompleteness {
        self.completeness
    }

    pub fn truncation(&self) -> Option<PortableProvenanceTruncation> {
        self.truncation
    }

    pub fn anchor(&self, anchor: ProvenanceAnchor) -> Option<&PortableAnchorRecord> {
        self.anchors.get(anchor.index())
    }

    pub fn node(&self, node: PortableProvenanceNodeId) -> Option<&PortableProvenanceNode> {
        self.nodes.get(node.index())
    }

    pub fn source_site(&self, site: PortableSourceSiteId) -> Option<&PortableSourceSite> {
        self.source_sites.get(site.index())
    }

    pub fn logical_bytes_proxy(&self) -> usize {
        size_of::<Self>()
            + self
                .anchors
                .iter()
                .map(PortableAnchorRecord::logical_bytes_proxy)
                .sum::<usize>()
            + self
                .nodes
                .iter()
                .map(PortableProvenanceNode::logical_bytes_proxy)
                .sum::<usize>()
            + self
                .edges
                .iter()
                .map(PortableProvenanceEdge::logical_bytes_proxy)
                .sum::<usize>()
            + self
                .source_sites
                .iter()
                .map(PortableSourceSite::logical_bytes_proxy)
                .sum::<usize>()
    }
}

impl Default for PortableProvenanceSnapshot {
    fn default() -> Self {
        Self::empty()
    }
}

/// Mutable construction boundary for an otherwise immutable portable snapshot.
pub struct PortableProvenanceSnapshotBuilder {
    snapshot: PortableProvenanceSnapshot,
}

impl PortableProvenanceSnapshotBuilder {
    pub fn new() -> Self {
        Self {
            snapshot: PortableProvenanceSnapshot::empty(),
        }
    }

    pub fn logical_bytes_proxy(&self) -> usize {
        self.snapshot.logical_bytes_proxy()
    }

    pub fn anchor_count(&self) -> usize {
        self.snapshot.anchors.len()
    }

    pub fn node_count(&self) -> usize {
        self.snapshot.nodes.len()
    }

    pub fn edge_count(&self) -> usize {
        self.snapshot.edges.len()
    }

    pub fn source_site_count(&self) -> usize {
        self.snapshot.source_sites.len()
    }

    pub fn push_anchor(&mut self, record: PortableAnchorRecord) -> ProvenanceAnchor {
        let id = ProvenanceAnchor::from_index(self.snapshot.anchors.len());
        self.snapshot.anchors.push(record);
        id
    }

    pub fn push_node(&mut self, kind: PortableProvenanceNodeKind) -> PortableProvenanceNodeId {
        let id = PortableProvenanceNodeId::from_index(self.snapshot.nodes.len());
        self.snapshot
            .nodes
            .push(PortableProvenanceNode { id, kind });
        id
    }

    pub fn push_edge(
        &mut self,
        child: PortableProvenanceNodeId,
        kind: PortableProvenanceEdgeKind,
        parents: Vec<PortableProvenanceNodeId>,
    ) -> PortableProvenanceEdgeId {
        let id = PortableProvenanceEdgeId::from_index(self.snapshot.edges.len());
        self.snapshot.edges.push(PortableProvenanceEdge {
            id,
            child,
            kind,
            parents,
        });
        id
    }

    pub fn push_source_site(&mut self, site: PortableSourceSite) -> PortableSourceSiteId {
        let id = PortableSourceSiteId::from_index(self.snapshot.source_sites.len());
        self.snapshot.source_sites.push(site);
        id
    }

    pub fn mark_incomplete(&mut self, reason: PortableProvenanceTruncation) {
        self.snapshot.completeness = ProvenanceCompleteness::Incomplete;
        self.snapshot.truncation.get_or_insert(reason);
    }

    pub fn finish(self) -> PortableProvenanceSnapshot {
        self.snapshot
    }
}

impl Default for PortableProvenanceSnapshotBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PortableAnchorRecord {
    pub node: PortableProvenanceNodeId,
    pub completeness: ProvenanceCompleteness,
}

impl PortableAnchorRecord {
    pub fn logical_bytes_proxy(&self) -> usize {
        size_of::<Self>()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortableProvenanceNode {
    pub id: PortableProvenanceNodeId,
    pub kind: PortableProvenanceNodeKind,
}

impl PortableProvenanceNode {
    pub fn logical_bytes_proxy(&self) -> usize {
        size_of::<Self>()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableBoundDirection {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableBoundState {
    Evidence,
    Ordinary,
    Tombstone,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableGeneralizedWitnessRole {
    ConstraintRelation,
    LowerBound,
    UpperBound,
    RecursiveLowerBound,
    RecursiveUpperBound,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableProvenanceNodeKind {
    Constraint {
        replay_complete: bool,
    },
    Bound {
        direction: PortableBoundDirection,
        state: PortableBoundState,
        weighted: bool,
    },
    Origin {
        kind: PortableConstraintOriginKind,
        source_site: Option<PortableSourceSiteId>,
    },
    RowDerivation {
        rule: PortableRowDerivationRule,
    },
    SubtractFact {
        active: bool,
    },
    LowerFilter,
    BoundDisposition {
        kind: PortableBoundDispositionKind,
    },
    GeneralizedWitness {
        role: PortableGeneralizedWitnessRole,
        path_depth: u32,
        complete: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortableProvenanceEdge {
    pub id: PortableProvenanceEdgeId,
    pub child: PortableProvenanceNodeId,
    pub kind: PortableProvenanceEdgeKind,
    pub parents: Vec<PortableProvenanceNodeId>,
}

impl PortableProvenanceEdge {
    pub fn logical_bytes_proxy(&self) -> usize {
        size_of::<Self>() + self.parents.len() * size_of::<PortableProvenanceNodeId>()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableProvenanceEdgeKind {
    RootOrigin,
    Structural(PortableStructuralDerivationRule),
    BinaryReplay,
    RowResult,
    Canonicalization,
    Bound(PortableBoundDerivationKind),
    Row(PortableRowDerivationRule),
    LowerFilter,
    SubtractFact(PortableSubtractFactDerivationKind),
    BoundDisposition(PortableBoundDispositionKind),
    Generalization(PortableGeneralizationDerivationRule),
    SchemeInstantiation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableBoundDerivationKind {
    Constraint,
    Origin,
    ReplayEvidence,
    Row,
    SchemeInstantiation,
    IncompleteReplay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableSubtractFactDerivationKind {
    Declaration,
    Import,
    Internal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableBoundDispositionKind {
    Inserted,
    Equivalent,
    Subsumed,
    Trivial,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableGeneralizationDerivationRule {
    BoundCollection,
    StructuralProjection,
    VariableSubstitution,
    SandwichSimplification,
    RecursiveBoundExtraction,
    Finalization,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableRowDerivationRule {
    WeightedResidual,
    UnweightedReduction,
    RowItemMatch,
    FilterInvariant,
    PayloadInvariant,
    SubtractFactTransformation,
    StoreUpperWithoutReplay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableInvariantDirection {
    LowerToUpper,
    UpperToLower,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableRecordSpreadKind {
    Head,
    Tail,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableRowItemRoute {
    Matched,
    DirectToUpperTail,
    MarkerAggregateToUpperTail,
    VariableToRemainingRow,
    UpperTailToMarkerItems,
    UpperTailToDirectItems,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableStructuralDerivationRule {
    LowerStackNormalization,
    LowerNonSubtractNormalization,
    UpperStackNormalization,
    UnionBranch {
        branch: u32,
    },
    IntersectionBranch {
        branch: u32,
    },
    FunctionArgument,
    FunctionArgumentEffect {
        pure_passthrough: bool,
    },
    FunctionReturnEffect,
    FunctionReturn,
    ConstructorArgument {
        index: u32,
        direction: PortableInvariantDirection,
    },
    TupleElement {
        index: u32,
    },
    RecordField {
        index: u32,
    },
    RecordSpreadField {
        spread: PortableRecordSpreadKind,
        index: u32,
    },
    RecordSpreadTail {
        spread: PortableRecordSpreadKind,
        index: u32,
    },
    VariantPayload {
        variant_index: u32,
        payload_index: u32,
    },
    RowItem {
        index: u32,
        route: PortableRowItemRoute,
    },
    RowItemArgument {
        item_index: u32,
        argument_index: u32,
        direction: PortableInvariantDirection,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableConstraintOriginKind {
    ApplicationArgument,
    Pattern,
    Annotation,
    Return,
    Field,
    Assignment,
    BodyRequirement(PortableBodyRequirementKind),
    Internal,
    UnknownInternal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableBodyRequirementKind {
    BooleanCondition,
    OperatorOperand { operand: u32 },
    PatternGuard,
    CalleeArgument { argument: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PortableSourceRole {
    ApplicationArgument,
    Pattern,
    Annotation,
    Return,
    Field,
    Assignment,
    BodyRequirement(PortableBodyRequirementKind),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PortableSourceLocation {
    pub module: Vec<String>,
    pub range: PortableByteRange,
}

impl PortableSourceLocation {
    pub fn logical_bytes_proxy(&self) -> usize {
        size_of::<Self>()
            + self.module.len() * size_of::<String>()
            + self.module.iter().map(String::len).sum::<usize>()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PortableByteRange {
    pub start: u32,
    pub end: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PortableSourceSite {
    pub role: PortableSourceRole,
    pub location: Option<PortableSourceLocation>,
}

impl PortableSourceSite {
    pub fn logical_bytes_proxy(&self) -> usize {
        size_of::<Self>()
            + self
                .location
                .as_ref()
                .map_or(0, PortableSourceLocation::logical_bytes_proxy)
    }
}
