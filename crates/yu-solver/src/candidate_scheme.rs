//! Private top-level successor graph capture and per-use reconstruction.
//! This retains live algebra, not a closed F5 scheme or a Call certificate.
use crate::*;

#[derive(Debug, Default)]
pub(super) struct GraphState {
    pub intrusion: candidate_intrusion::State,
    pub graphs: Vec<Option<Graph>>,
    pub routes: Vec<FreshRoute>,
    pub locals: Vec<Option<LocalScheme>>,
    pub local_routes: Vec<LocalFreshRoute>,
    /// Exact source Local-use occurrence to completed retained route index.
    pub local_route_by_occurrence: HashMap<HirOccurrenceId, usize>,
    pub local_use: Vec<LocalUse>,
    #[cfg(test)]
    pub local_use_census: Option<LocalUseCensus>,
    pub source: Option<candidate_source::Frame>,
    /// Declaration prerequisites indexed by the exact source provider root.
    pub source_role_obligations: HashMap<DefinitionRootId, Vec<SourceRoleObligation>>,
    /// Deferred source method lookups indexed by the exact local source root.
    pub source_field_tail_obligations: HashMap<SourceRootId, Vec<SourceFieldTailObligation>>,
    pub retained_bytes: usize,
    pub scratch_bytes: usize,
    pub orchestration_bytes: usize,
    pub capture_peak_bytes: usize,
    pub use_peak_bytes: usize,
    #[cfg(test)]
    pub evidence_failure: Option<candidate_context::EvidenceFailurePoint>,
    #[cfg(test)]
    pub failed_evidence_point: Option<candidate_context::EvidenceFailurePoint>,
    #[cfg(test)]
    pub failed_evidence_sample: Option<(candidate_context::EvidenceFailurePoint, usize, usize)>,
    #[cfg(test)]
    pub import_failure_sample: Option<(usize, usize, bool)>,
    #[cfg(test)]
    pub failed_import_count: Option<usize>,
    #[cfg(test)]
    pub capture_evidence_peak_capacity: usize,
    #[cfg(test)]
    pub import_evidence_peak_capacity: usize,
}

/// A retained where prerequisite whose subject is joined to the provider's
/// actual annotation row. The role spelling is intentionally not a resolved
/// role identity and cannot authorize implementation selection.
#[derive(Clone, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "role source identities await authentic role resolution and discharge"))]
pub(super) struct SourceRoleObligation {
    pub provider: DefinitionRootId,
    pub where_source: yu_hir::shadow::SourceNodeKey,
    pub subject_source: yu_hir::shadow::SourceNodeKey,
    pub role_source: yu_hir::shadow::SourceNodeKey,
    pub role_spelling: Box<str>,
    /// Present only when the import environment joined this spelling to an
    /// exact provider role declaration. It is retained pending discharge.
    #[allow(dead_code, reason = "retained until type-directed role obligation discharge is implemented")]
    pub role_identity: Option<yu_hir::shadow::SourceRoleId>,
    pub subject_row: RowKey,
}

#[derive(Clone, Debug)]
pub(super) struct SourceFieldTailObligation {
    pub owner: SourceRootId,
    pub occurrence: HirOccurrenceId,
    pub source: yu_hir::shadow::SourceNodeKey,
    pub member: Box<str>,
    pub role_member_candidates: Vec<yu_hir::shadow::SourceRoleMemberId>,
    pub receiver_row: RowKey,
    pub receiver_effect: RowKey,
    pub result_row: RowKey,
    pub result_effect: RowKey,
}

#[derive(Debug)]
pub(super) struct Graph {
    pub source_frontier: Vec<candidate_source::SourceRegionId>,
    pub owned_regions: Vec<candidate_source::SourceRegionId>,
    pub negative_functions: HashMap<Term, usize>,
    pub nodes: Vec<Node>,
    /// Ordered child node indexes for tuple nodes; ranges live in `Node::Tuple`.
    pub tuple_children: Vec<usize>,
    pub rows: Vec<Row>,
    /// Each prerequisite points at a row already present in this provider graph.
    pub source_role_obligations: Vec<SourceRoleObligation>,
    pub source_field_tail_obligations: Vec<SourceFieldTailObligation>,
    pub bounds: Vec<Bound>,
    pub bound_evidence: Vec<candidate_context::EvidenceSnapshot>,
    pub attachment_bundles: Vec<(candidate_context::RelationId, candidate_context::AttachmentBundleId)>,
    pub attachment_spans: HashMap<candidate_context::RelationId, (usize, usize)>,
    pub context_views: Vec<(candidate_context::LocalWeightId, u32, Option<usize>)>,
    pub root: usize,
    pub live_root: u32,
    pub boundary: u32,
    #[cfg(test)]
    pub capture_rows: Vec<CapturedRowObservation>,
    #[cfg(test)]
    pub capture_effect_frontiers: Vec<CaptureEffectFrontierObservation>,
    #[cfg(test)]
    pub capture_forest: candidate_intrusion::ForestSnapshot,
}
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(super) struct CapturedRowObservation {
    pub graph_row: usize,
    pub requested: RowKey,
    pub representative: RowKey,
    pub level: u32,
    pub non_generic: bool,
    pub boundary: u32,
    pub local: bool,
    pub forest_event_cursor: usize,
}
#[cfg(test)]
#[derive(Debug)]
pub(super) struct CaptureEffectFrontierObservation {
    pub graph_row: usize,
    pub requested: RowKey,
    pub representative: RowKey,
    pub direct_lower_rows: Vec<u32>,
    pub direct_upper_rows: Vec<u32>,
    pub truncated: bool,
}
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(super) struct ReconstructedRowObservation {
    pub graph_row: usize,
    pub captured: RowKey,
    pub source_representative: RowKey,
    pub level: u32,
    pub non_generic: bool,
    pub boundary: u32,
    pub stored_local: bool,
    pub canonical_rows_hit: bool,
    pub first_entry_graph_row: usize,
    pub existing_image: Option<RowKey>,
    pub allocated_fresh_image: bool,
    pub image: RowKey,
    pub forest_event_cursor: usize,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum RowKey {
    Value(u32),
    Effect(u32),
}
impl RowKey {
    pub fn kind(self) -> ComponentKind {
        match self {
            Self::Value(_) => ComponentKind::Value,
            Self::Effect(_) => ComponentKind::Effect,
        }
    }
    fn ordinal(self) -> u32 {
        match self {
            Self::Value(i) | Self::Effect(i) => i,
        }
    }
}
#[derive(Clone, Copy, Debug)]
pub(super) struct Row {
    pub key: RowKey,
    pub local: bool,
}
#[derive(Clone, Copy, Debug)]
pub(super) enum Node {
    Leaf(Atom),
    EffectOperand { endpoint: EffectEndpointKey, tail: Option<usize>, polarity: Polarity },
    Row {
        row: usize,
        polarity: Polarity,
    },
    Function {
        polarity: Polarity,
        children: [usize; 4],
    },
    Tuple {
        polarity: Polarity,
        start: usize,
        len: usize,
    },
}
#[derive(Clone, Copy, Debug)]
pub(super) enum Atom {
    Bottom,
    Top,
    NegativeBottom,
    IntPositive,
    IntNegative,
    UnitPositive,
    BoolPositive,
    StrPositive,
    UnitNegative,
    BoolNegative,
    StrNegative,
    EffectBottom,
    EmptyEffect,
}
// This reference is valid only inside its owning Graph.
#[derive(Clone, Copy, Debug)]
pub(super) struct CapturedEvidenceRef(pub usize);
#[derive(Clone, Copy, Debug)]
pub(super) struct Bound {
    pub evidence: CapturedEvidenceRef,
    pub relation: Option<candidate_context::RelationId>,
    pub source_bound: candidate_effect::BoundKey,
    pub kind: ComponentKind,
    pub side: Polarity,
    pub lower: usize,
    pub upper: usize,
}
#[derive(Debug)]
pub(super) struct FreshRoute {
    pub use_id: DefinitionUseId,
    pub graph: Graph,
    pub rows: Vec<RowKey>,
    pub(super) retained: RetainedFreshUseMaps,
}
#[derive(Debug)]
pub(super) struct LocalScheme {
    pub capture_region: Option<candidate_source::SourceRegionId>,
    pub id: yu_hir::HirLocalId,
    pub root: u32,
    pub boundary: u32,
}
#[derive(Debug)]
pub(super) struct LocalFreshRoute {
    pub slot: usize,
    pub local: yu_hir::HirLocalId,
    pub occurrence: HirOccurrenceId,
    pub use_instance: usize,
    pub graph: Graph,
    pub rows: Vec<RowKey>,
    pub(super) retained: RetainedFreshUseMaps,
}
impl LocalFreshRoute {
    pub(super) fn authentic_use_instance(&self) -> bool {
        self.use_instance == self.retained.context_use
    }
}
#[derive(Debug)]
pub(super) struct RetainedFreshUseMaps {
    scope_remap: candidate_source::ScopeRemap,
    scoped_relations: HashMap<candidate_context::RelationId, candidate_context::ScopedFlow>,
    #[allow(dead_code)]
    context_use: usize,
    terms: Vec<Option<Term>>,
    effect_operands: HashMap<usize, EffectEndpointKey>,
    bundle_remap: HashMap<candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId>,
    context_remap: HashMap<candidate_context::ContextId, candidate_context::ContextId>,
    evidence_remap: Vec<candidate_context::EvidenceSnapshotId>,
    source_role_obligation_rows: Vec<(usize, usize)>,
    source_field_tail_obligation_rows: Vec<(usize, [usize; 4])>,
    #[cfg(test)]
    row_observations: Vec<ReconstructedRowObservation>,
}
impl RetainedFreshUseMaps {
    pub(super) fn observed_context_use(&self) -> usize { self.context_use }
    pub(super) fn observe_maps<'a>(&'a self, mut observe: impl FnMut(&'static str, &'a dyn std::fmt::Debug)) {
        observe("scope_remap", &self.scope_remap);
        observe("scoped_relations", &self.scoped_relations);
        observe("terms", &self.terms);
        observe("effect_operands", &self.effect_operands);
        observe("bundle_remap", &self.bundle_remap);
        observe("context_remap", &self.context_remap);
        observe("evidence_remap", &self.evidence_remap);
        observe("source_role_obligation_rows", &self.source_role_obligation_rows);
        observe("source_field_tail_obligation_rows", &self.source_field_tail_obligation_rows);
    }
    pub(super) fn observe_map_entries(
        &self,
        mut observe: impl FnMut(&'static str, Option<crate::shadow_apply::CandidateFreshUseMapEntry>),
    ) {
        use crate::shadow_apply::{CandidateFreshUseDemand as Demand, CandidateFreshUseMapEntry as Entry,
            CandidateSourceEffectEndpoint as Effect};
        observe("context_use", Some(Entry::ContextUse(self.context_use)));
        if self.scope_remap.regions.is_empty() { observe("scope_regions", None); }
        for (from, to) in &self.scope_remap.regions {
            observe("scope_regions", Some(Entry::ScopeRegion { from: from.0, to: to.0 }));
        }
        if self.scope_remap.scopes.is_empty() { observe("scope_scopes", None); }
        for (from, to) in &self.scope_remap.scopes {
            observe("scope_scopes", Some(Entry::EffectScope { from: from.0, to: to.0 }));
        }
        if self.scope_remap.inputs.is_empty() { observe("scope_inputs", None); }
        for (from, to) in &self.scope_remap.inputs {
            observe("scope_inputs", Some(Entry::InputRoute { from: from.0, to: to.0 }));
        }
        if self.scoped_relations.is_empty() { observe("scoped_relations", None); }
        for (relation, flow) in &self.scoped_relations {
            observe("scoped_relations", Some(Entry::ScopedRelation {
                relation: relation.0 as usize,
                transformer: flow.transformer,
                demand: flow.demand.map(|demand| Demand {
                    original_call: demand.original_call, use_instance: demand.use_instance,
                    root: demand.root, output_scope: demand.output_scope.0, input: demand.input.0,
                }),
            }));
        }
        if self.terms.is_empty() { observe("terms", None); }
        for (index, value) in self.terms.iter().enumerate() {
            observe("terms", Some(Entry::Term { index, value: *value }));
        }
        if self.effect_operands.is_empty() { observe("effect_operands", None); }
        for (index, endpoint) in &self.effect_operands {
            let endpoint = match *endpoint {
                EffectEndpointKey::BottomPositive => Effect::BottomPositive,
                EffectEndpointKey::EmptyNegative => Effect::EmptyNegative,
                #[cfg(feature = "shadow-apply-candidate")]
                EffectEndpointKey::Contribution(id) => Effect::Contribution(id),
                #[cfg(feature = "shadow-apply-candidate")]
                EffectEndpointKey::Allowance(id) => Effect::Allowance(id),
                #[cfg(feature = "shadow-apply-candidate")]
                EffectEndpointKey::Support(id) => Effect::Support(id),
                #[cfg(feature = "shadow-apply-candidate")]
                EffectEndpointKey::AnnotationMember(a, b) => Effect::AnnotationMember(a, b),
                EffectEndpointKey::EffectRow(row) => Effect::EffectRow(row),
            };
            observe("effect_operands", Some(Entry::EffectOperand { index: *index, endpoint }));
        }
        if self.bundle_remap.is_empty() { observe("bundle_remap", None); }
        for (from, to) in &self.bundle_remap {
            observe("bundle_remap", Some(Entry::AttachmentBundle { from: from.0, to: to.0 }));
        }
        if self.context_remap.is_empty() { observe("context_remap", None); }
        for (from, to) in &self.context_remap {
            observe("context_remap", Some(Entry::Context { from: from.0, to: to.0 }));
        }
        if self.evidence_remap.is_empty() { observe("evidence_remap", None); }
        for (index, snapshot) in self.evidence_remap.iter().enumerate() {
            observe("evidence_remap", Some(Entry::EvidenceSnapshot { index, snapshot: snapshot.0 }));
        }
    }
}
impl RetainedFreshUseMaps {
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[
            self.scope_remap.bytes()?,
            bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(self.scoped_relations.capacity())?,
            bytes::<Option<Term>>(self.terms.capacity())?,
            bytes::<(usize, EffectEndpointKey)>(self.effect_operands.capacity())?,
            bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(self.bundle_remap.capacity())?,
            bytes::<(candidate_context::ContextId, candidate_context::ContextId)>(self.context_remap.capacity())?,
            bytes::<candidate_context::EvidenceSnapshotId>(self.evidence_remap.capacity())?,
            bytes::<(usize, usize)>(self.source_role_obligation_rows.capacity())?,
            #[cfg(test)]
            bytes::<ReconstructedRowObservation>(self.row_observations.capacity())?,
        ])
    }
}
// Disposable, explicitly enabled native-constructor observations. The route
// continues to own its graph and row map; this retains only expiring maps.
#[cfg(test)]
#[derive(Debug, Default)]
pub(super) struct LocalUseCensus {
    pub requested: HashSet<HirOccurrenceId>,
    pub snapshots: Vec<LocalUseSnapshot>,
    pub module_uses: Vec<(HirOccurrenceId, usize)>,
}
#[cfg(test)]
#[derive(Debug)]
pub(super) struct LocalUseSnapshot {
    pub route: usize,
    pub slot: usize,
    pub occurrence: HirOccurrenceId,
    pub target_component: usize,
    pub terms: Vec<Option<Term>>,
    pub effect_operands: HashMap<usize, EffectEndpointKey>,
    pub context_remap: HashMap<candidate_context::ContextId, candidate_context::ContextId>,
    pub evidence_remap: Vec<candidate_context::EvidenceSnapshotId>,
    pub context_use: usize,
    pub restored_bounds: usize,
}
// Construction is atomic. Only the ordered restoration frontier is mutable
// after this fresh use is retained; resume never rebuilds these remaps.
#[derive(Debug)]
pub(super) struct FreshUse {
    scope_remap: candidate_source::ScopeRemap,
    scoped_relations: HashMap<candidate_context::RelationId, candidate_context::ScopedFlow>,
    context_use: usize,
    rows: Vec<RowKey>,
    /// (obligation ordinal, provider graph row index), both transported by
    /// this same FreshUse row vector.
    source_role_obligation_rows: Vec<(usize, usize)>,
    /// (FieldTail obligation ordinal, receiver/value-effect and result/value-effect graph rows).
    source_field_tail_obligation_rows: Vec<(usize, [usize; 4])>,
    terms: Vec<Option<Term>>,
    effect_operands: HashMap<usize, EffectEndpointKey>,
    bundle_remap: HashMap<candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId>,
    context_remap: HashMap<candidate_context::ContextId, candidate_context::ContextId>,
    evidence_remap: Vec<candidate_context::EvidenceSnapshotId>,
    #[cfg(test)]
    row_observations: Vec<ReconstructedRowObservation>,
}
impl FreshUse {
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[self.scope_remap.bytes()?, bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(self.scoped_relations.capacity())?, bytes::<RowKey>(self.rows.capacity())?, bytes::<Option<Term>>(self.terms.capacity())?,
            bytes::<(usize, usize)>(self.source_role_obligation_rows.capacity())?,
            bytes::<(usize, [usize; 4])>(self.source_field_tail_obligation_rows.capacity())?,
            bytes::<(usize, EffectEndpointKey)>(self.effect_operands.capacity())?,
            bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(self.bundle_remap.capacity())?,
            bytes::<(candidate_context::ContextId, candidate_context::ContextId)>(self.context_remap.capacity())?,
            bytes::<candidate_context::EvidenceSnapshotId>(self.evidence_remap.capacity())?,
            #[cfg(test)]
            bytes::<ReconstructedRowObservation>(self.row_observations.capacity())?])
    }
    fn into_retained_parts(self) -> (Vec<RowKey>, RetainedFreshUseMaps) {
        let FreshUse { scope_remap, scoped_relations, context_use, rows, terms,
            source_role_obligation_rows,
            source_field_tail_obligation_rows,
            effect_operands, bundle_remap, context_remap, evidence_remap,
            #[cfg(test)] row_observations,
        } = self;
        (rows, RetainedFreshUseMaps { scope_remap, scoped_relations, context_use,
            terms, effect_operands, bundle_remap, context_remap, evidence_remap,
            source_role_obligation_rows,
            source_field_tail_obligation_rows,
            #[cfg(test)] row_observations,
        })
    }
}

/// Ephemeral, read-only witness reconstructed from a retained FreshUse. It is
/// intentionally not solver state: callers may report what the actual map
/// proves, while all authorization and propagation continue to use the
/// existing relations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DemandTransportEvidence {
    pub route_owner: FreshRouteOwner,
    pub route: usize,
    pub relation: candidate_context::RelationId,
    pub fresh_relation: candidate_context::RelationId,
    pub physical_emission: candidate_context::BoundEmissionId,
    pub consumer: candidate_context::RelationId,
    pub replay_child: candidate_context::RelationId,
    pub replay_lower: candidate_context::RelationId,
    pub replay_upper: candidate_context::RelationId,
    pub lower_input: candidate_effect::BoundKey,
    pub upper_input: candidate_effect::BoundKey,
    pub fresh_from: candidate_effect::BoundKey,
    pub fresh_to: candidate_effect::BoundKey,
    pub physical_fiber: candidate_context::PhysicalBoundSlot,
    pub physical_readback: candidate_context::PhysicalBoundReadback,
    pub port_relations: [candidate_context::RelationId; 4],
    pub port_transformers: [usize; 4],
    pub original_root: Term,
    pub copied_root: Term,
    pub replay_upper_root: Term,
    pub replay_child_root: Term,
    pub consumer_root: Term,
    pub original_scope: candidate_scope::EffectScopeId,
    pub copied_scope: candidate_scope::EffectScopeId,
    pub original_input: candidate_scope::InputRouteId,
    pub copied_input: candidate_scope::InputRouteId,
    pub scope_map_matches: bool,
    pub input_map_matches: bool,
    pub ports_match: [bool; 4],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FreshRouteOwner { Module, Local }

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DemandTransportStage {
    MatchingRoute,
    Rejected(&'static str),
    Accepted,
}

fn four_ports_match<T: Copy + Eq>(expected: [T; 4], observed: [T; 4]) -> [bool; 4] {
    std::array::from_fn(|index| expected[index] == observed[index])
}

fn mapped_endpoint_at(
    graph: &Graph, mapped_rows: &[RowKey], retained: &RetainedFreshUseMaps,
    node: usize,
) -> Option<ExtrusionEndpoint> {
    Some(match *graph.nodes.get(node)? {
        Node::Row { row, .. } => match *mapped_rows.get(row)? {
            RowKey::Value(index) => ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(index)),
            RowKey::Effect(index) => ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(index)),
        },
        Node::EffectOperand { .. } => ExtrusionEndpoint::Effect(*retained.effect_operands.get(&node)?),
        Node::Function { polarity: function_polarity, .. } => {
            let term = retained.terms.get(node).copied().flatten()?;
            ExtrusionEndpoint::Value(match function_polarity {
                Polarity::Positive => ValueEndpointKey::PositiveFunction(term),
                Polarity::Negative => ValueEndpointKey::NegativeFunction(term),
            })
        }
        Node::Tuple { polarity: tuple_polarity, len, .. } => {
            let term = retained.terms.get(node).copied().flatten()?;
            ExtrusionEndpoint::Value(match tuple_polarity {
                Polarity::Positive => ValueEndpointKey::PositiveTuple(term, len),
                Polarity::Negative => ValueEndpointKey::NegativeTuple(term, len),
            })
        }
        Node::Leaf(atom) => ExtrusionEndpoint::Value(match atom {
            Atom::Bottom => ValueEndpointKey::BottomPositive,
            Atom::Top => ValueEndpointKey::TopNegative,
            Atom::NegativeBottom => ValueEndpointKey::BottomNegative,
            Atom::IntPositive => ValueEndpointKey::IntPositive,
            Atom::IntNegative => ValueEndpointKey::IntNegative,
            Atom::UnitPositive => ValueEndpointKey::UnitPositive,
            Atom::UnitNegative => ValueEndpointKey::UnitNegative,
            Atom::BoolPositive => ValueEndpointKey::BoolPositive,
            Atom::BoolNegative => ValueEndpointKey::BoolNegative,
            Atom::StrPositive => ValueEndpointKey::StrPositive,
            Atom::StrNegative => ValueEndpointKey::StrNegative,
            Atom::EffectBottom | Atom::EmptyEffect => return None,
        }),
    })
}

fn typed_port_pair(
    graph: &Graph, mapped_rows: &[RowKey], retained: &RetainedFreshUseMaps,
    positive_children: [usize; 4], negative_children: [usize; 4], field_index: usize,
) -> Option<TypedPairKey> {
    let (lower_node, upper_node, kind) = match field_index {
        0 => (negative_children[0], positive_children[0], ComponentKind::Value),
        1 => (negative_children[1], positive_children[1], ComponentKind::Effect),
        2 => (positive_children[2], negative_children[2], ComponentKind::Effect),
        3 => (positive_children[3], negative_children[3], ComponentKind::Value),
        _ => return None,
    };
    let lower = mapped_endpoint_at(graph, mapped_rows, retained, lower_node)?;
    let upper = mapped_endpoint_at(graph, mapped_rows, retained, upper_node)?;
    Some(match (kind, lower, upper) {
        (ComponentKind::Value, ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) =>
            TypedPairKey::Value(CanonicalValuePairKey { lower, upper }),
        (ComponentKind::Effect, ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) =>
            TypedPairKey::Effect { lower, upper },
        _ => return None,
    })
}

impl GraphState {
    #[cfg(test)]
    pub(super) fn test_positive_function_census(&self, lower_root: Term) -> Vec<String> {
        let mut census = Vec::new();
        let mut visit = |owner: FreshRouteOwner, route: usize, graph: &Graph, retained: &RetainedFreshUseMaps| {
            for (node_index, node) in graph.nodes.iter().enumerate() {
                let Node::Function { polarity: Polarity::Positive, children } = *node else { continue; };
                let child_terms = children.map(|child| retained.terms.get(child).copied().flatten());
                let retained_term = retained.terms.get(node_index).copied().flatten();
                census.push(format!("owner={owner:?} route={route} context_use={} positive_function_node={node_index} children={children:?} child_terms={child_terms:?} retained_term={retained_term:?} lower_root_matches={}", retained.context_use, retained_term == Some(lower_root)));
            }
        };
        for (route, item) in self.routes.iter().enumerate() { visit(FreshRouteOwner::Module, route, &item.graph, &item.retained); }
        for (route, item) in self.local_routes.iter().enumerate() { visit(FreshRouteOwner::Local, route, &item.graph, &item.retained); }
        census
    }

    /// Authenticate a copied demand only through the LocalFreshRoute that owns
    /// its actual FreshUse maps. No root equality is inferred from endpoint
    /// identity, and siblings remain distinct by their context-use identity.
    pub(super) fn authenticate_demand_transport(
        &self,
        context: &candidate_context::State,
        row: candidate_context::ReplayDemandRow,
        original_root: Term,
        term_ports: impl Fn(Term) -> Option<[Term; 4]>,
        observed_ports_override: Option<[Term; 4]>,
    ) -> Option<DemandTransportEvidence> {
        self.authenticate_demand_transport_observed(
            context, row, original_root, term_ports, observed_ports_override, |_, _, _| {},
        )
    }

    fn authenticate_demand_transport_observed(
        &self,
        context: &candidate_context::State,
        row: candidate_context::ReplayDemandRow,
        original_root: Term,
        term_ports: impl Fn(Term) -> Option<[Term; 4]>,
        observed_ports_override: Option<[Term; 4]>,
        mut observe: impl FnMut(FreshRouteOwner, usize, DemandTransportStage),
    ) -> Option<DemandTransportEvidence> {
        let mut found = None;
        let copied = row.demand;
        let original_call = row.call;
        let module_routes = self.routes.iter().enumerate().map(|(index, route)|
            (FreshRouteOwner::Module, index, &route.graph, &route.rows, &route.retained, route.retained.context_use));
        let local_routes = self.local_routes.iter().enumerate().map(|(index, route)|
            (FreshRouteOwner::Local, index, &route.graph, &route.rows, &route.retained, route.use_instance));
        for (route_owner, route_index, graph, mapped_rows, retained, use_instance) in module_routes.chain(local_routes) {
            macro_rules! rejected {
                ($stage:literal) => {{
                    observe(route_owner, route_index, DemandTransportStage::Rejected($stage));
                    return None;
                }};
            }
            if use_instance != copied.use_instance || retained.context_use != copied.use_instance
            {
                continue;
            }
            observe(route_owner, route_index, DemandTransportStage::MatchingRoute);
            let Some(&node_index) = graph.negative_functions.get(&original_root) else {
                observe(route_owner, route_index, DemandTransportStage::Rejected("original-root-absent"));
                continue;
            };
            let Some(copied_root) = retained.terms.get(node_index).copied().flatten() else { rejected!("copied-root-absent"); };
            let mut source_relations = graph.bounds.iter().filter_map(|bound| bound.relation)
                .filter(|relation| context.scoped_flow(*relation).is_ok_and(|flow|
                    flow.demand.is_some_and(|source| source.original_call == original_call
                        && source.root == original_root)
                    && retained.scoped_relations.get(relation)
                        .is_some_and(|flow| flow.demand == Some(copied))));
            let Some(original_relation) = source_relations.next() else { rejected!("source-relation-absent"); };
            if source_relations.next().is_some() { rejected!("duplicate-source-relation"); }
            let mut captured_bounds = graph.bounds.iter().filter(|bound| bound.relation == Some(original_relation));
            let Some(captured) = captured_bounds.next() else { rejected!("captured-bound-absent"); };
            if captured_bounds.next().is_some()
                || retained.scoped_relations.get(&original_relation).and_then(|flow| flow.demand) != Some(copied)
            { rejected!("captured-bound-or-retained-demand-mismatch"); }
            let Some(snapshot) = graph.bound_evidence.get(captured.evidence.0).copied() else { rejected!("snapshot-absent"); };
            let Some(imported) = retained.evidence_remap.get(captured.evidence.0).copied() else { rejected!("imported-evidence-absent"); };
            if snapshot.source_bound != captured.source_bound || snapshot.relation != Some(original_relation)
                || !context.captured_snapshot_was_imported(snapshot, imported)
            { rejected!("snapshot-import-mismatch"); }
            let Ok(original_flow) = context.scoped_flow(original_relation) else { rejected!("original-flow-absent"); };
            let Some(original_demand) = original_flow.demand else { rejected!("original-demand-absent"); };
            let Some(retained_flow) = retained.scoped_relations.get(&original_relation) else { rejected!("retained-flow-absent"); };
            if original_flow.transformer != 0 || retained_flow.transformer != 0
            { rejected!("demand-transformer-mismatch"); }
            let original_scope = original_demand.output_scope;
            let original_input = original_demand.input;
            let mapped_scope = retained.scope_remap.scopes.get(&original_scope)
                .copied().unwrap_or(original_scope);
            let mapped_input = retained.scope_remap.inputs.get(&original_input)
                .copied().unwrap_or(original_input);
            if mapped_scope != copied.output_scope || mapped_input != copied.input {
                rejected!("scope-or-input-remap-mismatch");
            }
            let Some(node) = graph.nodes.get(node_index) else { rejected!("negative-function-node-absent"); };
            let Node::Function { polarity: Polarity::Negative, children } = *node else { rejected!("wrong-function-polarity"); };
            let mut expected = [copied_root; 4];
            for (index, child) in children.into_iter().enumerate() {
                let Some(port_term) = retained.terms.get(child).copied().flatten() else { rejected!("port-term-absent"); };
                expected[index] = port_term;
            }
            let Some(actual) = term_ports(copied_root) else { rejected!("actual-ports-absent"); };
            let observed = observed_ports_override.unwrap_or(actual);
            let ports_match = four_ports_match(expected, observed);
            if !ports_match.into_iter().all(|matches| matches) {
                rejected!("four-ports-mismatch");
            }
            let Some(fresh_witness) = context.fresh_use_witness(original_relation, copied) else { rejected!("fresh-use-witness-absent"); };
            let (fresh_relation, fresh_from, fresh_to) = fresh_witness;
            let Some((_, admitted_relation, physical_emission, physical_fiber, physical_readback)) = context.fresh_use_fiber_emission(imported,
                captured.source_bound, copied.use_instance, fresh_relation, fresh_to) else { rejected!("fresh-use-physical-emission-absent"); };
            if admitted_relation != fresh_relation { rejected!("fresh-use-admission-mismatch"); }
            let owner_node = if captured.side == Polarity::Positive { captured.upper } else { captured.lower };
            let item_node = if captured.side == Polarity::Positive { captured.lower } else { captured.upper };
            let Some(owner_node) = graph.nodes.get(owner_node) else { rejected!("capture-owner-node-absent"); };
            let Node::Row { row: owner_index, .. } = *owner_node else { rejected!("wrong-capture-owner-node"); };
            let Some(expected_owner) = mapped_rows.get(owner_index).copied() else { rejected!("mapped-capture-owner-absent"); };
            let Some(item_node) = graph.nodes.get(item_node) else { rejected!("capture-item-node-absent"); };
            let item_is_row = matches!(item_node, Node::Row { .. });
            let expected_lane = match (captured.kind, captured.side, item_is_row) {
                (ComponentKind::Value, Polarity::Positive, true) => candidate_context::BoundLane::ValueLowerRow,
                (ComponentKind::Value, Polarity::Positive, false) => candidate_context::BoundLane::ValueLowerAtom,
                (ComponentKind::Value, Polarity::Negative, true) => candidate_context::BoundLane::ValueUpperRow,
                (ComponentKind::Value, Polarity::Negative, false) => candidate_context::BoundLane::ValueUpperAtom,
                (ComponentKind::Effect, Polarity::Positive, true) => candidate_context::BoundLane::EffectLowerRow,
                (ComponentKind::Effect, Polarity::Positive, false) => candidate_context::BoundLane::EffectLowerAtom,
                (ComponentKind::Effect, Polarity::Negative, true) => candidate_context::BoundLane::EffectUpperRow,
                (ComponentKind::Effect, Polarity::Negative, false) => candidate_context::BoundLane::EffectUpperAtom,
            };
            if physical_fiber.owner != expected_owner || physical_fiber.lane != expected_lane { rejected!("physical-fiber-mismatch"); }
            if physical_readback.bound != fresh_to
                || physical_readback.phase != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
            { rejected!("physical-readback-mismatch"); }
            let replay_recipe = candidate_context::Dependency::Replay {
                child: row.child, lower: row.lower, upper: row.upper,
                lower_input: row.lower_input, upper_input: row.upper_input,
            };
            if !context.replay_recipe_is_retained(replay_recipe) { rejected!("replay-recipe-absent"); }
            let Some((consumer, port_relations, port_transformers, replay_upper_root, replay_child_root)) =
                context.authenticate_replay_ancestry(row, original_relation, fresh_relation,
                    row.child, fresh_from, fresh_to) else { rejected!("replay-ancestry-rejected"); };
            // The retained p1→h constructor is absent. Authenticate its
            // supported zero-step case explicitly; do not identify p1, h, q,
            // and C in the evidence record.
            if copied_root != replay_upper_root { rejected!("replay-upper-root-mismatch"); }
            let ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(positive_root)) = row.lower_input.2 else { rejected!("replay-lower-endpoint-mismatch"); };
            let ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(negative_root)) = row.upper_input.2 else { rejected!("replay-upper-endpoint-mismatch"); };
            let find_function = |term: Term, polarity: Polarity| {
                let mut found = None;
                for (index, node) in graph.nodes.iter().enumerate() {
                    if !matches!(node, Node::Function { polarity: actual, .. } if *actual == polarity)
                        || retained.terms.get(index).copied().flatten() != Some(term) { continue; }
                    if found.replace(index).is_some() { return None; }
                }
                found
            };
            let Some(positive_node) = find_function(positive_root, Polarity::Positive) else { rejected!("positive-function-node-absent"); };
            let Some(negative_node) = find_function(negative_root, Polarity::Negative) else { rejected!("negative-function-node-absent"); };
            let Some(positive_node) = graph.nodes.get(positive_node) else { rejected!("positive-function-absent"); };
            let Node::Function { children: positive_children, .. } = *positive_node else { rejected!("positive-function-wrong-node"); };
            let Some(negative_node) = graph.nodes.get(negative_node) else { rejected!("negative-function-absent"); };
            let Node::Function { children: negative_children, .. } = *negative_node else { rejected!("negative-function-wrong-node"); };
            for index in 0..4 {
                let Some(expected_pair) = typed_port_pair(graph, mapped_rows, retained,
                    positive_children, negative_children, index) else { rejected!("typed-port-pair-absent"); };
                if context.relation_pair(port_relations[index]) != Some(expected_pair) { rejected!("typed-port-pair-mismatch"); }
            }
            let evidence = DemandTransportEvidence {
                route_owner,
                route: route_index, relation: original_relation,
                fresh_relation, physical_emission, replay_upper: row.upper,
                replay_child: row.child, replay_lower: row.lower, consumer,
                lower_input: row.lower_input, upper_input: row.upper_input, port_relations, port_transformers,
                fresh_from, fresh_to,
                physical_fiber, physical_readback,
                original_root,
                copied_root, replay_upper_root, replay_child_root,
                consumer_root: replay_child_root,
                original_scope, copied_scope: copied.output_scope,
                original_input, copied_input: copied.input,
                scope_map_matches: mapped_scope == copied.output_scope,
                input_map_matches: mapped_input == copied.input,
                ports_match,
            };
            if found.replace(evidence).is_some() {
                rejected!("multiple-matching-routes");
            }
            observe(route_owner, route_index, DemandTransportStage::Accepted);
        }
        found
    }
}
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct LocalUseCursor {
    pub next_bound: usize,
    pub restoration: Option<candidate_context::ReplayOperationId>,
    pub complete: bool,
}
#[derive(Debug)]
pub(super) struct LocalUse {
    slot: usize,
    local: yu_hir::HirLocalId,
    occurrence: HirOccurrenceId,
    value: usize,
    level: u32,
    graph: Graph,
    fresh: FreshUse,
    pub cursor: LocalUseCursor,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LocalRun { Complete, Paused }
// This closed script holds one exclusive session borrow from the first pause
// through resume/rollback. It has no callback or external mutation operation.
// Idle is a conditional unchanged-wait control, not a readiness certificate.
#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(super) enum LocalScriptStep { DriveOne, Idle, FailOne, Complete }
#[cfg(test)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LocalScriptObservation {
    pub source_next: usize,
    pub use_origin: Option<usize>,
    pub cursor: Option<LocalUseCursor>,
    pub restoration: Option<candidate_context::BoundRestoration>,
    pub checkpoint: candidate_context::Checkpoint,
    pub retained_bytes: usize,
    pub routes: usize,
    pub facts: usize,
    pub typed_drains: usize,
}
#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Endpoint {
    Value(ValueEndpointKey, Polarity),
    Effect(EffectEndpointKey, Polarity),
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), SolveAvailabilityError> {
    values.try_reserve(1).map_err(|_| exhausted())?;
    values.push(value);
    Ok(())
}
fn clone_role_obligations(
    obligations: &[SourceRoleObligation],
) -> Result<Vec<SourceRoleObligation>, SolveAvailabilityError> {
    let mut cloned = Vec::new();
    cloned.try_reserve_exact(obligations.len()).map_err(|_| exhausted())?;
    cloned.extend(obligations.iter().cloned());
    Ok(cloned)
}
fn clone_field_tail_obligations(
    obligations: &[SourceFieldTailObligation],
) -> Result<Vec<SourceFieldTailObligation>, SolveAvailabilityError> {
    let mut cloned = Vec::new();
    cloned.try_reserve_exact(obligations.len()).map_err(|_| exhausted())?;
    cloned.extend(obligations.iter().cloned());
    Ok(cloned)
}
fn bytes<T>(capacity: usize) -> Result<usize, SolveAvailabilityError> {
    capacity
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(exhausted)
}
fn vec_bytes<T>(values: &Vec<T>) -> Result<usize, SolveAvailabilityError> {
    bytes::<T>(values.capacity())
}
fn sum(parts: &[usize]) -> Result<usize, SolveAvailabilityError> {
    parts
        .iter()
        .try_fold(0usize, |n, &part| n.checked_add(part).ok_or_else(exhausted))
}
impl Graph {
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        sum(&[
            bytes::<(candidate_context::LocalWeightId, u32, Option<usize>)>(self.context_views.capacity())?,
            bytes::<candidate_source::SourceRegionId>(self.source_frontier.capacity())?,
            bytes::<candidate_source::SourceRegionId>(self.owned_regions.capacity())?,
            bytes::<(Term, usize)>(self.negative_functions.capacity())?,
            bytes::<Node>(self.nodes.capacity())?,
            bytes::<usize>(self.tuple_children.capacity())?,
            bytes::<Row>(self.rows.capacity())?,
            bytes::<SourceRoleObligation>(self.source_role_obligations.capacity())?,
            bytes::<SourceFieldTailObligation>(self.source_field_tail_obligations.capacity())?,
            self.source_role_obligations.iter().try_fold(0usize, |total, obligation| sum(&[
                total,
                bytes::<u8>(obligation.role_spelling.len())?,
            ]))?,
            self.source_field_tail_obligations.iter().try_fold(0usize, |total, obligation| sum(&[
                total,
                bytes::<u8>(obligation.member.len())?,
                bytes::<yu_hir::shadow::SourceRoleMemberId>(obligation.role_member_candidates.capacity())?,
            ]))?,
            #[cfg(test)]
            bytes::<CapturedRowObservation>(self.capture_rows.capacity())?,
            #[cfg(test)]
            self.capture_effect_frontiers.iter().try_fold(
                bytes::<CaptureEffectFrontierObservation>(self.capture_effect_frontiers.capacity())?,
                |total, frontier| sum(&[
                    total,
                    bytes::<u32>(frontier.direct_lower_rows.capacity())?,
                    bytes::<u32>(frontier.direct_upper_rows.capacity())?,
                ]),
            )?,
            #[cfg(test)]
            bytes::<u32>(self.capture_forest.values.capacity())?,
            #[cfg(test)]
            bytes::<u32>(self.capture_forest.effects.capacity())?,
            bytes::<Bound>(self.bounds.capacity())?,
            bytes::<candidate_context::EvidenceSnapshot>(self.bound_evidence.capacity())?,
            bytes::<(candidate_context::RelationId, candidate_context::AttachmentBundleId)>(self.attachment_bundles.capacity())?,
            bytes::<(candidate_context::RelationId, (usize, usize))>(self.attachment_spans.capacity())?,
        ])
    }
}
impl GraphState {
    pub(super) fn retain_source_role_obligation(
        &mut self,
        obligation: SourceRoleObligation,
    ) -> Result<(), SolveAvailabilityError> {
        if self.source_role_obligations.get(&obligation.provider).is_some_and(|items| items.iter().any(|old|
            old.where_source == obligation.where_source
                && old.subject_source == obligation.subject_source
                && old.role_source == obligation.role_source
        )) {
            return Err(SolveAvailabilityError::ReceiptMismatch);
        }
        let old_map_capacity = self.source_role_obligations.capacity();
        if !self.source_role_obligations.contains_key(&obligation.provider) {
            self.source_role_obligations.try_reserve(1).map_err(|_| exhausted())?;
        }
        let map_growth = self.source_role_obligations.capacity() - old_map_capacity;
        let obligations = self.source_role_obligations.entry(obligation.provider.clone()).or_default();
        let old_items_capacity = obligations.capacity();
        obligations.try_reserve(1).map_err(|_| exhausted())?;
        let items_growth = obligations.capacity() - old_items_capacity;
        let added = sum(&[
            bytes::<(DefinitionRootId, Vec<SourceRoleObligation>)>(map_growth)?,
            bytes::<SourceRoleObligation>(items_growth)?,
            bytes::<u8>(obligation.role_spelling.len())?,
        ])?;
        self.retained_bytes = self.retained_bytes.checked_add(added).ok_or_else(exhausted)?;
        obligations.push(obligation);
        Ok(())
    }

    pub(super) fn retain_source_field_tail_obligation(
        &mut self,
        obligation: SourceFieldTailObligation,
    ) -> Result<(), SolveAvailabilityError> {
        if self.source_field_tail_obligations.get(&obligation.owner).is_some_and(|items|
            items.iter().any(|old| old.occurrence == obligation.occurrence)) {
            return Err(SolveAvailabilityError::ReceiptMismatch);
        }
        let old_map_capacity = self.source_field_tail_obligations.capacity();
        if !self.source_field_tail_obligations.contains_key(&obligation.owner) {
            self.source_field_tail_obligations.try_reserve(1).map_err(|_| exhausted())?;
        }
        let map_growth = self.source_field_tail_obligations.capacity() - old_map_capacity;
        let items = self.source_field_tail_obligations.entry(obligation.owner.clone()).or_default();
        let old_items_capacity = items.capacity();
        items.try_reserve(1).map_err(|_| exhausted())?;
        let added = sum(&[
            bytes::<(SourceRootId, Vec<SourceFieldTailObligation>)>(map_growth)?,
            bytes::<SourceFieldTailObligation>(items.capacity() - old_items_capacity)?,
            bytes::<u8>(obligation.member.len())?,
            bytes::<yu_hir::shadow::SourceRoleMemberId>(obligation.role_member_candidates.capacity())?,
        ])?;
        self.retained_bytes = self.retained_bytes.checked_add(added).ok_or_else(exhausted)?;
        items.push(obligation);
        Ok(())
    }

    pub(super) fn commit_local_use(&mut self) {
        let frame = self.local_use.pop().expect("completed local parent");
        let route_index = self.local_routes.len();
        let occurrence = frame.occurrence.clone();
        let slot = frame.slot;
        let local = frame.local.clone();
        let use_instance = frame.fresh.context_use;
        #[cfg(test)]
        if let Some(census) = &mut self.local_use_census {
            if census.requested.contains(&frame.occurrence) {
                census.snapshots.push(LocalUseSnapshot {
                    route: self.local_routes.len(), slot: frame.slot,
                    occurrence: frame.occurrence.clone(), target_component: frame.value,
                    terms: frame.fresh.terms.clone(),
                    effect_operands: frame.fresh.effect_operands.clone(),
                    context_remap: frame.fresh.context_remap.clone(),
                    evidence_remap: frame.fresh.evidence_remap.clone(),
                    context_use: frame.fresh.context_use,
                    restored_bounds: frame.cursor.next_bound,
                });
            }
        }

        // All capacities and arithmetic were preflighted by frame accounting and
        // final route reservation. Move retained maps without allocation.
        let (rows, retained) = frame.fresh.into_retained_parts();
        let previous = self.local_route_by_occurrence.insert(occurrence.clone(), route_index);
        debug_assert!(previous.is_none(), "one exact Local occurrence publishes one fresh route");
        self.local_routes.push(LocalFreshRoute { slot, local, occurrence,
            use_instance, graph: frame.graph, rows, retained });
    }
    pub fn refresh_bytes(&mut self) -> Result<(), SolveAvailabilityError> {
        let mut total = sum(&[
            bytes::<Option<Graph>>(self.graphs.capacity())?,
            bytes::<FreshRoute>(self.routes.capacity())?,
            bytes::<Option<LocalScheme>>(self.locals.capacity())?,
            bytes::<LocalFreshRoute>(self.local_routes.capacity())?,
            bytes::<(HirOccurrenceId, usize)>(self.local_route_by_occurrence.capacity())?,
            bytes::<LocalUse>(self.local_use.capacity())?,
            bytes::<(DefinitionRootId, Vec<SourceRoleObligation>)>(self.source_role_obligations.capacity())?,
            bytes::<(SourceRootId, Vec<SourceFieldTailObligation>)>(self.source_field_tail_obligations.capacity())?,
        ])?;
        for obligations in self.source_role_obligations.values() {
            total = sum(&[
                total,
                bytes::<SourceRoleObligation>(obligations.capacity())?,
                obligations.iter().try_fold(0usize, |accumulated, obligation| sum(&[
                    accumulated,
                    bytes::<u8>(obligation.role_spelling.len())?,
                ]))?,
            ])?;
        }
        for obligations in self.source_field_tail_obligations.values() {
            total = sum(&[
                total,
                bytes::<SourceFieldTailObligation>(obligations.capacity())?,
                obligations.iter().try_fold(0usize, |accumulated, obligation| sum(&[
                    accumulated, bytes::<u8>(obligation.member.len())?,
                    bytes::<yu_hir::shadow::SourceRoleMemberId>(obligation.role_member_candidates.capacity())?,
                ]))?,
            ])?;
        }
        for graph in self.graphs.iter().flatten() {
            total = total.checked_add(graph.bytes()?).ok_or_else(exhausted)?;
        }
        for route in &self.routes {
            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?, route.retained.bytes()?])?;
        }
        for route in &self.local_routes {
            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?, route.retained.bytes()?])?;
        }
        for frame in &self.local_use {
            total = sum(&[total, frame.graph.bytes()?, frame.fresh.bytes()?])?;
        }
        self.retained_bytes = total;
        Ok(())
    }
}
#[derive(Default)]
struct CaptureEvidenceMeter {
    bytes: std::cell::Cell<usize>,
    #[cfg(test)]
    capacity: std::cell::Cell<usize>,
}
struct Capture<'a> {
    evidence_keys: HashMap<candidate_context::EvidenceSnapshot, CapturedEvidenceRef>,
    evidence_charge: &'a CaptureEvidenceMeter,
    session: &'a InferenceSession,
    graph: Graph,
    /// Canonical (upper row, lower owner) pairs stored in lower rows' upper
    /// adjacency. Only rows local to this capture are indexed.
    incoming_effect_upper_owners: Vec<(u32, u32)>,
    incoming_effect_upper_owners_ready: bool,
    /// Effect rows reached through the captured type shape, before bound
    /// endpoints are added. Reverse-owner discovery starts at this frontier.
    shape_effect_rows: Vec<u32>,
    /// Completed Lambda body-to-result source Origins, the exact direct source
    /// owners whose reverse edges the local forwarding Capture must preserve.
    completed_lambda_effect_origins: Vec<candidate_context::RelationId>,
    endpoints: HashMap<Endpoint, usize>,
    rows: HashMap<RowKey, usize>,
    pending: Vec<Endpoint>,
    bound_keys: HashSet<(ComponentKind, Polarity, usize, usize, Option<candidate_context::RelationId>)>,
    boundary: u32,
}
impl<'a> Capture<'a> {
    fn ensure_incoming_effect_upper_owners(&mut self) -> Result<(), SolveAvailabilityError> {
        if self.incoming_effect_upper_owners_ready {
            return Ok(());
        }
        let session = self.session;
        let boundary = self.boundary;
        let context = &session.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra.context;
        let origin_count = context.origins.iter().filter(|origin| origin.occurrence.local_slot() == 4).count();
        self.completed_lambda_effect_origins
            .try_reserve_exact(origin_count)
            .map_err(|_| exhausted())?;
        for origin in context.origins.iter().filter(|origin| origin.occurrence.local_slot() == 4) {
            if origin.source_drain_receipt.as_ref()
                .is_some_and(|receipt| context.source_drain_completed(receipt))
            {
                self.completed_lambda_effect_origins.push(origin.relation);
            }
        }
        self.completed_lambda_effect_origins.sort_unstable_by_key(|relation| relation.0);
        self.completed_lambda_effect_origins.dedup_by_key(|relation| relation.0);
        self.charge_evidence()?;
        let is_local_upper = |upper: u32| -> Result<bool, SolveAvailabilityError> {
            let ordinal = upper as usize;
            let level = *session.effect_levels.get(ordinal).ok_or_else(exhausted)?;
            let metadata = session.effect_metadata.get(ordinal).ok_or_else(exhausted)?;
            Ok(level > boundary && !metadata.non_generic)
        };
        let mut edge_count = 0usize;
        for (raw_owner, bounds) in session.effect_bounds.iter().enumerate() {
            let owner = match session.canonical_effect(EffectEndpointKey::EffectRow(raw_owner as u32)) {
                EffectEndpointKey::EffectRow(owner) => owner,
                _ => return Err(exhausted()),
            };
            for &raw_upper in &bounds.direct_upper_rows {
                let upper = match session.canonical_effect(EffectEndpointKey::EffectRow(raw_upper)) {
                    EffectEndpointKey::EffectRow(upper) => upper,
                    _ => return Err(exhausted()),
                };
                let key = candidate_effect::BoundKey(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)),
                    Polarity::Negative,
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(upper)),
                );
                let has_completed_lambda_origin = context.bound_relations(key)
                    .any(|relation| self.completed_lambda_effect_origins
                        .binary_search_by_key(&relation.0, |candidate| candidate.0).is_ok());
                if upper != owner && is_local_upper(upper)? && has_completed_lambda_origin {
                    edge_count = edge_count.checked_add(1).ok_or_else(exhausted)?;
                }
            }
        }
        self.incoming_effect_upper_owners
            .try_reserve_exact(edge_count)
            .map_err(|_| exhausted())?;
        let indexed = (|| {
            for (raw_owner, bounds) in session.effect_bounds.iter().enumerate() {
                let owner = match session.canonical_effect(EffectEndpointKey::EffectRow(raw_owner as u32)) {
                    EffectEndpointKey::EffectRow(owner) => owner,
                    _ => return Err(exhausted()),
                };
                for &raw_upper in &bounds.direct_upper_rows {
                    let upper = match session.canonical_effect(EffectEndpointKey::EffectRow(raw_upper)) {
                        EffectEndpointKey::EffectRow(upper) => upper,
                        _ => return Err(exhausted()),
                    };
                    let key = candidate_effect::BoundKey(
                        ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(owner)),
                        Polarity::Negative,
                        ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(upper)),
                    );
                    let has_completed_lambda_origin = context.bound_relations(key)
                        .any(|relation| self.completed_lambda_effect_origins
                            .binary_search_by_key(&relation.0, |candidate| candidate.0).is_ok());
                    if upper != owner && is_local_upper(upper)? && has_completed_lambda_origin {
                        self.incoming_effect_upper_owners.push((upper, owner));
                    }
                }
            }
            self.incoming_effect_upper_owners.sort_unstable();
            self.incoming_effect_upper_owners.dedup();
            Ok(())
        })();
        let charged = self.charge_evidence();
        indexed?;
        charged?;
        self.incoming_effect_upper_owners_ready = true;
        Ok(())
    }
    fn charge_evidence(&self) -> Result<(), SolveAvailabilityError> {
        #[cfg(test)]
        self.evidence_charge.capacity.set(self.evidence_keys.capacity());
        self.evidence_charge.bytes.set(sum(&[
            bytes::<(candidate_context::EvidenceSnapshot, CapturedEvidenceRef)>(self.evidence_keys.capacity())?,
            bytes::<candidate_context::EvidenceSnapshot>(self.graph.bound_evidence.capacity())?,
            bytes::<(u32, u32)>(self.incoming_effect_upper_owners.capacity())?,
            bytes::<u32>(self.shape_effect_rows.capacity())?,
            bytes::<candidate_context::RelationId>(self.completed_lambda_effect_origins.capacity())?,
        ])?);
        Ok(())
    }
    fn intern(&mut self, endpoint: Endpoint) -> Result<usize, SolveAvailabilityError> {
        let endpoint = match endpoint { Endpoint::Value(v, p) => Endpoint::Value(self.session.canonical_value(v), p), Endpoint::Effect(e, p) => Endpoint::Effect(self.session.canonical_effect(e), p) };
        if let Some(&index) = self.endpoints.get(&endpoint) {
            return Ok(index);
        }
        self.endpoints.try_reserve(1).map_err(|_| exhausted())?;
        let index = self.graph.nodes.len();
        push(&mut self.graph.nodes, Node::Leaf(Atom::Bottom))?;
        push(&mut self.pending, endpoint)?;
        self.endpoints.insert(endpoint, index);
        Ok(index)
    }
    fn intern_shape(&mut self, endpoint: Endpoint) -> Result<usize, SolveAvailabilityError> {
        let endpoint = match endpoint {
            Endpoint::Value(value, polarity) => Endpoint::Value(self.session.canonical_value(value), polarity),
            Endpoint::Effect(effect, polarity) => Endpoint::Effect(self.session.canonical_effect(effect), polarity),
        };
        if let Endpoint::Effect(EffectEndpointKey::EffectRow(row), _) = endpoint {
            if !self.shape_effect_rows.contains(&row) {
                self.shape_effect_rows.try_reserve(1).map_err(|_| exhausted())?;
                self.shape_effect_rows.push(row);
                self.charge_evidence()?;
            }
        }
        self.intern(endpoint)
    }
    fn row(&mut self, key: RowKey) -> Result<usize, SolveAvailabilityError> {
        #[cfg(test)]
        let requested = key;
        let key = self.session.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.rep(key);
        if let Some(&index) = self.rows.get(&key) {
            return Ok(index);
        }
        let ordinal = key.ordinal() as usize;
        let (level, metadata) = match key {
            RowKey::Value(_) => (
                self.session.value_levels.get(ordinal),
                self.session.value_metadata.get(ordinal),
            ),
            RowKey::Effect(_) => (
                self.session.effect_levels.get(ordinal),
                self.session.effect_metadata.get(ordinal),
            ),
        };
        let (&level, metadata) = (
            level.ok_or_else(exhausted)?,
            metadata.ok_or_else(exhausted)?,
        );
        let local = level > self.boundary && !metadata.non_generic;
        self.rows.try_reserve(1).map_err(|_| exhausted())?;
        let index = self.graph.rows.len();
        push(&mut self.graph.rows, Row { key, local })?;
        #[cfg(test)]
        push(&mut self.graph.capture_rows, CapturedRowObservation {
            graph_row: index, requested, representative: key, level,
            non_generic: metadata.non_generic, boundary: self.boundary, local,
            forest_event_cursor: self.session.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.forest_event_cursor(),
        })?;
        #[cfg(test)]
        if let RowKey::Effect(effect) = key {
            const FRONTIER_LIMIT: usize = 256;
            let bounds = self.session.effect_bounds.get(effect as usize).ok_or_else(exhausted)?;
            let lower_len = bounds.direct_lower_rows.len();
            let upper_len = bounds.direct_upper_rows.len();
            let mut direct_lower_rows = Vec::new();
            let lower_count = lower_len.min(FRONTIER_LIMIT);
            direct_lower_rows.try_reserve_exact(lower_count).map_err(|_| exhausted())?;
            direct_lower_rows.extend_from_slice(&bounds.direct_lower_rows[..lower_count]);
            let mut direct_upper_rows = Vec::new();
            let upper_count = upper_len.min(FRONTIER_LIMIT);
            direct_upper_rows.try_reserve_exact(upper_count).map_err(|_| exhausted())?;
            direct_upper_rows.extend_from_slice(&bounds.direct_upper_rows[..upper_count]);
            push(&mut self.graph.capture_effect_frontiers, CaptureEffectFrontierObservation {
                graph_row: index,
                requested,
                representative: key,
                direct_lower_rows,
                direct_upper_rows,
                truncated: lower_len > FRONTIER_LIMIT || upper_len > FRONTIER_LIMIT,
            })?;
        }
        self.rows.insert(key, index);
        Ok(index)
    }
    fn term_endpoint(
        &self,
        term: Term,
        kind: ComponentKind,
        polarity: Polarity,
    ) -> Result<Endpoint, SolveAvailabilityError> {
        let endpoint = match self
            .session
            .store
            .term_view(term)
            .map_err(|_| exhausted())?
        {
            TermView::Component(component) if component.kind() == kind => {
                let row = self.session.component_endpoint(term);
                match kind {
                    ComponentKind::Value => {
                        Endpoint::Value(ValueEndpointKey::ValueRow(row.ordinal), polarity)
                    }
                    ComponentKind::Effect => {
                        Endpoint::Effect(EffectEndpointKey::EffectRow(row.ordinal), polarity)
                    }
                }
            }
            TermView::LiveVariable(v) if v.kind() == kind && v.polarity() == polarity => match kind
            {
                ComponentKind::Value => {
                    Endpoint::Value(ValueEndpointKey::ValueRow(v.ordinal()), polarity)
                }
                ComponentKind::Effect => {
                    Endpoint::Effect(EffectEndpointKey::EffectRow(v.ordinal()), polarity)
                }
            },
            TermView::PositiveFunction { .. }
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::PositiveFunction(term), polarity)
            }
            TermView::NegativeFunction { .. }
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::NegativeFunction(term), polarity)
            }
            TermView::PositiveTuple { elements }
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::PositiveTuple(term, elements.len()), polarity)
            }
            TermView::NegativeTuple { elements }
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::NegativeTuple(term, elements.len()), polarity)
            }
            TermView::PositiveBottom
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::BottomPositive, polarity)
            }
            TermView::NegativeTop
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::TopNegative, polarity)
            }
            TermView::NegativeBottom
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::BottomNegative, polarity)
            }
            TermView::Leaf(Leaf::IntPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::IntPositive, polarity)
            }
            TermView::Leaf(Leaf::UnitPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::UnitPositive, polarity)
            }
            TermView::Leaf(Leaf::BoolPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::BoolPositive, polarity)
            }
            TermView::Leaf(Leaf::StrPositive)
                if kind == ComponentKind::Value && polarity == Polarity::Positive =>
            {
                Endpoint::Value(ValueEndpointKey::StrPositive, polarity)
            }
            TermView::Leaf(Leaf::IntNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::IntNegative, polarity)
            }
            TermView::Leaf(Leaf::UnitNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::UnitNegative, polarity)
            }
            TermView::Leaf(Leaf::BoolNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::BoolNegative, polarity)
            }
            TermView::Leaf(Leaf::StrNegative)
                if kind == ComponentKind::Value && polarity == Polarity::Negative =>
            {
                Endpoint::Value(ValueEndpointKey::StrNegative, polarity)
            }
            TermView::Leaf(Leaf::EffectBottomPositive)
                if kind == ComponentKind::Effect && polarity == Polarity::Positive =>
            {
                Endpoint::Effect(EffectEndpointKey::BottomPositive, polarity)
            }
            TermView::Leaf(Leaf::EmptyEffectNegative)
                if kind == ComponentKind::Effect && polarity == Polarity::Negative =>
            {
                Endpoint::Effect(EffectEndpointKey::EmptyNegative, polarity)
            }
            _ => return Err(exhausted()),
        };
        Ok(endpoint)
    }
    fn expand_node(&mut self, endpoint: Endpoint) -> Result<(), SolveAvailabilityError> {
        use EffectEndpointKey as E;
        use ValueEndpointKey as V;
        let index = self.endpoints[&endpoint];
        let node = match endpoint {
            Endpoint::Value(V::ValueRow(i), p) => Node::Row {
                row: self.row(RowKey::Value(i))?,
                polarity: p,
            },
            Endpoint::Effect(E::EffectRow(i), p) => Node::Row {
                row: self.row(RowKey::Effect(i))?,
                polarity: p,
            },
            Endpoint::Value(V::BottomPositive, Polarity::Positive) => Node::Leaf(Atom::Bottom),
            Endpoint::Value(V::TopNegative, Polarity::Negative) => Node::Leaf(Atom::Top),
            Endpoint::Value(V::BottomNegative, Polarity::Negative) => {
                Node::Leaf(Atom::NegativeBottom)
            }
            Endpoint::Value(V::IntPositive, Polarity::Positive) => Node::Leaf(Atom::IntPositive),
            Endpoint::Value(V::UnitPositive, Polarity::Positive) => Node::Leaf(Atom::UnitPositive),
            Endpoint::Value(V::BoolPositive, Polarity::Positive) => Node::Leaf(Atom::BoolPositive),
            Endpoint::Value(V::StrPositive, Polarity::Positive) => Node::Leaf(Atom::StrPositive),
            Endpoint::Value(V::IntNegative, Polarity::Negative) => Node::Leaf(Atom::IntNegative),
            Endpoint::Value(V::UnitNegative, Polarity::Negative) => Node::Leaf(Atom::UnitNegative),
            Endpoint::Value(V::BoolNegative, Polarity::Negative) => Node::Leaf(Atom::BoolNegative),
            Endpoint::Value(V::StrNegative, Polarity::Negative) => Node::Leaf(Atom::StrNegative),
            Endpoint::Effect(E::BottomPositive, Polarity::Positive) => {
                Node::Leaf(Atom::EffectBottom)
            }
            Endpoint::Effect(E::EmptyNegative, Polarity::Negative) => Node::Leaf(Atom::EmptyEffect),
            Endpoint::Effect(endpoint @ E::Contribution(_), Polarity::Positive) => Node::EffectOperand { endpoint, tail: None, polarity: Polarity::Positive },
            Endpoint::Effect(endpoint @ E::AnnotationMember(id, _), Polarity::Positive) => {
                let tail = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[id as usize].tail;
                let tail = tail.map(|row| self.intern_shape(Endpoint::Effect(E::EffectRow(row), Polarity::Positive))).transpose()?;
                Node::EffectOperand { endpoint, tail, polarity: Polarity::Positive }
            },
            Endpoint::Effect(endpoint @ E::Allowance(id), Polarity::Negative)
            | Endpoint::Effect(endpoint @ E::Support(id), Polarity::Positive) => {
                let polarity = if matches!(endpoint, E::Support(_)) { Polarity::Positive } else { Polarity::Negative };
                let tail = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[id as usize].tail;
                let tail = tail.map(|row| self.intern_shape(Endpoint::Effect(E::EffectRow(row), polarity))).transpose()?;
                Node::EffectOperand { endpoint, tail, polarity }
            }
            Endpoint::Value(V::PositiveFunction(term), Polarity::Positive)
            | Endpoint::Value(V::NegativeFunction(term), Polarity::Negative) => {
                let (p, terms) = match self
                    .session
                    .store
                    .term_view(term)
                    .map_err(|_| exhausted())?
                {
                    TermView::PositiveFunction {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => (
                        Polarity::Positive,
                        [argument, argument_effect, result_effect, result],
                    ),
                    TermView::NegativeFunction {
                        argument,
                        argument_effect,
                        result_effect,
                        result,
                    } => (
                        Polarity::Negative,
                        [argument, argument_effect, result_effect, result],
                    ),
                    _ => return Err(exhausted()),
                };
                let expected = match endpoint {
                    Endpoint::Value(_, p) => p,
                    _ => unreachable!(),
                };
                if p != expected {
                    return Err(exhausted());
                }
                let opposite = if p == Polarity::Positive {
                    Polarity::Negative
                } else {
                    Polarity::Positive
                };
                let kinds = [
                    ComponentKind::Value,
                    ComponentKind::Effect,
                    ComponentKind::Effect,
                    ComponentKind::Value,
                ];
                let polarities = [opposite, opposite, p, p];
                let mut children = [0; 4];
                for i in 0..4 {
                    children[i] = self.intern_shape(self.term_endpoint(terms[i], kinds[i], polarities[i])?)?;
                }
                Node::Function {
                    polarity: p,
                    children,
                }
            }
            Endpoint::Value(V::PositiveTuple(term, arity), Polarity::Positive)
            | Endpoint::Value(V::NegativeTuple(term, arity), Polarity::Negative) => {
                let (polarity, elements) = match self.session.store.term_view(term).map_err(|_| exhausted())? {
                    TermView::PositiveTuple { elements } => (Polarity::Positive, elements),
                    TermView::NegativeTuple { elements } => (Polarity::Negative, elements),
                    _ => return Err(exhausted()),
                };
                if elements.len() != arity { return Err(exhausted()); }
                let start = self.graph.tuple_children.len();
                self.graph.tuple_children.try_reserve_exact(elements.len()).map_err(|_| exhausted())?;
                self.graph.tuple_children.resize(start.checked_add(elements.len()).ok_or_else(exhausted)?, usize::MAX);
                for (offset, &element) in elements.iter().enumerate() {
                    let child = self.intern_shape(self.term_endpoint(element, ComponentKind::Value, polarity)?)?;
                    self.graph.tuple_children[start + offset] = child;
                }
                Node::Tuple { polarity, start, len: elements.len() }
            }
            _ => return Err(exhausted()),
        };
        self.graph.nodes[index] = node;
        Ok(())
    }
    fn bound(
        &mut self,
        kind: ComponentKind,
        side: Polarity,
        lower: Endpoint,
        upper: Endpoint,
    ) -> Result<(), SolveAvailabilityError> {
        let endpoint = |endpoint| match endpoint { Endpoint::Value(v, _) => ExtrusionEndpoint::Value(v), Endpoint::Effect(e, _) => ExtrusionEndpoint::Effect(e) };
        let (owner, item) = if side == Polarity::Positive { (endpoint(upper), endpoint(lower)) } else { (endpoint(lower), endpoint(upper)) };
        let context = &self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let mut cursor = context.bound_cursor(candidate_effect::BoundKey(owner, side, item));
        let absent = cursor.is_none();
        let lower = self.intern(lower)?;
        let upper = self.intern(upper)?;
        let mut absent = absent;
        while cursor.is_some() || absent {
            let relation = if let Some(index) = cursor {
                let (relation, next) = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                cursor = next;
                Some(relation)
            } else { absent = false; None };
            let key = (kind, side, lower, upper, relation);
            if self.bound_keys.contains(&key) { continue; }
            self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
            let source_bound = candidate_effect::BoundKey(owner, side, item);
            let snapshot = self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.evidence_snapshot(source_bound, relation);
            let evidence = if let Some(&evidence) = self.evidence_keys.get(&snapshot) { evidence } else {
                let reserved = self.evidence_keys.try_reserve(1);
                self.charge_evidence()?;
                reserved.map_err(|_| exhausted())?;
                let reserved = self.graph.bound_evidence.try_reserve(1);
                self.charge_evidence()?;
                reserved.map_err(|_| exhausted())?;
                #[cfg(test)]
                if self.session.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::CaptureScratch) {
                    return Err(exhausted());
                }
                let evidence = CapturedEvidenceRef(self.graph.bound_evidence.len());
                self.graph.bound_evidence.push(snapshot);
                self.evidence_keys.insert(snapshot, evidence);
                evidence
            };
            push(&mut self.graph.bounds, Bound { evidence, relation, source_bound, kind, side, lower, upper })?;
            self.bound_keys.insert(key);
        }
        Ok(())
    }
    fn expand_row(&mut self, index: usize) -> Result<(), SolveAvailabilityError> {
        let Row { key, local } = self.graph.rows[index];
        let session = self.session;
        // freshenAbove stops at older identities. Their mutable bounds stay
        // in the session, so later constraints reach every shared anchor use.
        if !local { return Ok(()); }
        let p = Polarity::Positive;
        let n = Polarity::Negative;
        match key {
            RowKey::Value(i) => {
                let row = session.bounds.get(i as usize).ok_or_else(exhausted)?;
                for &lower in &row.direct_lower_rows {
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Positive,
                        Endpoint::Value(ValueEndpointKey::ValueRow(lower), p),
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), n),
                    )?;
                }
                for &upper in &row.direct_upper_rows {
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Negative,
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), p),
                        Endpoint::Value(ValueEndpointKey::ValueRow(upper), n),
                    )?;
                }
                for &lower in &row.exact_non_variable_lowers {
                    if matches!(lower, ValueEndpointKey::ValueRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Positive,
                        Endpoint::Value(lower, p),
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), n),
                    )?;
                }
                for &upper in &row.exact_non_variable_uppers {
                    if matches!(upper, ValueEndpointKey::ValueRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Value,
                        Polarity::Negative,
                        Endpoint::Value(ValueEndpointKey::ValueRow(i), p),
                        Endpoint::Value(upper, n),
                    )?;
                }
            }
            RowKey::Effect(i) => {
                let reverse_frontier = self.boundary > 0 && self.shape_effect_rows.contains(&i);
                if reverse_frontier {
                    self.ensure_incoming_effect_upper_owners()?;
                }
                let state = &session.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.effect_algebra;
                let mut record = state.capture_incidence.get(&i).map(|bucket| bucket.head);
                while let Some(index) = record {
                    let incidence = state.capture_records[index];
                    record = incidence.next;
                    self.bound(ComponentKind::Effect, n,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(incidence.source), p),
                        Endpoint::Effect(EffectEndpointKey::Allowance(incidence.view), n))?;
                }
                let row = session
                    .effect_bounds
                    .get(i as usize)
                    .ok_or_else(exhausted)?;
                for &lower in &row.direct_lower_rows {
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Positive,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(lower), p),
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), n),
                    )?;
                }
                for &upper in &row.direct_upper_rows {
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Negative,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), p),
                        Endpoint::Effect(EffectEndpointKey::EffectRow(upper), n),
                    )?;
                }
                if reverse_frontier {
                    let incoming_start = self.incoming_effect_upper_owners
                        .partition_point(|(upper, _)| *upper < i);
                    for cursor in incoming_start..self.incoming_effect_upper_owners.len() {
                        let (upper, lower) = self.incoming_effect_upper_owners[cursor];
                        if upper != i { break; }
                        self.bound(
                            ComponentKind::Effect,
                            Polarity::Negative,
                            Endpoint::Effect(EffectEndpointKey::EffectRow(lower), p),
                            Endpoint::Effect(EffectEndpointKey::EffectRow(i), n),
                        )?;
                    }
                }
                for &lower in &row.exact_non_variable_lowers {
                    if matches!(lower, EffectEndpointKey::EffectRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Positive,
                        Endpoint::Effect(lower, p),
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), n),
                    )?;
                }
                for &upper in &row.exact_non_variable_uppers {
                    if matches!(upper, EffectEndpointKey::EffectRow(_)) {
                        return Err(exhausted());
                    }
                    self.bound(
                        ComponentKind::Effect,
                        Polarity::Negative,
                        Endpoint::Effect(EffectEndpointKey::EffectRow(i), p),
                        Endpoint::Effect(upper, n),
                    )?;
                }
            }
        }
        Ok(())
    }
}
impl InferenceSession {
    pub(super) fn start_candidate_graph(&mut self) -> Result<(), SolveAvailabilityError> {
        let mut state = GraphState::default();
        state.intrusion.effect_algebra.initialize()?;
        state.intrusion.effect_algebra.context.scoped_enabled = self.batch.candidate_source.scoped_experiment;
        if self.batch.candidate_source.scoped_experiment {
            state.intrusion.effect_algebra.context.scope_inventory = candidate_source::ScopeInventory::from_plan(&self.batch.candidate_source)?;
        }
        state
            .graphs
            .try_reserve_exact(self.batch.definitions.len())
            .map_err(|_| exhausted())?;
        state
            .graphs
            .resize_with(self.batch.definitions.len(), || None);
        state.locals.try_reserve_exact(self.batch.candidate_source.locals.len()).map_err(|_| exhausted())?;
        state.locals.resize_with(self.batch.candidate_source.locals.len(), || None);
        state.refresh_bytes()?;
        self.candidate_graph = Some(state);
        Ok(())
    }
    pub(super) fn capture_candidate_graph(&mut self, row: u32, boundary: u32) -> Result<Graph, SolveAvailabilityError> {
        self.capture_candidate_graph_owned(row, boundary, &[], &[], &[])
    }
    fn capture_candidate_graph_owned(&mut self, row: u32, boundary: u32, frontier: &[candidate_source::SourceRegionId], obligations: &[SourceRoleObligation], field_tails: &[SourceFieldTailObligation]) -> Result<Graph, SolveAvailabilityError> {
        if self.batch.candidate_source.scoped_experiment && frontier.is_empty() { return Err(SolveAvailabilityError::ReceiptMismatch); }
        let entry = self.candidate_graph.as_ref().ok_or_else(exhausted)?.scratch_bytes;
        let evidence_charge = CaptureEvidenceMeter::default();
        let result = self.capture_candidate_graph_inner(row, boundary, &evidence_charge, frontier, obligations, field_tails);
        #[cfg(test)]
        {
            let state = self.candidate_graph.as_mut().unwrap();
            state.capture_evidence_peak_capacity = state.capture_evidence_peak_capacity.max(evidence_charge.capacity.get());
        }
        if result.is_err() {
            // Capture owns immutable session access. Its checked capacity meter
            // survives failure, so dropped transient evidence is still sampled.
            let state = self.candidate_graph.as_mut().unwrap();
            state.scratch_bytes = entry.checked_add(evidence_charge.bytes.get()).ok_or_else(exhausted)?;
            state.capture_peak_bytes = state.capture_peak_bytes.max(state.scratch_bytes);
            let sampled = self.sample_f4_resources(ResourceBoundary::SourceDrafts);
            #[cfg(test)]
            if self.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::CaptureScratch) {
                let total = self.resource_ledger.inference_session_retained_bytes;
                let state = self.candidate_graph.as_mut().unwrap();
                state.evidence_failure = None;
                state.failed_evidence_point = Some(candidate_context::EvidenceFailurePoint::CaptureScratch);
                state.failed_evidence_sample = Some((candidate_context::EvidenceFailurePoint::CaptureScratch, state.scratch_bytes, total));
            }
            self.candidate_graph.as_mut().unwrap().scratch_bytes = entry;
            // Preserve the original capture failure even if its sample also fails.
            let _ = sampled;
        }
        result
    }
    fn capture_candidate_graph_inner(&mut self, row: u32, boundary: u32, evidence_charge: &CaptureEvidenceMeter, frontier: &[candidate_source::SourceRegionId], obligations: &[SourceRoleObligation], field_tails: &[SourceFieldTailObligation]) -> Result<Graph, SolveAvailabilityError> {
        if let Some(first) = obligations.first() {
            if obligations.iter().any(|obligation| {
                obligation.provider != first.provider
                    || obligation.role_spelling.is_empty()
            }) {
                return Err(SolveAvailabilityError::ReceiptMismatch);
            }
        }
        let retained_obligations = clone_role_obligations(obligations)?;
        if let Some(first) = field_tails.first() {
            if first.owner.definition_root().is_none()
                || field_tails.iter().any(|obligation| obligation.owner != first.owner) {
                return Err(SolveAvailabilityError::ReceiptMismatch);
            }
        }
        let mut retained_field_tails = clone_field_tail_obligations(field_tails)?;
        let intrusion = &self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion;
        for obligation in &mut retained_field_tails {
            obligation.receiver_row = intrusion.rep(obligation.receiver_row);
            obligation.receiver_effect = intrusion.rep(obligation.receiver_effect);
            obligation.result_row = intrusion.rep(obligation.result_row);
            obligation.result_effect = intrusion.rep(obligation.result_effect);
        }
        let mut source_frontier = Vec::new(); source_frontier.try_reserve_exact(frontier.len()).map_err(|_| exhausted())?;
        source_frontier.extend_from_slice(frontier);
        let owned_regions = self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.context.scope_inventory.owned(frontier)?;
        #[cfg(test)]
        let capture_forest = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.forest_snapshot()?;
        let mut capture = Capture {
            evidence_keys: HashMap::new(),
            evidence_charge,
            session: self,
            graph: Graph {
                source_frontier, owned_regions, negative_functions: HashMap::new(),
                nodes: Vec::new(), tuple_children: Vec::new(),
                rows: Vec::new(),
                source_role_obligations: retained_obligations,
                source_field_tail_obligations: retained_field_tails,
                bounds: Vec::new(),
                bound_evidence: Vec::new(),
                attachment_bundles: Vec::new(),
                attachment_spans: HashMap::new(),
                context_views: Vec::new(),
                root: 0,
                live_root: row,
                boundary,
                #[cfg(test)]
                capture_rows: Vec::new(),
                #[cfg(test)]
                capture_effect_frontiers: Vec::new(),
                #[cfg(test)]
                capture_forest,
            },
            endpoints: HashMap::new(),
            rows: HashMap::new(),
            incoming_effect_upper_owners: Vec::new(),
            incoming_effect_upper_owners_ready: false,
            shape_effect_rows: Vec::new(),
            completed_lambda_effect_origins: Vec::new(),
            pending: Vec::new(),
            bound_keys: HashSet::new(),
            boundary,
        };
        capture.graph.root = capture.intern_shape(Endpoint::Value(
            ValueEndpointKey::ValueRow(row),
            Polarity::Positive,
        ))?;
        for index in 0..capture.graph.source_role_obligations.len() {
            let subject_row = capture.graph.source_role_obligations[index].subject_row;
            if let RowKey::Value(subject) = subject_row {
                capture.intern_shape(Endpoint::Value(
                    ValueEndpointKey::ValueRow(subject), Polarity::Positive,
                ))?;
            } else {
                return Err(SolveAvailabilityError::ReceiptMismatch);
            }
        }
        for index in 0..capture.graph.source_field_tail_obligations.len() {
            let (value_keys, effect_keys) = {
                let obligation = &capture.graph.source_field_tail_obligations[index];
                ([obligation.receiver_row, obligation.result_row],
                    [obligation.receiver_effect, obligation.result_effect])
            };
            for key in value_keys {
                let RowKey::Value(value) = key else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                capture.intern_shape(Endpoint::Value(ValueEndpointKey::ValueRow(value), Polarity::Positive))?;
            }
            for key in effect_keys {
                let RowKey::Effect(effect) = key else { return Err(SolveAvailabilityError::ReceiptMismatch); };
                capture.intern_shape(Endpoint::Effect(EffectEndpointKey::EffectRow(effect), Polarity::Positive))?;
            }
        }
        let mut row_cursor = 0;
        let mut bound_cursor = 0;
        let mut context_seen = HashSet::new();
        let mut payload_seen = HashSet::new();
        let mut context_pending = Vec::new();
        let mut payloads = Vec::new();
        loop {
            while !capture.pending.is_empty() || row_cursor < capture.graph.rows.len() {
                while let Some(endpoint) = capture.pending.pop() { capture.expand_node(endpoint)?; }
                if row_cursor < capture.graph.rows.len() {
                    capture.expand_row(row_cursor)?;
                    row_cursor += 1;
                }
            }
            while bound_cursor < capture.graph.bounds.len() {
                let bound = capture.graph.bounds[bound_cursor];
                bound_cursor += 1;
                if let Some(relation) = bound.relation {
                    let context = &capture.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
                    context.context_payloads(context.relation_context(relation)?, &mut context_seen, &mut context_pending, &mut payloads)?;
                    // A deferred original demand is a retained latent payload,
                    // even when no structural bound reaches its Function root.
                    if let Some(demand) = context.scoped_flow(relation)?.demand {
                        capture.intern_shape(Endpoint::Value(ValueEndpointKey::NegativeFunction(demand.root), Polarity::Negative))?;
                    }
                }
            }
            while let Some(weight) = payloads.pop() {
                if payload_seen.contains(&weight) { continue; }
                payload_seen.try_reserve(1).map_err(|_| exhausted())?;
                payload_seen.insert(weight);
                let algebra = &capture.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
                let id = algebra.context.payload_view(weight)?;
                let view = algebra.views.get(id as usize).ok_or_else(exhausted)?;
                algebra.context.validate_payload_view(weight, id, view)?;
                let tail = view.tail;
                let tail = tail.map(|tail| capture.intern_shape(Endpoint::Effect(EffectEndpointKey::EffectRow(tail), Polarity::Positive))).transpose()?;
                push(&mut capture.graph.context_views, (weight, id, tail))?;
            }
            if capture.pending.is_empty() && row_cursor == capture.graph.rows.len() { break; }
        }
        for obligation in &capture.graph.source_role_obligations {
            if !capture.graph.rows.iter().any(|row| row.key == obligation.subject_row) {
                return Err(SolveAvailabilityError::ReceiptMismatch);
            }
        }
        for obligation in &capture.graph.source_field_tail_obligations {
            if [obligation.receiver_row, obligation.receiver_effect, obligation.result_row, obligation.result_effect]
                .iter().any(|key| !capture.graph.rows.iter().any(|row| row.key == *key)) {
                return Err(SolveAvailabilityError::ReceiptMismatch);
            }
        }
        let context = &capture.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let mut attachment_resolved = HashSet::new();
        for bound in &capture.graph.bounds {
            if let Some(relation) = bound.relation {
                if attachment_resolved.contains(&relation) { continue; }
                attachment_resolved.try_reserve(1).map_err(|_| exhausted())?;
                attachment_resolved.insert(relation);
                let start = capture.graph.attachment_bundles.len();
                for bundle in context.relation_bundles(relation) {
                    push(&mut capture.graph.attachment_bundles, (relation, bundle))?;
                }
                let length = capture.graph.attachment_bundles.len() - start;
                if length != 0 {
                    capture.graph.attachment_spans.try_reserve(1).map_err(|_| exhausted())?;
                    capture.graph.attachment_spans.insert(relation, (start, length));
                }
            }
        }
        let scratch = sum(&[
            bytes::<(candidate_context::EvidenceSnapshot, CapturedEvidenceRef)>(capture.evidence_keys.capacity())?,
            bytes::<candidate_context::ContextId>(context_seen.capacity())?,
            bytes::<candidate_context::LocalWeightId>(payload_seen.capacity())?,
            bytes::<candidate_context::ContextId>(context_pending.capacity())?,
            bytes::<candidate_context::LocalWeightId>(payloads.capacity())?,
            bytes::<candidate_context::RelationId>(attachment_resolved.capacity())?,
            bytes::<(Endpoint, usize)>(capture.endpoints.capacity())?,
            bytes::<(RowKey, usize)>(capture.rows.capacity())?,
            bytes::<Endpoint>(capture.pending.capacity())?,
            bytes::<(ComponentKind, Polarity, usize, usize, Option<candidate_context::RelationId>)>(capture.bound_keys.capacity())?,
            bytes::<(u32, u32)>(capture.incoming_effect_upper_owners.capacity())?,
            bytes::<u32>(capture.shape_effect_rows.capacity())?,
            bytes::<candidate_context::RelationId>(capture.completed_lambda_effect_origins.capacity())?,
        ])?;
        if capture.session.batch.candidate_source.scoped_experiment {
            capture.graph.negative_functions.try_reserve(capture.endpoints.len()).map_err(|_| exhausted())?;
            for (&endpoint, &index) in &capture.endpoints {
                if let Endpoint::Value(ValueEndpointKey::NegativeFunction(term), Polarity::Negative) = endpoint {
                    capture.graph.negative_functions.insert(term, index);
                }
            }
        }
        let graph_bytes = capture.graph.bytes()?;
        let Capture {
            graph,
            endpoints,
            rows,
            pending,
            bound_keys,
            evidence_keys,
            ..
        } = capture;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.scratch_bytes = state
            .scratch_bytes
            .checked_add(graph_bytes)
            .and_then(|n| n.checked_add(scratch))
            .ok_or_else(exhausted)?;
        state.capture_peak_bytes = state.capture_peak_bytes.max(state.scratch_bytes);
        let sampled = self.sample_f4_resources(ResourceBoundary::SourceDrafts);
        drop((endpoints, rows, pending, bound_keys, evidence_keys, attachment_resolved, context_seen, payload_seen, context_pending, payloads));
        self.candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .scratch_bytes -= scratch;
        sampled?;
        #[cfg(test)]
        self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::CaptureScratch)?;
        Ok(graph)
    }
    pub(super) fn execute_candidate_graph_plan(&mut self) -> Result<(), SolveAvailabilityError> {
        // Internal occurrences observe open live roots. All member schedules
        // finish before any graph in the component is captured or published.
        let mut components = Vec::new();
        for component in self.batch.scc_plan().components_in_dependency_first_order() {
            push(&mut components, component.clone())?;
        }
        let component_bytes = vec_bytes(&components)?;
        for component in &components {
            let mut members = Vec::new();
            for member in self
                .batch
                .scc_component_members(&component)
                .map_err(|_| exhausted())?
            {
                push(&mut members, member.clone())?;
            }
            let mut staged = Vec::new();
            staged
                .try_reserve_exact(members.len())
                .map_err(|_| exhausted())?;
            self.candidate_graph
                .as_mut()
                .ok_or_else(exhausted)?
                .orchestration_bytes =
                sum(&[component_bytes, vec_bytes(&members)?, vec_bytes(&staged)?])?;
            {
                let state = &mut self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion;
                state.active_roots.try_reserve(members.len()).map_err(|_| exhausted())?;
                state.active_uses.try_reserve(self.batch.scc_plan().internal_uses(component).map_err(|_| exhausted())?.len()).map_err(|_| exhausted())?;
                for member in &members {
                    let root = &self.batch.definitions[member.ordinal() as usize].root;
                    let position = self.batch.root_component_positions[root].component;
                    state.active_roots.insert(member.clone(), self.live_components[position].ordinal);
                }
                for id in self.batch.scc_plan().internal_uses(component).map_err(|_| exhausted())? { state.active_uses.insert(id.clone()); }
            }
            if self.batch.candidate_source.active {
                for member in &members {
                    let root = self.batch.definitions[member.ordinal() as usize].root.clone();
                    self.execute_candidate_source_root(&root)?;
                }
            } else {
                let internal = self.batch.scc_plan().internal_uses(component).map_err(|_| exhausted())?;
                let mut uses = Vec::new();
                uses.try_reserve_exact(internal.len()).map_err(|_| exhausted())?;
                uses.extend(internal.iter().cloned());
                for id in &uses { self.route_candidate_open_use(id)?; }
            }
            let mut source_frontier = Vec::new();
            if self.batch.candidate_source.scoped_experiment {
                source_frontier.try_reserve_exact(members.len()).map_err(|_| exhausted())?;
                for member in &members {
                    let root = &self.batch.definitions[member.ordinal() as usize].root;
                    source_frontier.push(*self.batch.candidate_source.definition_regions.get(root).ok_or_else(exhausted)?);
                }
            }
            for member in &members {
                let position = member.ordinal() as usize;
                let root = self.batch.definitions[position].root.clone();
                let component = self.batch.root_component_positions[&root].component;
                staged.push((
                    position,
                    {
                        let obligations = self.candidate_graph.as_ref().ok_or_else(exhausted)?
                            .source_role_obligations.get(&root).map_or(Ok(Vec::new()), |items| clone_role_obligations(items))?;
                        let field_tails = self.candidate_graph.as_ref().ok_or_else(exhausted)?
                            .source_field_tail_obligations.get(&SourceRootId::Definition(root.clone()))
                            .map_or(Ok(Vec::new()), |items| clone_field_tail_obligations(items))?;
                        self.capture_candidate_graph_owned(self.live_components[component].ordinal, 0, &source_frontier, &obligations, &field_tails)?
                    },
                ));
            }
            // Every member graph is valid before any becomes visible to uses.
            let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
            let addition = staged.iter().try_fold(0usize, |total, (_, graph)| {
                total.checked_add(graph.bytes()?).ok_or_else(exhausted)
            })?;
            let released = members.iter().try_fold(0usize, |total, member| {
                let root = &self.batch.definitions[member.ordinal() as usize].root;
                let Some(obligations) = state.source_role_obligations.get(root) else { return Ok(total); };
                let strings = obligations.iter().try_fold(0usize, |bytes, obligation| {
                    bytes.checked_add(obligation.role_spelling.len()).ok_or_else(exhausted)
                })?;
                total.checked_add(bytes::<SourceRoleObligation>(obligations.capacity())?)
                    .and_then(|bytes| bytes.checked_add(strings))
                    .ok_or_else(exhausted)
            })?;
            let retained = state.retained_bytes.checked_sub(released)
                .and_then(|bytes| bytes.checked_add(addition)).ok_or_else(exhausted)?;
            for member in &members {
                let root = &self.batch.definitions[member.ordinal() as usize].root;
                state.source_role_obligations.remove(root);
            }
            for (position, graph) in staged {
                state.graphs[position] = Some(graph);
            }
            state.retained_bytes = retained;
            state.scratch_bytes = 0;
            state.intrusion.active_roots.clear();
            state.intrusion.active_uses.clear();
            self.sample_f4_resources(ResourceBoundary::AllDrafts)?;
            if self.batch.candidate_source.active { continue; }
            let count = self
                .batch
                .scc_component_incoming_uses(&component)
                .map_err(|_| exhausted())?
                .len();
            for i in 0..count {
                let id = self
                    .batch
                    .scc_component_incoming_uses(&component)
                    .map_err(|_| exhausted())?[i]
                    .clone();
                self.route_incoming(&id)?;
            }
        }
        self.candidate_graph
            .as_mut()
            .ok_or_else(exhausted)?
            .orchestration_bytes = 0;
        Ok(())
    }
    pub(super) fn route_candidate_open_use(&mut self, id: &DefinitionUseId) -> Result<usize, SolveAvailabilityError> {
        let record = Self::validated_route_use(&self.batch, id)?.clone();
        let state = &self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion;
        if !state.active_uses.contains(id) || record.parent.definition().is_none_or(|parent| !state.active_roots.contains_key(parent)) || !state.active_roots.contains_key(&record.target) { return Err(exhausted()); }
        // The original occurrence and cause enter the ordinary route owner;
        // the fresh occurrence row remains distinct from the live target root.
        self.route_internal(id)
    }

    pub(super) fn route_candidate_graph(
        &mut self,
        id: &DefinitionUseId,
        record: DefinitionUse,
    ) -> Result<usize, SolveAvailabilityError> {
        let target = record.target.ordinal() as usize;
        let stored = self.candidate_graph.as_ref()
            .and_then(|state| state.graphs[target].as_ref())
            .ok_or_else(exhausted)?;
        let (root, boundary) = (stored.live_root, stored.boundary);
        let mut source_frontier = Vec::new(); source_frontier.try_reserve_exact(stored.source_frontier.len()).map_err(|_| exhausted())?;
        source_frontier.extend_from_slice(&stored.source_frontier);
        let frontier_scratch = bytes::<candidate_source::SourceRegionId>(source_frontier.capacity())?;
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.scope_inventory.note_scratch(frontier_scratch);
        let entry_scratch = self.candidate_graph.as_ref().unwrap().scratch_bytes;
        let result = (|| {
            let graph = if source_frontier.is_empty() { self.capture_candidate_graph(root, boundary)? }
                else { self.capture_candidate_graph_owned(root, boundary, &source_frontier, &[], &[])? };
            self.instantiate_candidate_graph(id, &record, graph, entry_scratch)
        })();
        self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry_scratch;
        result
    }
    #[cfg(test)]
    pub(super) fn freshen_candidate_graph(
        &mut self, graph: &Graph, use_level: u32,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<(Term, Vec<RowKey>), SolveAvailabilityError> {
        let entry = self.candidate_graph.as_ref().ok_or_else(exhausted)?.scratch_bytes;
        let result = self.freshen_candidate_graph_core(graph, use_level, occurrence, cause);
        match result {
            Ok((root, fresh)) => {
                let (rows, retained) = fresh.into_retained_parts();
                drop(retained);
                self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry;
                Ok((root, rows))
            }
            Err(error) => {
                self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry;
                Err(error)
            }
        }
    }

    fn freshen_candidate_graph_retained(
        &mut self, graph: &Graph, use_level: u32,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<(Term, FreshUse), SolveAvailabilityError> {
        let entry = self.candidate_graph.as_ref().ok_or_else(exhausted)?.scratch_bytes;
        let result = self.freshen_candidate_graph_core(graph, use_level, occurrence, cause)
            .and_then(|(root, fresh)| {
                let transition = fresh.bytes()?;
                let charged = entry.checked_add(transition).ok_or_else(exhausted)?;
                self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = charged;
                Ok((root, fresh))
            });
        if result.is_err() {
            self.candidate_graph.as_mut().ok_or_else(exhausted)?.scratch_bytes = entry;
        }
        result
    }

    fn freshen_candidate_graph_core(
        &mut self, graph: &Graph, use_level: u32,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<(Term, FreshUse), SolveAvailabilityError> {
        (|| {
            let caller = self.batch.candidate_source.occurrence_regions.get(occurrence.occurrence()).copied();
            let fresh = self.prepare_candidate_fresh_use(graph, use_level, caller)?;
            for index in 0..graph.bounds.len() {
                let restoration = self.begin_candidate_fresh_bound(graph, &fresh, index, occurrence, cause)?;
                self.candidate_drive_bound_restoration(restoration)?;
            }
            #[cfg(test)]
            if let Some(census) = &mut self.candidate_graph.as_mut().unwrap().local_use_census {
                if census.requested.contains(occurrence.occurrence()) {
                    census.module_uses.push((occurrence.occurrence().clone(), fresh.context_use));
                }
            }
            let root = fresh.terms[graph.root].ok_or_else(exhausted)?;
            Ok((root, fresh))
        })()
    }
    fn prepare_candidate_fresh_use(
        &mut self, graph: &Graph, use_level: u32, caller: Option<candidate_source::SourceRegionId>,
    ) -> Result<FreshUse, SolveAvailabilityError> {
        let context_use = self.candidate_graph.as_mut().ok_or_else(exhausted)?.intrusion.effect_algebra.context.begin_use()?;
        let scope_remap = if self.batch.candidate_source.scoped_experiment {
            self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.scope_inventory.fresh(&graph.owned_regions, caller.ok_or_else(exhausted)?, graph.nodes.len(), graph.bounds.len())?
        } else { candidate_source::ScopeRemap::default() };
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(scope_remap.bytes()?).ok_or_else(exhausted)?;
        let mut canonical_rows = HashMap::new();
        canonical_rows.try_reserve(graph.rows.len()).map_err(|_| exhausted())?;
        let mut rows = Vec::new();
        rows.try_reserve_exact(graph.rows.len())
            .map_err(|_| exhausted())?;
        let mut source_role_obligation_rows = Vec::new();
        source_role_obligation_rows.try_reserve_exact(graph.source_role_obligations.len()).map_err(|_| exhausted())?;
        for (obligation_index, obligation) in graph.source_role_obligations.iter().enumerate() {
            let row_index = graph.rows.iter().position(|row| row.key == obligation.subject_row)
                .ok_or(SolveAvailabilityError::ReceiptMismatch)?;
            source_role_obligation_rows.push((obligation_index, row_index));
        }
        let mut source_field_tail_obligation_rows = Vec::new();
        source_field_tail_obligation_rows.try_reserve_exact(graph.source_field_tail_obligations.len()).map_err(|_| exhausted())?;
        for (obligation_index, obligation) in graph.source_field_tail_obligations.iter().enumerate() {
            let keys = [obligation.receiver_row, obligation.receiver_effect, obligation.result_row, obligation.result_effect];
            let mut indexes = [0usize; 4];
            for (slot, key) in keys.into_iter().enumerate() {
                indexes[slot] = graph.rows.iter().position(|row| row.key == key).ok_or(SolveAvailabilityError::ReceiptMismatch)?;
            }
            source_field_tail_obligation_rows.push((obligation_index, indexes));
        }
        #[cfg(test)]
        let mut row_observations = {
            let mut observations = Vec::new();
            observations.try_reserve_exact(graph.rows.len()).map_err(|_| exhausted())?;
            observations
        };
        let mut terms = Vec::new();
        terms
            .try_reserve_exact(graph.nodes.len())
            .map_err(|_| exhausted())?;
        terms.resize(graph.nodes.len(), None);
        let mut work = Vec::new();
        work.try_reserve_exact(graph.nodes.len().checked_mul(5).ok_or_else(exhausted)?)
            .map_err(|_| exhausted())?;
        let scratch = sum(&[
            bytes::<RowKey>(rows.capacity())?,
            bytes::<(usize, usize)>(source_role_obligation_rows.capacity())?,
            bytes::<(usize, [usize; 4])>(source_field_tail_obligation_rows.capacity())?,
            bytes::<(RowKey, RowKey)>(canonical_rows.capacity())?,
            #[cfg(test)]
            bytes::<ReconstructedRowObservation>(row_observations.capacity())?,
            bytes::<Option<Term>>(terms.capacity())?,
            bytes::<(usize, bool)>(work.capacity())?,
        ])?;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.scratch_bytes = state.scratch_bytes.checked_add(scratch).ok_or_else(exhausted)?;
        state.use_peak_bytes = state.use_peak_bytes.max(state.scratch_bytes);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        for row in &graph.rows {
            #[cfg(test)]
            let graph_row = rows.len();
            let source = self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.rep(row.key);
            let (level, metadata) = match source { RowKey::Value(i) => (self.value_levels[i as usize], self.value_metadata[i as usize]), RowKey::Effect(i) => (self.effect_levels[i as usize], self.effect_metadata[i as usize]) };
            let existing_image = canonical_rows.get(&source).copied();
            #[cfg(test)]
            let freshening_guard_would_match = row.local && level > graph.boundary && !metadata.non_generic;
            let key = if let Some(existing) = existing_image { existing }
            else {
                let key = if row.local && level > graph.boundary && !metadata.non_generic {
                    match source { RowKey::Value(_) => RowKey::Value(self.fresh_value_at_level(use_level)?), RowKey::Effect(_) => RowKey::Effect(self.fresh_effect_at_level(use_level)?) }
                } else { source };
                canonical_rows.insert(source, key);
                key
            };
            #[cfg(test)]
            {
                let first_entry_graph_row = row_observations.iter()
                    .find(|observation: &&ReconstructedRowObservation| observation.source_representative == source)
                    .map_or(graph_row, |observation| observation.first_entry_graph_row);
                row_observations.push(ReconstructedRowObservation {
                    graph_row, captured: row.key, source_representative: source,
                    level, non_generic: metadata.non_generic, boundary: graph.boundary,
                    stored_local: row.local, canonical_rows_hit: existing_image.is_some(),
                    first_entry_graph_row, existing_image,
                    allocated_fresh_image: existing_image.is_none() && freshening_guard_would_match,
                    image: key,
                    forest_event_cursor: self.candidate_graph.as_ref().ok_or_else(exhausted)?.intrusion.forest_event_cursor(),
                });
            }
            rows.push(key);
        }
        let mut bundle_remap = HashMap::new();
        bundle_remap.try_reserve(graph.attachment_bundles.len()).map_err(|_| exhausted())?;
        let bundle_scratch = bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(bundle_remap.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(bundle_scratch).ok_or_else(exhausted)?;
        for &(_, old) in &graph.attachment_bundles {
            if bundle_remap.contains_key(&old) { continue; }
            let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
            let original = &state.bundles[old.0];
            let mut sets = Vec::new();
            sets.try_reserve_exact(original.sets.len()).map_err(|_| exhausted())?;
            sets.extend_from_slice(&original.sets);
            let bundle = candidate_context::AttachmentBundle { occurrence: original.occurrence.clone(), sets };
            let fresh = state.retain_bundle(bundle, false)?;
            bundle_remap.insert(old, fresh);
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        let mut view_remap = HashMap::new();
        view_remap.try_reserve(graph.nodes.len().checked_add(graph.context_views.len()).ok_or_else(exhausted)?).map_err(|_| exhausted())?;
        let view_scratch = bytes::<((u32, Option<u32>), u32)>(view_remap.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(view_scratch).ok_or_else(exhausted)?;
        let mut effect_operands = HashMap::new();
        effect_operands.try_reserve(graph.nodes.len()).map_err(|_| exhausted())?;
        let operand_scratch = bytes::<(usize, EffectEndpointKey)>(effect_operands.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(operand_scratch).ok_or_else(exhausted)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        for (index, node) in graph.nodes.iter().enumerate() {
            if let Node::EffectOperand { endpoint, tail, .. } = *node {
                let endpoint = match endpoint {
                    EffectEndpointKey::Allowance(id) | EffectEndpointKey::Support(id) => {
                        let tail = tail.map(|index| match graph.nodes[index] {
                            Node::Row { row, .. } => match rows[row] { RowKey::Effect(row) => Ok(row), _ => Err(exhausted()) },
                            _ => Err(exhausted()),
                        }).transpose()?;
                        { let copy = self.candidate_remapped_effect_view(id, tail, &mut view_remap)?;
                            if matches!(endpoint, EffectEndpointKey::Support(_)) { EffectEndpointKey::Support(copy) } else { EffectEndpointKey::Allowance(copy) } }
                    }
                    EffectEndpointKey::AnnotationMember(id, member) => {
                        let tail = tail.map(|index| match graph.nodes[index] {
                            Node::Row { row, .. } => match rows[row] { RowKey::Effect(row) => Ok(row), _ => Err(exhausted()) },
                            _ => Err(exhausted()),
                        }).transpose()?;
                        EffectEndpointKey::AnnotationMember(self.candidate_remapped_effect_view(id, tail, &mut view_remap)?, member)
                    }
                    EffectEndpointKey::Contribution(id) => {
                        let atom = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.contributions[id as usize];
                        let (effect, origin) = (atom.effect.clone(), atom.origin.clone());
                        self.candidate_effect_contribution(effect, origin)?
                    }
                    _ => return Err(exhausted()),
                };
                effect_operands.insert(index, endpoint);
            }
        }
        let mut weight_remap = HashMap::new();
        weight_remap.try_reserve(graph.context_views.len()).map_err(|_| exhausted())?;
        let mut roots = Vec::new();
        roots.try_reserve_exact(graph.bounds.len()).map_err(|_| exhausted())?;
        for bound in &graph.bounds {
            if let Some(parent) = bound.relation {
                roots.push(self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.relation_context(parent)?);
            }
        }
        let mut context_remap = HashMap::new();
        let extra = sum(&[
            bytes::<(candidate_context::LocalWeightId, candidate_context::LocalWeightId)>(weight_remap.capacity())?,
            bytes::<candidate_context::ContextId>(roots.capacity())?,
        ])?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(extra).ok_or_else(exhausted)?;
        for &(weight, id, tail) in &graph.context_views {
            let tail = tail.map(|index| match graph.nodes.get(index) {
                Some(Node::Row { row, .. }) => match rows[*row] { RowKey::Effect(row) => Ok(row), _ => Err(exhausted()) },
                _ => Err(exhausted()),
            }).transpose()?;
            let algebra = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let source = algebra.views.get(id as usize).ok_or_else(exhausted)?;
            algebra.context.validate_payload_view(weight, id, source)?;
            let copy = self.candidate_remapped_effect_view(id, tail, &mut view_remap)?;
            let algebra = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
            let view = algebra.views.get(copy as usize).ok_or_else(exhausted)?;
            let mapped = view.source_weight.ok_or_else(exhausted)?;
            algebra.context.validate_payload_view(mapped, copy, view)?;
            weight_remap.insert(weight, mapped);
        }
        {
            let state = self.candidate_graph.as_mut().unwrap();
            state.intrusion.effect_algebra.context.rename_fresh_contexts(&roots, &weight_remap, &mut context_remap, &mut state.scratch_bytes, &mut state.use_peak_bytes)?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        // Structural Function nodes form a DAG. Cycles run through rows,
        // whose preallocated identities terminate structural reconstruction.
        for root in 0..graph.nodes.len() {
            if terms[root].is_some() {
                continue;
            }
            push(&mut work, (root, false))?;
            while let Some((index, finish)) = work.pop() {
                if terms[index].is_some() {
                    continue;
                }
                let term = match graph.nodes[index] {
                    Node::EffectOperand { .. } => continue,
                    Node::Leaf(atom) => match atom {
                        Atom::Bottom => self.positive_bottom_term()?,
                        Atom::Top => self.negative_top_term()?,
                        Atom::NegativeBottom => self.negative_bottom_term()?,
                        Atom::IntPositive => self.batch.collected_leaf_term(Leaf::IntPositive),
                        Atom::UnitPositive => self.batch.collected_leaf_term(Leaf::UnitPositive),
                        Atom::BoolPositive => self.batch.collected_leaf_term(Leaf::BoolPositive),
                        Atom::StrPositive => self.batch.collected_leaf_term(Leaf::StrPositive),
                        Atom::IntNegative => self.batch.collected_leaf_term(Leaf::IntNegative),
                        Atom::UnitNegative => self.batch.collected_leaf_term(Leaf::UnitNegative),
                        Atom::BoolNegative => self.batch.collected_leaf_term(Leaf::BoolNegative),
                        Atom::StrNegative => self.batch.collected_leaf_term(Leaf::StrNegative),
                        Atom::EffectBottom => {
                            self.batch.collected_leaf_term(Leaf::EffectBottomPositive)
                        }
                        Atom::EmptyEffect => {
                            self.batch.collected_leaf_term(Leaf::EmptyEffectNegative)
                        }
                    },
                    Node::Row { row, polarity } => match rows[row] {
                        RowKey::Value(i) => self.live_value_term(polarity, i)?,
                        RowKey::Effect(i) => self.live_effect_term(polarity, i)?,
                    },
                    Node::Function { polarity, children } => {
                        if !finish {
                            push(&mut work, (index, true))?;
                            for child in children.into_iter().rev() {
                                if terms[child].is_none() {
                                    push(&mut work, (child, false))?;
                                }
                            }
                            continue;
                        }
                        let [a, ae, re, r] = children
                            .map(|child| terms[child].expect("validated structural dependency"));
                        if polarity == Polarity::Positive {
                            self.positive_function_term(a, ae, re, r)?
                        } else {
                            self.negative_function_term(a, ae, re, r)?
                        }
                    }
                    Node::Tuple { polarity, start, len } => {
                        let end = start.checked_add(len).ok_or_else(exhausted)?;
                        let children = graph.tuple_children.get(start..end).ok_or_else(exhausted)?;
                        if !finish {
                            push(&mut work, (index, true))?;
                            for &child in children.iter().rev() {
                                if terms[child].is_none() { push(&mut work, (child, false))?; }
                            }
                            continue;
                        }
                        let mut elements = Vec::new();
                        elements.try_reserve_exact(len).map_err(|_| exhausted())?;
                        for &child in children {
                            elements.push(terms[child].expect("validated tuple dependency"));
                        }
                        if polarity == Polarity::Positive {
                            self.store.terms.positive_tuple(&elements)?
                        } else {
                            self.store.terms.negative_tuple(&elements)?
                        }
                    }
                };
                terms[index] = Some(term);
            }
        }
        let mut scoped_relations = HashMap::new();
        if self.batch.candidate_source.scoped_experiment {
            scoped_relations.try_reserve(graph.bounds.len()).map_err(|_| exhausted())?;
            for bound in &graph.bounds {
                let Some(parent) = bound.relation else { continue; };
                if scoped_relations.contains_key(&parent) { continue; }
                let context = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let mut flow = context.scoped_flow(parent)?;
                if flow.transformer != 0 {
                    context.prepare_scope_remap(flow.transformer)?;
                    let renamed = context.scope_transformer(flow.transformer)?.remap(
                        |id| scope_remap.scopes.get(&id).copied().unwrap_or(id),
                        |id| scope_remap.inputs.get(&id).copied().unwrap_or(id))?;
                    flow.transformer = context.intern_scope(renamed)?;
                }
                if let Some(demand) = &mut flow.demand {
                    let local = scope_remap.inputs.contains_key(&demand.input);
                    demand.output_scope = scope_remap.scopes.get(&demand.output_scope).copied().unwrap_or(demand.output_scope);
                    demand.input = scope_remap.inputs.get(&demand.input).copied().unwrap_or(demand.input);
                    let index = graph.negative_functions.get(&demand.root).copied().ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                    demand.root = terms[index].ok_or_else(exhausted)?;
                    if local { demand.use_instance = context_use; }
                }
                scoped_relations.insert(parent, flow);
            }
        }
        let extra_scoped = bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(scoped_relations.capacity())?;
        self.candidate_graph.as_mut().unwrap().scratch_bytes = self.candidate_graph.as_ref().unwrap().scratch_bytes.checked_add(extra_scoped).ok_or_else(exhausted)?;
        let mut evidence_remap = Vec::new();
        let reserve_count = graph.bound_evidence.len();
        #[cfg(test)]
        let reserve_count = if self.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::ImportReserve) {
            // Exercise the real capacity-overflow error without allocating.
            usize::MAX
        } else { reserve_count };
        let reserved = evidence_remap.try_reserve_exact(reserve_count);
        let evidence_scratch = bytes::<candidate_context::EvidenceSnapshotId>(evidence_remap.capacity())?;
        let state = self.candidate_graph.as_mut().unwrap();
        #[cfg(test)]
        { state.import_evidence_peak_capacity = state.import_evidence_peak_capacity.max(evidence_remap.capacity()); }
        state.scratch_bytes = state.scratch_bytes.checked_add(evidence_scratch).ok_or_else(exhausted)?;
        state.use_peak_bytes = state.use_peak_bytes.max(state.scratch_bytes);
        let reservation = reserved.map_err(|_| exhausted());
        let sampled = self.sample_f4_resources(ResourceBoundary::IncomingRoute);
        if let Err(error) = reservation {
            #[cfg(test)]
            {
                let state = self.candidate_graph.as_mut().unwrap();
                state.import_failure_sample = Some((state.scratch_bytes, self.resource_ledger.inference_session_retained_bytes, sampled.is_ok()));
                if state.evidence_failure == Some(candidate_context::EvidenceFailurePoint::ImportReserve) {
                    state.evidence_failure = None;
                    state.failed_evidence_point = Some(candidate_context::EvidenceFailurePoint::ImportReserve);
                    state.failed_evidence_sample = Some((candidate_context::EvidenceFailurePoint::ImportReserve, state.scratch_bytes, self.resource_ledger.inference_session_retained_bytes));
                    state.failed_import_count = Some(evidence_remap.len());
                }
            }
            return Err(error);
        }
        sampled?;
        let imported = (|| {
            for &snapshot in &graph.bound_evidence {
                let id = self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.import_evidence(snapshot)?;
                evidence_remap.push(id);
                #[cfg(test)]
                if evidence_remap.len() == 1 && evidence_remap.len() < graph.bound_evidence.len()
                    && self.candidate_graph.as_ref().unwrap().evidence_failure == Some(candidate_context::EvidenceFailurePoint::ImportedSnapshot) {
                    self.candidate_graph.as_mut().unwrap().failed_import_count = Some(evidence_remap.len());
                    self.candidate_evidence_failure(candidate_context::EvidenceFailurePoint::ImportedSnapshot)?;
                }
            }
            Ok::<(), SolveAvailabilityError>(())
        })();
        if let Err(error) = imported {
            // The remap is still alive and charged at this error sample.
            let sampled = self.sample_f4_resources(ResourceBoundary::IncomingRoute);
            #[cfg(test)]
            {
                let state = self.candidate_graph.as_mut().unwrap();
                state.import_failure_sample = Some((state.scratch_bytes, self.resource_ledger.inference_session_retained_bytes, sampled.is_ok()));
            }
            let _ = sampled;
            return Err(error);
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(FreshUse { scope_remap, scoped_relations, context_use, rows, source_role_obligation_rows, source_field_tail_obligation_rows, terms, effect_operands, bundle_remap, context_remap, evidence_remap,
            #[cfg(test)] row_observations,
        })
    }
    fn begin_candidate_fresh_bound(
        &mut self, graph: &Graph, fresh: &FreshUse, index: usize,
        occurrence: &ConstraintOccurrenceId, cause: &CauseId,
    ) -> Result<candidate_context::ReplayOperationId, SolveAvailabilityError> {
        // Preserve captured owner orientation and construct transport only once,
        // immediately before this bound's physical admission.
        let bound = graph.bounds.get(index).ok_or_else(exhausted)?;
        let (lower, upper) = match bound.kind {
            ComponentKind::Value => {
                let lower = fresh.terms[bound.lower].ok_or_else(exhausted)?;
                let upper = fresh.terms[bound.upper].ok_or_else(exhausted)?;
                (ExtrusionEndpoint::Value(self.value_endpoint(lower, Polarity::Positive)),
                 ExtrusionEndpoint::Value(self.value_endpoint(upper, Polarity::Negative)))
            }
            ComponentKind::Effect => {
                let lower = if let Some(&operand) = fresh.effect_operands.get(&bound.lower) { operand }
                    else { self.effect_endpoint(fresh.terms[bound.lower].ok_or_else(exhausted)?, Polarity::Positive) };
                let upper = if let Some(&operand) = fresh.effect_operands.get(&bound.upper) { operand }
                    else { self.effect_endpoint(fresh.terms[bound.upper].ok_or_else(exhausted)?, Polarity::Negative) };
                (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper))
            }
        };
        let (owner, item) = if bound.side == Polarity::Positive {
            (upper, lower)
        } else {
            (lower, upper)
        };
        let mut mapped_relation = None;
        if let Some(parent) = bound.relation {
            // One reconstruction route shares all captured relation inputs.
            // Independent uses retain independent transport origins even
            // when an older, nongeneric coordinate is shared.
            let root = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.relation_context(parent)?;
            let child = self.candidate_context_fresh_transport_scoped(parent, candidate_effect::BoundKey(owner, bound.side, item),
                fresh.context_use, *fresh.context_remap.get(&root).ok_or_else(exhausted)?, bound.source_bound,
                fresh.scoped_relations.get(&parent).copied())?;
            mapped_relation = Some(child);
            if let Some(&(start, length)) = graph.attachment_spans.get(&parent) {
                for &(_, old) in &graph.attachment_bundles[start..start + length] {
                    self.candidate_context_fresh_bundle(child, fresh.bundle_remap[&old])?;
                }
            }
        }
        let antecedent = *fresh.evidence_remap.get(bound.evidence.0).ok_or_else(exhausted)?;
        self.candidate_begin_bound_restoration(owner, bound.side, item, occurrence, cause,
            candidate_context::BoundAdmissionCause::FreshUse { antecedent, use_origin: fresh.context_use,
                source_bound: bound.source_bound, mapped_relation })
    }
    fn instantiate_candidate_graph(
        &mut self,
        id: &DefinitionUseId,
        record: &DefinitionUse,
        graph: Graph,
        entry_scratch: usize,
    ) -> Result<usize, SolveAvailabilityError> {
        let occurrence = ConstraintOccurrenceId::new(record.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(occurrence.clone());
        let (lower, fresh) = self.freshen_candidate_graph_retained(&graph, record.use_level, &occurrence, &cause)?;
        let (rows, retained_maps) = fresh.into_retained_parts();
        let remap_bytes = sum(&[bytes::<RowKey>(rows.capacity())?, retained_maps.bytes()?])?;
        let upper = self.batch.component_term_at(record.use_value_component);
        let key = CanonicalValuePairKey {
            lower: self.value_endpoint(lower, Polarity::Positive),
            upper: ValueEndpointKey::ValueRow(
                self.live_components[record.use_value_component].ordinal,
            ),
        };
        // Capture allocation and accounting failure precede route publication.
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        let old_capacity = state.routes.capacity();
        state.routes.try_reserve(1).map_err(|_| exhausted())?;
        let growth = bytes::<FreshRoute>(state.routes.capacity() - old_capacity)?;
        let graph_bytes = graph.bytes()?;
        let retained = sum(&[state.retained_bytes, growth, graph_bytes, remap_bytes])?;
        // The captured Graph is already present in scratch at entry_scratch;
        // FreshUse rows/maps were added by the retained helper. Transfer both
        // categories to route ownership and leave the caller's scratch intact.
        let transfer_bytes = sum(&[graph_bytes, remap_bytes])?;
        let scratch = state.scratch_bytes.checked_sub(transfer_bytes).ok_or_else(exhausted)?;
        state.retained_bytes = retained;
        state.scratch_bytes = scratch;
        #[cfg(test)]
        assert_eq!(state.scratch_bytes, entry_scratch,
            "module route transfer preserves caller scratch before resource sampling");
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        let transitions = self.route(
            id,
            record,
            lower,
            upper,
            key,
            RoutedUseKind::IncomingStructured,
        )?;
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        state.routes.push(FreshRoute {
            use_id: id.clone(),
            graph,
            rows,
            retained: retained_maps,
        });
        state.scratch_bytes = entry_scratch;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(transitions)
    }
    pub(super) fn install_candidate_local(&mut self, slot: usize, endpoint: shadow_apply::CandidateEndpoint, boundary: u32) -> Result<(), SolveAvailabilityError> {
        let term = self.candidate_endpoint(endpoint, Polarity::Positive)?;
        self.install_candidate_local_term(slot, term, boundary)
    }
    pub(super) fn install_candidate_local_term(&mut self, slot: usize, term: Term, boundary: u32) -> Result<(), SolveAvailabilityError> {
        let ValueEndpointKey::ValueRow(root) = self.value_endpoint(term, Polarity::Positive) else { return Err(exhausted()); };
        let id = self.batch.candidate_source.locals.get(slot).ok_or_else(exhausted)?.clone();
        if self.candidate_graph.as_ref().and_then(|state| state.locals.get(slot)).is_none_or(Option::is_some) {
            return Err(exhausted());
        }
        #[cfg(feature = "shadow-apply-candidate")]
        if let Some(journal) = &mut self.route_journal {
            journal.candidate_local_slots.try_reserve(1).map_err(|_| exhausted())?;
            journal.candidate_local_slots.push(slot);
        }
        let state = self.candidate_graph.as_mut().ok_or_else(exhausted)?;
        let destination = state.locals.get_mut(slot).ok_or_else(exhausted)?;
        let capture_region = self.batch.candidate_source.local_regions.get(&id).copied();
        *destination = Some(LocalScheme { capture_region, id, root, boundary });
        self.sample_f4_resources(ResourceBoundary::SourceDrafts)?;
        Ok(())
    }
    pub(super) fn admit_candidate_value_link(&mut self, source: &HirOccurrenceId, slot: u8, lower: Term, upper: Term) -> Result<(), SolveAvailabilityError> {
        let id = ConstraintOccurrenceId::new(source.clone(), slot);
        let cause = CauseId::for_occurrence(id.clone());
        self.store.admit_and_record_provenance(&ConstraintOccurrence { id: id.clone(), cause: cause.clone(), lower, upper })
            .map_err(SolveAvailabilityError::from)?;
        let key = CanonicalValuePairKey { lower: self.value_endpoint(lower, Polarity::Positive), upper: self.value_endpoint(upper, Polarity::Negative) };
        self.constrain_live_value(key, &id, &cause)?;
        Ok(())
    }
    pub(super) fn route_candidate_local(&mut self, slot: usize, occurrence: &HirOccurrenceId, value: usize, level: u32) -> Result<(), SolveAvailabilityError> {
        match self.route_candidate_local_run(slot, occurrence, value, level, None)? {
            LocalRun::Complete => Ok(()),
            LocalRun::Paused => unreachable!("production local routing cannot inject a pause"),
        }
    }
    // A pause budget is supplied only by the enclosed test script. This is not
    // authenticated support, incidence deferral, or a production suspension API.
    fn route_candidate_local_run(&mut self, slot: usize, occurrence: &HirOccurrenceId, value: usize, level: u32,
        pause_after: Option<usize>) -> Result<LocalRun, SolveAvailabilityError> {
        #[cfg(not(test))]
        assert!(pause_after.is_none());
        self.incoming_route_accounting_active = true;
        self.route_attempt_physical_change = false;
        self.incoming_route_event_sample_failed = false;
        let result = self.begin_route_transaction().and_then(|()| self.finish_route_transaction_with_candidate_accounting(|session| {
            if session.candidate_graph.as_ref().ok_or_else(exhausted)?.local_use.is_empty() {
                let (root, boundary, local, capture_region) = {
                    let scheme = session.candidate_graph.as_ref().and_then(|state| state.locals.get(slot)).and_then(Option::as_ref).ok_or_else(exhausted)?;
                    (scheme.root, scheme.boundary, scheme.id.clone(), scheme.capture_region)
                };
                let scoped = session.batch.candidate_source.scoped_experiment;
                let state = session.candidate_graph.as_mut().unwrap();
                if state.local_route_by_occurrence.contains_key(occurrence) { return Err(exhausted()); }
                let old_index_capacity = state.local_route_by_occurrence.capacity();
                if scoped {
                    let work = if state.local_route_by_occurrence.len() == old_index_capacity {
                        state.local_route_by_occurrence.len().checked_add(4).ok_or_else(exhausted)?
                    } else { 4 };
                    state.intrusion.effect_algebra.context.scope_inventory.charge(work)?;
                }
                state.local_route_by_occurrence.try_reserve(1).map_err(|_| exhausted())?;
                state.retained_bytes = state.retained_bytes.checked_add(
                    bytes::<(HirOccurrenceId, usize)>(state.local_route_by_occurrence.capacity() - old_index_capacity)?,
                ).ok_or_else(exhausted)?;
                let old_capacity = state.local_use.capacity();
                state.local_use.try_reserve(1).map_err(|_| exhausted())?;
                state.retained_bytes = state.retained_bytes.checked_add(bytes::<LocalUse>(state.local_use.capacity() - old_capacity)?).ok_or_else(exhausted)?;
                session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
                // Capture and construction remain atomic; no child has started.
                let frontier = capture_region.as_slice();
                let graph = session.capture_candidate_graph_owned(root, boundary, frontier, &[], &[])?;
                let caller = session.batch.candidate_source.occurrence_regions.get(occurrence).copied();
                let fresh = session.prepare_candidate_fresh_use(&graph, level, caller)?;
                let retained = sum(&[session.candidate_graph.as_ref().unwrap().retained_bytes, graph.bytes()?, fresh.bytes()?])?;
                let state = session.candidate_graph.as_mut().unwrap();
                state.local_use.push(LocalUse { slot, local, occurrence: occurrence.clone(), value, level,
                    graph, fresh, cursor: LocalUseCursor::default() });
                state.scratch_bytes = 0;
                state.retained_bytes = retained;
                session.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            }
            {
                let frame = session.candidate_graph.as_ref().unwrap().local_use.last().ok_or_else(exhausted)?;
                if frame.slot != slot || &frame.occurrence != occurrence || frame.value != value || frame.level != level {
                    return Err(exhausted());
                }
            }
            let mut steps = 0;
            loop {
                // Ownership is transferred temporarily during an atomic owner
                // step and restored before every fallible return or pause.
                let mut frame = session.candidate_graph.as_mut().unwrap().local_use.pop().unwrap();
                let result = session.step_candidate_local_use(&mut frame);
                let complete = frame.cursor.complete;
                session.candidate_graph.as_mut().unwrap().local_use.push(frame);
                result?;
                if session.incoming_route_event_sample_failed { return Err(exhausted()); }
                if complete { return Ok(LocalRun::Complete); }
                steps += 1;
                if pause_after == Some(steps) { return Ok(LocalRun::Paused); }
            }
        }, true));
        self.incoming_route_accounting_active = false;
        self.route_attempt_physical_change = false;
        self.incoming_route_event_sample_failed = false;
        if let Some(state) = &mut self.candidate_graph { state.scratch_bytes = 0; }
        result
    }
    #[cfg(test)]
    pub(super) fn candidate_test_local_script(&mut self, script: &[LocalScriptStep]) -> Result<Vec<LocalScriptObservation>, SolveAvailabilityError> {
        let source = self.candidate_graph.as_ref().and_then(|state| state.source).ok_or_else(exhausted)?;
        if source.stage != candidate_source::Stage::Execute { return Err(exhausted()); }
        let actions = match source.schedule {
            candidate_source::Schedule::Loose => &self.batch.candidate_source.loose,
            candidate_source::Schedule::Expression(index) => &self.batch.candidate_source.expressions.get(index).ok_or_else(exhausted)?.actions,
            candidate_source::Schedule::Member(index) => &self.batch.candidate_source.members.get(index).ok_or_else(exhausted)?.actions,
            candidate_source::Schedule::Root(index) => {
                let root = &self.batch.definitions.get(index).ok_or_else(exhausted)?.root;
                self.batch.candidate_source.schedules.get(root).ok_or_else(exhausted)?
            }
        };
        let Some(candidate_source::Action::Local { slot, occurrence, value, level }) = actions.get(source.next).cloned() else { return Err(exhausted()); };
        let mut observations = Vec::new();
        observations.try_reserve_exact(script.len()).map_err(|_| exhausted())?;
        for step in script {
            match step {
                LocalScriptStep::DriveOne => {
                    if self.route_candidate_local_run(slot, &occurrence, value, level, Some(1))? != LocalRun::Paused { return Err(exhausted()); }
                }
                LocalScriptStep::Idle => {
                    if self.candidate_graph.as_ref().unwrap().local_use.is_empty() { return Err(exhausted()); }
                }
                LocalScriptStep::FailOne => {
                    let result = self.begin_route_transaction().and_then(|()| self.finish_route_transaction_with_candidate_accounting(|session| {
                        let mut frame = session.candidate_graph.as_mut().unwrap().local_use.pop().ok_or_else(exhausted)?;
                        let result = session.step_candidate_local_use(&mut frame);
                        session.candidate_graph.as_mut().unwrap().local_use.push(frame);
                        result?;
                        Err::<(), _>(exhausted())
                    }, true));
                    if result != Err(exhausted()) { return Err(exhausted()); }
                }
                LocalScriptStep::Complete => {
                    if self.route_candidate_local_run(slot, &occurrence, value, level, None)? != LocalRun::Complete { return Err(exhausted()); }
                    self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().next += 1;
                }
            }
            // Test-only enumeration checks incremental frame/publication charges
            // after both commit and rollback; production has no route rescan.
            let graph = self.candidate_graph.as_mut().unwrap();
            let tracked = graph.retained_bytes;
            graph.refresh_bytes()?;
            assert_eq!(graph.retained_bytes, tracked, "local continuation retained accounting");
            let context = &graph.intrusion.effect_algebra.context;
            assert_eq!(context.bytes()?, context.enumerated_bytes(), "owner operation and undo accounting");
            if !context.typed_drains.is_empty() || !self.typed_worklist.is_empty() { return Err(exhausted()); }
            let frame = graph.local_use.last();
            let restoration = frame.and_then(|frame| frame.cursor.restoration)
                .map(|id| context.restoration(id).cloned()).transpose()?;
            observations.push(LocalScriptObservation { source_next: graph.source.unwrap().next,
                use_origin: frame.map(|frame| frame.fresh.context_use), cursor: frame.map(|frame| frame.cursor),
                restoration, checkpoint: context.checkpoint(), retained_bytes: graph.retained_bytes,
                routes: graph.local_routes.len(), facts: self.store.facts.len(), typed_drains: context.typed_drains.len() });
        }
        Ok(observations)
    }
    #[cfg(test)]
    pub(super) fn candidate_test_retained_local_step(&mut self, fail_after: bool) -> Result<(), SolveAvailabilityError> {
        if self.route_journal.is_some() { return Err(exhausted()); }
        let state = self.candidate_graph.as_ref().ok_or_else(exhausted)?;
        if state.local_use.len() != 1 || state.local_use[0].cursor.complete { return Err(exhausted()); }
        self.begin_route_transaction_for(RoutePurpose::RetainedResume)?;
        self.finish_route_transaction(|session| {
            let restoration = session.candidate_graph.as_ref().unwrap().local_use[0].cursor.restoration;
            if let Some(restoration) = restoration {
                let state = session.candidate_graph.as_ref().unwrap();
                let operation = state.intrusion.effect_algebra.context.restoration(restoration)?;
                let occurrence = ConstraintOccurrenceId::new(state.local_use[0].occurrence.clone(), 0);
                if operation.occurrence != occurrence || operation.cause != CauseId::for_occurrence(occurrence) { return Err(exhausted()); }
                // The Local remains in its owner vector throughout child execution
                // and receipt delivery, including all fallible returns.
                if session.candidate_step_bound_restoration_child(restoration, true)?.is_some() {
                    let frame = &mut session.candidate_graph.as_mut().unwrap().local_use[0];
                    frame.cursor.restoration = None;
                    frame.cursor.next_bound += 1;
                }
            } else {
                if !session.typed_worklist.is_empty()
                    || !session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.typed_drains.is_empty() {
                    return Err(exhausted());
                }
                let mut frame = session.candidate_graph.as_mut().unwrap().local_use.pop().unwrap();
                let result = session.step_candidate_local_use(&mut frame);
                session.candidate_graph.as_mut().unwrap().local_use.push(frame);
                result?;
            }
            if fail_after { return Err(exhausted()); }
            Ok(())
        })
    }
    fn step_candidate_local_use(&mut self, frame: &mut LocalUse) -> Result<(), SolveAvailabilityError> {
        if frame.cursor.complete { return Err(exhausted()); }
        let id = ConstraintOccurrenceId::new(frame.occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(id.clone());
        if let Some(restoration) = frame.cursor.restoration {
            if self.candidate_step_bound_restoration(restoration)?.is_some() {
                frame.cursor.restoration = None;
                frame.cursor.next_bound += 1;
            }
            return Ok(());
        }
        if frame.cursor.next_bound < frame.graph.bounds.len() {
            let restoration = self.begin_candidate_fresh_bound(&frame.graph, &frame.fresh, frame.cursor.next_bound, &id, &cause)?;
            frame.cursor.restoration = Some(restoration);
            return Ok(());
        }
        let lower = frame.fresh.terms[frame.graph.root].ok_or_else(exhausted)?;
        let upper = self.batch.component_term_at(frame.value);
        self.admit_candidate_value_link(&frame.occurrence, 0, lower, upper)?;
        if self.batch.candidate_source.scoped_experiment {
            self.candidate_graph.as_mut().ok_or_else(exhausted)?
                .intrusion.effect_algebra.context.scope_inventory.charge(1)?;
            if self.candidate_graph.as_ref().ok_or_else(exhausted)?.local_routes.len() >= candidate_source::SCOPED_RECORD_LIMIT {
                return Err(exhausted());
            }
        }
        let state = self.candidate_graph.as_mut().unwrap();
        let old = state.local_routes.capacity();
        if state.local_routes.len() == old {
            // Keep the original allocation in undo. Moving the existing entries
            // avoids cloning their graphs/rows, and rollback can move them back
            // without allocating. Geometric growth keeps publication amortized.
            let capacity = old.checked_mul(2).ok_or_else(exhausted)?.max(4);
            if self.batch.candidate_source.scoped_experiment {
                let work = state.local_routes.len().checked_mul(2).and_then(|n| n.checked_add(2)).ok_or_else(exhausted)?;
                state.intrusion.effect_algebra.context.scope_inventory.charge(work)?;
            }
            let mut replacement = Vec::new();
            replacement.try_reserve_exact(capacity).map_err(|_| exhausted())?;
            let retained_bytes = state.retained_bytes.checked_add(
                bytes::<LocalFreshRoute>(replacement.capacity() - old)?).ok_or_else(exhausted)?;
            let journal = self.route_journal.as_mut().ok_or_else(exhausted)?;
            if journal.candidate_local_routes_allocation.is_some() { return Err(exhausted()); }
            replacement.append(&mut state.local_routes);
            journal.candidate_local_routes_allocation = Some(std::mem::replace(&mut state.local_routes, replacement));
            state.retained_bytes = retained_bytes;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        frame.cursor.complete = true;
        Ok(())
    }
}

#[cfg(test)]
mod authentic_demand_capture_tests {
    use super::*;

    #[test]
    fn imported_binding_uses_keep_distinct_hir_artifacts_in_one_freshuse_world() {
        let provider_text: Arc<yu_syntax::SourceText> = Arc::from("pub id x = x\n");
        let provider_parsed = yu_syntax::parse_file(
            provider_text.clone(), Arc::new(yu_syntax::scan_header(provider_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let provider_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("multi-hir-import", "lib/std/prelude.yu"),
        ));
        let exports = yu_hir::shadow::index_source_exports(provider_identity.clone(), &provider_parsed).unwrap();
        let std_text: Arc<yu_syntax::SourceText> = Arc::from("pub mod prelude;\n");
        let std_parsed = yu_syntax::parse_file(
            std_text.clone(), Arc::new(yu_syntax::scan_header(std_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let std_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("multi-hir-import", "lib/std.yu"),
        ));
        let std_exports = yu_hir::shadow::index_source_exports(std_identity, &std_parsed).unwrap();
        let provider = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            provider_identity, &provider_parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());

        let consumer_text: Arc<yu_syntax::SourceText> = Arc::from(
            "pub first = id 42\npub second = id \"Yulang\"\n",
        );
        let consumer_parsed = yu_syntax::parse_file(
            consumer_text.clone(), Arc::new(yu_syntax::scan_header(consumer_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let consumer_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("multi-hir-import", "consumer.yu"),
        ));
        let imports = yu_hir::SemanticImports::with_implicit_prelude(
            &consumer_parsed, &consumer_identity, &[std_exports, exports],
        ).unwrap();
        let consumer = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            consumer_identity, &consumer_parsed, imports,
        ).unwrap());
        let foreign = lower("pub id x = x\n");
        assert!(!Arc::ptr_eq(&provider, &consumer));

        let candidate = crate::shadow_apply::CandidateInference::solve_modules(vec![
            consumer.clone(), provider.clone(),
        ]).unwrap();
        assert!(candidate.observes_hir(&consumer));
        assert!(candidate.observes_hir(&provider));
        assert!(!candidate.observes_hir(&foreign));
        assert!(candidate.candidate_conflicts().is_empty());
        let consumer_root = |name: &str| consumer.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        for (name, leaf) in [
            ("first", crate::shadow_apply::CandidateGraphLeaf::IntPositive),
            ("second", crate::shadow_apply::CandidateGraphLeaf::StrPositive),
        ] {
            let graph = candidate.export(&consumer_root(name)).unwrap();
            assert!(graph.bounds().any(|bound| {
                bound.lower().leaf() == Some(leaf) || bound.upper().leaf() == Some(leaf)
            }), "the imported polymorphic use retains its concrete {name} constraint");
        }
        let provider_root = provider.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "id" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let provider_graph = candidate.export(&provider_root).unwrap();
        assert!(provider_graph.rows().any(|row| row.is_local()));

        let use_occurrences: HashSet<_> = consumer.items().iter().filter_map(|item| match item {
            HirItem::Binding(binding) if matches!(binding.name().spelling(), "first" | "second") => {
                let source = consumer.local_source(binding.definition_root()).unwrap().unwrap();
                source.expressions().iter().find_map(|expression| matches!(
                    &expression.form,
                    yu_hir::shadow::LocalSourceForm::Name {
                        resolution: yu_hir::shadow::LocalSourceResolution::Imported(_), ..
                    }
                ).then(|| expression.occurrence.clone()))
            }
            _ => None,
        }).collect();
        assert_eq!(use_occurrences.len(), 2);
        let imported_uses = use_occurrences.iter().map(|occurrence| {
            let fresh = candidate.fresh_use(occurrence).expect("authenticated imported use retains its FreshUse route");
            assert_eq!(fresh.occurrence(), occurrence);
            fresh.rows().collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        assert_eq!(imported_uses.len(), 2);
        let first_local: Vec<_> = imported_uses[0].iter().filter(|row| row.source_row().is_local()).collect();
        let second_local: Vec<_> = imported_uses[1].iter().filter(|row| row.source_row().is_local()).collect();
        assert!(!first_local.is_empty(), "the provider function's quantified value row is captured");
        assert!(!second_local.is_empty());
        assert!(first_local.iter().all(|first| second_local.iter().all(|second| !first.same_identity(*second))),
            "independent imported uses get disjoint local rows");
    }

    fn lower(text: &str) -> Arc<HirModule> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(), Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "multi-hir-import-foreign", "foreign.yu",
            ))), &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap())
    }

    #[test]
    fn declaration_where_subject_uses_provider_row_and_same_freshuse_image() {
        const SOURCE: &str = "my display(value: 'a) =\n    where 'a: Display\n    value";
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "where-freshuse-identity", "source.yu",
            ))), &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let root = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "display" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.start_candidate_graph().unwrap();
        session.execute_candidate_source_root(&root).unwrap();

        let retained = session.candidate_graph.as_ref().unwrap().retained_bytes;
        session.candidate_graph.as_mut().unwrap().refresh_bytes().unwrap();
        assert_eq!(session.candidate_graph.as_ref().unwrap().retained_bytes, retained,
            "source prerequisite storage is included in incremental accounting");

        let obligations = session.candidate_graph.as_ref().unwrap().source_role_obligations[&root].clone();
        assert_eq!(obligations.len(), 1);
        let obligation = &obligations[0];
        assert_eq!(obligation.provider, root);
        assert_eq!(obligation.role_spelling.as_ref(), "Display");
        assert_eq!(obligation.subject_row.kind(), ComponentKind::Value);
        let source = session.batch.hir.local_source(&root).unwrap().unwrap();
        assert_eq!(obligation.where_source, source.where_clauses()[0].source);
        assert_eq!(obligation.subject_source, source.where_clauses()[0].subject.source);
        assert_eq!(obligation.role_source, source.where_clauses()[0].role.source);

        let component = session.batch.root_component_positions[&root].component;
        let graph = session.capture_candidate_graph_owned(
            session.live_components[component].ordinal, 0, &[], &obligations, &[],
        ).unwrap();
        assert_eq!(graph.source_role_obligations.len(), 1);
        let row_index = graph.rows.iter().position(|row| row.key == obligation.subject_row).unwrap();
        let fresh = session.prepare_candidate_fresh_use(&graph, 1, None).unwrap();
        assert_eq!(fresh.source_role_obligation_rows, [(0, row_index)]);
        assert_eq!(fresh.rows.len(), graph.rows.len());
        if graph.rows[row_index].local {
            assert_ne!(fresh.rows[row_index], graph.rows[row_index].key,
                "the prerequisite subject follows the same generic row's FreshUse image");
        } else {
            assert_eq!(fresh.rows[row_index], graph.rows[row_index].key);
        }
        let mapped_subject = fresh.rows[row_index];
        let (mapped_rows, retained) = fresh.into_retained_parts();
        assert_eq!(retained.source_role_obligation_rows, [(0, row_index)]);
        assert_eq!(mapped_rows[row_index], mapped_subject);

        let provider_text: Arc<yu_syntax::SourceText> =
            Arc::from("pub role Display 'a:\n    pub a.show: str\n");
        let provider_parsed = yu_syntax::parse_file(
            provider_text.clone(),
            Arc::new(yu_syntax::scan_header(provider_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let provider_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("where-role-provider", "lib/std/prelude.yu"),
        ));
        let exports = yu_hir::shadow::index_source_exports(
            provider_identity.clone(),
            &provider_parsed,
        )
        .unwrap();
        let std_text: Arc<yu_syntax::SourceText> = Arc::from("pub mod prelude;\n");
        let std_parsed = yu_syntax::parse_file(
            std_text.clone(),
            Arc::new(yu_syntax::scan_header(std_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let std_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("where-role-provider", "lib/std.yu"),
        ));
        let std_exports =
            yu_hir::shadow::index_source_exports(std_identity, &std_parsed).unwrap();
        let roles = yu_hir::shadow::index_role_impl_sources(
            provider_identity,
            &provider_parsed,
        )
        .unwrap();
        let authenticated_id = roles.roles()[0].id.clone();
        let resolution = yu_hir::shadow::resolve_public_export(
            &[std_exports.clone(), exports.clone()],
            "std::prelude",
            "Display",
        )
        .unwrap();
        yu_hir::shadow::resolve_source_export_owner(&[], &[roles.clone()], &resolution).unwrap();

        let consumer_text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let consumer_parsed = yu_syntax::parse_file(
            consumer_text.clone(),
            Arc::new(yu_syntax::scan_header(consumer_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let consumer_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("where-role-consumer", "consumer.yu"),
        ));
        let imports = yu_hir::SemanticImports::with_implicit_prelude_and_role_indexes(
            &consumer_parsed,
            &consumer_identity,
            &[std_exports, exports],
            &[roles],
        )
        .unwrap();
        assert_eq!(
            imports.source_imports().unwrap().role_id("Display"),
            Some(&authenticated_id),
        );
        let imported_hir = Arc::new(
            yu_hir::shadow::lower_module_with_local_source(
                consumer_identity,
                &consumer_parsed,
                imports,
            )
            .unwrap(),
        );
        let imported_root = imported_hir
            .items()
            .iter()
            .find_map(|item| match item {
                yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "display" => {
                    Some(binding.definition_root().clone())
                }
                _ => None,
            })
            .unwrap();
        let imported_batch =
            ConstraintBatch::collect_candidate_mode(imported_hir, true, true).unwrap();
        let mut imported_session = InferenceSession::try_new_candidate(imported_batch).unwrap();
        imported_session.start_candidate_graph().unwrap();
        imported_session
            .execute_candidate_source_root(&imported_root)
            .unwrap();
        assert_eq!(
            imported_session.candidate_graph.as_ref().unwrap().source_role_obligations
                [&imported_root][0]
                .role_identity,
            Some(authenticated_id),
            "the exact imported role identity reaches the retained declaration obligation",
        );
    }

    #[test]
    fn deferred_field_tail_rows_survive_capture_and_same_freshuse_map() {
        const SOURCE: &str = "my select x = x.show\n";
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "fieldtail-freshuse-identity", "source.yu",
            ))), &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let root = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "select" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.start_candidate_graph().unwrap();
        session.execute_candidate_source_root(&root).unwrap();

        let retained_bytes = session.candidate_graph.as_ref().unwrap().retained_bytes;
        session.candidate_graph.as_mut().unwrap().refresh_bytes().unwrap();
        assert_eq!(session.candidate_graph.as_ref().unwrap().retained_bytes, retained_bytes,
            "deferred FieldTail records participate in checked accounting");
        let owner = SourceRootId::Definition(root.clone());
        let obligations = clone_field_tail_obligations(session.candidate_graph.as_ref().unwrap()
            .source_field_tail_obligations.get(&owner).unwrap()).unwrap();
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].member.as_ref(), "show");
        assert_eq!(obligations[0].owner, owner);
        let source = hir.local_source(&root).unwrap().unwrap();
        let field = source.expressions().iter().find(|expression|
            matches!(expression.form, yu_hir::shadow::LocalSourceForm::FieldTail { .. })).unwrap();
        assert_eq!(obligations[0].occurrence, field.occurrence);
        assert_eq!(obligations[0].source, field.source);

        let component = session.batch.root_component_positions[&root].component;
        let graph = session.capture_candidate_graph_owned(
            session.live_components[component].ordinal, 0, &[], &[], &obligations,
        ).unwrap();
        assert_eq!(graph.source_field_tail_obligations.len(), 1);
        let transported = &graph.source_field_tail_obligations[0];
        let keys = [transported.receiver_row, transported.receiver_effect, transported.result_row, transported.result_effect];
        let indexes = keys.map(|key| graph.rows.iter().position(|row| row.key == key).unwrap());
        let fresh = session.prepare_candidate_fresh_use(&graph, 1, None).unwrap();
        assert_eq!(fresh.source_field_tail_obligation_rows, [(0, indexes)]);
        for index in indexes {
            if graph.rows[index].local {
                assert_ne!(fresh.rows[index], graph.rows[index].key,
                    "each local value/effect row uses its same FreshUse image");
            } else {
                assert_eq!(fresh.rows[index], graph.rows[index].key,
                    "shared value/effect anchors remain fixed");
            }
        }
        let (rows, retained) = fresh.into_retained_parts();
        assert_eq!(retained.source_field_tail_obligation_rows, [(0, indexes)]);
        for index in indexes { let _same_use_image = rows[index]; }
    }

    #[test]
    fn deferred_field_tail_keeps_authenticated_role_member_candidates() {
        let provider_text: Arc<yu_syntax::SourceText> =
            Arc::from("pub role Display 'a:\n    pub a.show: str\n");
        let provider_parsed = yu_syntax::parse_file(
            provider_text.clone(), Arc::new(yu_syntax::scan_header(provider_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let provider_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("fieldtail-role-candidates", "lib/std/prelude.yu"),
        ));
        let provider_exports = yu_hir::shadow::index_source_exports(
            provider_identity.clone(), &provider_parsed,
        ).unwrap();
        let provider_roles = yu_hir::shadow::index_role_impl_sources(
            provider_identity, &provider_parsed,
        ).unwrap();
        let expected_member = provider_roles.roles()[0].body.as_ref().unwrap().members[0].id.clone();
        let std_text: Arc<yu_syntax::SourceText> = Arc::from("pub mod prelude;\n");
        let std_parsed = yu_syntax::parse_file(
            std_text.clone(), Arc::new(yu_syntax::scan_header(std_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let std_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("fieldtail-role-candidates", "lib/std.yu"),
        ));
        let std_exports = yu_hir::shadow::index_source_exports(std_identity, &std_parsed).unwrap();

        let consumer_text: Arc<yu_syntax::SourceText> =
            Arc::from("use std::prelude::Display\nmy select x = x.show\n");
        let consumer_parsed = yu_syntax::parse_file(
            consumer_text.clone(), Arc::new(yu_syntax::scan_header(consumer_text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let consumer_identity = yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(
            yu_hir::FileKey::new("fieldtail-role-candidates", "consumer.yu"),
        ));
        let imports = yu_hir::SemanticImports::with_source_imports_and_role_indexes(
            &consumer_parsed, &consumer_identity, &[std_exports, provider_exports], &[provider_roles],
        ).unwrap();
        assert_eq!(imports.source_imports().unwrap().role_member_id("Display", "show"), Some(&expected_member));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            consumer_identity, &consumer_parsed, imports,
        ).unwrap());
        let root = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "select" => {
                Some(binding.definition_root().clone())
            }
            _ => None,
        }).unwrap();
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.start_candidate_graph().unwrap();
        session.execute_candidate_source_root(&root).unwrap();
        let owner = SourceRootId::Definition(root.clone());
        let obligations = &session.candidate_graph.as_ref().unwrap().source_field_tail_obligations[&owner];
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].member.as_ref(), "show");
        assert_eq!(obligations[0].role_member_candidates, [expected_member]);
    }

    #[test]
    fn types_sample_fieldtail_receiver_bounds_expose_ordered_pair_shape() {
        const SOURCE: &str = "my id x = x\nmy answer = id 42\nmy name = id \"Yulang\"\nmy pair = (answer, name)\npair.say\n";
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(
            text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "fieldtail-types-bounds", "Types.yu",
            ))), &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.start_candidate_graph().unwrap();
        session.execute().unwrap();

        let obligations = session.candidate_graph.as_ref().unwrap().source_field_tail_obligations.values()
            .flat_map(|items| items.iter()).collect::<Vec<_>>();
        assert_eq!(obligations.len(), 1);
        assert_eq!(obligations[0].member.as_ref(), "say");
        let RowKey::Value(receiver) = obligations[0].receiver_row else { panic!("FieldTail receiver is a Value row"); };
        let mut pending = vec![receiver];
        let mut visited = HashSet::new();
        let mut pair_element_rows = None;
        while let Some(row) = pending.pop() {
            if !visited.insert(row) { continue; }
            let bounds = &session.bounds[row as usize];
            pending.extend(bounds.direct_lower_rows.iter().copied());
            for endpoint in &bounds.exact_non_variable_lowers {
                let ValueEndpointKey::PositiveTuple(term, 2) = *endpoint else { continue; };
                let TermView::PositiveTuple { elements } = session.store.term_view(term).unwrap() else {
                    panic!("positive tuple endpoint retains a positive tuple term");
                };
                pair_element_rows = Some(elements.iter().map(|element| {
                    let TermView::LiveVariable(variable) = session.store.term_view(*element).unwrap() else {
                        panic!("tuple element type remains a live Value row before its bounds are inspected");
                    };
                    assert_eq!(variable.kind(), ComponentKind::Value);
                    assert_eq!(variable.polarity(), Polarity::Positive);
                    variable.ordinal()
                }).collect::<Vec<_>>());
            }
        }
        let pair_element_rows = pair_element_rows.expect("receiver has a two-element tuple lower bound");
        assert_eq!(pair_element_rows.len(), 2);
        for (row, expected_leaf) in pair_element_rows.into_iter().zip([ValueEndpointKey::IntPositive, ValueEndpointKey::StrPositive]) {
            let mut pending = vec![row];
            let mut visited = HashSet::new();
            let mut observed_expected_leaf = false;
            while let Some(row) = pending.pop() {
                if !visited.insert(row) { continue; }
                let bounds = &session.bounds[row as usize];
                pending.extend(bounds.direct_lower_rows.iter().copied());
                observed_expected_leaf |= bounds.exact_non_variable_lowers.iter().any(|endpoint| *endpoint == expected_leaf);
            }
            assert!(observed_expected_leaf, "pair element row retains its corresponding source lower bound");
        }
    }

    #[test]
    fn tuple_fresh_use_reconstructs_each_captured_child_in_order() {
        const SOURCE: &str = "my tuple = (1, (true, \"x\"))\nmy copied = tuple";
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(
            text.clone(),
            Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "tuple-fresh-use-order", "source.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).unwrap());
        let copied_root = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "copied" =>
                Some(binding.definition_root()),
            _ => None,
        }).unwrap();
        let source = hir.local_source(copied_root).unwrap().unwrap();
        let occurrence = source.expressions().iter().find_map(|expression| match &expression.form {
            yu_hir::shadow::LocalSourceForm::Name {
                resolution: yu_hir::shadow::LocalSourceResolution::ModuleDef(_), ..
            } => Some(expression.occurrence.clone()),
            _ => None,
        }).unwrap();

        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.execute().unwrap();
        assert!(session.errors.is_empty());
        let state = session.candidate_graph.as_ref().unwrap();
        let route = state.routes.iter().find(|route| route.use_id.occurrence() == &occurrence)
            .expect("the source Name use owns a retained FreshUse route");
        assert!(route.graph.nodes.iter().any(|node|
            matches!(node, Node::Tuple { len: 2, .. })));

        let mut tuple_arities = Vec::new();
        for (node_index, node) in route.graph.nodes.iter().enumerate() {
            let Node::Tuple { polarity, start, len } = *node else { continue; };
            tuple_arities.push(len);
            let rebuilt = route.retained.terms[node_index].expect("tuple node has a FreshUse term");
            let elements = match session.store.term_view(rebuilt).unwrap() {
                TermView::PositiveTuple { elements } if polarity == Polarity::Positive => elements,
                TermView::NegativeTuple { elements } if polarity == Polarity::Negative => elements,
                other => panic!("tuple polarity/shape changed during FreshUse: {other:?}"),
            };
            let end = start.checked_add(len).unwrap();
            let children = &route.graph.tuple_children[start..end];
            assert_eq!(elements.len(), children.len());
            for (offset, &child) in children.iter().enumerate() {
                assert_eq!(
                    elements[offset], route.retained.terms[child].unwrap(),
                    "FreshUse tuple child {offset} must preserve its captured position",
                );
            }
        }
        tuple_arities.sort_unstable();
        assert_eq!(tuple_arities, [2, 2], "both nested tuple nodes are reconstructed");
    }

    #[test]
    fn r226_callback_formal_use_origin() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("r225-map-owners", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();
        assert!(session.errors.is_empty());
        let graph_state = session.candidate_graph.as_ref().unwrap();
        let actual_loop = graph_state.local_routes.iter().find(|route| route.occurrence.ordinal() == 28).unwrap();
        let repeat = graph_state.local_routes.iter().find(|route| route.occurrence.ordinal() == 27).unwrap();
        let context = &graph_state.intrusion.effect_algebra.context;
        let callback_origin = context.test_relation_lineage(candidate_context::RelationId(146));
        let provider_origin = context.test_relation_lineage(candidate_context::RelationId(357));
        assert!(callback_origin.iter().any(|line| line.contains("ordinal: 19")));
        let callback_call_index = session.batch.candidate_calls.calls.iter().position(|call|
            call.checking.occurrence().ordinal() == 19).unwrap();
        let callback_call = &session.batch.candidate_calls.calls[callback_call_index];
        let callback_name_index = callback_call.formal_name.unwrap();
        let callback_registration = session.batch.candidate_calls.names[callback_name_index].registration;
        assert!(session.batch.candidate_calls.formal_use_by_occurrence.iter().any(|(ordinal, encoded)|
            *ordinal == 19 && encoded.get() as usize == callback_registration + 1));
        let callback_source_origin = context.origins.iter().find(|origin| origin.relation == candidate_context::RelationId(146)).unwrap();
        assert_eq!(callback_source_origin.occurrence.occurrence().ordinal(), 19);
        assert_eq!(session.batch.candidate_calls.formal_use_registration(&session.batch.hir,
            callback_source_origin.occurrence.occurrence()), Some(callback_registration));
        assert!(provider_origin.iter().any(|line| line.contains("ordinal: 26")));
        let provider_call_index = session.batch.candidate_calls.calls.iter().position(|call|
            call.checking.occurrence().ordinal() == 26).unwrap();
        assert!(session.batch.candidate_calls.calls[provider_call_index].formal_name.is_none());
        let provider_source_origin = context.origins.iter().find(|origin| origin.relation == candidate_context::RelationId(357)).unwrap();
        assert_eq!(session.batch.candidate_calls.formal_use_registration(&session.batch.hir,
            provider_source_origin.occurrence.occurrence()), None);
        assert!(actual_loop.retained.scoped_relations.is_empty());
        assert!(repeat.retained.scoped_relations.is_empty());
        let function_endpoint = |relation: u32, upper: bool, positive: bool| {
            let TypedPairKey::Value(pair) = context.relation_pair(candidate_context::RelationId(relation)).unwrap() else { panic!("value pair"); };
            match (if upper { pair.upper } else { pair.lower }, positive) {
                (ValueEndpointKey::PositiveFunction(term), true) | (ValueEndpointKey::NegativeFunction(term), false) => term,
                other => panic!("function endpoint: {other:?}"),
            }
        };
        let provider_callee_type = function_endpoint(234, false, true);
        let provider_argument_type = function_endpoint(356, false, true);
        let provider_expected_argument_type = function_endpoint(362, true, false);
        let callback_demand_type = function_endpoint(146, true, false);
        let repeat_callback_type = repeat.graph.nodes.iter().enumerate().find_map(|(index, node)| {
            let Node::Function { polarity: Polarity::Positive, children } = node else { return None; };
            matches!(repeat.graph.nodes[children[1]], Node::Row { row, .. }
                if repeat.graph.rows[row].key == RowKey::Effect(31))
                .then(|| repeat.retained.terms[index].unwrap())
        }).unwrap();
        let provider_callee_view = session.store.term_view(provider_callee_type).unwrap();
        let callee_argument_port = match provider_callee_view {
            TermView::PositiveFunction { argument, .. } => argument, _ => panic!("provider function"),
        };
        assert_eq!(context.relation_pair(candidate_context::RelationId(362)), Some(TypedPairKey::Value(
            CanonicalValuePairKey { lower: ValueEndpointKey::ValueRow(28), upper: ValueEndpointKey::NegativeFunction(provider_expected_argument_type) }
        )));
        assert_eq!(context.relation_pair(candidate_context::RelationId(363)), Some(TypedPairKey::Value(
            CanonicalValuePairKey { lower: ValueEndpointKey::PositiveFunction(provider_argument_type), upper: ValueEndpointKey::NegativeFunction(provider_expected_argument_type) }
        )));
        assert_eq!(callee_argument_port, provider_expected_argument_type);
        assert_eq!(context.relation_pair(candidate_context::RelationId(368)), Some(TypedPairKey::Effect {
            lower: EffectEndpointKey::EffectRow(69), upper: EffectEndpointKey::EffectRow(54),
        }));
        assert!(context.observed_dependencies().any(|dependency|
            matches!(dependency, candidate_context::Dependency::FunctionPort {
                child: candidate_context::RelationId(368), parent: candidate_context::RelationId(363),
                field: crate::FunctionField::ResultEffect, operation: candidate_context::FunctionPortOperation::Preserve,
            })));
        assert_ne!(provider_expected_argument_type, repeat_callback_type);
        assert_ne!(provider_expected_argument_type, callback_demand_type);
        assert!(!context.observed_dependencies().any(|dependency|
            matches!(dependency, candidate_context::Dependency::FunctionPort { parent: candidate_context::RelationId(146), .. })));
        println!("R226 callback Apply19 retains its exact formal registration; provider Apply26 has none; the typed route/WorkBound bridge remains open");
    }

    #[test]
    fn r227_formal_registration_route_term_ownership() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("r227-formal-route", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();
        assert!(session.errors.is_empty());
        let graph_state = session.candidate_graph.as_ref().unwrap();
        let repeat = graph_state.local_routes.iter().find(|route| route.occurrence.ordinal() == 27).unwrap();
        let callback_call = session.batch.candidate_calls.calls.iter().find(|call|
            call.checking.occurrence().ordinal() == 19).unwrap();
        let formal_registration = callback_call.formal_name.unwrap();
        let registration = session.batch.candidate_calls.names[formal_registration].registration;
        assert_eq!(session.batch.candidate_calls.formal_use_registration(&session.batch.hir,
            callback_call.checking.occurrence()), Some(registration));
        let formal = &session.batch.candidate_calls.formals[registration];
        assert_eq!(session.batch.parameter_recipes[formal.recipe_position], formal.parameter);
        let source_row = session.parameter_live_base + u32::try_from(formal.recipe_position).unwrap();
        let formal_nodes = repeat.graph.nodes.iter().enumerate().filter_map(|(index, node)| {
            let term = repeat.retained.terms[index]?;
            let view = session.store.term_view(term).ok()?;
            matches!(node, Node::Function { .. }).then_some((index, term, view))
        }).collect::<Vec<_>>();
        let endpoint = |relation: u32, upper: bool| {
            let TypedPairKey::Value(pair) = graph_state.intrusion.effect_algebra.context
                .relation_pair(candidate_context::RelationId(relation)).unwrap() else { panic!("value relation") };
            match if upper { pair.upper } else { pair.lower } {
                ValueEndpointKey::PositiveFunction(term) | ValueEndpointKey::NegativeFunction(term) => term,
                other => panic!("function endpoint: {other:?}"),
            }
        };
        let provider_expected = endpoint(362, true);
        let callback_demand = endpoint(146, true);
        assert!(matches!(session.store.term_view(formal.native_root.unwrap()),
            Ok(TermView::LiveVariable(view)) if view.kind() == ComponentKind::Value
                && view.polarity() == Polarity::Positive && view.ordinal() == source_row));
        assert!(!repeat.graph.rows.iter().any(|row| row.key == RowKey::Value(source_row)));
        assert!(repeat.retained.terms.iter().flatten().any(|term| *term == provider_expected));
        assert!(!repeat.retained.terms.iter().flatten().any(|term| *term == callback_demand));
        println!("R227 registration={} recipe={} lambda={} native_root={:?} source_row={} graph_rows={:?} route_rows={:?} provider_expected={provider_expected:?} callback_demand={callback_demand:?} route_function_terms={formal_nodes:?}; root row is absent from route graph, provider expected term is retained, callback demand is absent",
            registration, formal.recipe_position, formal.lambda, formal.native_root, source_row,
            repeat.graph.rows, repeat.rows);
    }

    #[test]
    fn r228_provider_argument_local_route_owner_path() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("r228-provider-route", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();
        assert!(session.errors.is_empty());
        let graph_state = session.candidate_graph.as_ref().unwrap();
        let provider = session.batch.candidate_calls.calls.iter().find(|call|
            call.checking.occurrence().ordinal() == 26).unwrap();
        let route = graph_state.local_routes.iter().find(|route|
            route.occurrence.ordinal() == 28).unwrap();
        let source = session.batch.hir.local_source_for(&provider.owner).unwrap().unwrap();
        let argument = source.expression(&provider.argument).unwrap();
        assert_eq!(argument.occurrence, route.occurrence);
        let yu_hir::shadow::LocalSourceForm::Name {
            resolution: yu_hir::shadow::LocalSourceResolution::Local(local), ..
        } = &argument.form else { panic!("provider argument is the exact resolved local Name") };
        assert_eq!(local, &route.local);
        let argument_position = match provider.argument_value {
            crate::shadow_apply::CandidateEndpoint::Component(position) => position,
            other => panic!("direct local provider argument must use a component endpoint: {other:?}"),
        };
        let native = provider.native.unwrap();
        let argument_ordinal = session.live_components[argument_position].ordinal;
        assert!(matches!(session.store.term_view(native.argument),
            Ok(TermView::LiveVariable(view)) if view.kind() == ComponentKind::Value
                && view.polarity() == Polarity::Positive && view.ordinal() == argument_ordinal));
        let native_argument = native.argument;

        let route_root = route.retained.terms[route.graph.root].unwrap();
        let route_target = session.batch.component_term_at(argument_position);
        let route_slot_zero = ConstraintOccurrenceId::new(route.occurrence.clone(), 0);
        assert!(session.store.facts().iter().any(|fact| {
            fact.lower() == route_root && fact.upper() == route_target
                && session.store.provenance().iter().any(|edge| edge.fact() == fact.id()
                    && edge.cause().occurrence() == &route_slot_zero)
        }), "the route's exact source occurrence owns its graph-root-to-component constraint");
        let route_root_pair = TypedPairKey::Value(CanonicalValuePairKey {
            lower: session.value_endpoint(route_root, Polarity::Positive),
            upper: session.value_endpoint(route_target, Polarity::Negative),
        });
        let route_root_relations = graph_state.intrusion.effect_algebra.context.observed_relations()
            .filter(|(_, pair, _)| **pair == route_root_pair).collect::<Vec<_>>();
        assert!(!route_root_relations.is_empty(),
            "the route's own restoration must constrain its exact root to its source Apply argument row");
        let route_relation_events = route_root_relations.iter().map(|(index, _, _)|
            graph_state.intrusion.effect_algebra.context.test_source_events_for_relation(
                candidate_context::RelationId(*index as u32)).unwrap_or(&[]).to_vec()
        ).collect::<Vec<_>>();

        let route_function_node = route.graph.nodes.iter().enumerate().find_map(|(index, node)| {
            let Node::Function { polarity: Polarity::Positive, children } = node else { return None; };
            matches!(route.graph.nodes[children[2]], Node::Row { row, .. }
                if route.graph.rows[row].key == RowKey::Effect(41)).then_some(index)
        }).unwrap();
        let provider_function = route.retained.terms[route_function_node].unwrap();
        let context = &graph_state.intrusion.effect_algebra.context;
        let provider_origin = context.origins.iter()
            .find(|origin| origin.relation == candidate_context::RelationId(357)).unwrap();
        assert_eq!(provider_origin.occurrence.occurrence().ordinal(), 26);
        assert_eq!(provider_origin.occurrence, provider.checking);
        assert!(context.observed_dependencies().any(|dependency| matches!(dependency,
            candidate_context::Dependency::FunctionPort {
                child: candidate_context::RelationId(362),
                parent: candidate_context::RelationId(358),
                field: FunctionField::Argument,
                operation: candidate_context::FunctionPortOperation::Swap,
            })));
        let route_to_function = context.observed_dependencies().any(|dependency| matches!(dependency,
            candidate_context::Dependency::Replay {
                child: candidate_context::RelationId(356),
                upper: candidate_context::RelationId(355),
                lower_input: candidate_effect::BoundKey(
                    ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(42)), Polarity::Positive,
                    ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(term))),
                upper_input: candidate_effect::BoundKey(
                    ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(42)), Polarity::Negative,
                    ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(28))), ..
            } if *term == provider_function));
        assert!(route_to_function, "the route-owned root-to-component relation participates in the replay that yields the actual function port");
        let apply_argument_to_expected = context.observed_dependencies().any(|dependency| matches!(dependency,
            candidate_context::Dependency::Replay {
                child: candidate_context::RelationId(363),
                lower: candidate_context::RelationId(356),
                upper: candidate_context::RelationId(362),
                lower_input: candidate_effect::BoundKey(
                    ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(28)), Polarity::Positive,
                    ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(term))),
                upper_input: candidate_effect::BoundKey(
                    ExtrusionEndpoint::Value(ValueEndpointKey::ValueRow(28)), Polarity::Negative,
                    ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(_))),
            } if *term == provider_function));
        assert!(apply_argument_to_expected, "the exact Apply argument row replays the retained actual function against its expected callback function");
        let (actual, expected) = {
            let TypedPairKey::Value(pair) = context
                .relation_pair(candidate_context::RelationId(363)).unwrap() else { panic!("provider actual-function replay relation") };
            let actual = match pair.lower {
                ValueEndpointKey::PositiveFunction(term) => term,
                other => panic!("provider actual callback endpoint: {other:?}"),
            };
            let expected = match pair.upper {
                ValueEndpointKey::NegativeFunction(term) => term,
                other => panic!("provider expected callback endpoint: {other:?}"),
            };
            (actual, expected)
        };
        assert_eq!(provider_function, actual,
            "the exact source-owned route function node is the actual endpoint consumed by provider Apply replay relation 363");
        let relevant_dependencies = context.observed_dependencies()
            .filter(|dependency| match dependency {
                candidate_context::Dependency::Derived { child, parent }
                | candidate_context::Dependency::FunctionPort { child, parent, .. }
                | candidate_context::Dependency::TuplePort { child, parent, .. }
                | candidate_context::Dependency::Transport { child, parent, .. } =>
                    [355, 362, 363].into_iter().any(|id| child.0 == id || parent.0 == id),
                candidate_context::Dependency::Replay { child, lower, upper, .. } =>
                    [355, 362, 363].into_iter().any(|id| child.0 == id || lower.0 == id || upper.0 == id),
            }).map(|dependency| format!("{dependency:?}")).collect::<Vec<_>>();
        println!("R228 provider Apply 26 argument expression={} occurrence={} resolves local={:?}; route occurrence={} local={:?} target_component={} native_argument={native_argument:?}; route_root={route_root:?}; root relation pair={route_root_pair:?} relation_indices={:?} source_events={route_relation_events:?}; route function node={route_function_node} provider actual={actual:?} expected={expected:?}",
            provider.argument.ordinal(), argument.occurrence.ordinal(), local,
            route.occurrence.ordinal(), route.local, argument_position,
            route_root_relations.iter().map(|(index, _, _)| *index).collect::<Vec<_>>());
        println!("R228 route/Apply typed dependency edges: {relevant_dependencies:?}");
    }

    #[test]
    fn r224_apply_fresh_route_terms() {
        const SOURCE: &str = r#"act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    my repeat (f:[io] int -> int) (z:[io] int) = {
        my first = f z
        f z
    }
    repeat loop q
}"#;
        let text: Arc<yu_syntax::SourceText> = Arc::from(SOURCE);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("r224-route-terms", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.execute().unwrap();
        assert!(session.errors.is_empty());
        let graph_state = session.candidate_graph.as_ref().unwrap();
        let route = |occurrence| graph_state.local_routes.iter().find(|route| route.occurrence.ordinal() == occurrence).unwrap();
        let actual_loop = route(28);
        let repeat = route(27);
        assert!(actual_loop.authentic_use_instance() && repeat.authentic_use_instance());
        let term_for_row = |route: &LocalFreshRoute, row: RowKey, port: usize| {
            route.graph.nodes.iter().enumerate().find_map(|(index, node)| {
                let Node::Function { polarity: Polarity::Positive, children } = node else { return None; };
                let child = children[port];
                matches!(route.graph.nodes[child], Node::Row { row: row_index, .. }
                    if route.graph.rows[row_index].key == row)
                    .then(|| route.retained.terms.get(index).copied().flatten())
                    .flatten()
            })
        };
        let actual_function = term_for_row(actual_loop, RowKey::Effect(41), 2)
            .expect("actual loop positive function node with slot-4 result-effect port");
        let callback_function = term_for_row(repeat, RowKey::Effect(31), 1)
            .expect("repeat positive callback function node with formal argument-effect port");
        let provider = session.batch.candidate_calls.calls.iter()
            .find(|call| call.checking.occurrence().ordinal() == 26).unwrap().native.unwrap();
        let callback_call = session.batch.candidate_calls.calls.iter()
            .find(|call| call.checking.occurrence().ordinal() == 19).unwrap();
        let callback = session.batch.candidate_calls.calls.iter()
            .find(|call| call.checking.occurrence().ordinal() == 19).unwrap().native.unwrap();
        println!("R224 actual_loop_function={actual_function:?} view={:?} callback_scheme_function={callback_function:?} view={:?}",
            session.store.term_view(actual_function), session.store.term_view(callback_function));
        println!("R224 provider_native_argument={:?} view={:?} provider_native_callee={:?} callback_native_callee={:?} registered_root={:?}",
            provider.argument, session.store.term_view(provider.argument), provider.callee,
            callback.callee, callback_call.formal_name
                .and_then(|name| session.batch.candidate_calls.names.get(name))
                .and_then(|name| session.batch.candidate_calls.formals.get(name.registration))
                .and_then(|registration| registration.native_root));
        println!("R224 identity actual_to_provider={} callback_scheme_to_callback_callee={} actual_to_callback_scheme={}",
            actual_function == provider.argument, callback_function == callback.callee,
            actual_function == callback_function);
        let mut term_edges = std::collections::HashMap::<Term, Vec<(Term, Option<crate::FactId>)>>::new();
        let mut term_pending = Vec::new();
        for fact in session.store.facts() {
            term_edges.entry(fact.lower()).or_default().push((fact.upper(), Some(fact.id())));
            term_edges.entry(fact.upper()).or_default().push((fact.lower(), Some(fact.id())));
            term_pending.extend([fact.lower(), fact.upper()]);
        }
        term_pending.extend([actual_function, callback_function, provider.argument, callback.callee]);
        let mut term_seen = std::collections::HashSet::new();
        while let Some(term) = term_pending.pop() {
            if !term_seen.insert(term) { continue; }
            let children = match session.store.term_view(term).unwrap() {
                crate::TermView::PositiveFunction { argument, argument_effect, result_effect, result }
                | crate::TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                    [argument, argument_effect, result_effect, result],
                _ => continue,
            };
            for child in children {
                term_edges.entry(term).or_default().push((child, None));
                term_edges.entry(child).or_default().push((term, None));
                term_pending.push(child);
            }
        }
        let term_path = |start: Term, target: Term| {
            let mut queue = std::collections::VecDeque::from([start]);
            let mut parent = std::collections::HashMap::<Term, (Term, Option<crate::FactId>)>::new();
            let mut visited = std::collections::HashSet::from([start]);
            while let Some(term) = queue.pop_front() {
                if term == target { break; }
                for &(next, fact) in term_edges.get(&term).into_iter().flatten() {
                    if visited.insert(next) { parent.insert(next, (term, fact)); queue.push_back(next); }
                }
            }
            if !visited.contains(&target) { return None; }
            let mut path = Vec::new(); let mut cursor = target;
            while cursor != start { let edge = parent[&cursor]; path.push((cursor, edge.1)); cursor = edge.0; }
            path.reverse(); Some(path)
        };
        let actual_to_argument = term_path(actual_function, provider.argument);
        let callback_to_formal = term_path(callback_function, callback.callee);
        let argument_to_formal = term_path(provider.argument, callback.callee);
        let actual_to_callback = term_path(actual_function, callback_function);
        assert!(actual_to_argument.is_none());
        assert!(argument_to_formal.is_none());
        let shared_term_view = callback_to_formal.as_ref().and_then(|path| path.first())
            .map(|(term, _)| session.store.term_view(*term));
        println!("R224 source_to_native_paths actual_function_to_argument={actual_to_argument:?} callback_scheme_to_formal_root={callback_to_formal:?} provider_argument_to_formal_root={argument_to_formal:?} actual_function_to_callback_scheme={actual_to_callback:?} shared_term1={:?}",
            shared_term_view);
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum ApplyCaptureMiss {
        WrongSourceOccurrence,
        SourceEventMissing,
        ForgedParent,
        WrongTriggerComparison,
        PairOutsideSourceGroup,
        PairNotInHelperCapture,
        WrongSiblingRoute,
        ReconstructionMapMismatch,
    }

    #[derive(Clone, Copy, Debug)]
    struct ApplyCaptureEvidence {
        group: usize,
        route_index: usize,
        inspection_event_cursor: usize,
        graph_row: usize,
        signed_copy: RowKey,
        signed_parent: RowKey,
        polarity: Polarity,
        capture: CapturedRowObservation,
        reconstruction: ReconstructedRowObservation,
        parent_graph_row: usize,
        parent_capture: CapturedRowObservation,
        parent_reconstruction: ReconstructedRowObservation,
    }

    fn replay_forest_to(
        graph: &Graph,
        state: &GraphState,
        cursor: usize,
    ) -> Option<candidate_intrusion::ForestSnapshot> {
        let capture = &graph.capture_forest;
        let events = state.intrusion.forest_events();
        if !state.intrusion.forest_event_log_complete()
            || capture.event_cursor > cursor || cursor > events.len()
        { return None; }
        let mut replay = capture.clone();
        for event in &events[capture.event_cursor..cursor] {
            match *event {
                candidate_intrusion::ForestEvent::Birth(RowKey::Value(row)) => {
                    if row as usize != replay.values.len() { return None; }
                    replay.values.push(row);
                }
                candidate_intrusion::ForestEvent::Birth(RowKey::Effect(row)) => {
                    if row as usize != replay.effects.len() { return None; }
                    replay.effects.push(row);
                }
                candidate_intrusion::ForestEvent::ParentWrite { key: RowKey::Value(row), before, after, .. } => {
                    let length = replay.values.len();
                    let parent = replay.values.get_mut(row as usize)?;
                    if *parent != before || after as usize >= length { return None; }
                    *parent = after;
                }
                candidate_intrusion::ForestEvent::ParentWrite { key: RowKey::Effect(row), before, after, .. } => {
                    let length = replay.effects.len();
                    let parent = replay.effects.get_mut(row as usize)?;
                    if *parent != before || after as usize >= length { return None; }
                    *parent = after;
                }
                candidate_intrusion::ForestEvent::Truncate { values_len, effects_len } => {
                    if values_len > replay.values.len() || effects_len > replay.effects.len() { return None; }
                    replay.values.truncate(values_len);
                    replay.effects.truncate(effects_len);
                }
            }
        }
        replay.event_cursor = cursor;
        Some(replay)
    }

    fn snapshot_rep(snapshot: &candidate_intrusion::ForestSnapshot, key: RowKey) -> RowKey {
        let (forest, row) = match key {
            RowKey::Value(row) => (&snapshot.values, row),
            RowKey::Effect(row) => (&snapshot.effects, row),
        };
        let mut current = row;
        while let Some(&parent) = forest.get(current as usize) {
            if parent == current { break; }
            current = parent;
        }
        match key { RowKey::Value(_) => RowKey::Value(current), RowKey::Effect(_) => RowKey::Effect(current) }
    }

    fn owner_source_at_reconstruction(
        state: &GraphState,
        graph: &Graph,
        reconstruction: ReconstructedRowObservation,
        requested: RowKey,
    ) -> bool {
        replay_forest_to(graph, state, reconstruction.forest_event_cursor)
            .is_some_and(|snapshot| snapshot_rep(&snapshot, requested) == reconstruction.source_representative)
    }

    // Replay all owner transitions from capture through inspection. A live
    // representative is accepted only if it agrees with that complete replay.
    fn captured_source_matches(
        state: &GraphState,
        graph: &Graph,
        capture: CapturedRowObservation,
        reconstruction: ReconstructedRowObservation,
    ) -> bool {
        if capture.graph_row != reconstruction.graph_row
            || capture.representative != reconstruction.captured
            || capture.requested.kind() != capture.representative.kind()
            || capture.representative.kind() != reconstruction.source_representative.kind()
            || capture.forest_event_cursor != graph.capture_forest.event_cursor
        { return false; }
        let Some(at_capture) = replay_forest_to(graph, state, capture.forest_event_cursor) else { return false; };
        if snapshot_rep(&at_capture, capture.requested) != capture.representative { return false; }
        let Some(at_reconstruction) = replay_forest_to(graph, state, reconstruction.forest_event_cursor) else { return false; };
        if snapshot_rep(&at_reconstruction, reconstruction.captured) != reconstruction.source_representative
            || snapshot_rep(&at_reconstruction, capture.requested) != reconstruction.source_representative
        { return false; }
        let inspection_cursor = state.intrusion.forest_event_cursor();
        let Some(at_inspection) = replay_forest_to(graph, state, inspection_cursor) else { return false; };
        let Ok(live) = state.intrusion.forest_snapshot() else { return false; };
        at_inspection.values == live.values
            && at_inspection.effects == live.effects
            && snapshot_rep(&at_inspection, reconstruction.captured) == state.intrusion.rep(reconstruction.captured)
            && snapshot_rep(&at_inspection, capture.requested) == state.intrusion.rep(capture.requested)
    }

    // Test-only relation over retained records. Every edge is checked in its
    // owning representation; endpoint locality never implies a fresh image.
    fn join_apply_pair_capture(
        state: &GraphState,
        context: &candidate_context::State,
        source_graph: &candidate_value_graph::Graph,
        apply: &candidate_call::ApplySourceInput,
        expected_apply: &HirOccurrenceId,
        event: usize,
        group: (usize, usize, usize, usize, bool),
        expected_comparison: TypedPairKey,
        parent_index: usize,
        parent: candidate_intrusion::Parent,
        route: &LocalFreshRoute,
        expected_local: &yu_hir::HirLocalId,
        expected_use: &HirOccurrenceId,
        expected_parent: RowKey,
        expected_polarity: Polarity,
        supplied_rows: &[RowKey],
        supplied_maps: &[ReconstructedRowObservation],
    ) -> Result<ApplyCaptureEvidence, ApplyCaptureMiss> {
        if apply.checking.occurrence() != expected_apply {
            return Err(ApplyCaptureMiss::WrongSourceOccurrence);
        }
        if source_graph.observed_checking(event) != Some(&apply.checking) {
            return Err(ApplyCaptureMiss::SourceEventMissing);
        }
        let retained_parent = *state.intrusion.parents.get(parent_index)
            .ok_or(ApplyCaptureMiss::PairOutsideSourceGroup)?;
        if parent.copy != retained_parent.copy
            || parent.parent != retained_parent.parent
            || parent.polarity != retained_parent.polarity
            || parent.target != retained_parent.target
            || parent.sources != retained_parent.sources
            || parent.comparison != retained_parent.comparison
            || parent.occurrence != retained_parent.occurrence
        { return Err(ApplyCaptureMiss::ForgedParent); }
        // All following checks use the owner-indexed record, never an
        // independently supplied edge.
        let parent = retained_parent;
        let (group_id, group_occurrence, start, end, active) = group;
        if !active { return Err(ApplyCaptureMiss::PairOutsideSourceGroup); }
        if state.intrusion.observed_groups().nth(group_id) != Some(group) {
            return Err(ApplyCaptureMiss::PairOutsideSourceGroup);
        }
        if group_occurrence != parent.occurrence || !(start..end).contains(&parent_index)
        { return Err(ApplyCaptureMiss::PairOutsideSourceGroup); }
        // The active typed comparison is the trigger. Its structural endpoints
        // stay intact here; the extrusion link below is a separate relation.
        if parent.comparison != Some(expected_comparison) {
            return Err(ApplyCaptureMiss::WrongTriggerComparison);
        }
        let Some(source_set) = parent.sources else { return Err(ApplyCaptureMiss::SourceEventMissing); };
        if !context.source_events(source_set).contains(&event) {
            return Err(ApplyCaptureMiss::SourceEventMissing);
        }
        if parent.parent != expected_parent || parent.polarity != expected_polarity
            || parent.copy.kind() != parent.parent.kind()
        {
            return Err(ApplyCaptureMiss::PairOutsideSourceGroup);
        }
        if route.local != *expected_local || route.occurrence != *expected_use {
            return Err(ApplyCaptureMiss::WrongSiblingRoute);
        }
        let route_index = state.local_routes.iter().position(|retained| std::ptr::eq(retained, route))
            .ok_or(ApplyCaptureMiss::WrongSiblingRoute)?;
        if supplied_rows.len() != route.rows.len()
            || supplied_maps.len() != route.retained.row_observations.len()
            || !std::ptr::eq(supplied_rows, route.rows.as_slice())
            || !std::ptr::eq(supplied_maps, route.retained.row_observations.as_slice())
            || route.rows.len() != route.graph.rows.len()
            || route.graph.capture_rows.len() != route.graph.rows.len()
            || route.retained.row_observations.len() != route.graph.rows.len()
        { return Err(ApplyCaptureMiss::ReconstructionMapMismatch); }
        for (index, (row, observation)) in supplied_rows.iter().zip(supplied_maps).enumerate() {
            let actual = route.retained.row_observations[index];
            let capture = route.graph.capture_rows[index];
            if *row != route.rows[index]
                || capture.graph_row != index
                || capture.representative != route.graph.rows[index].key
                || capture.requested.kind() != capture.representative.kind()
                || observation.graph_row != actual.graph_row
                || observation.captured != actual.captured
                || observation.source_representative != actual.source_representative
                || observation.image != actual.image
                || observation.allocated_fresh_image != actual.allocated_fresh_image
                || observation.forest_event_cursor != actual.forest_event_cursor
                || observation.canonical_rows_hit
                || observation.image != route.rows[index]
                || capture.forest_event_cursor != route.graph.capture_forest.event_cursor
                || !captured_source_matches(state, &route.graph, capture, *observation)
            { return Err(ApplyCaptureMiss::ReconstructionMapMismatch); }
        }
        // The signed copy is canonicalized by the owning intrusion map before
        // the helper graph captures it. Keep the original request, canonical
        // representative, and later route image as distinct evidence.
        // Select by the signed key's representative at this graph's capture
        // time. A final equivalence class cannot select a historical row.
        let capture_copy = snapshot_rep(&route.graph.capture_forest, parent.copy);
        let capture_parent = snapshot_rep(&route.graph.capture_forest, parent.parent);
        let graph_row = route.graph.capture_rows.iter().position(|capture|
            capture.representative == capture_copy)
            .ok_or(ApplyCaptureMiss::PairNotInHelperCapture)?;
        let parent_graph_row = route.graph.capture_rows.iter().position(|capture|
            capture.representative == capture_parent)
            .ok_or(ApplyCaptureMiss::PairNotInHelperCapture)?;
        let capture = *route.graph.capture_rows.get(graph_row)
            .ok_or(ApplyCaptureMiss::ReconstructionMapMismatch)?;
        let reconstruction = *supplied_maps.get(graph_row)
            .ok_or(ApplyCaptureMiss::ReconstructionMapMismatch)?;
        let parent_capture = *route.graph.capture_rows.get(parent_graph_row)
            .ok_or(ApplyCaptureMiss::ReconstructionMapMismatch)?;
        let parent_reconstruction = *supplied_maps.get(parent_graph_row)
            .ok_or(ApplyCaptureMiss::ReconstructionMapMismatch)?;
        if capture.graph_row != graph_row
            || capture.representative != route.graph.rows[graph_row].key
            || parent_capture.graph_row != parent_graph_row
            || parent_capture.representative != route.graph.rows[parent_graph_row].key
            || !captured_source_matches(state, &route.graph, capture, reconstruction)
            || !owner_source_at_reconstruction(state, &route.graph, reconstruction, parent.copy)
            || supplied_rows.get(graph_row) != Some(&reconstruction.image)
            || reconstruction.image != route.rows[graph_row]
            || !captured_source_matches(state, &route.graph, parent_capture, parent_reconstruction)
            || !owner_source_at_reconstruction(state, &route.graph, parent_reconstruction, parent.parent)
            || supplied_rows.get(parent_graph_row) != Some(&parent_reconstruction.image)
            || parent_reconstruction.image != route.rows[parent_graph_row]
        { return Err(ApplyCaptureMiss::ReconstructionMapMismatch); }
        for (row, observation) in [
            (graph_row, reconstruction),
            (parent_graph_row, parent_reconstruction),
        ] {
            if observation.canonical_rows_hit {
                if observation.existing_image != Some(observation.image)
                    || observation.first_entry_graph_row >= row
                    || observation.allocated_fresh_image
                    || supplied_maps.get(observation.first_entry_graph_row)
                        .map_or(true, |first| first.image != observation.existing_image.unwrap())
                    || (observation.image != observation.source_representative
                        && !supplied_maps[observation.first_entry_graph_row].allocated_fresh_image)
                { return Err(ApplyCaptureMiss::ReconstructionMapMismatch); }
            } else if observation.existing_image.is_some()
                || observation.first_entry_graph_row != row
                || (observation.allocated_fresh_image
                    && (observation.image == observation.source_representative
                        || !observation.stored_local
                        || observation.non_generic
                        || observation.level <= observation.boundary))
                || (!observation.allocated_fresh_image
                    && observation.image != observation.source_representative)
            { return Err(ApplyCaptureMiss::ReconstructionMapMismatch); }
        }
        Ok(ApplyCaptureEvidence {
            group: group_id,
            route_index,
            inspection_event_cursor: state.intrusion.forest_event_cursor(),
            graph_row,
            signed_copy: parent.copy,
            signed_parent: parent.parent,
            polarity: parent.polarity,
            capture,
            reconstruction,
            parent_graph_row,
            parent_capture,
            parent_reconstruction,
        })
    }

    #[test]
    fn four_typed_function_ports_reject_every_pairwise_swap() {
        let expected = [11u8, 22, 33, 44];
        assert_eq!(four_ports_match(expected, expected), [true; 4]);
        for left in 0..4 {
            for right in left + 1..4 {
                let mut substituted = expected;
                substituted.swap(left, right);
                let matches = four_ports_match(expected, substituted);
                assert!(!matches.into_iter().all(|value| value),
                    "port substitution {left}<->{right} fails all-port authentication");
                assert_eq!(matches.iter().filter(|value| !**value).count(), 2,
                    "only the two swapped positions differ for {left}<->{right}");
                assert!(matches.iter().enumerate().all(|(index, value)|
                    *value == (index != left && index != right)),
                    "untouched positions match for {left}<->{right}");
            }
        }
    }

    #[test]
    fn module_fresh_route_retains_full_remap_crosswalk_and_capacity_accounting() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "my identity x = x\nmy first = identity 0\nmy second = identity true",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("module-retained-map", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();

        let state = session.candidate_graph.as_mut().unwrap();
        let route = state.routes.iter().find(|route| !route.rows.is_empty()).unwrap();
        assert_eq!(route.rows.len(), route.graph.rows.len());
        assert_eq!(route.retained.terms.len(), route.graph.nodes.len());
        assert_eq!(route.retained.evidence_remap.len(), route.graph.bound_evidence.len());
        // All FreshUse fields move together, including currently empty maps;
        // the retained record's backing capacities are included once in the
        // route total, while the route's inline headers are in FreshRoute.
        let route_maps = route.retained.bytes().unwrap();
        assert_eq!(
            route_maps,
            sum(&[
                route.retained.scope_remap.bytes().unwrap(),
                bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(route.retained.scoped_relations.capacity()).unwrap(),
                bytes::<Option<Term>>(route.retained.terms.capacity()).unwrap(),
                bytes::<(usize, EffectEndpointKey)>(route.retained.effect_operands.capacity()).unwrap(),
                bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(route.retained.bundle_remap.capacity()).unwrap(),
                bytes::<(candidate_context::ContextId, candidate_context::ContextId)>(route.retained.context_remap.capacity()).unwrap(),
                bytes::<candidate_context::EvidenceSnapshotId>(route.retained.evidence_remap.capacity()).unwrap(),
            ]).unwrap(),
        );
        let accounted = state.retained_bytes;
        state.refresh_bytes().unwrap();
        assert_eq!(state.retained_bytes, accounted);
        assert!(state.scratch_bytes == 0, "completed module routes leave no crosswalk in transition scratch");
    }

    #[test]
    fn structural_bound_scoped_payload_authentic_capture_uses_shared_reconstruction() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "my outer z = { my local h x = h z; local }\nmy first = outer 0\nmy second = outer 1",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("latent-demand", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();
        let owner = session.batch.hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "outer" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let source = session.batch.hir.local_source(&owner).unwrap().unwrap();
        let initializer = source.bindings().iter().find(|binding| binding.spelling.as_ref() == "local").unwrap().id.clone();
        let original_call = session.batch.candidate_calls.calls.iter().enumerate().find_map(|(index, call)| {
            if call.owner.definition_root() != Some(&owner) { return None; }
            let name = session.batch.candidate_calls.names.get(call.formal_name?)?;
            let registration = &session.batch.candidate_calls.formals[name.registration];
            let lambda = &source.expressions()[registration.lambda];
            let yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. } = &lambda.form else { return None; };
            (parameter.spelling.as_ref() == "h").then_some(index)
        }).unwrap();
        let local = session.candidate_graph.as_ref().unwrap().locals.iter().flatten().find(|local| local.id == initializer).unwrap();
        let (root, boundary, capture_region) = (local.root, local.boundary, local.capture_region);
        let graph = session.capture_candidate_graph_owned(root, boundary, capture_region.as_slice(), &[], &[]).unwrap();
        let context = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        // Strict latent-only reachability is not established for this source.
        // This control selects an authentic local-formal demand and its real scheme.
        let demands: Vec<_> = graph.bounds.iter().filter_map(|bound| {
            let relation = bound.relation?;
            let demand = context.scoped_flow(relation).unwrap().demand?;
            if demand.original_call != original_call { return None; }
            assert!(matches!(bound.source_bound, candidate_effect::BoundKey(_, Polarity::Negative,
                ExtrusionEndpoint::Value(ValueEndpointKey::NegativeFunction(root))) if root == demand.root));
            assert_eq!(bound.upper, graph.negative_functions[&demand.root]);
            Some((relation, demand))
        }).collect();
        assert!(!demands.is_empty());
        assert_eq!(graph.nodes.iter().filter(|node| matches!(node,
            Node::Function { polarity: Polarity::Negative, .. })).count(), graph.negative_functions.len(),
            "structural and latent discovery share the same interned Function nodes");
        for row in &graph.rows {
            let ordinal = row.key.ordinal() as usize;
            let (level, non_generic) = match row.key {
                RowKey::Value(_) => (session.value_levels[ordinal], session.value_metadata[ordinal].non_generic),
                RowKey::Effect(_) => (session.effect_levels[ordinal], session.effect_metadata[ordinal].non_generic),
            };
            assert_eq!(row.local, level > graph.boundary && !non_generic);
        }
        assert!(graph.rows.iter().any(|row| !row.local), "the local h demand retains borrowed outer z rows");
        let caller = capture_region.unwrap();
        let first = session.prepare_candidate_fresh_use(&graph, 1, Some(caller)).unwrap();
        let second = session.prepare_candidate_fresh_use(&graph, 1, Some(caller)).unwrap();
        assert_ne!(first.context_use, second.context_use);
        for fresh in [&first, &second] {
            for (index, row) in graph.rows.iter().enumerate() {
                if !row.local { assert_eq!(fresh.rows[index], row.key, "borrowed coordinates stay shared with later constraints"); }
            }
            for (relation, demand) in &demands {
                let index = graph.negative_functions[&demand.root];
                let Node::Function { polarity: Polarity::Negative, children } = graph.nodes[index] else { panic!("negative demand root"); };
                let term = fresh.terms[index].unwrap();
                let TermView::NegativeFunction { argument, argument_effect, result_effect, result } = session.store.term_view(term).unwrap() else { panic!("reconstructed demand"); };
                assert_eq!([argument, argument_effect, result_effect, result], children.map(|child| fresh.terms[child].unwrap()),
                    "all four ports use the common reconstruction map");
                let copied = fresh.scoped_relations[relation].demand.unwrap();
                assert_eq!(copied.original_call, demand.original_call);
                assert_eq!(copied.root, term);
                assert_eq!(copied.output_scope, fresh.scope_remap.scopes.get(&demand.output_scope).copied().unwrap_or(demand.output_scope));
                assert_eq!(copied.input, fresh.scope_remap.inputs.get(&demand.input).copied().unwrap_or(demand.input));
                assert_eq!(copied.use_instance, fresh.context_use);
                let first_copy = first.scoped_relations[relation].demand.unwrap();
                let second_copy = second.scoped_relations[relation].demand.unwrap();
                assert_ne!(first_copy.output_scope, second_copy.output_scope);
                assert_ne!(first_copy.input, second_copy.input);
            }
        }
    }

    #[test]
    fn active_outer_root_two_helper_uses() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "nested-helper-native-r37", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode_scoped(hir.clone(), true, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();

        let owner = session.batch.hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "outer" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let source = session.batch.hir.local_source(&owner).unwrap().unwrap();
        let local_id = |name: &str| source.bindings().iter()
            .find(|binding| binding.spelling.as_ref() == name).unwrap().id.clone();
        let loop_local = local_id("loop");
        let helper_local = local_id("helper");
        let helper_names: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
            yu_hir::shadow::LocalSourceForm::Name {
                resolution: yu_hir::shadow::LocalSourceResolution::Local(id), ..
            } if id == &helper_local)).collect();
        assert_eq!(helper_names.len(), 3, "three literal helper Name uses are present in the source");
        let loop_applies: Vec<_> = session.batch.candidate_calls.calls.iter().filter(|call| {
            call.owner.definition_root() == Some(&owner)
                && source.expressions().get(call.expression).is_some_and(|expression|
                    matches!(&expression.form, yu_hir::shadow::LocalSourceForm::Apply { callee, .. }
                        if source.expressions().get(callee.ordinal() as usize).is_some_and(|callee|
                            matches!(&callee.form, yu_hir::shadow::LocalSourceForm::Name {
                                resolution: yu_hir::shadow::LocalSourceResolution::Local(id), ..
                            } if id == &loop_local))))
        }).collect();
        assert_eq!(loop_applies.len(), 2, "direct loop x and helper loop y remain distinct Apply occurrences");
        let apply = loop_applies.iter().copied().find(|call|
            matches!(&source.expressions()[call.expression].form,
                yu_hir::shadow::LocalSourceForm::Apply { argument, .. }
                    if source.expressions().get(argument.ordinal() as usize).is_some_and(|argument|
                        matches!(&argument.form, yu_hir::shadow::LocalSourceForm::Name { spelling, .. }
                            if spelling.as_ref() == "y"))))
            .expect("the nested helper owns the exact loop y Apply");
        let apply_occurrence = source.expressions()[apply.expression].occurrence.clone();
        let direct_occurrence = source.expressions()[loop_applies.iter().copied().find(|call| call.expression != apply.expression).unwrap().expression].occurrence.clone();
        let recipe = &session.batch.candidate_recipes[apply.recipe];
        assert_eq!(recipe.occurrence, apply_occurrence);
        assert!(matches!(&recipe.relation, shadow_apply::CandidateRelation::Apply { .. }));
        let schedule = &session.batch.candidate_source.schedules[&owner];
        assert!(schedule.iter().any(|action| matches!(action,
            candidate_source::Action::Candidate(index) if *index == apply.recipe)));
        let event = *session.batch.candidate_source.references.checking.get(&apply.checking).unwrap();
        assert_eq!(session.batch.candidate_source.references.observed_checking(event), Some(&apply.checking));

        let state = session.candidate_graph.as_ref().unwrap();
        let context = &state.intrusion.effect_algebra.context;
        let routes: Vec<_> = helper_names.iter().take(2).map(|name| state.local_routes.iter().find(|route|
            route.local == helper_local && route.occurrence == name.occurrence)
            .expect("each selected literal use owns an actual FreshUse route")).collect();
        assert_ne!(routes[0].occurrence, routes[1].occurrence);
        let scheme = state.locals[routes[0].slot].as_ref().unwrap();
        assert_eq!(scheme.id, helper_local);
        for route in &routes {
            assert!(route.authentic_use_instance(), "route identity is retained by the actual FreshUse map");
            assert_eq!(route.slot, routes[0].slot);
            assert_eq!(route.graph.live_root, scheme.root);
            assert_eq!(route.graph.boundary, scheme.boundary);
        }

        let argument_row = match apply.argument_value {
            LambdaValueEndpoint::Component(position) => RowKey::Value(session.live_components[position].ordinal),
            LambdaValueEndpoint::Parameter(position) => RowKey::Value(session.parameter_live_base + position as u32),
        };
        let result_row = RowKey::Value(session.live_components[apply.result].ordinal);
        let mut joined = None;
        for group in state.intrusion.observed_groups().filter(|(_, _, _, _, active)| *active) {
            let (_, _, start, end, _) = group;
            let Some(trigger_comparison) = state.intrusion.parents.get(start)
                .and_then(|parent| parent.comparison) else { continue; };
            if state.intrusion.parents[start..end].iter()
                .any(|parent| parent.comparison != Some(trigger_comparison))
            { continue; }
            let mut value_parent = None;
            let mut result_parent = None;
            for parent_index in start..end {
                let parent = state.intrusion.parents[parent_index];
                if !parent.sources.is_some_and(|sources| context.source_events(sources).contains(&event)) { continue; }
                let selected_coordinate = if parent.parent == argument_row && parent.polarity == Polarity::Positive {
                    Some((argument_row, Polarity::Positive))
                } else if parent.parent == result_row && parent.polarity == Polarity::Negative {
                    Some((result_row, Polarity::Negative))
                } else { None };
                let Some((expected_parent, expected_polarity)) = selected_coordinate else { continue; };
                let route = routes[0];
                let Ok(evidence) = join_apply_pair_capture(
                    state, context, &session.batch.candidate_source.references,
                    apply, &apply_occurrence, event, group, trigger_comparison,
                    parent_index, parent, route, &helper_local, &route.occurrence,
                    expected_parent, expected_polarity, &route.rows,
                    &route.retained.row_observations,
                ) else { continue; };
                let selection = (parent_index, parent, evidence);
                if expected_parent == argument_row { value_parent = Some(selection); }
                else { result_parent = Some(selection); }
            }
            if let (Some(value_parent), Some(result_parent)) = (value_parent, result_parent) {
                joined = Some((group, value_parent, result_parent));
                break;
            }
        }
        let (group, value_parent, result_parent) = joined
            .expect("source event, both signed C/D parents, installed helper and two retained FreshUse maps join");
        let (value_index, value_parent, value_evidence) = value_parent;
        let (result_index, result_parent, result_evidence) = result_parent;
        let trigger_comparison = value_parent.comparison.unwrap();
        assert_eq!(result_parent.comparison, Some(trigger_comparison),
            "triggering comparison endpoints remain identical across the C and D extrusion records");
        assert_eq!(value_parent.parent, argument_row);
        assert_eq!(value_parent.polarity, Polarity::Positive);
        assert_eq!(result_parent.parent, result_row);
        assert_eq!(result_parent.polarity, Polarity::Negative);
        assert_eq!(value_evidence.group, group.0);
        assert_eq!(result_evidence.group, group.0);
        assert!((group.2..group.3).contains(&value_index));
        assert!((group.2..group.3).contains(&result_index));
        let sibling = routes[1];
        for (parent_index, parent, primary, expected_parent, polarity) in [
            (value_index, value_parent, value_evidence, argument_row, Polarity::Positive),
            (result_index, result_parent, result_evidence, result_row, Polarity::Negative),
        ] {
            assert_eq!(primary.signed_copy, parent.copy);
            assert_eq!(primary.signed_parent, expected_parent);
            assert_eq!(primary.polarity, polarity);
            assert!(captured_source_matches(state, &routes[0].graph, primary.capture, primary.reconstruction),
                "complete owner transitions connect capture and reconstruction to inspection");
            assert!(owner_source_at_reconstruction(state, &routes[0].graph,
                primary.reconstruction, primary.signed_copy),
                "the signed copy is resolved at the recorded reconstruction cursor");
            for route in &routes {
                let expected_route_index = state.local_routes.iter()
                    .position(|retained| std::ptr::eq(retained, *route)).unwrap();
                let evidence = join_apply_pair_capture(state, context,
                    &session.batch.candidate_source.references,
                    apply, &apply_occurrence, event, group, trigger_comparison,
                    parent_index, parent, route, &helper_local, &route.occurrence,
                    expected_parent, polarity, &route.rows,
                    &route.retained.row_observations).unwrap();
                assert_eq!(evidence.group, group.0);
                assert_eq!(evidence.route_index, expected_route_index,
                    "the inspected graph belongs to this exact retained Local route");
                assert_eq!(evidence.inspection_event_cursor, state.intrusion.forest_event_cursor(),
                    "the full forest log is replayed to one inspection boundary");
                assert_eq!(evidence.signed_copy, parent.copy);
                assert_eq!(evidence.signed_parent, parent.parent);
                assert_eq!(evidence.polarity, polarity);
                assert_eq!(evidence.graph_row, primary.graph_row);
                assert_eq!(evidence.capture.requested, primary.capture.requested,
                    "both routes retain the original requested key");
                assert_eq!(evidence.capture.representative, primary.capture.representative,
                    "both routes retain the same capture-time representative");
                assert!(captured_source_matches(state, &route.graph, evidence.capture, evidence.reconstruction),
                    "route-owned Capture and reconstruction records authenticate current source");
                assert_eq!(evidence.reconstruction.graph_row, evidence.graph_row);
                assert_eq!(evidence.reconstruction.image, route.rows[evidence.graph_row],
                    "each route retains its own image; shared images are not required to be unequal");
                assert_eq!(evidence.parent_graph_row, primary.parent_graph_row);
                assert!(captured_source_matches(state, &route.graph, evidence.parent_capture, evidence.parent_reconstruction),
                    "parent Capture and reconstruction records authenticate current source");
                assert!(owner_source_at_reconstruction(state, &route.graph,
                    evidence.parent_reconstruction, parent.parent),
                    "the signed parent is resolved at the recorded reconstruction cursor");
                for (graph_row, reconstruction) in [
                    (evidence.graph_row, evidence.reconstruction),
                    (evidence.parent_graph_row, evidence.parent_reconstruction),
                ] {
                    assert_eq!(reconstruction.image, route.rows[graph_row]);
                    assert!(!reconstruction.canonical_rows_hit,
                        "R47 proves this actual helper constructor has no canonical map hits");
                    if reconstruction.allocated_fresh_image {
                        assert_ne!(reconstruction.image, reconstruction.source_representative);
                    } else {
                        assert_eq!(reconstruction.image, reconstruction.source_representative,
                            "non-hit, nonallocated rows reuse their source representative");
                    }
                }
            }
        }

        let (group_id, group_occurrence, group_start, group_end, _) = group;
        let (missing_index, missing_parent) = (group_start..group_end).find_map(|index| {
            let parent = state.intrusion.parents[index];
            (parent.comparison == Some(trigger_comparison)
                && parent.sources.is_some_and(|sources|
                    !context.source_events(sources).contains(&event)))
                .then_some((index, parent))
        }).expect("same active comparison group retains a source-qualified parent without this Apply event");
        let missing_event_group = (group_id, group_occurrence, group_start, group_end, true);
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, missing_event_group, trigger_comparison,
            missing_index, missing_parent, routes[0], &helper_local, &routes[0].occurrence,
            missing_parent.parent, missing_parent.polarity, &routes[0].rows,
            &routes[0].retained.row_observations), Err(ApplyCaptureMiss::SourceEventMissing)),
            "indexed parent and structural-trigger premises hold; only event membership is absent");
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &direct_occurrence, event, group, trigger_comparison,
            value_index, value_parent, routes[0], &helper_local, &routes[0].occurrence,
            argument_row, Polarity::Positive, &routes[0].rows,
            &routes[0].retained.row_observations), Err(ApplyCaptureMiss::WrongSourceOccurrence)));
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, group, trigger_comparison,
            value_index, value_parent, routes[0], &helper_local, &routes[0].occurrence,
            result_row, Polarity::Negative, &routes[0].rows,
            &routes[0].retained.row_observations), Err(ApplyCaptureMiss::PairOutsideSourceGroup)),
            "the signed value pair cannot be substituted for the result pair");
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, group, trigger_comparison,
            result_index, result_parent, routes[0], &helper_local, &routes[0].occurrence,
            argument_row, Polarity::Positive, &routes[0].rows,
            &routes[0].retained.row_observations), Err(ApplyCaptureMiss::PairOutsideSourceGroup)),
            "the result C/D parent cannot be substituted for the argument C/D parent");
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, group, trigger_comparison,
            value_index, value_parent, sibling, &helper_local, &routes[0].occurrence,
            argument_row, Polarity::Positive,
            &sibling.rows, &sibling.retained.row_observations), Err(ApplyCaptureMiss::WrongSiblingRoute)));
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, group, trigger_comparison,
            value_index, value_parent, routes[0], &helper_local, &routes[0].occurrence,
            argument_row, Polarity::Positive, &sibling.rows,
            &sibling.retained.row_observations), Err(ApplyCaptureMiss::ReconstructionMapMismatch)));
        let wrong_trigger_comparison = state.intrusion.parents.iter()
            .filter_map(|parent| parent.comparison)
            .find(|comparison| *comparison != trigger_comparison)
            .expect("the source run retains a distinct structural comparison for the wrong-trigger control");
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, group, wrong_trigger_comparison,
            value_index, value_parent, routes[0], &helper_local, &routes[0].occurrence,
            argument_row, Polarity::Positive, &routes[0].rows,
            &routes[0].retained.row_observations), Err(ApplyCaptureMiss::WrongTriggerComparison)),
            "absence of the structural triggering comparison cannot stand in for the actual one");
        let mut forged_copy = value_parent;
        forged_copy.copy = forged_copy.parent;
        assert_eq!(forged_copy.copy.kind(), value_parent.copy.kind(),
            "the forged endpoint preserves component kind");
        assert!(routes[0].graph.capture_rows.iter().any(|capture|
            state.intrusion.rep(capture.representative) == state.intrusion.rep(forged_copy.copy)),
            "the forged endpoint remains canonically represented in the helper capture");
        assert!(matches!(join_apply_pair_capture(state, context, &session.batch.candidate_source.references,
            apply, &apply_occurrence, event, group, trigger_comparison,
            value_index, forged_copy, routes[0], &helper_local, &routes[0].occurrence,
            argument_row, Polarity::Positive, &routes[0].rows,
            &routes[0].retained.row_observations), Err(ApplyCaptureMiss::ForgedParent)),
            "kind and canonical membership do not authenticate a caller-supplied Parent");
    }

    #[test]
    fn retained_demand_transport_authenticates_distinct_uses_and_rejects_wrong_use_or_root() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "my invoke f = f 1\nmy id x = x\nmy first = invoke id\nmy second = invoke id\nmy outer z = { my local h = h z; my first_local = local id; my second_local = local id; second_local }\nmy local_first = outer 0\nmy local_second = outer 1",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("demand-route-auth", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();
        let state = session.candidate_graph.as_mut().unwrap();
        let context = &state.intrusion.effect_algebra.context;
        let mut traced_module_uses = Vec::new();
        for (route_index, route) in state.routes.iter().enumerate()
            .filter(|(_, route)| matches!(route.retained.context_use, 1 | 2))
        {
            assert_eq!(route_index, route.retained.context_use - 1,
                "Module route 0/use 1 and route 1/use 2 stay distinct");
            traced_module_uses.push((route_index, route.retained.context_use));
            assert_eq!(route.graph.capture_rows.len(), route.graph.rows.len());
            assert_eq!(route.retained.row_observations.len(), route.rows.len());
            eprintln!("ReplayRouteRows owner=Module route={route_index} use={} occurrence={:?} live_root={} boundary={} rows=", route.retained.context_use, route.use_id.occurrence(), route.graph.live_root, route.graph.boundary);
            for (index, ((capture, reconstruction), image)) in route.graph.capture_rows.iter()
                .zip(&route.retained.row_observations).zip(&route.rows).enumerate()
            {
                assert_eq!(capture.graph_row, reconstruction.graph_row);
                assert_eq!(reconstruction.graph_row, index);
                assert_eq!(*image, reconstruction.image);
                eprintln!("capture={capture:?} reconstruction={reconstruction:?} route_row_image={image:?}");
            }
        }
        traced_module_uses.sort_unstable();
        assert_eq!(traced_module_uses, [(0, 1), (1, 2)]);
        let mut authenticated = Vec::new();
        let mut emission_cases = Vec::new();
        for replay_row in context.replay_demand_rows() {
            let call_index = replay_row.call;
            let copied = replay_row.demand;
            let Some(native) = session.batch.candidate_calls.calls.get(call_index).and_then(|call| call.native) else { continue; };
            let ports = |root| match session.store.term_view(root).ok()? {
                TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                    Some([argument, argument_effect, result_effect, result]),
                _ => None,
            };
            let mut diagnostic = Vec::new();
            let evidence = state.authenticate_demand_transport_observed(
                context, replay_row, native.demand, ports, None,
                |owner, index, stage| diagnostic.push((owner, index, stage)),
            );
            eprintln!("ReplayDemandRow={replay_row:?}; matching-routes/first-rejection={diagnostic:?}");
            let lower_root = match replay_row.lower_input.2 {
                ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(root)) => Some(root),
                _ => None,
            };
            let lower_relations: Vec<_> = context.bound_relations(replay_row.lower_input).map(|relation| (
                relation, context.relation_pair(relation), context.scoped_flow(relation).ok(),
                context.test_relation_lineage(relation),
            )).collect();
            let positive_functions = lower_root.map_or_else(Vec::new, |root| state.test_positive_function_census(root));
            eprintln!("ReplayProvenanceCensus call={call_index} lower_root={lower_root:?} lower_relations={lower_relations:?} positive_functions={positive_functions:?} source_constructor_root={:?} source_ports={:?} fresh_use={} copied_root={:?} copied_ports={:?} authentication_found={}",
                native.demand, ports(native.demand), copied.use_instance, copied.root, ports(copied.root), evidence.is_some());
            let evidence = evidence
                .expect("actual retained FreshUse map authenticates the copied demand");
            eprintln!("ReplayAuthenticated row={replay_row:?} evidence={evidence:?} lower_lineage={:?} upper_lineage={:?} child_lineage={:?}",
                context.test_relation_lineage(replay_row.lower), context.test_relation_lineage(replay_row.upper),
                context.test_relation_lineage(replay_row.child));
            let port_fields = [FunctionField::Argument, FunctionField::ArgumentEffect,
                FunctionField::ResultEffect, FunctionField::Result];
            for (index, relation) in evidence.port_relations.iter().copied().enumerate() {
                eprintln!("ReplayFunctionPort index={index} field={:?} relation={relation:?} pair={:?} transformer={} flow={:?} lineage={:?}",
                    port_fields[index], context.relation_pair(relation), evidence.port_transformers[index],
                    context.scoped_flow(relation), context.test_relation_lineage(relation));
            }
            for (label, root) in [("native", native.demand), ("copied", copied.root),
                ("replay-upper", evidence.replay_upper_root), ("replay-child", evidence.replay_child_root),
                ("consumer", evidence.consumer_root)]
            {
                let observed = session.store.term_view(root).ok().and_then(|view| match view {
                    TermView::PositiveFunction { argument, argument_effect, result_effect, result }
                    | TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                        Some([argument, argument_effect, result_effect, result]),
                    _ => None,
                });
                eprintln!("ReplayFunctionRoot label={label} root={root:?} ordered_ports={observed:?}");
            }
            assert_eq!(evidence.fresh_relation, replay_row.upper,
                "the constructor-owned p1/h join is exact RelationId equality");
            assert_ne!(replay_row.child, replay_row.upper,
                "the Replay child q remains separately identified from h");
            assert_eq!(evidence.ports_match, [true; 4]);
            assert!(evidence.scope_map_matches && evidence.input_map_matches);
            assert_ne!(native.demand, copied.root, "raw native root equality remains false");
            let emission = evidence.physical_emission;
            let saved_record = context.test_emission_record(emission).expect("constructor emission retained");
            assert_eq!(saved_record, (evidence.physical_fiber, evidence.physical_readback));
            assert_eq!(evidence.physical_readback.slot, evidence.physical_fiber);
            assert_eq!(evidence.physical_readback.bound, evidence.fresh_to);
            let copied_ports = ports(copied.root).expect("copied route has a negative-function port view");
            emission_cases.push((replay_row, native.demand, copied_ports, evidence));

            // Mutate the actual route-owned capture, not the selected Replay
            // tuple. Its imported antecedent must stop authenticating.
            if evidence.route_owner == FreshRouteOwner::Local {
                let (snapshot_index, original) = {
                    let route = &state.local_routes[evidence.route];
                    let bound = route.graph.bounds.iter().find(|bound| bound.relation == Some(evidence.relation)).unwrap();
                    (bound.evidence.0, route.graph.bound_evidence[bound.evidence.0])
                };
                {
                    let mut changed = original;
                    changed.source_bound.1 = if changed.source_bound.1 == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
                    state.local_routes[evidence.route].graph.bound_evidence[snapshot_index] = changed;
                }
                assert!(state.authenticate_demand_transport(context, replay_row, native.demand, ports, None).is_none(),
                    "altering the actual captured snapshot rejects the route");
                state.local_routes[evidence.route].graph.bound_evidence[snapshot_index] = original;

                let original_flow = *state.local_routes[evidence.route].retained.scoped_relations.get(&evidence.relation).unwrap();
                state.local_routes[evidence.route].retained.scoped_relations.get_mut(&evidence.relation).unwrap().transformer =
                    original_flow.transformer.checked_add(1).unwrap();
                assert!(state.authenticate_demand_transport(context, replay_row, native.demand, ports, None).is_none(),
                    "altering the actual retained scoped flow rejects the route");
                *state.local_routes[evidence.route].retained.scoped_relations.get_mut(&evidence.relation).unwrap() = original_flow;
            } else {
                let (snapshot_index, original) = {
                    let route = &state.routes[evidence.route];
                    let bound = route.graph.bounds.iter().find(|bound| bound.relation == Some(evidence.relation)).unwrap();
                    (bound.evidence.0, route.graph.bound_evidence[bound.evidence.0])
                };
                let mut changed = original;
                changed.source_bound.1 = if changed.source_bound.1 == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
                state.routes[evidence.route].graph.bound_evidence[snapshot_index] = changed;
                assert!(state.authenticate_demand_transport(context, replay_row, native.demand, ports, None).is_none(),
                    "altering the actual module-route capture rejects the route");
                state.routes[evidence.route].graph.bound_evidence[snapshot_index] = original;

                let original_flow = *state.routes[evidence.route].retained.scoped_relations.get(&evidence.relation).unwrap();
                state.routes[evidence.route].retained.scoped_relations.get_mut(&evidence.relation).unwrap().transformer =
                    original_flow.transformer.checked_add(1).unwrap();
                assert!(state.authenticate_demand_transport(context, replay_row, native.demand, ports, None).is_none(),
                    "altering the actual module-route scoped flow rejects the route");
                *state.routes[evidence.route].retained.scoped_relations.get_mut(&evidence.relation).unwrap() = original_flow;
            }

            let mut wrong_use = copied;
            wrong_use.use_instance = wrong_use.use_instance.checked_add(1).unwrap();
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { demand: wrong_use, ..replay_row }, native.demand, ports, None).is_none(),
                "a sibling use cannot authenticate this route");
            let mut wrong_root = copied;
            wrong_root.root = native.demand;
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { demand: wrong_root, ..replay_row }, native.demand, ports, None).is_none(),
                "the original root is not the copied FreshUse root");
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { upper: replay_row.lower, ..replay_row }, native.demand, ports, None).is_none(),
                "substituting the selected Replay upper relation fails closed");
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { child: replay_row.lower, ..replay_row }, native.demand, ports, None).is_none(),
                "substituting the selected Replay child relation fails closed");
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { lower_input: replay_row.upper_input, ..replay_row }, native.demand, ports, None).is_none(),
                "substituting a Replay BoundKey fails closed");
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { call: call_index.wrapping_add(1), ..replay_row }, native.demand, ports, None).is_none(),
                "a different source snapshot/call cannot select this retained route");
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { lower: replay_row.child, ..replay_row }, native.demand, ports, None).is_none(),
                "a relation without the captured lower edge fails closed");
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow { upper: replay_row.child, ..replay_row }, native.demand, ports, None).is_none(),
                "an unsupported Replay ancestry edge fails closed");
            let sibling = context.replay_demand_rows().find(|candidate|
                candidate.call == call_index && candidate.demand.use_instance != copied.use_instance)
                .expect("fixture contains the same source demand at a sibling FreshUse");
            assert_ne!(replay_row.child, sibling.child);
            assert!(state.authenticate_demand_transport(context, candidate_context::ReplayDemandRow {
                lower: sibling.lower, upper: sibling.upper,
                lower_input: sibling.lower_input, upper_input: sibling.upper_input,
                ..replay_row
            }, native.demand, ports, None).is_none(),
                "matching source/use metadata cannot authenticate a sibling Replay relation pair");
            authenticated.push((copied.use_instance, evidence.route));
        }
        assert!(authenticated.len() >= 2, "both same-source FreshUse siblings reach retained Replay");
        assert_ne!(authenticated[0].0, authenticated[1].0);
        assert_ne!(authenticated[0].1, authenticated[1].1);
        assert!(emission_cases.iter().any(|(_, _, _, evidence)| evidence.route_owner == FreshRouteOwner::Module),
            "the fixture retains a positive module FreshUse route");
        assert!(emission_cases.iter().any(|(_, _, _, evidence)| evidence.route_owner == FreshRouteOwner::Local),
            "the fixture retains a positive local FreshUse route");
        eprintln!("ReplayDrainReturns={:?}", state.intrusion.effect_algebra.context.test_replay_drain_observations());
        let emission_ids: Vec<_> = emission_cases.iter().map(|(_, _, _, evidence)| evidence.physical_emission).collect();
        for (row, native_root, copied_ports, evidence) in emission_cases {
            let emission = evidence.physical_emission;
            let (slot, readback) = state.intrusion.effect_algebra.context.test_emission_record(emission).unwrap();
            let mut out_of_range = slot;
            out_of_range.index = usize::MAX;
            state.intrusion.effect_algebra.context.test_replace_emission_slot(emission, out_of_range);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "an out-of-range/replaced slot address fails closed");
            state.intrusion.effect_algebra.context.test_replace_emission_slot(emission, slot);

            let mut different_contents = readback;
            different_contents.bound.1 = if different_contents.bound.1 == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
            state.intrusion.effect_algebra.context.test_replace_emission_readback(emission, different_contents);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "different full physical-slot contents fail closed");
            state.intrusion.effect_algebra.context.test_replace_emission_readback(emission, readback);

            let old_admission = state.intrusion.effect_algebra.context.test_orphan_emission(emission);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "a missing/replaced emission-to-admission link fails closed");
            state.intrusion.effect_algebra.context.test_restore_emission_admission(emission, old_admission);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_some(), "restoring the actual constructor record restores authentication");

            let upper_member = state.intrusion.effect_algebra.context.test_remove_bound_member(
                evidence.fresh_to, evidence.fresh_relation).expect("p1 belongs to the actual upper fiber");
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(),
                "removing p1 from the actual upper/destination fiber fails closed");
            state.intrusion.effect_algebra.context.test_restore_bound_member(evidence.fresh_to, upper_member);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_some(),
                "restoring p1's actual upper-fiber membership restores authentication");

            let lower_member = state.intrusion.effect_algebra.context.test_remove_bound_member(
                row.lower_input, row.lower).expect("Replay lower belongs to the actual lower fiber");
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(),
                "removing the actual Replay lower membership fails closed");
            state.intrusion.effect_algebra.context.test_restore_bound_member(row.lower_input, lower_member);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_some(),
                "restoring Replay lower-fiber membership restores authentication");

            let mut wrong_owner = slot;
            wrong_owner.owner = match slot.owner {
                candidate_scheme::RowKey::Value(row) => candidate_scheme::RowKey::Effect(row),
                candidate_scheme::RowKey::Effect(row) => candidate_scheme::RowKey::Value(row),
            };
            state.intrusion.effect_algebra.context.test_replace_emission_slot(emission, wrong_owner);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "an actual physical-slot owner mutation fails closed");
            state.intrusion.effect_algebra.context.test_replace_emission_slot(emission, slot);
            let mut wrong_lane = slot;
            wrong_lane.lane = match slot.lane {
                candidate_context::BoundLane::ValueLowerRow => candidate_context::BoundLane::ValueUpperRow,
                candidate_context::BoundLane::ValueUpperRow => candidate_context::BoundLane::ValueLowerRow,
                candidate_context::BoundLane::ValueLowerAtom => candidate_context::BoundLane::ValueUpperAtom,
                candidate_context::BoundLane::ValueUpperAtom => candidate_context::BoundLane::ValueLowerAtom,
                candidate_context::BoundLane::EffectLowerRow => candidate_context::BoundLane::EffectUpperRow,
                candidate_context::BoundLane::EffectUpperRow => candidate_context::BoundLane::EffectLowerRow,
                candidate_context::BoundLane::EffectLowerAtom => candidate_context::BoundLane::EffectUpperAtom,
                candidate_context::BoundLane::EffectUpperAtom => candidate_context::BoundLane::EffectLowerAtom,
            };
            state.intrusion.effect_algebra.context.test_replace_emission_slot(emission, wrong_lane);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "an actual physical-slot lane mutation fails closed");
            state.intrusion.effect_algebra.context.test_replace_emission_slot(emission, slot);

            if let Some(donor) = emission_ids.iter().copied().find(|candidate| *candidate != emission) {
                let donor_contents = state.intrusion.effect_algebra.context.test_emission_contents(donor).unwrap();
                let original_contents = state.intrusion.effect_algebra.context.test_emission_contents(emission).unwrap();
                state.intrusion.effect_algebra.context.test_replace_emission_contents(emission, donor_contents);
                assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                    native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "a replaced actual emission record fails closed");
                state.intrusion.effect_algebra.context.test_replace_emission_contents(emission, original_contents);
            }

            let fresh = candidate_context::Dependency::Transport {
                child: evidence.fresh_relation, parent: evidence.relation, use_origin: row.demand.use_instance,
                witness: Some(candidate_context::TransportWitness {
                    from: evidence.fresh_from, to: evidence.fresh_to,
                    reason: candidate_context::TransportReason::FreshUse,
                }),
            };
            let mut wrong_endpoint = fresh;
            if let candidate_context::Dependency::Transport { witness: Some(witness), .. } = &mut wrong_endpoint {
                witness.to.1 = if witness.to.1 == Polarity::Positive { Polarity::Negative } else { Polarity::Positive };
            }
            state.intrusion.effect_algebra.context.test_replace_dependency(fresh, wrong_endpoint);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "an actual FreshUse endpoint mutation fails closed");
            state.intrusion.effect_algebra.context.test_replace_dependency(wrong_endpoint, fresh);

            let replay = candidate_context::Dependency::Replay {
                child: row.child, lower: row.lower, upper: row.upper,
                lower_input: row.lower_input, upper_input: row.upper_input,
            };
            let substituted = candidate_context::Dependency::Derived { child: row.child, parent: row.upper };
            state.intrusion.effect_algebra.context.test_replace_dependency(replay, substituted);
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "a changed actual Replay dependency kind fails closed");
            state.intrusion.effect_algebra.context.test_replace_dependency(substituted, replay);

            let port_index = evidence.port_transformers.iter().position(|transformer| *transformer != 0)
                .expect("the scoped consumer retains an effect transformer");
            let port = evidence.port_relations[port_index];
            let original_flow = state.intrusion.effect_algebra.context.scoped_flow(port).unwrap();
            let changed_flow = candidate_context::ScopedFlow { transformer: usize::MAX, demand: original_flow.demand };
            let saved_flow = state.intrusion.effect_algebra.context.test_replace_scoped_flow(port, changed_flow).expect("effect port retains a nonidentity flow record");
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "an actual retained port-transformer mutation fails closed");
            state.intrusion.effect_algebra.context.test_replace_scoped_flow(port, saved_flow).unwrap();
            let changed_child_flow = candidate_context::ScopedFlow { transformer: original_flow.transformer, demand: Some(row.demand) };
            let saved_child_flow = state.intrusion.effect_algebra.context.test_replace_scoped_flow(port, changed_child_flow).unwrap();
            assert!(state.authenticate_demand_transport(&state.intrusion.effect_algebra.context, row,
                native_root, |_| Some(copied_ports), Some(copied_ports)).is_none(), "an actual port child-demand mutation fails closed");
            state.intrusion.effect_algebra.context.test_replace_scoped_flow(port, saved_child_flow).unwrap();
        }
    }

    #[test]
    fn replay_constructor_lineage_observes_rejected_cross_route_authentication() {
        let fixture = "my invoke f = f 1\nmy id x = x\nmy first = invoke id\nmy second = invoke id\nmy outer z = { my local h = h z; my first_local = local id; my second_local = local id; second_local }\nmy local_first = outer 0\nmy local_second = outer 1";
        let text: Arc<yu_syntax::SourceText> = Arc::from(fixture);
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("demand-route-auth", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap(),
        ).unwrap();
        session.execute().unwrap();

        let state = session.candidate_graph.as_mut().unwrap();
        let context = &state.intrusion.effect_algebra.context;
        let module_routes: Vec<_> = state.routes.iter().enumerate()
            .filter(|(_, route)| matches!(route.retained.context_use, 1 | 2)).collect();
        eprintln!("ReplayFixture={{exact_source:{}, module_route_count:{}}}", fixture == "my invoke f = f 1\nmy id x = x\nmy first = invoke id\nmy second = invoke id\nmy outer z = { my local h = h z; my first_local = local id; my second_local = local id; second_local }\nmy local_first = outer 0\nmy local_second = outer 1", module_routes.len());
        for (route_index, route) in &module_routes {
            eprintln!("ReplayRoute owner=Module route={route_index} use={} occurrence={:?} live_root={} boundary={} capture_rows={} reconstruction_rows={} complete_rows=", route.retained.context_use, route.use_id.occurrence(), route.graph.live_root, route.graph.boundary, route.graph.capture_rows.len(), route.retained.row_observations.len());
            let row_count = route.graph.capture_rows.len().max(route.retained.row_observations.len()).max(route.rows.len());
            for index in 0..row_count {
                let capture = route.graph.capture_rows.get(index);
                let reconstruction = route.retained.row_observations.get(index);
                let image = route.rows.get(index);
                eprintln!("ReplayRow index={index} capture={capture:?} reconstruction={reconstruction:?} complete_image={image:?}");
            }
        }

        let replay_rows: Vec<_> = context.replay_demand_rows().collect();
        eprintln!("ReplayRows={replay_rows:?}");
        let target_rows: Vec<_> = replay_rows.iter().copied().filter(|row| row.call == 0).collect();
        for (row_index, row) in replay_rows.iter().copied().enumerate() {
            let native_call = session.batch.candidate_calls.calls.get(row.call)
                .map(|call| (row.call, call.native));
            let source_uses: Vec<_> = module_routes.iter().filter_map(|(route_index, route)| {
                let matching_nodes: Vec<_> = route.graph.nodes.iter().enumerate().filter_map(|(node_index, node)| {
                    (route.retained.terms.get(node_index).copied().flatten() == Some(row.demand.root))
                        .then_some((node_index, *node))
                }).collect();
                (!matching_nodes.is_empty()).then_some((
                    *route_index, route.retained.context_use, route.use_id.occurrence(),
                    route.graph.live_root, route.graph.boundary, matching_nodes,
                    &route.graph.capture_rows, &route.retained.row_observations, &route.rows,
                ))
            }).collect();
            let lower_lineage = context.test_relation_lineage(row.lower);
            let child_lineage = context.test_relation_lineage(row.child);
            let upper_lineage = context.test_relation_lineage(row.upper);
            let producer_admissions = context.test_admission_emissions_for_relation(row.lower);
            let lower_input_relations: Vec<_> = context.bound_relations(row.lower_input).map(|relation| (
                relation, context.relation_pair(relation), context.scoped_flow(relation).ok(),
                context.test_relation_lineage(relation),
            )).collect();
            let function_port_edges: Vec<_> = context.observed_dependencies().filter_map(|dependency| {
                let candidate_context::Dependency::FunctionPort { child, parent, field, operation } = *dependency else {
                    return None;
                };
                (parent == row.child).then(|| (
                    child, parent, field, operation, context.relation_pair(child),
                    context.test_relation_lineage(child),
                ))
            }).collect();
            eprintln!(
                "ReplayRowDiagnostic index={row_index} row={row:?} native_call={native_call:?} source_use_identities={source_uses:?} child_lineage={child_lineage:?} lower_lineage={lower_lineage:?} upper_lineage={upper_lineage:?} lower_input_relations={lower_input_relations:?} lower_producer_admissions_emissions_readback={producer_admissions:?} function_port_edges_for_child={function_port_edges:?}"
            );
        }
        let target_row = if target_rows.len() == 1 { Some(target_rows[0]) } else { None };
        let native = session.batch.candidate_calls.calls.get(0).and_then(|call| call.native);
        eprintln!("ReplayNativeCall={{call:0, native:{native:?}}}");
        let lower_root = target_row.and_then(|row| match row.lower_input.2 {
            ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(root)) => Some(root),
            _ => None,
        });
        let lower_lineage = target_row.map(|row| context.test_relation_lineage(row.lower));
        let lower_provenance = target_row.map(|row| context.test_admission_emissions_for_relation(row.lower));
        if let Some(row) = target_row {
            let lower_relations: Vec<_> = context.bound_relations(row.lower_input).map(|relation| (
                relation, context.relation_pair(relation), context.scoped_flow(relation).ok(),
                context.test_relation_lineage(relation),
            )).collect();
            eprintln!("ReplayLowerProducer occurrence_ancestry={lower_lineage:?} relation_pair={:?} admission_emission_readback={lower_provenance:?}",
                context.relation_pair(row.lower));
            eprintln!("ReplayLowerInputRelations={lower_relations:?}");
            eprintln!("ReplayUpperLineage={:?}; ReplayChildLineage={:?}",
                context.test_relation_lineage(row.upper), context.test_relation_lineage(row.child));
        }
        let ports = |root| match session.store.term_view(root).ok()? {
            TermView::PositiveFunction { argument, argument_effect, result_effect, result }
            | TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                Some([argument, argument_effect, result_effect, result]),
            _ => None,
        };
        eprintln!("ReplayFunctionRoots source_native={:?} copied_demand={:?} lower_producer={:?} source_ports={:?} copied_ports={:?} lower_ports={:?}",
            native.map(|call| call.demand), target_row.map(|row| row.demand.root), lower_root,
            native.and_then(|call| ports(call.demand)), target_row.and_then(|row| ports(row.demand.root)),
            lower_root.and_then(ports));

        let mut ordered_function_port_edges = Vec::new();
        let mut ordered_function_port_pairs = Vec::new();
        if let (Some(lower_root), Some(route)) = (lower_root, module_routes.iter().find(|(_, route)| route.retained.context_use == 2).map(|(_, route)| *route)) {
            let positive = route.graph.nodes.iter().enumerate().find_map(|(index, node)| match *node {
                Node::Function { polarity: Polarity::Positive, children }
                    if route.retained.terms.get(index).copied().flatten() == Some(lower_root) => Some(children),
                _ => None,
            });
            let negative_root = target_row.map(|row| row.demand.root);
            let negative = negative_root.and_then(|root| route.graph.nodes.iter().enumerate().find_map(|(index, node)| match *node {
                Node::Function { polarity: Polarity::Negative, children }
                    if route.retained.terms.get(index).copied().flatten() == Some(root) => Some(children),
                _ => None,
            }));
            if let (Some(positive), Some(negative)) = (positive, negative) {
                let fields = [FunctionField::Argument, FunctionField::ArgumentEffect,
                    FunctionField::ResultEffect, FunctionField::Result];
                for index in 0..4 {
                    let expected = typed_port_pair(&route.graph, &route.rows, &route.retained,
                        positive, negative, index);
                    let matching: Vec<_> = context.observed_dependencies().filter_map(|dependency| {
                        let candidate_context::Dependency::FunctionPort { child, parent, field, operation } = *dependency else { return None; };
                        let target_child = target_row?.child;
                        (parent == target_child && field == fields[index])
                            .then(|| (child, parent, field, operation, context.relation_pair(child), context.test_relation_lineage(child)))
                    }).collect();
                    eprintln!("ReplayFunctionPort index={index} field={:?} expected_pair={expected:?} relation_ids_endpoints_source_ancestry={matching:?}", fields[index]);
                    ordered_function_port_edges.push(matching);
                    ordered_function_port_pairs.push(expected);
                }
            } else {
                eprintln!("ReplayFunctionPortsUnavailable positive_root_match={} negative_root_match={}", positive.is_some(), negative.is_some());
            }
        }

        let drain_observations = context.test_replay_drain_observations();
        #[derive(Debug)]
        enum DrainStatus {
            Matched { operation: candidate_context::ReplayOperationId, ack: candidate_context::ReplayChildAck,
                child_return: candidate_context::ReplayDrainObservation, drive_return: candidate_context::ReplayDrainObservation },
            NotRetainedReachabilityUnknown,
        }
        let matching_child_returns: Vec<_> = target_row.into_iter().flat_map(|row| drain_observations.iter().copied().filter(move |observation| {
            matches!(observation, candidate_context::ReplayDrainObservation::ChildReturn { child: Some(child), .. } if *child == row.child)
        })).collect();
        let drain_status = if matching_child_returns.len() == 1 {
            let child_return = matching_child_returns[0];
            if let candidate_context::ReplayDrainObservation::ChildReturn { operation, ack, child: Some(child), stage, .. } = child_return {
                let drives: Vec<_> = drain_observations.iter().copied().filter(|observation| matches!(observation,
                    candidate_context::ReplayDrainObservation::DriveReturn { operation: drive_operation, .. }
                        if *drive_operation == operation)).collect();
                let drive_completed = drives.len() == 1 && matches!(drives[0],
                    candidate_context::ReplayDrainObservation::DriveReturn {
                        outcome: candidate_context::ReplayDriveOutcome::Complete,
                        operation_state: Some((true, candidate_context::ReplayChildWait::Idle, queued, consumed)), ..
                    } if queued == consumed);
                if child == target_row.unwrap().child && ack.operation == operation
                    && stage == candidate_context::TypedDrainStage::ReturnReady && drive_completed {
                    DrainStatus::Matched { operation, ack, child_return, drive_return: drives[0] }
                } else { DrainStatus::NotRetainedReachabilityUnknown }
            } else { DrainStatus::NotRetainedReachabilityUnknown }
        } else { DrainStatus::NotRetainedReachabilityUnknown };
        eprintln!("ReplayDrainObservations={drain_observations:?}; ReplayDrainStatus={drain_status:?}");

        let selected_provenance = lower_provenance.as_ref().and_then(|records| {
            (records.len() == 1).then(|| &records[0])
        });
        eprintln!("ReplayRelationKeyedProducerAdmissions={lower_provenance:?}; unique_chain={selected_provenance:?}");

        let authentication = match (target_row, native) {
            (Some(row), Some(native)) => state.authenticate_demand_transport_observed(
                context, row, native.demand, ports, None,
                |owner, index, stage| eprintln!("ReplayAuthenticationClassification owner={owner:?} route={index} stage={stage:?}"),
            ),
            _ => None,
        };
        eprintln!("ReplayAuthenticationAttempted={}; result={authentication:?}; expected=None",
            target_row.is_some() && native.is_some());

        assert_eq!(fixture, "my invoke f = f 1\nmy id x = x\nmy first = invoke id\nmy second = invoke id\nmy outer z = { my local h = h z; my first_local = local id; my second_local = local id; second_local }\nmy local_first = outer 0\nmy local_second = outer 1",
            "the test remains bound to the pinned rejected source specimen");
        assert_eq!(module_routes.len(), 2, "both keyed Module routes are present");
        assert_eq!(module_routes.iter().map(|(route_index, route)| (*route_index, route.retained.context_use)).collect::<Vec<_>>(), [(0, 1), (1, 2)],
            "Module route 0/use 1 and route 1/use 2 are distinct keyed identities");
        for (_, route) in &module_routes {
            assert!(!route.graph.capture_rows.is_empty(), "route has nonempty row observations");
            assert_eq!(route.graph.capture_rows.len(), route.retained.row_observations.len(), "capture/reconstruction rows are complete");
            assert_eq!(route.retained.row_observations.len(), route.rows.len(), "reconstruction/full-image rows are complete");
            for index in 0..route.graph.capture_rows.len() {
                assert_eq!(route.graph.capture_rows[index].graph_row, index, "capture row is keyed at its exact index");
                assert_eq!(route.retained.row_observations[index].graph_row, index, "reconstruction row is keyed at its exact index");
                assert_eq!(route.retained.row_observations[index].image, route.rows[index], "full image matches the keyed reconstruction row");
            }
        }
        assert_eq!(target_rows.len(), 1, "exactly one target Replay row selects call 0");
        assert!(native.is_some(), "the pinned native call and provenance/readback path are present");
        assert!(target_row.is_some(), "the pinned source call has an observed Replay row");
        assert!(lower_root.is_some(), "the Replay lower endpoint is an observed positive Function root");
        assert!(target_row.is_some_and(|row| row.lower_matches), "selected lower Relation58 producer matches its input key");
        assert!(lower_lineage.as_ref().is_some_and(|lineage| lineage.iter().any(|entry| entry.contains("source-origin"))),
            "lower producer has retained occurrence ancestry");
        assert_eq!(lower_provenance.as_ref().map(Vec::len), Some(1),
            "selected lower producer relation has exactly one admission before BoundKey validation");
        assert!(selected_provenance.is_some(),
            "the unique relation-keyed admission is available for BoundKey validation");
        let (admission_id, admission, emissions) = selected_provenance.unwrap();
        assert_eq!(admission.relation, target_row.map(|row| row.lower));
        assert_eq!(admission.bound, target_row.unwrap().lower_input,
            "admission retains the complete selected producer BoundKey");
        assert_eq!(emissions.len(), 1, "selected producer admission has one exact emission");
        let (_, emission) = emissions[0];
        assert_eq!(emission.admission, *admission_id);
        assert_eq!(emission.bound, admission.bound, "emission retains its admission's complete BoundKey");
        assert_eq!(emission.physical, emission.readback.slot, "physical slot equals exact readback slot");
        assert_eq!(emission.readback.bound, target_row.unwrap().lower_input,
            "readback identifies the same complete selected producer BoundKey");
        assert_eq!(emission.readback.phase, candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend);
        assert_eq!(ordered_function_port_edges.len(), 4, "all four ordered FunctionPort classifications were emitted");
        let expected_fields = [FunctionField::Argument, FunctionField::ArgumentEffect,
            FunctionField::ResultEffect, FunctionField::Result];
        let expected_operations = [candidate_context::FunctionPortOperation::Swap,
            candidate_context::FunctionPortOperation::Swap, candidate_context::FunctionPortOperation::Preserve,
            candidate_context::FunctionPortOperation::Preserve];
        let mut child_relations = Vec::new();
        for index in 0..4 {
            assert_eq!(ordered_function_port_edges[index].len(), 1, "each exact field has one selected-child FunctionPort edge");
            let (child, parent, field, operation, pair, _) = &ordered_function_port_edges[index][0];
            assert_eq!(Some(*parent), target_row.map(|row| row.child), "FunctionPort parent is the selected Replay child");
            assert_eq!(*field, expected_fields[index]);
            assert_eq!(*operation, expected_operations[index]);
            assert!(ordered_function_port_pairs[index].is_some(), "selected child field has a derived exact typed endpoint pair");
            assert_eq!(*pair, ordered_function_port_pairs[index], "selected edge retains its exact endpoint pair");
            child_relations.push(*child);
        }
        child_relations.sort_by_key(|relation| relation.0);
        child_relations.dedup();
        assert_eq!(child_relations.len(), 4, "four fields have four distinct child relation IDs");
        assert!(matches!(authentication, None), "the pinned specimen's authentication result is None");
    }
}
