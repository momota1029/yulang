//! Experimental value projection only; no source Apply typing or admission.
use crate::*;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use yu_hir::HirErrorKind;
pub use crate::candidate_call::{CandidateComputationSourcePlan, CandidateDirectionalIntroduction, CandidateSourceCall, OriginalGenCall0Input, PendingCallConstruction, PendingCallSupplier};
mod local_source_observation;
pub use local_source_observation::{CandidateLocalProviderRoute, CandidateLocalSourceProviderObservation};

/// Every entry remains unresolved, including after successful structural solving.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    CandidatePureEffectModelUnresolved,
    CandidateOwnRowGeneralizationModelUnresolved,
    ApplicationTypingRule,
    CompleteInvocationImage,
    WholeArgumentProviderCompatibility,
    SourceTypingAndAdmission,
    RoleEntryAndProtection,
    WholeTupleScopeTransport,
    GeneralizationAndFreshUseCorrespondence,
    OriginalGenCall0MembershipSourceReferenceOnly,
    CompleteFunctionInterpretation,
    QIndependentCallViewFormation,
    EventOutputCorrespondence,
    ImmediateCallEffectPositionFormation,
    TypedOccurrenceIntroduction,
    FormalApplicability,
    DirectionalProtection,
    ModuleNameSourceTypingAndAdmission,
    ModuleUseReceivingExportCorrespondence,
}
pub const UNRESOLVED: &[UnresolvedPremise] = &[
    UnresolvedPremise::CandidatePureEffectModelUnresolved,
    UnresolvedPremise::CandidateOwnRowGeneralizationModelUnresolved,
    UnresolvedPremise::ApplicationTypingRule,
    UnresolvedPremise::CompleteInvocationImage,
    UnresolvedPremise::WholeArgumentProviderCompatibility,
    UnresolvedPremise::SourceTypingAndAdmission,
    UnresolvedPremise::RoleEntryAndProtection,
    UnresolvedPremise::WholeTupleScopeTransport,
    UnresolvedPremise::GeneralizationAndFreshUseCorrespondence,
    UnresolvedPremise::OriginalGenCall0MembershipSourceReferenceOnly,
    UnresolvedPremise::CompleteFunctionInterpretation,
    UnresolvedPremise::QIndependentCallViewFormation,
    UnresolvedPremise::EventOutputCorrespondence,
    UnresolvedPremise::ImmediateCallEffectPositionFormation,
    UnresolvedPremise::TypedOccurrenceIntroduction,
    UnresolvedPremise::FormalApplicability,
    UnresolvedPremise::DirectionalProtection,
    UnresolvedPremise::ModuleNameSourceTypingAndAdmission,
    UnresolvedPremise::ModuleUseReceivingExportCorrespondence,
];
/// Same actual returned provider/world/whole carrier/source incidence/original
/// shared scope/xi are all unresolved under WholeArgumentProviderCompatibility.
pub struct CandidateCall {
    pub occurrence: HirOccurrenceId,
    pub callee: HirOccurrenceId,
    pub argument: HirOccurrenceId,
    pub unresolved: &'static [UnresolvedPremise],
}
#[derive(Debug)]
pub enum CandidateError {
    Unsupported,
    Collection(CollectionAvailabilityError),
    Solve(SolveAvailabilityError),
}
/// Owns a private solver result which cannot be published as a SolvedModule.
/// Invocation/evaluation effects are intentionally absent from this API.
pub struct CandidateValueObservation {
    solved: SolvedModule,
    calls: Vec<CandidateCall>,
    definition_uses: Vec<CandidateDefinitionUse>,
    apply_recipe_occurrences: Vec<HirOccurrenceId>,
}
/// Private successor inference using retained value and effect variable graphs.
/// Complete Call, source admission and public scheme correspondence remain open.
pub struct CandidateInference {
    solved: CandidateSolvedResult,
}
/// Research-only receipt for one source-linked native callback-field bound.
/// A yielded row exists only after its exact typed task drains successfully.
pub struct CandidateOperationFieldV1Receipt<'a> {
    pub id: u32,
    pub request: &'a HirOccurrenceId,
    pub callback_apply: &'a HirOccurrenceId,
    pub callback_operation: &'a yu_hir::shadow::SourceOperationId,
    pub callback_operation_use: &'a HirOccurrenceId,
    pub response_definition: &'a yu_hir::HirLocalId,
    pub family: &'a yu_hir::shadow::SourceEffectId,
    pub consumed: bool,
}
/// Read-only map-backed correspondence for one retained typed Replay row.
/// Raw native root equality is reported separately from transport evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateReplayDemandTransport {
    pub call_index: usize,
    pub child_relation: usize,
    pub lower_relation: usize,
    pub upper_relation: usize,
    pub fresh_relation: Option<usize>,
    pub consumer_relation: Option<usize>,
    pub lower_input: String,
    pub upper_input: String,
    pub fresh_from: Option<String>,
    pub fresh_to: Option<String>,
    pub physical_fiber: Option<String>,
    pub physical_readback: Option<String>,
    pub port_relations: Option<[usize; 4]>,
    pub port_transformers: Option<[usize; 4]>,
    pub use_instance: usize,
    pub native_root: Term,
    pub copied_root: Term,
    pub replay_upper_root: Option<Term>,
    pub replay_child_root: Option<Term>,
    pub consumer_root: Option<Term>,
    pub native_root_matches: bool,
    pub route_owner: Option<CandidateReplayRouteOwner>,
    pub route: Option<usize>,
    pub scope_map_matches: bool,
    pub input_map_matches: bool,
    pub ports: [Term; 4],
    pub ports_match: [bool; 4],
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateReplayRouteOwner { Module, Local }
/// One row from the bounded, borrowed ordinary-provider diagnostic view.
/// `record` is an existing retained structure, not a reconstructed event.
#[derive(Debug)]
pub struct CandidateProviderObservationRow<'a> {
    pub graph_index: usize,
    /// Index of the retained AE/RE FunctionPort record whose parent relation
    /// this row describes.
    pub function_port_ordinal: usize,
    pub relation: u32,
    pub ordinal: usize,
    pub kind: CandidateProviderObservationKind,
    pub record: &'a dyn std::fmt::Debug,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateProviderObservationKind {
    FunctionPort,
    IncomingDependency,
    BoundAdmission,
    BoundEmission,
    SourceOrigin,
}
/// Retained Capture and fresh-use map records associated with actual candidate
/// graph routes. These are structural inputs, not constructor-event history.
#[derive(Debug)]
pub struct CandidateProviderCaptureRow<'a> {
    pub graph_index: usize,
    pub route_owner: CandidateReplayRouteOwner,
    pub route: usize,
    pub route_occurrence: &'a dyn std::fmt::Debug,
    pub context_use: usize,
    pub relation: Option<u32>,
    pub ordinal: usize,
    pub kind: CandidateProviderCaptureKind,
    pub map_name: Option<&'static str>,
    pub record: &'a dyn std::fmt::Debug,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateProviderCaptureKind {
    CaptureGraph,
    FreshUseMap,
    CapturedBound,
    CaptureSnapshot,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateProviderSourceJoin {
    /// Context-local provider records are not directly joined to the retained
    /// Lambda slot-2 source receipt by this observation.
    NotJoinedToContextRecord,
}
/// Rows borrow the final retained graph. The cap limits total rows across all
/// candidate graphs; hitting it is reported, never silently presented as a
/// complete census.
pub struct CandidateProviderObservation<'a> {
    rows: Vec<CandidateProviderObservationRow<'a>>,
    capture_rows: Vec<CandidateProviderCaptureRow<'a>>,
    truncated: bool,
}
/// Exact retained source admissions selected by their HIR occurrence. The
/// occurrence, cause and fact are borrowed from the owning store; this view
/// does not infer a missing source-to-route edge.
#[derive(Debug)]
pub struct CandidateSourceFactRecord<'a> {
    pub occurrence: &'a HirOccurrenceId,
    pub cause: &'a ConstraintOccurrenceId,
    pub fact: &'a SemanticFact,
}
/// A drain Origin sharing the requested source Cause's full occurrence key.
/// This key match is only a candidate association: it does not distinguish a
/// direct source seed from a replay child or prove downstream reachability.
#[derive(Debug)]
pub struct CandidateSourceOriginRecord<'a> {
    pub graph_index: usize,
    pub occurrence: &'a HirOccurrenceId,
    pub local_slot: u8,
    pub relation: usize,
    pub attribution: CandidateSourceOriginAttribution,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateSourceOriginAttribution {
    OccurrenceCandidateOnly,
}
/// Source-keyed exact records. Completeness applies to the corresponding
/// retained collection after selecting by source occurrence.
pub struct CandidateSourceOccurrenceObservation<'a> {
    facts: Vec<CandidateSourceFactRecord<'a>>,
    origins: Vec<CandidateSourceOriginRecord<'a>>,
    facts_complete: bool,
    origins_complete: bool,
}
impl<'a> CandidateSourceOccurrenceObservation<'a> {
    pub fn facts(&self) -> impl Iterator<Item = &CandidateSourceFactRecord<'a>> + '_ { self.facts.iter() }
    pub fn origins(&self) -> impl Iterator<Item = &CandidateSourceOriginRecord<'a>> + '_ { self.origins.iter() }
    pub fn facts_complete(&self) -> bool { self.facts_complete }
    pub fn origins_complete(&self) -> bool { self.origins_complete }
}
#[derive(Debug)]
pub struct CandidateSourceDependencyRecord {
    pub graph_index: usize,
    pub seed_relation: usize,
    pub seed_origin_index: usize,
    pub ordinal: usize,
    pub dependency: CandidateSourceDependency,
    pub replay: Option<CandidateSourceReplayInputs>,
    pub function_port: Option<(FunctionField, crate::candidate_context::FunctionPortOperation)>,
    pub transport: Option<(usize, Option<crate::candidate_context::TransportWitness>)>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateSourceDependency {
    Derived { child: u32, parent: u32 },
    FunctionPort { child: u32, parent: u32 },
    Replay { child: u32, lower: u32, upper: u32 },
    Transport { child: u32, parent: u32 },
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CandidateSourceReplayInputs {
    pub lower: crate::candidate_effect::BoundKey,
    pub upper: crate::candidate_effect::BoundKey,
}
pub struct CandidateSourceProviderConsumer<'a> {
    pub apply: &'a HirOccurrenceId,
    pub callee: &'a HirOccurrenceId,
    pub module_target: &'a DefId,
    pub native_callee: Term,
    pub native_demand: Term,
}
pub struct CandidateSourceProviderObservation<'a> {
    pub facts: Vec<CandidateSourceFactRecord<'a>>,
    pub origins: Vec<CandidateSourceOriginRecord<'a>>,
    pub dependencies: Vec<CandidateSourceDependencyRecord>,
    pub captures: Vec<CandidateProviderCaptureRow<'a>>,
    pub consumer: CandidateSourceProviderConsumer<'a>,
    pub facts_complete: bool,
    pub origins_complete: bool,
    pub dependencies_complete: bool,
    pub provider_route_complete: bool,
    pub provider_route_matches: usize,
    pub capture_bounds_complete: bool,
    pub maps_complete: bool,
    pub direct_source_drain_attribution: CandidateSourceAttributionStatus,
    pub captures_structured: bool,
    pub maps_structured: bool,
    pub consumer_relation_join_complete: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateSourceAttributionStatus {
    Unknown,
}
impl CandidateSourceProviderObservation<'_> {
    pub fn source_to_consumer_discriminating(&self) -> bool {
        self.facts_complete
            && self.origins_complete
            && self.dependencies_complete
            && self.provider_route_complete
            && self.capture_bounds_complete
            && self.maps_complete
            && self.direct_source_drain_attribution != CandidateSourceAttributionStatus::Unknown
            && self.captures_structured
            && self.maps_structured
            && self.consumer_relation_join_complete
    }
}
impl<'a> CandidateProviderObservation<'a> {
    pub fn rows(&self) -> impl Iterator<Item = &CandidateProviderObservationRow<'a>> + '_ {
        self.rows.iter()
    }
    pub fn truncated(&self) -> bool { self.truncated }
    pub fn capture_rows(&self) -> impl Iterator<Item = &CandidateProviderCaptureRow<'a>> + '_ {
        self.capture_rows.iter()
    }
    pub fn lambda_slot2_source_join(&self) -> CandidateProviderSourceJoin {
        CandidateProviderSourceJoin::NotJoinedToContextRecord
    }
}
/// Borrowed final retained state, not an execution trace or soundness certificate.
pub struct CandidateIntrusionObservation<'a> {
    references: &'a crate::candidate_value_graph::Graph,
    state: &'a crate::candidate_intrusion::State,
}
#[derive(Debug)]
pub enum CandidateSourceValueIdentity<'a> {
    Module(&'a DefId),
    Local(&'a yu_hir::HirLocalId),
    Parameter(&'a HirParameterId),
    CatchBinder(&'a yu_hir::shadow::LocalSourceCatchBinderId),
    Expression(&'a HirOccurrenceId),
}
#[derive(Debug)]
pub struct CandidateSourceValue<'a> {
    pub ordinal: usize,
    pub component: usize,
    pub identity: CandidateSourceValueIdentity<'a>,
}
pub struct CandidateIntrusionEvent<'a> {
    pub ordinal: usize,
    pub checking: &'a ConstraintOccurrenceId,
    pub origin: CandidateSourceValue<'a>,
    pub receiver: CandidateSourceValue<'a>,
    pub same_scc: bool,
}
#[derive(Clone, Copy, Debug)]
pub struct CandidateIntrusionRow {
    pub kind: ComponentKind,
    pub ordinal: u32,
    pub representative: u32,
}
pub struct CandidateIntrusionParent<'a> {
    pub ordinal: usize,
    pub copy: CandidateIntrusionRow,
    pub parent: CandidateIntrusionRow,
    pub polarity: Polarity,
    pub target: u32,
    pub occurrence: usize,
    pub source_set: Option<usize>,
    pub source_events: &'a [usize],
}
pub struct CandidateIntrusionGroup {
    pub ordinal: usize,
    pub occurrence: usize,
    pub start: usize,
    pub end: usize,
    pub activated: bool,
}
pub struct CandidateIntrusionReuse<'a> {
    pub ordinal: usize,
    pub group: usize,
    pub occurrence: usize,
    pub source_set: usize,
    pub source_events: &'a [usize],
}
impl<'a> CandidateIntrusionObservation<'a> {
    fn value(&self, ordinal: usize) -> CandidateSourceValue<'a> {
        use crate::candidate_value_graph::Value;
        let (value, component) = self.references.observed_value(ordinal).expect("retained event has a sealed source Value");
        let identity = match value {
            Value::Module(id) => CandidateSourceValueIdentity::Module(id),
            Value::Local(id) => CandidateSourceValueIdentity::Local(id),
            Value::CatchBinder(id) => CandidateSourceValueIdentity::CatchBinder(id),
            Value::Parameter(id) => CandidateSourceValueIdentity::Parameter(id),
            Value::Expression(id) => CandidateSourceValueIdentity::Expression(id),
        };
        CandidateSourceValue { ordinal, component, identity }
    }
    /// Ordered by retained event ordinal. Checking lookup is expected O(1) per
    /// event (HashMap collision worst case O(E)); descriptor lookup is expected
    /// O(1) (collision worst case O(V)). Full iteration is expected O(E), worst
    /// case O(E * (V + E)), with no allocation.
    /// Auxiliary fragment nodes are deliberately absent from these endpoints.
    pub fn events(&self) -> impl Iterator<Item = CandidateIntrusionEvent<'a>> + '_ {
        self.references.events.iter().enumerate().map(|(ordinal, event)| CandidateIntrusionEvent {
            ordinal,
            checking: self.references.observed_checking(ordinal).expect("retained event has its source checking occurrence"),
            origin: self.value(event.origin), receiver: self.value(event.receiver),
            same_scc: self.references.qualifies(ordinal),
        })
    }
    fn row(&self, row: crate::candidate_scheme::RowKey) -> CandidateIntrusionRow {
        use crate::candidate_scheme::RowKey;
        let ordinal = match row { RowKey::Value(id) | RowKey::Effect(id) => id };
        let representative = match self.state.rep(row) { RowKey::Value(id) | RowKey::Effect(id) => id };
        CandidateIntrusionRow { kind: row.kind(), ordinal, representative }
    }
    pub fn parents(&self) -> impl Iterator<Item = CandidateIntrusionParent<'a>> + '_ {
        self.state.parents.iter().enumerate().map(|(ordinal, parent)| CandidateIntrusionParent {
            ordinal, copy: self.row(parent.copy), parent: self.row(parent.parent),
            polarity: parent.polarity, target: parent.target, occurrence: parent.occurrence,
            source_set: parent.sources,
            source_events: parent.sources.map(|id| self.state.effect_algebra.context.source_events(id)).unwrap_or(&[]),
        })
    }
    pub fn groups(&self) -> impl Iterator<Item = CandidateIntrusionGroup> + '_ {
        self.state.observed_groups().map(|(ordinal, occurrence, start, end, activated)| CandidateIntrusionGroup { ordinal, occurrence, start, end, activated })
    }
    pub fn reuses(&self) -> impl Iterator<Item = CandidateIntrusionReuse<'a>> + '_ {
        self.state.observed_reuses().map(|(ordinal, group, occurrence, source_set)| CandidateIntrusionReuse {
            ordinal, group, occurrence, source_set,
            source_events: self.state.effect_algebra.context.source_events(source_set),
        })
    }
    pub fn pending_total(&self) -> usize { self.state.observed_pending().0 }
    pub fn pending_consumed(&self) -> usize { self.state.observed_pending().1 }
}
/// Atomic native route observation from the opt-in scope experiment. This is
/// neither Catch subtraction evidence nor a principal scheme presentation.
pub struct CandidateScopedObservation<'a> {
    record: &'a crate::candidate_context::ScopedObservation,
    context: &'a crate::candidate_context::State,
    views: &'a [crate::candidate_effect::View],
    state: crate::candidate_scope::ScopeState,
    pair: crate::TypedPairKey,
    transformer: usize,
}
impl CandidateScopedObservation<'_> {
    pub fn relation_id(&self) -> u32 { self.record.relation.0 }
    pub fn pair(&self) -> &impl std::fmt::Debug { &self.pair }
    pub fn transformer_id(&self) -> usize { self.transformer }
    pub fn transformer(&self) -> Option<&impl std::fmt::Debug> {
        if self.transformer == 0 { None } else { self.context.scope_transformer(self.transformer).ok() }
    }
    pub fn member_count(&self) -> usize {
        match self.record.operand { EffectEndpointKey::Support(view) => self.views[view as usize].allowed.len(), _ => 1 }
    }
    pub fn member_operand(&self, member: usize) -> Option<impl std::fmt::Debug> {
        if member >= self.member_count() { return None; }
        Some(match self.record.operand {
            EffectEndpointKey::Support(view) => EffectEndpointKey::AnnotationMember(view, u32::try_from(member).ok()?),
            operand => operand,
        })
    }
    pub fn input_routes(&self) -> impl Iterator<Item = u32> + '_ { self.state.inputs.iter().map(|id| id.0) }
    pub fn protection_scopes(&self) -> impl Iterator<Item = u32> + '_ { self.state.protections.iter().map(|id| id.0) }
}
impl CandidateInference {
    pub fn intrusion_observation(&self) -> Result<CandidateIntrusionObservation<'_>, ArtifactMismatch> {
        if !self.solved.data.errors.is_empty() { return Err(ArtifactMismatch); }
        let state = &self.solved.data.candidate_graph.as_ref().ok_or(ArtifactMismatch)?.intrusion;
        let references = &self.solved.data.candidate_references;
        Ok(CandidateIntrusionObservation { references, state })
    }
    /// Bounded borrowed view of retained ordinary AE/RE FunctionPort records
    /// and the relation-local dependency, producer and source-origin records
    /// already associated with their parent relation. This does not reconstruct
    /// event order or certify a unique provider route.
    pub fn ordinary_provider_observation(
        &self, max_rows: usize,
    ) -> Result<CandidateProviderObservation<'_>, ArtifactMismatch> {
        const HARD_MAX_ROWS: usize = 256;
        if !self.solved.data.errors.is_empty() { return Err(ArtifactMismatch); }
        let cap = max_rows.min(HARD_MAX_ROWS);
        let mut rows = Vec::new();
        rows.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        let mut truncated = false;
        let mut push = |row| {
            if rows.len() == cap { truncated = true; false }
            else { rows.push(row); true }
        };
        'graphs: for (graph_index, graph) in self.solved.data.candidate_graph.iter().enumerate() {
            let context = &graph.intrusion.effect_algebra.context;
            for (ordinal, dependency) in context.observed_dependencies().enumerate() {
                let crate::candidate_context::Dependency::FunctionPort { parent, field, .. } = *dependency else { continue; };
                if !matches!(field, FunctionField::ArgumentEffect | FunctionField::ResultEffect) { continue; }
                if !push(CandidateProviderObservationRow {
                    graph_index, function_port_ordinal: ordinal, relation: parent.0, ordinal,
                    kind: CandidateProviderObservationKind::FunctionPort, record: dependency,
                }) { break 'graphs; }
                for (incoming_ordinal, incoming) in context.observed_dependencies().enumerate() {
                    let child = match *incoming {
                        crate::candidate_context::Dependency::Derived { child, .. }
                        | crate::candidate_context::Dependency::FunctionPort { child, .. }
                        | crate::candidate_context::Dependency::Replay { child, .. }
                        | crate::candidate_context::Dependency::Transport { child, .. } => child,
                    };
                    if child != parent { continue; }
                    if !push(CandidateProviderObservationRow {
                        graph_index, function_port_ordinal: ordinal, relation: parent.0, ordinal: incoming_ordinal,
                        kind: CandidateProviderObservationKind::IncomingDependency, record: incoming,
                    }) { break 'graphs; }
                }
                for (admission_ordinal, admission) in context.observed_bound_admissions() {
                    if admission.relation != Some(parent) { continue; }
                    if !push(CandidateProviderObservationRow {
                        graph_index, function_port_ordinal: ordinal, relation: parent.0, ordinal: admission_ordinal,
                        kind: CandidateProviderObservationKind::BoundAdmission, record: admission,
                    }) { break 'graphs; }
                }
                for (emission_ordinal, emission) in context.observed_bound_emissions_for_relation(parent) {
                    if !push(CandidateProviderObservationRow {
                        graph_index, function_port_ordinal: ordinal, relation: parent.0, ordinal: emission_ordinal,
                        kind: CandidateProviderObservationKind::BoundEmission, record: emission,
                    }) { break 'graphs; }
                }
                for (origin_ordinal, origin) in context.origins.iter().enumerate() {
                    if origin.relation != parent { continue; }
                    if !push(CandidateProviderObservationRow {
                        graph_index, function_port_ordinal: ordinal, relation: parent.0, ordinal: origin_ordinal,
                        kind: CandidateProviderObservationKind::SourceOrigin, record: origin,
                    }) { break 'graphs; }
                }
            }
        }
        drop(push);
        let mut capture_rows = Vec::new();
        capture_rows.try_reserve(cap.saturating_sub(rows.len())).map_err(|_| ArtifactMismatch)?;
        let mut push_capture = |row| {
            if rows.len() + capture_rows.len() == cap { truncated = true; false }
            else { capture_rows.push(row); true }
        };
        'captures: for (graph_index, state) in self.solved.data.candidate_graph.iter().enumerate() {
            for (route, item) in state.routes.iter().enumerate() {
                let context_use = item.retained.observed_context_use();
                let route_occurrence = item.use_id.occurrence();
                if !push_capture(CandidateProviderCaptureRow {
                    graph_index, route_owner: CandidateReplayRouteOwner::Module, route, route_occurrence, context_use,
                    relation: None, ordinal: route, kind: CandidateProviderCaptureKind::CaptureGraph,
                    map_name: None, record: &item.graph,
                }) { break 'captures; }
                let mut maps_complete = true;
                item.retained.observe_maps(|map_name, record| {
                    if maps_complete {
                        maps_complete = push_capture(CandidateProviderCaptureRow {
                            graph_index, route_owner: CandidateReplayRouteOwner::Module, route, route_occurrence, context_use,
                            relation: None, ordinal: route, kind: CandidateProviderCaptureKind::FreshUseMap,
                            map_name: Some(map_name), record,
                        });
                    }
                });
                if !maps_complete { break 'captures; }
                for (ordinal, bound) in item.graph.bounds.iter().enumerate() {
                    if !push_capture(CandidateProviderCaptureRow {
                        graph_index, route_owner: CandidateReplayRouteOwner::Module, route, route_occurrence, context_use,
                        relation: bound.relation.map(|id| id.0), ordinal,
                        kind: CandidateProviderCaptureKind::CapturedBound, map_name: None, record: bound,
                    }) { break 'captures; }
                }
                for (ordinal, snapshot) in item.graph.bound_evidence.iter().enumerate() {
                    if !push_capture(CandidateProviderCaptureRow {
                        graph_index, route_owner: CandidateReplayRouteOwner::Module, route, route_occurrence, context_use,
                        relation: None, ordinal, kind: CandidateProviderCaptureKind::CaptureSnapshot,
                        map_name: None, record: snapshot,
                    }) { break 'captures; }
                }
            }
            for (route, item) in state.local_routes.iter().enumerate() {
                let context_use = item.retained.observed_context_use();
                let route_occurrence = &item.occurrence;
                if !push_capture(CandidateProviderCaptureRow {
                    graph_index, route_owner: CandidateReplayRouteOwner::Local, route, route_occurrence, context_use,
                    relation: None, ordinal: route, kind: CandidateProviderCaptureKind::CaptureGraph,
                    map_name: None, record: &item.graph,
                }) { break 'captures; }
                let mut maps_complete = true;
                item.retained.observe_maps(|map_name, record| {
                    if maps_complete {
                        maps_complete = push_capture(CandidateProviderCaptureRow {
                            graph_index, route_owner: CandidateReplayRouteOwner::Local, route, route_occurrence, context_use,
                            relation: None, ordinal: route, kind: CandidateProviderCaptureKind::FreshUseMap,
                            map_name: Some(map_name), record,
                        });
                    }
                });
                if !maps_complete { break 'captures; }
                for (ordinal, bound) in item.graph.bounds.iter().enumerate() {
                    if !push_capture(CandidateProviderCaptureRow {
                        graph_index, route_owner: CandidateReplayRouteOwner::Local, route, route_occurrence, context_use,
                        relation: bound.relation.map(|id| id.0), ordinal,
                        kind: CandidateProviderCaptureKind::CapturedBound, map_name: None, record: bound,
                    }) { break 'captures; }
                }
                for (ordinal, snapshot) in item.graph.bound_evidence.iter().enumerate() {
                    if !push_capture(CandidateProviderCaptureRow {
                        graph_index, route_owner: CandidateReplayRouteOwner::Local, route, route_occurrence, context_use,
                        relation: None, ordinal, kind: CandidateProviderCaptureKind::CaptureSnapshot,
                        map_name: None, record: snapshot,
                    }) { break 'captures; }
                }
            }
        }
        drop(push_capture);
        Ok(CandidateProviderObservation { rows, capture_rows, truncated })
    }
    pub fn solve(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        Self::solve_mode(hir, false, false)
    }
    /// Explicit, research-only entry for the statically linked operation field candidate.
    pub fn solve_operation_v1_research(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        Self::solve_mode(hir, false, true)
    }
    /// Reversible private-candidate experiment; unsupported source provenance
    /// defers the attempt instead of publishing a partly scoped result.
    pub fn solve_scoped_experiment(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        Self::solve_mode(hir, true, false)
    }
    pub fn scoped_observations(&self) -> impl Iterator<Item = Result<CandidateScopedObservation<'_>, SolveAvailabilityError>> {
        self.solved.data.candidate_graph.iter().flat_map(|graph| {
            let algebra = &graph.intrusion.effect_algebra;
            algebra.context.scope_observations.iter().map(move |record| {
                let (transformer, state) = algebra.context.evaluate_observation(record.relation)?;
                let pair = algebra.context.observed_pair(record.relation)?;
                Ok(CandidateScopedObservation { record, context: &algebra.context, views: &algebra.views, state, pair, transformer })
            })
        })
    }
    pub fn scoped_scope_lineage(&self) -> impl Iterator<Item = (u32, u32, &HirOccurrenceId)> {
        self.solved.data.candidate_graph.iter().flat_map(|graph| {
            let inventory = &graph.intrusion.effect_algebra.context.scope_inventory;
            inventory.scope_origins.iter().enumerate().map(move |(actual, original)|
                (actual as u32, original.0, &inventory.scope_occurrences[original.0 as usize]))
        })
    }
    pub fn scoped_input_lineage(&self) -> impl Iterator<Item = (u32, u32, &HirOccurrenceId)> {
        self.solved.data.candidate_graph.iter().flat_map(|graph|
            graph.intrusion.effect_algebra.context.scope_inventory.input_origins.iter().enumerate())
            .map(move |(actual, original)| (actual as u32, original.0, self.solved.data.candidate_calls.calls[original.0 as usize].checking.occurrence()))
    }
    pub fn scoped_relation_flows(&self) -> impl Iterator<Item = (usize, impl std::fmt::Debug + '_, impl std::fmt::Debug + '_, bool)> + '_ {
        self.solved.data.candidate_graph.iter().flat_map(|graph| graph.intrusion.effect_algebra.context.observed_relations())
            .map(|(index, pair, flow)| (index, pair, flow, flow != crate::candidate_context::ScopedFlow::default()))
    }
    pub fn scoped_dependencies(&self) -> impl Iterator<Item = impl std::fmt::Debug + '_> + '_ {
        self.solved.data.candidate_graph.iter().flat_map(|graph| graph.intrusion.effect_algebra.context.observed_dependencies())
    }
    pub fn scoped_origins(&self) -> impl Iterator<Item = impl std::fmt::Debug + '_> + '_ {
        self.solved.data.candidate_graph.iter().flat_map(|graph| graph.intrusion.effect_algebra.context.origins.iter())
    }
    pub fn scoped_copy_statistics(&self) -> impl Iterator<Item = impl std::fmt::Debug + '_> + '_ {
        self.solved.data.candidate_graph.iter().flat_map(|graph| graph.intrusion.effect_algebra.context.scope_inventory.copies.iter())
            .map(|copy| (copy.regions, copy.scopes, copy.inputs, copy.graph_nodes, copy.graph_bounds))
    }
    /// Actual map-backed correspondence for retained scoped Replay demands.
    /// This provisional source-evidence observation does not alter solver state.
    pub fn scoped_replay_demand_transports(&self) -> impl Iterator<Item = CandidateReplayDemandTransport> + '_ {
        self.solved.data.candidate_graph.iter().flat_map(move |graph| {
            let context = &graph.intrusion.effect_algebra.context;
            context.replay_demand_rows().filter_map(move |row| {
                let demand = row.demand;
                let native = self.solved.data.candidate_calls.calls.get(row.call)?.native?;
                let ports = |root| match self.solved.data.store.term_view(root).ok()? {
                    TermView::NegativeFunction { argument, argument_effect, result_effect, result } => Some([argument, argument_effect, result_effect, result]),
                    _ => None,
                };
                let evidence = graph.authenticate_demand_transport(context, row, native.demand, ports, None);
                Some(CandidateReplayDemandTransport {
                    call_index: row.call, child_relation: row.child.0 as usize,
                    lower_relation: row.lower.0 as usize, upper_relation: row.upper.0 as usize,
                    fresh_relation: evidence.map(|value| value.fresh_relation.0 as usize),
                    consumer_relation: evidence.map(|value| value.consumer.0 as usize),
                    lower_input: format!("{:?}", row.lower_input), upper_input: format!("{:?}", row.upper_input),
                    fresh_from: evidence.map(|value| format!("{:?}", value.fresh_from)),
                    fresh_to: evidence.map(|value| format!("{:?}", value.fresh_to)),
                    physical_fiber: evidence.map(|value| format!("{:?}", value.physical_fiber)),
                    physical_readback: evidence.map(|value| format!("{:?}", value.physical_readback)),
                    port_relations: evidence.map(|value| value.port_relations.map(|id| id.0 as usize)),
                    port_transformers: evidence.map(|value| value.port_transformers),
                    use_instance: demand.use_instance,
                    native_root: native.demand, copied_root: demand.root,
                    replay_upper_root: evidence.map(|value| value.replay_upper_root),
                    replay_child_root: evidence.map(|value| value.replay_child_root),
                    consumer_root: evidence.map(|value| value.consumer_root),
                    native_root_matches: native.demand == demand.root,
                    route_owner: evidence.map(|value| match value.route_owner {
                        candidate_scheme::FreshRouteOwner::Module => CandidateReplayRouteOwner::Module,
                        candidate_scheme::FreshRouteOwner::Local => CandidateReplayRouteOwner::Local,
                    }),
                    route: evidence.map(|value| value.route),
                    scope_map_matches: evidence.is_some_and(|value| value.scope_map_matches),
                    input_map_matches: evidence.is_some_and(|value| value.input_map_matches),
                    ports: ports(demand.root).unwrap_or([demand.root; 4]),
                    ports_match: evidence.map_or([false; 4], |value| value.ports_match),
                })
            })
        })
    }
    /// Re-check an observation after replacing a route coordinate or one of its
    /// four port values. This supports direct falsifiers in the focused harness.
    pub fn authenticate_scoped_replay_demand(
        &self, call_index: usize, use_instance: usize, copied_root: Term,
        observed_ports: Option<[Term; 4]>,
    ) -> bool {
        let Some(graph) = self.solved.data.candidate_graph.as_ref() else { return false; };
        let context = &graph.intrusion.effect_algebra.context;
        let Some(row) = context.replay_demand_rows().find(|row|
            row.call == call_index && row.demand.use_instance == use_instance && row.demand.root == copied_root) else { return false; };
        let Some(native) = self.solved.data.candidate_calls.calls.get(call_index).and_then(|call| call.native) else { return false; };
        let ports = |root| match self.solved.data.store.term_view(root).ok()? {
            TermView::NegativeFunction { argument, argument_effect, result_effect, result } => Some([argument, argument_effect, result_effect, result]),
            _ => None,
        };
        graph.authenticate_demand_transport(context, row, native.demand, ports, observed_ports).is_some()
    }
    /// Counts and maximum recorded scoped scratch envelope. The envelope is
    /// not a total peak: simultaneous and failure-path peaks are not covered.
    pub fn scoped_resource_statistics(&self) -> Option<(usize, usize, usize, usize, usize)> {
        let inventory = &self.solved.data.candidate_graph.as_ref()?.intrusion.effect_algebra.context.scope_inventory;
        Some((inventory.regions.len(), inventory.scope_regions.len(), inventory.input_regions.len(), inventory.work_used, inventory.scratch_peak_bytes))
    }
    fn solve_mode(hir: Arc<HirModule>, scoped: bool, operation_v1: bool) -> Result<Self, CandidateError> {
        let mut permitted_errors = HashSet::new();
        let mut declaration_errors = HashSet::new();
        for declaration in hir.source_effect_declarations() {
            declaration_errors.extend(declaration.placeholder_errors.iter().copied());
        }
        for item in hir.items() {
            if let HirItem::Error { errors, .. } = item {
                if !errors.is_empty() && errors.iter().all(|error| declaration_errors.contains(error)) { continue; }
            }
            let (expression, owner) = match item {
                HirItem::Binding(binding) => (Some(binding.value()), Some(SourceRootId::Definition(binding.definition_root().clone()))),
                HirItem::Expression(expression) => (Some(expression), hir.expression_root(expression.occurrence())
                    .map_err(|_| CandidateError::Unsupported)?.cloned().map(SourceRootId::Expression)),
                _ => (None, None),
            };
            if let (Some(expression), Some(owner)) = (expression, owner) {
                if let Some(source) = hir.local_source_for(&owner).map_err(|_| CandidateError::Unsupported)? {
                    crate::candidate_source::preflight(source, operation_v1)?;
                    crate::candidate_source::retain_placeholder_errors(expression, &mut permitted_errors)?;
                    continue;
                }
            }
            let expr = match item {
                HirItem::Binding(binding) => binding.value(),
                HirItem::Expression(expr) if matches!(expr, ResolvedExpr::Integer { .. }) => expr,
                _ => return Err(CandidateError::Unsupported),
            };
            preflight_expression(expr, None, &mut permitted_errors)?;
        }
        if hir.errors().iter().any(|error| {
            !(permitted_errors.contains(&error.id()) && error.kind() == HirErrorKind::UnsupportedExpression)
                && !(declaration_errors.contains(&error.id()) && error.kind() == HirErrorKind::UnsupportedItem)
        }) {
            return Err(CandidateError::Unsupported);
        }
        let batch = ConstraintBatch::collect_candidate_mode_scoped_v1(hir, true, true, scoped, operation_v1).map_err(CandidateError::Collection)?;
        if scoped && batch.scc_plan().components_in_dependency_first_order().any(|component|
            batch.scc_plan().internal_uses(component).is_ok_and(|uses| !uses.is_empty())) {
            return Err(CandidateError::Unsupported);
        }
        let session = InferenceSession::try_new_candidate(batch).map_err(CandidateError::Solve)?;
        let solved = session.run_candidate().map_err(CandidateError::Solve)?;
        #[cfg(test)]
        if scoped && std::env::var_os("YU_CALL_REPLAY_OBSERVER").is_some() {
            if let Some(graph) = &solved.data.candidate_graph {
                let context = &graph.intrusion.effect_algebra.context;
                let stderr = std::io::stderr();
                let mut output = stderr.lock();
                use std::io::Write as _;
                for row in context.replay_demand_rows() {
                    let demand = row.demand;
                    let native = solved.data.candidate_calls.calls.get(row.call).and_then(|call| call.native);
                    let root_matches = native.is_some_and(|native| native.demand == demand.root);
                    let lower_root = match row.lower_input.2 {
                        ExtrusionEndpoint::Value(ValueEndpointKey::PositiveFunction(root)) => Some(root),
                        _ => None,
                    };
                    let positive_census = lower_root.map_or_else(Vec::new, |root| graph.test_positive_function_census(root));
                    let lower_relations: Vec<_> = context.bound_relations(row.lower_input).map(|relation| (
                        relation, context.relation_pair(relation), context.scoped_flow(relation).ok(),
                        context.test_provenance_for_relation(relation),
                    )).collect();
                    if writeln!(output,
                        "candidate.call_replay_census call={} lower_root={lower_root:?} all_lower_bound_relations={lower_relations:?} positive_function_routes={positive_census:?}",
                        row.call).is_err() { break; }
                    let source_ports = native.and_then(|native| match solved.data.store.term_view(native.demand).ok()? {
                        TermView::PositiveFunction { argument, argument_effect, result_effect, result }
                        | TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                            Some([argument, argument_effect, result_effect, result]),
                        _ => None,
                    });
                    let copied_ports = match solved.data.store.term_view(demand.root).ok() {
                        Some(TermView::PositiveFunction { argument, argument_effect, result_effect, result })
                        | Some(TermView::NegativeFunction { argument, argument_effect, result_effect, result }) =>
                            Some([argument, argument_effect, result_effect, result]),
                        _ => None,
                    };
                    if writeln!(output,
                        "candidate.call_replay_source call={} constructor_root={:?} source_ports={source_ports:?} fresh_use={} copied_root={:?} copied_ports={copied_ports:?}",
                        row.call, native.map(|value| value.demand), demand.use_instance, demand.root).is_err()
                    { break; }
                    let transported = native.and_then(|native| graph.authenticate_demand_transport(
                        context, row, native.demand,
                        |root| match solved.data.store.term_view(root).ok()? {
                            TermView::NegativeFunction { argument, argument_effect, result_effect, result } =>
                                Some([argument, argument_effect, result_effect, result]),
                            _ => None,
                        },
                        None,
                    ));
                    let (transported, route_owner, route, relation, consumer, fresh_relation, fresh_from, fresh_to, physical_fiber, physical_readback,
                        replay_upper_root, replay_child_root, port_relations, port_transformers, scope_map, input_map, ports) =
                        if let Some(evidence) = transported {
                            (true, Some(evidence.route_owner), Some(evidence.route), Some(evidence.relation.0), Some(evidence.consumer.0),
                                Some(evidence.fresh_relation.0),
                                Some(evidence.fresh_from), Some(evidence.fresh_to),
                                Some(evidence.physical_fiber), Some(evidence.physical_readback),
                                Some(evidence.replay_upper_root), Some(evidence.replay_child_root),
                                evidence.port_relations.map(|id| id.0),
                                Some(evidence.port_transformers),
                                evidence.scope_map_matches,
                                evidence.input_map_matches,
                                evidence.ports_match)
                        } else { (false, None, None, None, None, None, None, None, None, None, None, None, [0; 4], None, false, false, [false; 4]) };
                    if writeln!(output,
                        "candidate.call_replay call={} child={} lower={} upper={} lower_input={:?} upper_input={:?} use_instance={} demand_root={:?} native_root_matches={root_matches} endpoint_pairs=(lower:{},upper:{}) transport_authenticated={transported} route_owner={route_owner:?} route={route:?} source_relation={relation:?} fresh_relation={fresh_relation:?} consumer={consumer:?} fresh_from={fresh_from:?} fresh_to={fresh_to:?} physical_fiber={physical_fiber:?} physical_readback={physical_readback:?} replay_upper_root={replay_upper_root:?} replay_child_root={replay_child_root:?} port_relations={port_relations:?} port_transformers={port_transformers:?} scope_map={scope_map} input_map={input_map} ports={ports:?}",
                        row.call, row.child.0, row.lower.0, row.upper.0, row.lower_input, row.upper_input,
                        demand.use_instance, demand.root, row.lower_matches, row.upper_matches).is_err()
                    { break; }
                }
            }
        }
        Ok(Self { solved })
    }
    pub fn observes_hir(&self, hir: &HirModule) -> bool {
        std::ptr::eq(self.solved.data.hir.as_ref(), hir)
    }
    /// Candidate conflicts never establish source rejection.
    pub fn candidate_conflicts(&self) -> &[SolverError] {
        &self.solved.data.errors
    }
    pub fn operation_v1_field_bounds(&self) -> impl Iterator<Item = CandidateOperationFieldV1Receipt<'_>> {
        self.solved.data.candidate_graph.iter().flat_map(|graph| {
            graph.intrusion.effect_algebra.field_bounds_v1.iter()
                // A drained edge is not a successful source receipt if any
                // required typing elsewhere in this inference failed. Errors
                // can be discovered after the v1 action, so gate publication
                // on the final result rather than the local membership pair.
                .filter(|record| record.consumed && self.solved.data.errors.is_empty())
                .map(|record| CandidateOperationFieldV1Receipt {
                id: record.id, request: &record.q.owner_request, callback_apply: &record.m0.apply_occurrence,
                callback_operation: &record.m0.operation.id, callback_operation_use: &record.m0.operation_occurrence,
                response_definition: &record.m0.response_definition,
                family: &record.q.family, consumed: record.consumed,
            })
        })
    }
    pub fn export(
        &self,
        root: &DefinitionRootId,
    ) -> Result<CandidateGraphExport<'_>, ArtifactMismatch> {
        // Conflicts remain available for diagnostics, but invalidate graph export.
        if !self.solved.data.errors.is_empty() {
            return Err(ArtifactMismatch);
        }
        if !self.solved.data.hir.owns_definition_root(root) {
            return Err(ArtifactMismatch);
        }
        let position = self
            .solved
            .data
            .root_scheme_positions
            .get(root)
            .ok_or(ArtifactMismatch)?;
        let state = self
            .solved
            .data
            .candidate_graph
            .as_ref()
            .ok_or(ArtifactMismatch)?;
        let graph = state.graphs[*position].as_ref().ok_or(ArtifactMismatch)?;
        Ok(CandidateGraphExport { state, graph })
    }
    pub fn fresh_use(&self, occurrence: &HirOccurrenceId) -> Option<CandidateGraphFreshUse<'_>> {
        // Conflicts remain available for diagnostics, but invalidate fresh-use graphs.
        if !self.solved.data.errors.is_empty() {
            return None;
        }
        if !self.solved.data.hir.owns_occurrence(occurrence) {
            return None;
        }
        let state = self.solved.data.candidate_graph.as_ref()?;
        if let Some(&route_index) = state.local_route_by_occurrence.get(occurrence) {
            let route = state.local_routes.get(route_index)?;
            let scheme = state.locals.get(route.slot)?.as_ref()?;
            if route.occurrence != *occurrence || scheme.id != route.local
                || !route.authentic_use_instance()
            { return None; }
            return Some(CandidateGraphFreshUse {
                state, occurrence: &route.occurrence, rows: &route.rows, graph: &route.graph,
            });
        }
        let route = state.routes.iter().find(|route| route.use_id.occurrence() == occurrence)?;
        Some(CandidateGraphFreshUse {
            state,
            occurrence: route.use_id.occurrence(),
            rows: &route.rows,
            graph: &route.graph,
        })
    }
    pub fn effect_conflict(&self, kind: SolverErrorKind) -> Result<CandidateEffectConflict<'_>, ArtifactMismatch> {
        let SolverErrorKind::IncompatibleEffect { operand, annotation } = kind else { return Err(ArtifactMismatch); };
        let state = &self.solved.data.candidate_graph.as_ref().ok_or(ArtifactMismatch)?.intrusion.effect_algebra;
        let (operand, annotation) = state.observe(operand, annotation).ok_or(ArtifactMismatch)?;
        let operand = match operand {
            crate::candidate_effect::ObservedOperand::Contribution(value) => CandidateEffectOperand::Contribution { effect: &value.effect, origin: &value.origin, instance: value.instance },
            crate::candidate_effect::ObservedOperand::AnnotationMember { view, member, effect } => match &view.provenance {
                crate::candidate_effect::ViewOrigin::Operation(origin) => CandidateEffectOperand::OperationInterfaceMember { declaration: &origin.declaration, owner: &view.owner, position: &view.position, occurrence: &origin.occurrence, member, effect },
                crate::candidate_effect::ViewOrigin::Annotation => CandidateEffectOperand::AnnotationMember { annotation: CandidateEffectAnnotation { owner: &view.owner, position: &view.position }, member, effect },
            },
        };
        Ok(CandidateEffectConflict {
            operand,
            annotation: annotation.map(|view| CandidateEffectAnnotation { owner: &view.owner, position: &view.position }),
        })
    }
    /// Indexed observations retain one pending construction request per source Call.
    pub fn source_call_count(&self) -> usize { self.solved.data.candidate_calls.calls.len() }
    pub fn source_call(&self, index: usize) -> Result<CandidateSourceCall<'_>, ArtifactMismatch> {
        let data = &self.solved.data;
        if let Some(graph) = data.candidate_graph.as_ref() {
            if graph.intrusion.effect_algebra.context.scoped_enabled {
                return crate::candidate_call::observe_scoped(&data.hir, &data.store, &data.candidate_calls, index, graph);
            }
        }
        crate::candidate_call::observe(&data.hir, &data.store, &data.candidate_calls, index)
    }
    /// Select source provenance and occurrence-matching Origin candidates by
    /// one owned HIR occurrence before applying presentation bounds. Full
    /// Cause identity and FactId/Terms are retained; source-vs-Replay seed
    /// attribution and Capture/consumer reachability remain separate joins.
    pub fn source_occurrence_observation<'a>(
        &'a self,
        occurrence: &'a HirOccurrenceId,
        max_rows: usize,
    ) -> Result<CandidateSourceOccurrenceObservation<'a>, ArtifactMismatch> {
        const HARD_MAX_ROWS: usize = 256;
        if !self.solved.data.errors.is_empty() { return Err(ArtifactMismatch); }
        if !self.solved.data.hir.owns_occurrence(occurrence) { return Err(ArtifactMismatch); }
        let cap = max_rows.min(HARD_MAX_ROWS);
        let mut facts = Vec::new();
        let mut origins = Vec::new();
        facts.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        origins.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        let mut facts_complete = true;
        for edge in self.solved.data.store.provenance() {
            let cause = edge.cause().occurrence();
            if cause.occurrence() != occurrence { continue; }
            let Some(fact) = self.solved.data.store.facts().get(edge.fact().index() as usize)
                .filter(|fact| fact.id() == edge.fact()) else {
                return Err(ArtifactMismatch);
            };
            if facts.len() == cap { facts_complete = false; break; }
            facts.push(CandidateSourceFactRecord { occurrence, cause, fact });
        }
        let mut origins_complete = true;
        'graphs: for (graph_index, graph) in self.solved.data.candidate_graph.iter().enumerate() {
            for origin in &graph.intrusion.effect_algebra.context.origins {
                if origin.occurrence.occurrence() != occurrence
                    || !self.solved.data.store.provenance().iter().any(|edge| edge.cause().occurrence() == &origin.occurrence)
                { continue; }
                if origins.len() == cap { origins_complete = false; break 'graphs; }
                origins.push(CandidateSourceOriginRecord {
                    graph_index,
                    occurrence,
                    local_slot: origin.occurrence.local_slot(),
                    relation: origin.relation.0 as usize,
                    attribution: CandidateSourceOriginAttribution::OccurrenceCandidateOnly,
                });
            }
        }
        Ok(CandidateSourceOccurrenceObservation { facts, origins, facts_complete, origins_complete })
    }
    /// Source-keyed view for one concrete forwarding Apply. Each selected
    /// Origin relation is followed through its retained ordered dependency
    /// alternatives; only that Apply's resolved module-callee route is then
    /// selected for Capture and FreshUse-map rows. All records remain borrowed
    /// from their owning solver structures. This is structural evidence, not
    /// an admission or preservation certificate.
    pub fn source_provider_observation<'a>(
        &'a self,
        source_keys: &[(&'a HirOccurrenceId, u8)],
        forwarding_apply: &'a HirOccurrenceId,
        max_rows: usize,
    ) -> Result<CandidateSourceProviderObservation<'a>, ArtifactMismatch> {
        use crate::candidate_context::Dependency;
        use std::collections::HashSet;
        const HARD_MAX_ROWS: usize = 256;
        if !self.solved.data.errors.is_empty()
            || !self.solved.data.hir.owns_occurrence(forwarding_apply)
            || source_keys.len() > 64
            || source_keys.iter().any(|(occurrence, _)| !self.solved.data.hir.owns_occurrence(occurrence))
        { return Err(ArtifactMismatch); }
        let cap = max_rows.min(HARD_MAX_ROWS);
        let consumer_index = self.solved.data.candidate_calls.calls.iter()
            .position(|call| call.checking.occurrence() == forwarding_apply)
            .ok_or(ArtifactMismatch)?;
        let native = self.source_call(consumer_index)?;
        let callee = &native.callee_source().occurrence;
        let module_target = native.module_callee_target().ok_or(ArtifactMismatch)?;
        let consumer = CandidateSourceProviderConsumer {
            apply: forwarding_apply, callee, module_target,
            native_callee: native.native_callee(), native_demand: native.native_demand(),
        };
        let mut facts = Vec::new();
        let mut origins = Vec::new();
        facts.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        origins.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        let mut facts_complete = true;
        for edge in self.solved.data.store.provenance() {
            let cause = edge.cause().occurrence();
            if !source_keys.iter().any(|(source, slot)| cause.occurrence() == *source && cause.local_slot() == *slot) { continue; }
            let Some(fact) = self.solved.data.store.facts().get(edge.fact().index() as usize)
                .filter(|fact| fact.id() == edge.fact()) else { return Err(ArtifactMismatch); };
            if facts.len() == cap { facts_complete = false; break; }
            facts.push(CandidateSourceFactRecord { occurrence: cause.occurrence(), cause, fact });
        }
        let mut origins_complete = true;
        let mut seeds = Vec::new();
        for (graph_index, graph) in self.solved.data.candidate_graph.iter().enumerate() {
            for origin in &graph.intrusion.effect_algebra.context.origins {
                let source = origin.occurrence.occurrence();
                let slot = origin.occurrence.local_slot();
                if !source_keys.iter().any(|(key, key_slot)| *key == source && *key_slot == slot)
                    || !self.solved.data.store.provenance().iter().any(|edge| edge.cause().occurrence() == &origin.occurrence)
                { continue; }
                if origins.len() == cap { origins_complete = false; break; }
                let origin_index = origins.len();
                origins.push(CandidateSourceOriginRecord {
                    graph_index, occurrence: source, local_slot: slot, relation: origin.relation.0 as usize,
                    attribution: CandidateSourceOriginAttribution::OccurrenceCandidateOnly,
                });
                seeds.push((graph_index, origin.relation, origin_index));
            }
            if !origins_complete { break; }
        }
        let mut dependencies = Vec::new();
        dependencies.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        let mut dependencies_complete = true;
        let mut reachable: Vec<HashSet<crate::candidate_context::RelationId>> = self.solved.data.candidate_graph.iter().map(|_| HashSet::new()).collect();
        if !facts_complete || !origins_complete { dependencies_complete = false; }
        for (graph_index, seed_relation, seed_origin_index) in &seeds {
            let graph = &self.solved.data.candidate_graph[*graph_index];
            let context = &graph.intrusion.effect_algebra.context;
            let mut seed_reachable = HashSet::new();
            let mut selected_edges = HashSet::new();
            seed_reachable.insert(*seed_relation);
            reachable[*graph_index].insert(*seed_relation);
            loop {
                let mut changed = false;
                for (ordinal, dependency) in context.observed_dependencies().enumerate() {
                    let (parents, child) = match *dependency {
                        Dependency::Derived { child, parent }
                        | Dependency::FunctionPort { child, parent, .. }
                        | Dependency::Transport { child, parent, .. } => ([Some(parent), None], child),
                        Dependency::Replay { child, lower, upper, .. } => ([Some(lower), Some(upper)], child),
                    };
                    if !parents.into_iter().flatten().any(|parent| seed_reachable.contains(&parent)) { continue; }
                    if selected_edges.insert(ordinal) {
                        if dependencies.len() == cap { dependencies_complete = false; }
                        else {
                            let (dependency, replay, function_port, transport) = match *dependency {
                                Dependency::Derived { child, parent } => (
                                    CandidateSourceDependency::Derived { child: child.0, parent: parent.0 }, None, None, None,
                                ),
                                Dependency::FunctionPort { child, parent, field, operation } => (
                                    CandidateSourceDependency::FunctionPort { child: child.0, parent: parent.0 },
                                    None, Some((field, operation)), None,
                                ),
                                Dependency::Replay { child, lower, upper, lower_input, upper_input } => (
                                    CandidateSourceDependency::Replay { child: child.0, lower: lower.0, upper: upper.0 },
                                    Some(CandidateSourceReplayInputs { lower: lower_input, upper: upper_input }), None, None,
                                ),
                                Dependency::Transport { child, parent, use_origin, witness } => (
                                    CandidateSourceDependency::Transport { child: child.0, parent: parent.0 },
                                    None, None, Some((use_origin, witness)),
                                ),
                            };
                            dependencies.push(CandidateSourceDependencyRecord {
                                graph_index: *graph_index, seed_relation: seed_relation.0 as usize,
                                seed_origin_index: *seed_origin_index, ordinal, dependency, replay, function_port, transport,
                            });
                        }
                    }
                    changed |= seed_reachable.insert(child);
                    reachable[*graph_index].insert(child);
                }
                if !changed { break; }
            }
        }
        let mut captures = Vec::new();
        captures.try_reserve(cap).map_err(|_| ArtifactMismatch)?;
        let mut provider_route_complete = true;
        let mut provider_route_matches = 0usize;
        let mut capture_bounds_complete = true;
        let mut maps_complete = true;
        'routes: for (graph_index, graph) in self.solved.data.candidate_graph.iter().enumerate() {
            for (route, item) in graph.routes.iter().enumerate() {
                if item.use_id.occurrence() != callee { continue; }
                provider_route_matches += 1;
                let context_use = item.retained.observed_context_use();
                let mut push_capture = |kind, ordinal, relation, map_name, record: &'a dyn std::fmt::Debug| {
                    if captures.len() == cap { return false; }
                    captures.push(CandidateProviderCaptureRow {
                        graph_index, route_owner: CandidateReplayRouteOwner::Module, route,
                        route_occurrence: item.use_id.occurrence(), context_use, relation,
                        ordinal, kind, map_name, record,
                    });
                    true
                };
                if !push_capture(CandidateProviderCaptureKind::CaptureGraph, route, None, None, &item.graph) {
                    provider_route_complete = false;
                    capture_bounds_complete = false;
                    maps_complete = false;
                    break 'routes;
                }
                item.retained.observe_maps(|name, record| {
                    if !push_capture(CandidateProviderCaptureKind::FreshUseMap, route, None, Some(name), record) { maps_complete = false; }
                });
                for (ordinal, bound) in item.graph.bounds.iter().enumerate() {
                    if !bound.relation.is_some_and(|relation| reachable[graph_index].contains(&relation)) { continue; }
                    if !push_capture(CandidateProviderCaptureKind::CapturedBound, ordinal, bound.relation.map(|id| id.0 as usize), None, bound) {
                        capture_bounds_complete = false;
                        provider_route_complete = false;
                        maps_complete = false;
                        break 'routes;
                    }
                }
                for (ordinal, snapshot) in item.graph.bound_evidence.iter().enumerate() {
                    if !push_capture(CandidateProviderCaptureKind::CaptureSnapshot, ordinal, None, None, snapshot) {
                        capture_bounds_complete = false;
                        provider_route_complete = false;
                        maps_complete = false;
                        break 'routes;
                    }
                }
            }
        }
        provider_route_complete &= provider_route_matches > 0;
        capture_bounds_complete &= origins_complete && facts_complete;
        if provider_route_matches == 0 { capture_bounds_complete = false; maps_complete = false; }
        Ok(CandidateSourceProviderObservation {
            facts, origins, dependencies, captures, consumer, facts_complete, origins_complete,
            dependencies_complete, provider_route_complete, provider_route_matches,
            capture_bounds_complete, maps_complete,
            direct_source_drain_attribution: CandidateSourceAttributionStatus::Unknown,
            captures_structured: false,
            maps_structured: false,
            consumer_relation_join_complete: false,
        })
    }
    /// Indexed by original formal registration, including Value formals whose
    /// computation source plan is absent. Observation borrows constructor outputs
    /// and adds no solver state or independent Function/AE/FreshUse validation.
    pub fn computation_source_plan_count(&self) -> usize { self.solved.data.candidate_calls.formals.len() }
    pub fn computation_source_plan(&self, index: usize) -> Result<Option<CandidateComputationSourcePlan<'_>>, ArtifactMismatch> {
        crate::candidate_call::observe_computation_source_plan(&self.solved.data.hir, &self.solved.data.store, &self.solved.data.candidate_calls, index)
    }
    pub fn unresolved(&self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
pub enum CandidateEffectOperand<'a> {
    OperationInterfaceMember { declaration: &'a yu_hir::shadow::SourceOperationDeclaration, owner: &'a SourceRootId, position: &'a yu_hir::shadow::SourceNodeKey, occurrence: &'a HirOccurrenceId, member: u32, effect: &'a yu_hir::shadow::SourceEffectId },
    Contribution { effect: &'a yu_hir::shadow::SourceEffectId, origin: &'a yu_hir::shadow::SourceNodeKey, instance: u32 },
    AnnotationMember { annotation: CandidateEffectAnnotation<'a>, member: u32, effect: &'a yu_hir::shadow::SourceEffectId },
}
pub struct CandidateEffectConflict<'a> {
    pub operand: CandidateEffectOperand<'a>,
    pub annotation: Option<CandidateEffectAnnotation<'a>>,
}
pub struct CandidateEffectAnnotation<'a> {
    pub owner: &'a SourceRootId,
    pub position: &'a yu_hir::shadow::SourceNodeKey,
}
/// Exact immutable leaf of the private retained graph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CandidateGraphLeaf {
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
pub struct CandidateGraphExport<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
}
impl<'a> CandidateGraphExport<'a> {
    pub fn root(&self) -> CandidateGraphNode<'a> {
        CandidateGraphNode {
            state: self.state,
            graph: self.graph,
            index: self.graph.root,
        }
    }
    pub fn node_count(&self) -> usize {
        self.graph.nodes.len()
    }
    pub fn rows(&self) -> impl Iterator<Item = CandidateGraphRow<'a>> + 'a {
        let state = self.state;
        let graph = self.graph;
        (0..graph.rows.len()).map(move |index| CandidateGraphRow { state, graph, index })
    }
    pub fn bounds(&self) -> impl Iterator<Item = CandidateGraphBound<'a>> + 'a {
        let state = self.state;
        let graph = self.graph;
        graph
            .bounds
            .iter()
            .map(move |bound| CandidateGraphBound { state, graph, bound })
    }
    pub fn unresolved(&self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
#[derive(Clone, Copy)]
pub struct CandidateGraphNode<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
    index: usize,
}
impl<'a> CandidateGraphNode<'a> {
    pub fn same_identity(self, other: Self) -> bool {
        std::ptr::eq(self.graph, other.graph) && self.index == other.index
    }
    pub fn leaf(self) -> Option<CandidateGraphLeaf> {
        use crate::candidate_scheme::{Atom, Node};
        Some(match self.graph.nodes[self.index] {
            Node::Leaf(atom) => match atom {
                Atom::Bottom => CandidateGraphLeaf::Bottom,
                Atom::Top => CandidateGraphLeaf::Top,
                Atom::NegativeBottom => CandidateGraphLeaf::NegativeBottom,
                Atom::IntPositive => CandidateGraphLeaf::IntPositive,
                Atom::UnitPositive => CandidateGraphLeaf::UnitPositive,
                Atom::BoolPositive => CandidateGraphLeaf::BoolPositive,
                Atom::StrPositive => CandidateGraphLeaf::StrPositive,
                Atom::IntNegative => CandidateGraphLeaf::IntNegative,
                Atom::UnitNegative => CandidateGraphLeaf::UnitNegative,
                Atom::BoolNegative => CandidateGraphLeaf::BoolNegative,
                Atom::StrNegative => CandidateGraphLeaf::StrNegative,
                Atom::EffectBottom => CandidateGraphLeaf::EffectBottom,
                Atom::EmptyEffect => CandidateGraphLeaf::EmptyEffect,
            },
            _ => return None,
        })
    }
    pub fn polarity(self) -> Polarity {
        use crate::candidate_scheme::{Atom, Node};
        match self.graph.nodes[self.index] {
            Node::Row { polarity, .. } | Node::Function { polarity, .. } | Node::EffectOperand { polarity, .. } => polarity,
            Node::Leaf(Atom::Bottom | Atom::IntPositive | Atom::UnitPositive | Atom::BoolPositive | Atom::StrPositive | Atom::EffectBottom) => Polarity::Positive,
            Node::Leaf(_) => Polarity::Negative,
        }
    }
    pub fn children(self) -> Option<[Self; 4]> {
        match self.graph.nodes[self.index] {
            crate::candidate_scheme::Node::Function { children, .. } => {
                Some(children.map(|index| Self {
                    state: self.state,
                    graph: self.graph,
                    index,
                }))
            }
            _ => None,
        }
    }
    pub fn row(self) -> Option<CandidateGraphRow<'a>> {
        match self.graph.nodes[self.index] {
            crate::candidate_scheme::Node::Row { row, .. } => Some(CandidateGraphRow {
                state: self.state,
                graph: self.graph,
                index: row,
            }),
            _ => None,
        }
    }
}
impl PartialEq for CandidateGraphNode<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.graph, other.graph) && self.index == other.index
    }
}
impl Eq for CandidateGraphNode<'_> {}
impl Hash for CandidateGraphNode<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::from_ref(self.graph).hash(state);
        self.index.hash(state);
    }
}
#[derive(Clone, Copy)]
pub struct CandidateGraphRow<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
    index: usize,
}
impl CandidateGraphRow<'_> {
    pub fn kind(self) -> ComponentKind {
        self.graph.rows[self.index].key.kind()
    }
    pub fn is_local(self) -> bool {
        self.graph.rows[self.index].local
    }
    pub fn same_identity(self, other: Self) -> bool {
        std::ptr::eq(self.state, other.state)
            && self.state.intrusion.rep(self.graph.rows[self.index].key)
                == other.state.intrusion.rep(other.graph.rows[other.index].key)
    }
}
impl PartialEq for CandidateGraphRow<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.state, other.state)
            && self.state.intrusion.rep(self.graph.rows[self.index].key)
                == other.state.intrusion.rep(other.graph.rows[other.index].key)
    }
}
impl Eq for CandidateGraphRow<'_> {}
impl Hash for CandidateGraphRow<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::from_ref(self.state).hash(state);
        self.state
            .intrusion
            .rep(self.graph.rows[self.index].key)
            .hash(state);
    }
}
pub struct CandidateGraphBound<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    graph: &'a crate::candidate_scheme::Graph,
    bound: &'a crate::candidate_scheme::Bound,
}
impl<'a> CandidateGraphBound<'a> {
    pub fn kind(&self) -> ComponentKind {
        self.bound.kind
    }
    pub fn lower(&self) -> CandidateGraphNode<'a> {
        CandidateGraphNode {
            state: self.state,
            graph: self.graph,
            index: self.bound.lower,
        }
    }
    pub fn upper(&self) -> CandidateGraphNode<'a> {
        CandidateGraphNode {
            state: self.state,
            graph: self.graph,
            index: self.bound.upper,
        }
    }
}
pub struct CandidateGraphFreshUse<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    occurrence: &'a HirOccurrenceId,
    rows: &'a [crate::candidate_scheme::RowKey],
    graph: &'a crate::candidate_scheme::Graph,
}
impl<'a> CandidateGraphFreshUse<'a> {
    pub fn occurrence(&self) -> &'a HirOccurrenceId {
        self.occurrence
    }
    pub fn rows(&self) -> impl Iterator<Item = CandidateGraphFreshRow<'a>> + 'a {
        let state = self.state;
        let rows = self.rows;
        let graph = self.graph;
        (0..rows.len()).map(move |index| CandidateGraphFreshRow {
            state,
            rows,
            graph,
            index,
        })
    }
    pub fn unresolved(&self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
pub struct CandidateGraphFreshRow<'a> {
    state: &'a crate::candidate_scheme::GraphState,
    rows: &'a [crate::candidate_scheme::RowKey],
    graph: &'a crate::candidate_scheme::Graph,
    index: usize,
}
impl<'a> CandidateGraphFreshRow<'a> {
    pub fn source_row(&self) -> CandidateGraphRow<'a> {
        CandidateGraphRow {
            state: self.state,
            graph: self.graph,
            index: self.index,
        }
    }
    pub fn kind(&self) -> ComponentKind {
        self.rows[self.index].kind()
    }
    pub fn same_identity(&self, other: &Self) -> bool {
        std::ptr::eq(self.state, other.state)
            && self.state.intrusion.rep(self.rows[self.index]) == other.state.intrusion.rep(other.rows[other.index])
    }
}
/// Borrowed retained candidate solver relation only. All semantic premises
/// remain unresolved; this does not establish source typing or admission.
#[derive(Clone, Copy)]
pub struct CandidateApplyFactObservation<'a> {
    edge: &'a ProvenanceEdge,
    fact: &'a SemanticFact,
    call: &'a CandidateCall,
}
impl<'a> CandidateApplyFactObservation<'a> {
    pub fn edge(self) -> &'a ProvenanceEdge {
        self.edge
    }
    pub fn fact(self) -> &'a SemanticFact {
        self.fact
    }
    pub fn unresolved(self) -> &'static [UnresolvedPremise] {
        self.call.unresolved
    }
}
pub struct CandidateExport<'a> {
    pub unresolved: &'static [UnresolvedPremise],
    pub value: SolvedValue,
    scheme: crate::shadow_f5::ClosedSchemeRef<'a>,
}
impl<'a> CandidateExport<'a> {
    /// Exact borrowed scheme behind this candidate value observation.
    pub fn scheme(&self) -> crate::shadow_f5::ClosedSchemeRef<'a> {
        self.scheme
    }
    /// Whole four-port observation under the named unresolved effect model.
    pub fn endpoints(&self) -> yu_types::ClosedValueSchemeView<'_> {
        self.scheme.endpoints()
    }
}
/// Collection-owned identity retained before the batch is consumed.
struct CandidateDefinitionUse {
    record: DefinitionUse,
    target_root: DefinitionRootId,
    receiving_root: SourceRootId,
}

/// Borrowed current module Name use. No source typing or export transport follows.
#[derive(Clone, Copy)]
pub struct CandidateDefinitionUseRef<'a> {
    observation: &'a CandidateValueObservation,
    retained: &'a CandidateDefinitionUse,
    target: crate::shadow_f5::ClosedSchemeRef<'a>,
    receiving: crate::shadow_f5::ClosedSchemeRef<'a>,
}
impl<'a> CandidateDefinitionUseRef<'a> {
    pub fn occurrence(self) -> &'a HirOccurrenceId {
        self.retained.record.id().occurrence()
    }
    pub fn same_identity(self, other: Self) -> bool {
        self.retained.record.id() == other.retained.record.id()
    }
    pub fn target_scheme(self) -> crate::shadow_f5::ClosedSchemeRef<'a> {
        self.target
    }
    pub fn receiving_scheme(self) -> crate::shadow_f5::ClosedSchemeRef<'a> {
        self.receiving
    }
    /// Actual receiving-root candidate observation from this same solve.
    /// This does not establish semantic source typing or export transport.
    pub fn receiving_export(self) -> Result<CandidateExport<'a>, ArtifactMismatch> {
        self.observation.export(self.retained.receiving_root.definition_root().ok_or(ArtifactMismatch)?)
    }
    pub fn fresh_instantiation(self) -> crate::shadow_f5::FreshCaptureState<'a> {
        self.target.fresh_capture(
            self.retained.record.id(),
            self.retained.record.target(),
            true,
        )
    }
    /// Exact retained store causes; an empty inventory supplies no invented fact.
    pub fn provenance_causes(self) -> impl Iterator<Item = &'a CauseId> + 'a {
        self.observation
            .solved
            .store
            .provenance()
            .iter()
            .map(|edge| edge.cause())
            .filter(move |cause| cause.occurrence().occurrence() == self.occurrence())
    }
    pub fn unresolved(self) -> &'static [UnresolvedPremise] {
        UNRESOLVED
    }
}
/// Historical row identity within this candidate's ordinary use substitution.
pub struct CandidateFreshRow<'a> {
    capture: &'a ShadowFreshCapture,
    use_id: &'a DefinitionUseId,
    row: u32,
    binder: crate::shadow_f5::FreshBinderRef<'a>,
}
impl<'a> CandidateFreshRow<'a> {
    pub fn source_binder(&self) -> crate::shadow_f5::FreshBinderRef<'a> {
        self.binder
    }
    pub fn source_use(&self) -> &HirOccurrenceId {
        self.use_id.occurrence()
    }
    pub fn same_identity(&self, other: &Self) -> bool {
        std::ptr::eq(self.capture, other.capture) && self.row == other.row
    }
}
impl CandidateValueObservation {
    pub fn solve(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        let mut calls = Vec::new();
        let mut permitted_errors = HashSet::new();
        // Preflight bounds recursive emission without consuming the native stack.
        // Only retained HIR shapes are admitted; no CST reconstruction occurs.
        for item in hir.items() {
            if let HirItem::Binding(binding) = item {
                if let Some(local) = hir
                    .shadow_local_binding(binding.definition_root())
                    .map_err(|_| CandidateError::Unsupported)?
                {
                    preflight_local_binding(
                        &hir,
                        binding.value(),
                        local,
                        &mut calls,
                        &mut permitted_errors,
                    )?;
                    continue;
                }
            }
            let expr = match item {
                HirItem::Binding(b) => b.value(),
                HirItem::Expression(e) if matches!(e, ResolvedExpr::Integer { .. }) => e,
                _ => return Err(CandidateError::Unsupported),
            };
            preflight_expression(expr, Some(&mut calls), &mut permitted_errors)?;
        }
        if hir.errors().iter().any(|e| {
            !permitted_errors.contains(&e.id()) || e.kind() != HirErrorKind::UnsupportedExpression
        }) {
            return Err(CandidateError::Unsupported);
        }
        let batch = ConstraintBatch::collect_mode(hir, true).map_err(CandidateError::Collection)?;
        if batch
            .scc_plan()
            .components_in_dependency_first_order()
            .any(|c| {
                !batch
                    .scc_plan()
                    .internal_uses(c)
                    .expect("owned SCC")
                    .is_empty()
            })
        {
            return Err(CandidateError::Unsupported);
        }
        let definition_uses = batch
            .definition_uses()
            .iter()
            .map(|record| CandidateDefinitionUse {
                record: record.clone(),
                target_root: batch.definitions[record.target().ordinal() as usize]
                    .root
                    .clone(),
                receiving_root: match record.parent() {
                    SourceReceiver::Definition(parent) => SourceRootId::Definition(batch.definitions[parent.ordinal() as usize].root.clone()),
                    SourceReceiver::Expression(root) => SourceRootId::Expression(root.clone()),
                },
            })
            .collect();
        // Slot zero also belongs to Group recipes; retain the relation kind
        // before consuming the batch rather than inferring it from store terms.
        let apply_recipe_occurrences = batch
            .candidate_recipes
            .iter()
            .filter(|recipe| matches!(recipe.relation, CandidateRelation::Apply { .. }))
            .map(|recipe| recipe.occurrence.clone())
            .collect();
        let solved =
            SolvedModule::solve_with_shadow_fresh_capture(batch).map_err(CandidateError::Solve)?;
        Ok(Self {
            solved,
            calls,
            definition_uses,
            apply_recipe_occurrences,
        })
    }
    /// Tests the exact retained HIR instance even when it has no module uses.
    pub fn observes_hir(&self, hir: &HirModule) -> bool {
        std::ptr::eq(self.solved.hir.as_ref(), hir)
    }
    /// Borrows the retained startup row for this candidate's exact HIR parameter.
    /// `FreshRowRef::same_identity` compares it with retained generalization
    /// origins without assigning source meaning or successor ownership.
    pub fn parameter_row(
        &self,
        parameter: &HirParameterId,
    ) -> Result<crate::shadow_f5::ParameterRowState<'_>, yu_hir::shadow::SourceIdentityError> {
        self.solved.shadow_parameter_row(parameter)
    }
    /// Ordinary incoming source-use substitution; aliases receive one route,
    /// with no second candidate-specific freshening.
    pub fn fresh_rows(&self, occurrence: &HirOccurrenceId) -> Option<Vec<CandidateFreshRow<'_>>> {
        let use_observation = self.definition_use(occurrence)?;
        let crate::shadow_f5::FreshCaptureState::Captured(instantiation) =
            use_observation.fresh_instantiation()
        else {
            return None;
        };
        let capture = self.solved.shadow_fresh_capture.as_ref()?;
        let route = &capture.routes[*capture
            .positions
            .get(use_observation.retained.record.id())?];
        Some(
            route
                .rows
                .iter()
                .zip(instantiation.bindings())
                .map(|((_, _, row), (binder, _))| CandidateFreshRow {
                    capture,
                    use_id: &route.use_id,
                    row: *row,
                    binder,
                })
                .collect(),
        )
    }
    /// Non-module occurrences have no definition use; capture availability is a
    /// separate state on a validated module use, including zero-binder routes.
    pub fn definition_use(
        &self,
        occurrence: &HirOccurrenceId,
    ) -> Option<CandidateDefinitionUseRef<'_>> {
        let retained = self
            .definition_uses
            .iter()
            .find(|u| u.record.occurrence() == occurrence)?;
        if retained.record.id() != retained.record.cause().id()
            || retained.record.id().occurrence() != retained.record.occurrence()
            || !self.solved.hir.owns_occurrence(occurrence)
        {
            return None;
        }
        let schemes = self.solved.shadow_closed_schemes();
        Some(CandidateDefinitionUseRef {
            observation: self,
            retained,
            target: schemes.for_root(&retained.target_root).ok()?,
            receiving: schemes.for_root(retained.receiving_root.definition_root()?).ok()?,
        })
    }
    pub fn definition_uses(&self) -> impl Iterator<Item = CandidateDefinitionUseRef<'_>> {
        self.definition_uses
            .iter()
            .filter_map(|u| self.definition_use(u.record.occurrence()))
    }
    pub fn calls(&self) -> &[CandidateCall] {
        &self.calls
    }
    /// Observes only an exact retained call from this solve and its Apply recipe.
    /// Missing or ambiguous provenance/facts fail closed. This borrowed solver
    /// relation leaves every call premise unresolved and performs no solving.
    pub fn apply_fact(&self, call: &CandidateCall) -> Option<CandidateApplyFactObservation<'_>> {
        let mut calls = self.calls.iter().filter(|owned| std::ptr::eq(*owned, call));
        let call = calls.next()?;
        if calls.next().is_some()
            || self
                .apply_recipe_occurrences
                .iter()
                .filter(|occurrence| *occurrence == &call.occurrence)
                .count()
                != 1
        {
            return None;
        }
        let mut edges = self.solved.store.provenance().iter().filter(|edge| {
            edge.cause().occurrence().occurrence() == &call.occurrence
                && edge.cause().occurrence().local_slot() == 0
        });
        let edge = edges.next()?;
        if edges.next().is_some() {
            return None;
        }
        let mut facts = self
            .solved
            .store
            .facts()
            .iter()
            .filter(|fact| fact.id() == edge.fact());
        let fact = facts.next()?;
        if facts.next().is_some() {
            return None;
        }
        Some(CandidateApplyFactObservation { edge, fact, call })
    }
    /// Candidate conflicts never establish source rejection.
    pub fn candidate_conflicts(&self) -> &[SolverError] {
        self.solved.errors()
    }
    pub fn export(&self, root: &DefinitionRootId) -> Result<CandidateExport<'_>, ArtifactMismatch> {
        Ok(CandidateExport {
            unresolved: UNRESOLVED,
            value: self.solved.root_value_for(root)?,
            scheme: self.solved.shadow_closed_schemes().for_root(root)?,
        })
    }
}
// The HIR owner already restricted this carrier to the approved source fixture.
// Validate its lexical incidences before allocating any candidate solver state.
fn preflight_local_binding(
    hir: &HirModule,
    expr: &ResolvedExpr,
    local: &yu_hir::shadow::ShadowLocalBind,
    calls: &mut Vec<CandidateCall>,
    permitted_errors: &mut HashSet<yu_hir::HirErrorId>,
) -> Result<(), CandidateError> {
    let ResolvedExpr::Lambda {
        parameter: outer,
        body: placeholder,
        ..
    } = expr
    else {
        return Err(CandidateError::Unsupported);
    };
    let ResolvedExpr::Error {
        errors: placeholder_errors,
        ..
    } = placeholder.as_ref()
    else {
        return Err(CandidateError::Unsupported);
    };
    let ResolvedExpr::Lambda {
        parameter: inner,
        body,
        ..
    } = &local.initializer
    else {
        return Err(CandidateError::Unsupported);
    };
    let ResolvedExpr::Apply {
        occurrence,
        callee,
        argument,
        errors,
        ..
    } = body.as_ref()
    else {
        return Err(CandidateError::Unsupported);
    };
    if outer == inner
        || local.captures.as_ref() != std::slice::from_ref(outer)
        || local.continuation.local != local.local
        || hir
            .shadow_parameter_local_owner(inner)
            .map_err(|_| CandidateError::Unsupported)?
            != Some(&local.local)
        || !matches!(callee.as_ref(), ResolvedExpr::Name { resolution: NameResolution::Parameter(p), .. } if p == outer)
        || !matches!(argument.as_ref(), ResolvedExpr::Name { resolution: NameResolution::Parameter(p), .. } if p == inner)
        || errors != placeholder_errors
    {
        return Err(CandidateError::Unsupported);
    }
    permitted_errors
        .try_reserve(errors.len())
        .map_err(|_| CandidateError::Unsupported)?;
    permitted_errors.extend(errors.iter().copied());
    reserve_call_inventory(calls)?;
    calls.push(CandidateCall {
        occurrence: occurrence.clone(),
        callee: callee.occurrence().clone(),
        argument: argument.occurrence().clone(),
        unresolved: UNRESOLVED,
    });
    Ok(())
}
#[cfg(test)]
thread_local! {
    static FAIL_CALL_INVENTORY_RESERVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
fn reserve_call_inventory(calls: &mut Vec<CandidateCall>) -> Result<(), CandidateError> {
    #[cfg(test)]
    if FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.replace(false)) {
        return Err(CandidateError::Unsupported);
    }
    calls.try_reserve(1).map_err(|_| CandidateError::Unsupported)
}
fn preflight_expression(
    expr: &ResolvedExpr,
    mut calls: Option<&mut Vec<CandidateCall>>,
    permitted_errors: &mut HashSet<yu_hir::HirErrorId>,
) -> Result<(), CandidateError> {
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| CandidateError::Unsupported)?;
    pending.push((Some(expr), 1usize));
    let mut formals = Vec::new();
    while let Some((expr, depth)) = pending.pop() {
        let Some(expr) = expr else {
            formals.pop();
            continue;
        };
        if depth > 128 {
            return Err(CandidateError::Unsupported);
        }
        pending
            .try_reserve(2)
            .map_err(|_| CandidateError::Unsupported)?;
        match expr {
            ResolvedExpr::Integer { .. }
            | ResolvedExpr::Name {
                resolution: NameResolution::Resolved(_),
                ..
            } => {}
            ResolvedExpr::Name {
                resolution: NameResolution::Parameter(p),
                ..
            } if formals.contains(&p) => {}
            ResolvedExpr::Group { inner, .. } => pending.push((Some(inner), depth + 1)),
            ResolvedExpr::Apply {
                occurrence,
                callee,
                argument,
                errors,
                ..
            } => {
                permitted_errors
                    .try_reserve(errors.len())
                    .map_err(|_| CandidateError::Unsupported)?;
                permitted_errors.extend(errors.iter().copied());
                if let Some(calls) = calls.as_deref_mut() {
                    reserve_call_inventory(calls)?;
                    calls.push(CandidateCall {
                        occurrence: occurrence.clone(),
                        callee: callee.occurrence().clone(),
                        argument: argument.occurrence().clone(),
                        unresolved: UNRESOLVED,
                    });
                }
                pending.push((Some(argument), depth + 1));
                pending.push((Some(callee), depth + 1));
            }
            ResolvedExpr::Lambda {
                parameter, body, ..
            } => {
                formals
                    .try_reserve(1)
                    .map_err(|_| CandidateError::Unsupported)?;
                formals.push(parameter);
                pending.push((None, depth));
                pending.push((Some(body.as_ref()), depth + 1));
            }
            _ => return Err(CandidateError::Unsupported),
        }
    }
    Ok(())
}

pub(super) type CandidateEndpoint = LambdaValueEndpoint;
#[derive(Clone, Debug)]
pub(super) enum CandidateRelation {
    Group {
        child: CandidateEndpoint,
        child_effect: usize,
        result: usize,
        result_effect: usize,
    },
    Apply {
        callee: CandidateEndpoint,
        callee_effect: usize,
        argument: CandidateEndpoint,
        argument_effect: usize,
        result: usize,
        result_effect: usize,
    },
}
#[derive(Clone, Debug)]
pub(super) struct CandidateConstraintRecipe {
    pub(super) occurrence: HirOccurrenceId,
    pub(super) relation: CandidateRelation,
    pub(super) after_collected_fact: usize,
    pub(super) source_input: Option<usize>,
}
impl ConstraintBatch {
    pub(super) fn emit_candidate_local_value<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        local: &'a yu_hir::shadow::ShadowLocalBind,
        root: &DefinitionRootId,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        let unsupported = || CollectionAvailabilityError::MissingDefinitionEndpoint;
        let ResolvedExpr::Lambda {
            occurrence: outer_occurrence,
            parameter: outer,
            ..
        } = expr
        else {
            return Err(unsupported());
        };
        let ResolvedExpr::Lambda {
            occurrence: inner_occurrence,
            parameter: inner,
            body,
            ..
        } = &local.initializer
        else {
            return Err(unsupported());
        };
        let ResolvedExpr::Apply {
            occurrence,
            callee,
            argument,
            ..
        } = body.as_ref()
        else {
            return Err(unsupported());
        };
        self.parameter_recipes
            .try_reserve(2)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let outer_position = self.parameter_recipes.len();
        self.parameter_recipes.push(outer.clone());
        let inner_position = self.parameter_recipes.len();
        self.parameter_recipes.push(inner.clone());
        // The capture is the actual outer row, not a fresh local Name use.
        let mut formals = Vec::new();
        formals
            .try_reserve(2)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        formals.push(outer_position);
        formals.push(inner_position);
        let (callee, callee_effect) =
            self.emit_candidate_expression(callee, &mut formals, parent, uses)?;
        let (argument, argument_effect) =
            self.emit_candidate_expression(argument, &mut formals, parent, uses)?;
        let call = self.candidate_component(occurrence)?;
        self.retain_candidate_relation(
            occurrence,
            CandidateRelation::Apply {
                callee,
                callee_effect,
                argument,
                argument_effect,
                result: call.value,
                result_effect: call.effect,
            },
        )?;
        self.occurrence_component(inner_occurrence.clone(), ComponentKind::Value)?;
        self.occurrence_component(inner_occurrence.clone(), ComponentKind::Effect)?;
        let inner_value = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        self.occurrence_component_positions
            .insert(inner_occurrence.clone(), inner_value);
        self.candidate_local_lambda_effect(inner_occurrence, inner_value.effect)?;
        self.retain_candidate_local_lambda(
            inner_occurrence,
            inner_position,
            inner_value.value,
            call.value,
            call.effect,
            inner_value.effect,
        )?;
        // The terminal local reference reuses its initializer's endpoint,
        // just as a formal reference reuses its row. No proxy bound, call,
        // local generalization or freshening is introduced by returning it.
        self.occurrence_component(outer_occurrence.clone(), ComponentKind::Effect)?;
        let outer_effect = self.components.len() - 1;
        self.candidate_local_lambda_effect(outer_occurrence, outer_effect)?;
        self.retain_candidate_local_lambda(
            outer_occurrence,
            outer_position,
            self.root_component_positions[root].component,
            inner_value.value,
            inner_value.effect,
            outer_effect,
        )
    }
    pub(super) fn candidate_local_lambda_effect(
        &mut self,
        occurrence: &HirOccurrenceId,
        position: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        let effect = self.component_term_at(position);
        let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(occurrence.clone(), 0, bottom, effect)?;
        self.emit(occurrence.clone(), 1, effect, empty)
    }
    pub(super) fn retain_candidate_local_lambda(
        &mut self,
        occurrence: &HirOccurrenceId,
        parameter_position: usize,
        root_component: usize,
        body_value_component: usize,
        body_effect_component: usize,
        lambda_effect_component: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        self.lambda_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.lambda_recipes.push(LambdaRecipe {
            occurrence: occurrence.clone(),
            parameter_position,
            formal_registration: None,
            root_component,
            body_value_endpoint: LambdaValueEndpoint::Component(body_value_component),
            body_effect_component,
            lambda_effect_component,
            after_collected_fact: self.occurrences.len(),
        });
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(if self.candidate_graph_effects { 3 } else { 1 })
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(if self.candidate_graph_effects { 3 } else { 1 })
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        Ok(())
    }
    pub(super) fn candidate_component(
        &mut self,
        occurrence: &HirOccurrenceId,
    ) -> Result<ComponentPositions, CollectionAvailabilityError> {
        self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
        self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        self.occurrence_component_positions
            .insert(occurrence.clone(), positions);
        if !self.candidate_graph_effects {
            self.candidate_pure_effect(occurrence, positions.effect)?;
        }
        Ok(positions)
    }
    fn candidate_pure_effect(
        &mut self,
        occurrence: &HirOccurrenceId,
        position: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        // These bounds belong only to CandidatePureEffectModelUnresolved.
        let effect = self.component_term_at(position);
        let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(occurrence.clone(), 1, bottom, effect)?;
        self.emit(occurrence.clone(), 2, effect, empty)
    }
    pub(super) fn retain_candidate_relation(
        &mut self,
        occurrence: &HirOccurrenceId,
        relation: CandidateRelation,
    ) -> Result<(), CollectionAvailabilityError> {
        self.candidate_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let fact_count = if self.candidate_graph_effects {
            match &relation {
                CandidateRelation::Group { .. } => 2,
                CandidateRelation::Apply { .. } => 3,
            }
        } else {
            1
        };
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(fact_count)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(fact_count)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.candidate_recipes.push(CandidateConstraintRecipe {
            occurrence: occurrence.clone(),
            relation,
            after_collected_fact: self.occurrences.len(),
            source_input: None,
        });
        Ok(())
    }
    pub(super) fn emit_candidate_value<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        root: Option<&DefinitionRootId>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        let mut formals = Vec::new();
        if matches!(expr, ResolvedExpr::Lambda { .. }) {
            let root = root.ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
            self.emit_candidate_lambda(
                expr,
                self.root_component_positions[root].component,
                &mut formals,
                parent,
                uses,
            )?;
        } else {
            let (value, _) = self.emit_candidate_expression(expr, &mut formals, parent, uses)?;
            if let Some(root) = root {
                let CandidateEndpoint::Component(position) = value else {
                    return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
                };
                let component = self.root_value_component_for_collect(root)?;
                self.emit(
                    expr.occurrence().clone(),
                    10,
                    self.component_term_at(position),
                    self.term_for_component(&component),
                )?;
            }
        }
        Ok(())
    }
    fn emit_candidate_lambda<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        value_component: usize,
        formals: &mut Vec<usize>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<usize, CollectionAvailabilityError> {
        let ResolvedExpr::Lambda {
            occurrence,
            parameter,
            body,
            ..
        } = expr
        else {
            return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
        };
        self.parameter_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        formals
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        let parameter_position = self.parameter_recipes.len();
        self.parameter_recipes.push(parameter.clone());
        formals.push(parameter_position);
        let body_result = self.emit_candidate_expression(body, formals, parent, uses);
        formals.pop();
        let (value, effect) = body_result?;
        self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let lambda_effect_component = self.components.len() - 1;
        self.candidate_local_lambda_effect(occurrence, lambda_effect_component)?;
        self.lambda_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.lambda_recipes.push(LambdaRecipe {
            occurrence: occurrence.clone(),
            parameter_position,
            formal_registration: None,
            root_component: value_component,
            body_value_endpoint: value,
            body_effect_component: effect,
            lambda_effect_component,
            after_collected_fact: self.occurrences.len(),
        });
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(if self.candidate_graph_effects { 3 } else { 1 })
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(if self.candidate_graph_effects { 3 } else { 1 })
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        Ok(lambda_effect_component)
    }
    fn emit_candidate_expression<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        formals: &mut Vec<usize>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(CandidateEndpoint, usize), CollectionAvailabilityError> {
        let occurrence = expr.occurrence();
        let positions = match expr {
            ResolvedExpr::Integer { .. } => {
                self.emit_integer(occurrence.clone(), None)?;
                self.occurrence_component_positions[occurrence]
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Resolved(target),
                ..
            } => {
                self.emit_resolved_binding_name(occurrence.clone(), None)?;
                let old_capacity = uses.capacity();
                uses.try_reserve(1)
                    .map_err(|_| CollectionAvailabilityError::DefinitionUseIdentityExhausted)?;
                uses.push(PendingDefinitionUse {
                    parent: SourceReceiver::Definition(parent
                        .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?.clone()),
                    target,
                    occurrence: occurrence.clone(),
                });
                self.counters
                    .definition_use_endpoint_workspace_peak_capacity = self
                    .counters
                    .definition_use_endpoint_workspace_peak_capacity
                    .max(uses.capacity());
                if uses.capacity() != old_capacity {
                    self.counters
                        .definition_use_endpoint_workspace_capacity_growths += 1;
                }
                self.occurrence_component_positions[occurrence]
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Parameter(parameter),
                ..
            } => {
                let position = formals
                    .iter()
                    .rev()
                    .copied()
                    .find(|p| &self.parameter_recipes[*p] == parameter)
                    .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
                self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
                let effect = self.components.len() - 1;
                let term = self.component_term_at(effect);
                let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                self.emit(occurrence.clone(), 0, bottom, term)?;
                self.emit(occurrence.clone(), 1, term, empty)?;
                return Ok((CandidateEndpoint::Parameter(position), effect));
            }
            ResolvedExpr::Lambda { .. } => {
                self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
                let value = self.components.len() - 1;
                let effect = self.emit_candidate_lambda(expr, value, formals, parent, uses)?;
                let positions = ComponentPositions { value, effect };
                self.occurrence_component_positions
                    .insert(occurrence.clone(), positions);
                positions
            }
            ResolvedExpr::Group { inner, .. } => {
                let (child, child_effect) =
                    self.emit_candidate_expression(inner, formals, parent, uses)?;
                let positions = self.candidate_component(occurrence)?;
                self.retain_candidate_relation(
                    occurrence,
                    CandidateRelation::Group {
                        child,
                        child_effect,
                        result: positions.value,
                        result_effect: positions.effect,
                    },
                )?;
                positions
            }
            ResolvedExpr::Apply {
                callee, argument, ..
            } => {
                let (callee, callee_effect) =
                    self.emit_candidate_expression(callee, formals, parent, uses)?;
                let (argument, argument_effect) =
                    self.emit_candidate_expression(argument, formals, parent, uses)?;
                let positions = self.candidate_component(occurrence)?;
                self.retain_candidate_relation(
                    occurrence,
                    CandidateRelation::Apply {
                        callee,
                        callee_effect,
                        argument,
                        argument_effect,
                        result: positions.value,
                        result_effect: positions.effect,
                    },
                )?;
                positions
            }
            _ => return Err(CollectionAvailabilityError::MissingDefinitionEndpoint),
        };
        Ok((
            CandidateEndpoint::Component(positions.value),
            positions.effect,
        ))
    }
}
impl InferenceSession {
    pub(super) fn candidate_endpoint(
        &mut self,
        endpoint: CandidateEndpoint,
        polarity: Polarity,
    ) -> Result<Term, SolveAvailabilityError> {
        let row = match endpoint {
            CandidateEndpoint::Component(position) => self.live_components[position].ordinal,
            CandidateEndpoint::Parameter(position) => self
                .parameter_live_base
                .checked_add(
                    u32::try_from(position)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                )
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        };
        self.live_value_term(polarity, row)
    }
    pub(super) fn admit_candidate_fact(
        &mut self,
        recipe: &CandidateConstraintRecipe,
    ) -> Result<(), SolveAvailabilityError> {
        if let Some(source_input) = recipe.source_input {
            let input = self.batch.candidate_calls.calls.get(source_input)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            let registered_recipe = self.batch.candidate_recipes.get(input.recipe)
                .ok_or(SolveAvailabilityError::IdentityExhausted)?;
            if self.batch.candidate_source.scoped_experiment {
                let graph = self.candidate_graph.as_ref().ok_or(SolveAvailabilityError::IdentityExhausted)?;
                crate::candidate_call::authenticate_scoped_apply(&self.batch.hir, input, graph)
                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
            }
            let CandidateRelation::Apply {
                callee, callee_effect, argument, argument_effect, result, result_effect,
            } = recipe.relation else { return Err(SolveAvailabilityError::IdentityExhausted); };
            if registered_recipe.source_input != Some(source_input)
                || registered_recipe.occurrence != recipe.occurrence
                || input.checking.occurrence() != &recipe.occurrence
                || !crate::candidate_call::same_endpoint(input.callee_value, callee)
                || !crate::candidate_call::same_endpoint(input.argument_value, argument)
                || input.callee_effect != callee_effect || input.argument_effect != argument_effect
                || input.result != result || input.application_effect != result_effect
            { return Err(SolveAvailabilityError::IdentityExhausted); }
        }
        let mut invocation_effect = None;
        let (lower, upper) = match recipe.relation {
            CandidateRelation::Group { child, result, .. } => (
                self.candidate_endpoint(child, Polarity::Positive)?,
                self.candidate_endpoint(CandidateEndpoint::Component(result), Polarity::Negative)?,
            ),
            CandidateRelation::Apply {
                callee,
                argument,
                argument_effect,
                result,
                result_effect,
                ..
            } => {
                let callee = self.candidate_endpoint(callee, Polarity::Positive)?;
                let argument = self.candidate_endpoint(argument, Polarity::Positive)?;
                let result = self
                    .candidate_endpoint(CandidateEndpoint::Component(result), Polarity::Negative)?;
                let (argument_effect, return_effect) = if self.batch.candidate_graph_effects {
                    let EffectEndpointKey::EffectRow(application_row) = self.canonical_effect(EffectEndpointKey::EffectRow(self.live_components[result_effect].ordinal)) else { unreachable!() };
                    let level = self.effect_levels[application_row as usize];
                    let row = self.fresh_effect_at_level(level)?;
                    invocation_effect = Some(row);
                    (
                        self.live_effect_term(
                            Polarity::Positive,
                            self.live_components[argument_effect].ordinal,
                        )?,
                        self.live_effect_term(Polarity::Negative, row)?,
                    )
                } else {
                    (
                        self.batch.collected_leaf_term(Leaf::EffectBottomPositive),
                        self.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    )
                };
                let demand =
                    self.negative_function_term(argument, argument_effect, return_effect, result)?;
                if let Some(source_input) = recipe.source_input {
                    let row = invocation_effect.ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    let application_effect = self.live_effect_term(
                        Polarity::Negative, self.live_components[result_effect].ordinal,
                    )?;
                    let CandidateRelation::Apply { callee_effect, .. } = recipe.relation
                        else { return Err(SolveAvailabilityError::IdentityExhausted); };
                    let callee_effect = self.live_effect_term(
                        Polarity::Positive, self.live_components[callee_effect].ordinal,
                    )?;
                    // Join the original source registration, never a solved endpoint or scope.
                    // This is retained before constraint admission and has no semantic consumer.
                    let source_call = &self.batch.candidate_calls.calls[source_input];
                    let introduction = if let Some(name_index) = source_call.formal_name {
                        let name = &self.batch.candidate_calls.names[name_index];
                        let registration = &self.batch.candidate_calls.formals[name.registration];
                        let source = self.batch.hir.local_source_for(&registration.owner)
                            .map_err(|_| SolveAvailabilityError::IdentityExhausted)?
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let lambda = source.expressions().get(registration.lambda)
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        self.batch.candidate_source.omitted_formals.get(&lambda.occurrence)
                            .map(|omitted| crate::candidate_call::DirectionalIntroduction {
                                registration: name.registration, name: name_index,
                                omitted: omitted.clone(), checking: source_call.checking.clone(),
                                cause: source_call.cause.clone(), demand,
                                field: FunctionField::ResultEffect, effect: return_effect, row,
                            })
                    } else { None };
                    let input = self.batch.candidate_calls.calls.get_mut(source_input)
                        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    if input.checking.occurrence() != &recipe.occurrence || input.native.is_some() {
                        return Err(SolveAvailabilityError::IdentityExhausted);
                    }
                    input.introduction = introduction;
                    input.native = Some(crate::candidate_call::NativeInterface {
                        callee, argument, callee_effect, argument_effect, result, demand,
                        invocation_effect: return_effect, invocation_row: row, application_effect,
                    });
                }
                (callee, demand)
            }
        };
        let id = ConstraintOccurrenceId::new(recipe.occurrence.clone(), 0);
        let occurrence = ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower,
            upper,
        };
        self.store
            .admit_and_record_provenance(&occurrence)
            .map_err(SolveAvailabilityError::from)?;
        let key = CanonicalValuePairKey {
            lower: self.value_endpoint(lower, Polarity::Positive),
            upper: self.value_endpoint(upper, Polarity::Negative),
        };
        let transitions = self.constrain_live_value(key, &occurrence.id, &occurrence.cause)?;
        #[cfg(test)]
        {
            self.initial_value_pair_probes += 1;
            self.summary_false_to_true_transitions += transitions;
        }
        #[cfg(not(test))]
        let _ = transitions;
        if self.batch.candidate_graph_effects {
            match recipe.relation {
                CandidateRelation::Group {
                    child_effect,
                    result_effect,
                    ..
                } => {
                    self.admit_candidate_effect(
                        recipe,
                        1,
                        self.live_components[child_effect].ordinal,
                        self.live_components[result_effect].ordinal,
                    )?;
                }
                CandidateRelation::Apply {
                    callee_effect,
                    result_effect,
                    ..
                } => {
                    let result = self.live_components[result_effect].ordinal;
                    self.admit_candidate_effect(
                        recipe,
                        1,
                        self.live_components[callee_effect].ordinal,
                        result,
                    )?;
                    self.admit_candidate_effect(
                        recipe,
                        2,
                        invocation_effect.expect("graph Apply allocates its invocation effect"),
                        result,
                    )?;
                }
            }
        }
        self.sample_f4_resources(ResourceBoundary::InitialAdmission)
    }

    fn admit_candidate_effect(
        &mut self,
        recipe: &CandidateConstraintRecipe,
        slot: u8,
        lower: u32,
        upper: u32,
    ) -> Result<(), SolveAvailabilityError> {
        let id = ConstraintOccurrenceId::new(recipe.occurrence.clone(), slot);
        let occurrence = ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower: self.live_effect_term(Polarity::Positive, lower)?,
            upper: self.live_effect_term(Polarity::Negative, upper)?,
        };
        self.store
            .admit_and_record_provenance(&occurrence)
            .map_err(SolveAvailabilityError::from)?;
        self.constrain_live_effect(
            EffectEndpointKey::EffectRow(lower),
            EffectEndpointKey::EffectRow(upper),
            &occurrence.id,
            &occurrence.cause,
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    fn module(text: &str) -> Arc<HirModule> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        Arc::new(
            yu_hir::shadow::lower_module_with_shadow_applications(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "candidate-internal",
                    "candidate.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .unwrap(),
        )
    }
    #[test]
    fn candidate_inference_does_not_reserve_historical_call_inventory() {
        struct ResetFailure;
        impl Drop for ResetFailure {
            fn drop(&mut self) {
                FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.set(false));
            }
        }
        let _reset = ResetFailure;
        let hir = module("my id x = x; my first = id 1");
        FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.set(true));
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.get()));
        let first = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "first" => {
                Some(binding.definition_root())
            }
            _ => None,
        }).unwrap();
        let export = candidate.export(first).unwrap();
        let mut pending = vec![export.root()];
        let mut visited = Vec::<CandidateGraphRow<'_>>::new();
        let mut integer = false;
        while let Some(node) = pending.pop() {
            assert_eq!(node.polarity(), Polarity::Positive);
            if let Some(leaf) = node.leaf() {
                match leaf {
                    CandidateGraphLeaf::IntPositive => integer = true,
                    CandidateGraphLeaf::Bottom => {}
                    _ => panic!("first has a non-Integer value lower bound: {leaf:?}"),
                }
                continue;
            }
            let row = node.row().expect("first value fiber contains only rows and Integer");
            assert_eq!(row.kind(), ComponentKind::Value);
            if visited.iter().any(|seen| seen.same_identity(row)) {
                continue;
            }
            visited.push(row);
            for bound in export.bounds() {
                if bound.kind() == ComponentKind::Value
                    && bound.upper().row().is_some_and(|upper| upper.same_identity(row))
                {
                    pending.push(bound.lower());
                }
            }
        }
        assert!(integer, "first's reachable value fiber retains Integer");
        assert!(FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.get()));

        // LocalSource owns source Call inputs; the expression-only fixture above
        // exercises graph inference without that separate retained input carrier.
        let source_hir = crate::candidate_lifecycle_retirement::hir(
            "my id x = x; my first = id 1",
        );
        let source_candidate = CandidateInference::solve(source_hir).unwrap();
        assert_eq!(source_candidate.source_call_count(), 1);
        assert!(source_candidate.source_call(0).is_ok());
        assert!(FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.get()));
        assert!(matches!(
            CandidateValueObservation::solve(hir.clone()),
            Err(CandidateError::Unsupported)
        ));
        assert!(!FAIL_CALL_INVENTORY_RESERVE.with(|failure| failure.get()));
        let observer = CandidateValueObservation::solve(hir).unwrap();
        assert_eq!(observer.calls().len(), 1);
        assert!(observer.apply_fact(&observer.calls()[0]).is_some());
    }
    #[test]
    fn candidate_lifecycle_retirement_keeps_borrowed_effect_handles_and_rejects_foreign_call_hir() {
        let hir = crate::candidate_lifecycle_retirement::hir("act E\nmy left x = x; my result = left 1");
        let foreign = crate::candidate_lifecycle_retirement::hir("act E\nmy left x = x; my result = left 1");
        let effect = hir.source_effect_declarations()[0].id.clone();
        let origin = effect.declaration.clone();
        let root = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "left" => Some(binding.definition_root().clone()),
            _ => None,
        }).unwrap();
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap()).unwrap();
        session.execute().unwrap();
        let operand = session.candidate_effect_contribution(effect.clone(), origin.clone()).unwrap();
        let occurrence = ConstraintOccurrenceId::new(hir.local_source(&root).unwrap().unwrap().expressions()[0].occurrence.clone(), 0);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session.constrain_live_effect(operand, EffectEndpointKey::EmptyNegative, &occurrence, &cause).unwrap();
        let candidate = CandidateInference { solved: session.finish_candidate().unwrap() };
        let kind = candidate.candidate_conflicts().iter().find_map(|error| matches!(error.kind(), SolverErrorKind::IncompatibleEffect { .. }).then_some(error.kind())).unwrap();
        let observed = candidate.effect_conflict(kind).unwrap();
        let CandidateEffectOperand::Contribution { effect: actual, origin: actual_origin, .. } = observed.operand else { panic!("actual contribution"); };
        assert_eq!((actual, actual_origin), (&effect, &origin));
        assert!(observed.annotation.is_none());
        let other = CandidateInference::solve(foreign.clone()).unwrap();
        assert!(other.effect_conflict(kind).is_err());
        assert!(crate::candidate_call::observe(&foreign, &candidate.solved.data.store, &candidate.solved.data.candidate_calls, 0).is_err());
        assert!(candidate.source_call(0).is_ok());
    }
    #[test]
    fn directional_introductions_are_exact_original_upper_result_effects() {
        for (source, expected, providers) in [
            ("my apply f = f 1; my id x = x; my good = apply id", 1, 1),
            ("my apply f = f (f 1)", 2, 0),
            ("my compose f g = { my relay x = f (g x); relay }", 2, 0),
            ("my outer cb = { my inner x = cb x; inner }", 1, 0),
            ("my apply f = { my first = f 1; my second = (f) 1; my step x = ({ f }) x; step }", 3, 0),
        ] {
            let candidate = CandidateInference::solve(crate::candidate_lifecycle_retirement::hir(source)).unwrap();
            let mut introductions = Vec::new();
            let mut absent = 0;
            for index in 0..candidate.source_call_count() {
                let call = candidate.source_call(index).unwrap();
                let Some(introduction) = call.directional_introduction() else { absent += 1; continue; };
                assert_eq!(introduction.original_demand(), call.native_demand());
                assert_eq!(introduction.result_effect(), call.native_invocation_effect());
                assert_ne!(introduction.result_effect(), call.native_application_effect());
                assert_ne!(introduction.result_effect(), call.native_argument_evaluation_effect());
                assert_ne!(introduction.result_effect(), call.native_result());
                assert_eq!(introduction.original_formal(), &call.formal_registration().unwrap().id);
                assert_eq!(introduction.checking_occurrence(), call.checking_occurrence());
                assert!(introductions.iter().all(|(checking, demand)| checking != introduction.checking_occurrence() && *demand != introduction.original_demand()));
                introductions.push((introduction.checking_occurrence().clone(), introduction.original_demand()));
            }
            assert_eq!(introductions.len(), expected, "{source}");
            assert_eq!(absent, providers, "{source}");
        }
    }
    #[test]
    fn directional_observer_rejects_wrong_field_use_and_formal() {
        let candidate = CandidateInference::solve(crate::candidate_lifecycle_retirement::hir(
            "my compose f g = { my relay x = f (g x); relay }",
        )).unwrap();
        let original = &candidate.solved.data.candidate_calls;
        assert_eq!(original.calls.len(), 2);
        for corruption in 0..4 {
            let mut state = original.clone();
            let other = state.calls[1].introduction.as_ref().unwrap().clone();
            let application_effect = state.calls[0].native.unwrap().application_effect;
            let record = state.calls[0].introduction.as_mut().unwrap();
            match corruption {
                0 => record.field = FunctionField::ArgumentEffect,
                1 => record.checking = other.checking,
                2 => record.omitted = other.omitted,
                _ => record.effect = application_effect,
            }
            assert!(crate::candidate_call::observe(
                &candidate.solved.data.hir, &candidate.solved.data.store, &state, 0,
            ).is_err());
        }
        for corrupt_registration in [false, true] {
            let mut state = original.clone();
            let record = state.calls[0].introduction.as_ref().unwrap();
            let registration = record.registration;
            let source = candidate.solved.data.hir.local_source_for(&record.omitted.owner)
                .unwrap().unwrap();
            let wrong_scope = crate::candidate_effect::AnnotationScope::Expression(source.body().clone());
            if corrupt_registration {
                state.formals[registration].scope = wrong_scope;
            } else {
                let record = state.calls[0].introduction.as_mut().unwrap();
                Arc::make_mut(&mut record.omitted).scope = wrong_scope;
            }
            assert!(crate::candidate_call::observe(
                &candidate.solved.data.hir, &candidate.solved.data.store, &state, 0,
            ).is_err());
        }
    }
    #[test]
    fn source_call_retains_registered_root_across_wrapped_and_captured_uses() {
        let hir = crate::candidate_lifecycle_retirement::hir(
            "my apply f = { my first = f 1; my second = (f) 1; my step x = ({ f }) x; step }",
        );
        let mut session = InferenceSession::try_new_candidate(
            ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap(),
        )
        .unwrap();
        let registration = &session.batch.candidate_calls.formals[0];
        assert_eq!(
            session.batch.parameter_recipes[registration.recipe_position],
            registration.parameter,
        );
        let root = registration
            .native_root
            .expect("root retained at initialization");
        assert!(
            matches!(session.store.term_view(root), Ok(TermView::LiveVariable(row))
            if row.kind() == ComponentKind::Value && row.polarity() == Polarity::Positive
                && row.ordinal() == session.parameter_live_base + registration.recipe_position as u32)
        );
        session.execute().unwrap();
        let candidate = CandidateInference {
            solved: session.finish_candidate().unwrap(),
        };
        assert_eq!(candidate.source_call_count(), 3);
        let calls: Vec<_> = (0..3).map(|i| candidate.source_call(i).unwrap()).collect();
        assert!(
            calls
                .iter()
                .all(|call| call.native_registered_root() == Some(root))
        );
        assert!(
            calls
                .iter()
                .all(|call| call.formal_registration().unwrap().id
                    == calls[0].formal_registration().unwrap().id)
        );
        assert!(calls.iter().all(|call| call.native_demand() != root));
        assert!(calls.iter().any(|call| call.native_callee() == root));
        assert!(calls.iter().any(|call| call.native_callee() != root));
        for left in 0..calls.len() {
            for right in left + 1..calls.len() {
                assert_ne!(
                    calls[left].source().occurrence,
                    calls[right].source().occurrence
                );
                assert_ne!(
                    calls[left].checking_occurrence(),
                    calls[right].checking_occurrence()
                );
            }
        }
    }
    #[test]
    fn source_call_registered_root_survives_conflicting_apply() {
        let candidate = CandidateInference::solve(crate::candidate_lifecycle_retirement::hir(
            "my apply f = f 1; my bad = apply 1",
        ))
        .unwrap();
        assert!(!candidate.candidate_conflicts().is_empty());
        assert_eq!(candidate.source_call_count(), 2);
        let calls: Vec<_> = (0..2)
            .map(|index| candidate.source_call(index).unwrap())
            .collect();
        let formal_call = calls
            .iter()
            .find(|call| call.formal_registration().is_some())
            .unwrap();
        assert_eq!(
            formal_call.native_registered_root(),
            Some(formal_call.native_callee())
        );
        assert!(calls.iter().all(|call| call.unresolved() == UNRESOLVED));
    }
    #[test]
    fn direct_source_int_application_records_int_function_conflict() {
        let candidate = CandidateInference::solve(crate::candidate_lifecycle_retirement::hir(
            "my bridge x = 1 1",
        ))
        .unwrap();
        assert!(candidate.candidate_conflicts().iter().any(|error| {
            error.kind()
                == SolverErrorKind::IncompatibleValue {
                    lower: ValueShape::Int,
                    upper: ValueShape::Function,
                }
        }));
    }
    #[test]
    fn candidate_graph_export_refuses_conflicts_and_preserves_valid_export() {
        let hir = crate::candidate_lifecycle_retirement::hir("my bridge x = 1 1");
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let root = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) => Some(binding.definition_root()),
            _ => None,
        }).unwrap();
        assert!(matches!(candidate.export(root), Err(ArtifactMismatch)));
        assert!(candidate.candidate_conflicts().iter().any(|error| {
            error.kind()
                == SolverErrorKind::IncompatibleValue {
                    lower: ValueShape::Int,
                    upper: ValueShape::Function,
                }
        }));

        let hir = crate::candidate_lifecycle_retirement::hir("my bridge x = x");
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let root = hir.items().iter().find_map(|item| match item {
            HirItem::Binding(binding) => Some(binding.definition_root()),
            _ => None,
        }).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
        assert!(candidate.export(root).is_ok());
    }

    #[test]
    fn candidate_graph_node_hashing_matches_identity() {
        let hir = crate::candidate_lifecycle_retirement::hir("my first = 1; my second = 2");
        let roots: Vec<_> = hir
            .items()
            .iter()
            .filter_map(|item| match item {
                HirItem::Binding(binding) => Some(binding.definition_root()),
                _ => None,
            })
            .collect();
        assert_eq!(roots.len(), 2);

        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let first_graph = candidate.export(roots[0]).unwrap();
        let first = first_graph.root();
        let same = first_graph.root();
        assert_eq!(first == same, first.same_identity(same));
        assert!(first == same);

        let second = candidate.export(roots[1]).unwrap().root();
        assert_eq!(first == second, first.same_identity(second));
        assert!(first != second);

        let independent = CandidateInference::solve(hir.clone()).unwrap();
        let independent = independent.export(roots[0]).unwrap().root();
        assert_eq!(first == independent, first.same_identity(independent));
        assert!(first != independent);

        let mut indices = HashMap::new();
        indices.insert(first, 0);
        indices.insert(second, 1);
        indices.insert(independent, 2);
        assert_eq!(indices.get(&same), Some(&0));
        assert_eq!(indices.len(), 3);
    }

    #[test]
    fn candidate_graph_row_hashing_matches_identity() {
        use crate::candidate_scheme::{Graph, GraphState, Row, RowKey};

        let state = GraphState::default();
        let graph = Graph {
            source_frontier: Vec::new(),
            owned_regions: Vec::new(),
            negative_functions: HashMap::new(),
            nodes: Vec::new(),
            rows: vec![
                Row { key: RowKey::Value(7), local: false },
                Row { key: RowKey::Value(7), local: true },
                Row { key: RowKey::Effect(7), local: false },
            ],
            bounds: Vec::new(),
            bound_evidence: Vec::new(),
            attachment_bundles: Vec::new(),
            attachment_spans: HashMap::new(),
            context_views: Vec::new(),
            root: 0,
            live_root: 0,
            boundary: 0,
            capture_rows: Vec::new(),
            capture_forest: state.intrusion.forest_snapshot().unwrap(),
        };
        let first = CandidateGraphRow { state: &state, graph: &graph, index: 0 };
        let repeated = CandidateGraphRow { state: &state, graph: &graph, index: 0 };
        let duplicate = CandidateGraphRow { state: &state, graph: &graph, index: 1 };
        let effect = CandidateGraphRow { state: &state, graph: &graph, index: 2 };
        assert!(first.same_identity(repeated));
        assert!(first == repeated);
        assert!(first.same_identity(duplicate));
        assert!(first == duplicate);
        assert!(first != effect, "Value and Effect row namespaces stay distinct");

        let mut indices = HashMap::new();
        indices.insert(first, 0);
        assert_eq!(indices.get(&repeated), Some(&0));
        assert_eq!(indices.get(&duplicate), Some(&0));
        indices.entry(duplicate).or_insert(1);
        assert_eq!(indices.len(), 1, "duplicate stored rows share one index");
        indices.insert(effect, 2);
        assert_eq!(indices.len(), 2);
        assert_eq!(graph.rows[first.index].local, false);
        assert_eq!(graph.rows[duplicate.index].local, true);

        let independent_state = GraphState::default();
        let independent = CandidateGraphRow {
            state: &independent_state,
            graph: &graph,
            index: 0,
        };
        assert!(!first.same_identity(independent));
        assert!(first != independent, "separate inference states stay distinct");
        indices.insert(independent, 3);
        assert_eq!(indices.len(), 3);

        let hir = crate::candidate_lifecycle_retirement::hir("my identity x = x");
        let root = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == "identity" => {
                    Some(binding.definition_root())
                }
                _ => None,
            })
            .unwrap();
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        let candidate_row = candidate.export(root).unwrap().rows().next().unwrap();
        let independent = CandidateInference::solve(hir.clone()).unwrap();
        let independent_row = independent.export(root).unwrap().rows().next().unwrap();
        assert!(!candidate_row.same_identity(independent_row));
        assert!(candidate_row != independent_row);
        let mut solve_indices = HashMap::new();
        solve_indices.insert(candidate_row, 0);
        solve_indices.insert(independent_row, 1);
        assert_eq!(solve_indices.len(), 2);
    }

    #[test]
    fn candidate_graph_row_hashing_uses_merged_representatives() {
        use crate::candidate_scheme::{Graph, Row};
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let hir = crate::candidate_lifecycle_retirement::hir(
            "my loop x = { my helper y = loop y; helper x }",
        );
        let candidate = CandidateInference::solve(hir).unwrap();
        let observation = candidate.intrusion_observation().unwrap();
        let events: Vec<_> = observation.events().collect();
        let parents: Vec<_> = observation.parents().collect();
        let selected = parents
            .iter()
            .find(|parent| {
                parent.copy.ordinal != parent.parent.ordinal
                    && parent.copy.kind == parent.parent.kind
                    && parent.copy.representative == parent.parent.representative
                    && parent.source_events.iter().any(|&event| {
                        events.get(event).is_some_and(|event| event.same_scc)
                    })
            })
            .expect("nested recursion retains a same-SCC parent/copy merge");
        let state = candidate.solved.data.candidate_graph.as_ref().unwrap();
        let retained = state.intrusion.parents[selected.ordinal];
        let copy_key = retained.copy;
        let parent_key = retained.parent;
        assert_ne!(copy_key, parent_key, "selected raw parent/copy keys differ");
        assert_eq!(state.intrusion.rep(copy_key), state.intrusion.rep(parent_key));

        let graph = Graph {
            source_frontier: Vec::new(),
            owned_regions: Vec::new(),
            negative_functions: HashMap::new(),
            nodes: Vec::new(),
            rows: vec![
                Row { key: copy_key, local: false },
                Row { key: parent_key, local: true },
            ],
            bounds: Vec::new(),
            bound_evidence: Vec::new(),
            attachment_bundles: Vec::new(),
            attachment_spans: HashMap::new(),
            context_views: Vec::new(),
            root: 0,
            live_root: 0,
            boundary: 0,
            capture_rows: Vec::new(),
            capture_forest: state.intrusion.forest_snapshot().unwrap(),
        };
        let first = CandidateGraphRow { state, graph: &graph, index: 0 };
        let second = CandidateGraphRow { state, graph: &graph, index: 1 };
        assert_eq!(first.same_identity(second), first == second);
        assert!(first.same_identity(second));

        let mut first_hasher = DefaultHasher::new();
        first.hash(&mut first_hasher);
        let mut second_hasher = DefaultHasher::new();
        second.hash(&mut second_hasher);
        assert_eq!(first_hasher.finish(), second_hasher.finish());

        let mut indices = HashMap::new();
        indices.insert(first, 0);
        assert_eq!(indices.get(&second), Some(&0));
        indices.entry(second).or_insert(1);
        assert_eq!(indices.len(), 1, "merged rows share one index");
        let (stored, index) = indices.get_key_value(&second).unwrap();
        assert_eq!(*index, 0);
        assert_eq!(stored.index, 0);
        assert!(!graph.rows[stored.index].local);
    }

    #[test]
    fn candidate_graph_fresh_use_refuses_conflicts_and_preserves_valid_use() {
        for (source, conflicted) in [
            ("my apply f = f 1; my bad = apply 1", true),
            ("my apply f = f 1; my id x = x; my good = apply id", false),
        ] {
            let hir = crate::candidate_lifecycle_retirement::hir(source);
            let candidate = CandidateInference::solve(hir.clone()).unwrap();
            let root = hir
                .items()
                .iter()
                .find_map(|item| match item {
                    HirItem::Binding(binding) => Some(binding.definition_root()),
                    _ => None,
                })
                .unwrap();
            assert_eq!(candidate.export(root).is_err(), conflicted);
            assert_eq!(!candidate.candidate_conflicts().is_empty(), conflicted);
            if conflicted {
                assert!(candidate.candidate_conflicts().iter().any(|error| {
                    error.kind()
                        == SolverErrorKind::IncompatibleValue {
                            lower: ValueShape::Int,
                            upper: ValueShape::Function,
                        }
                }));
            }
            assert_eq!(candidate.source_call_count(), 2);
            assert!(candidate.source_call(0).is_ok());
            assert!(candidate.source_call(1).is_ok());
            let state = candidate.solved.data.candidate_graph.as_ref().unwrap();
            let occurrences: Vec<_> = state
                .routes
                .iter()
                .map(|route| route.use_id.occurrence())
                .chain(state.local_routes.iter().map(|route| &route.occurrence))
                .collect();
            assert!(!occurrences.is_empty(), "fixture retains fresh-use routes");
            for occurrence in occurrences {
                assert_eq!(candidate.fresh_use(occurrence).is_none(), conflicted);
            }
        }
    }
    #[test]
    fn computation_source_plan_rejects_contradictory_registration_associations() {
        let hir = crate::candidate_lifecycle_retirement::hir("my first (thunk:[] int) = thunk; my second (thunk:[] int) = thunk");
        let mut candidate = CandidateInference::solve(hir).unwrap();
        let negative_value = candidate.solved.data.store.terms
            .live_variable(ComponentKind::Value, Polarity::Negative, 0).unwrap();
        let positive_effect = candidate.solved.data.store.terms
            .live_variable(ComponentKind::Effect, Polarity::Positive, 0).unwrap();
        let data = &candidate.solved.data;
        let observe = |state: &crate::candidate_call::State| {
            crate::candidate_call::observe_computation_source_plan(&data.hir, &data.store, state, 0).is_err()
        };
        assert!(candidate.computation_source_plan(0).unwrap().is_some());
        let original = &data.candidate_calls;
        for root in [negative_value, positive_effect] {
            let mut state = original.clone();
            state.formals[0].native_root = Some(root);
            assert!(observe(&state));
        }
        let mut state = original.clone();
        state.formals[0].parameter = state.formals[1].parameter.clone();
        assert!(observe(&state));
        let mut state = original.clone();
        state.formals[0].entry_effect = None;
        assert!(observe(&state));
        let mut state = original.clone();
        state.formals[0].role = crate::candidate_call::FormalRole::Value;
        assert!(observe(&state));
    }
    #[test]
    fn source_call_registered_root_rejects_invalid_registration_and_native_polarity() {
        let hir = crate::candidate_lifecycle_retirement::hir("my apply f = f 1");
        let mut batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
        batch.candidate_calls.formals[0].recipe_position = batch.parameter_recipes.len();
        assert!(InferenceSession::try_new_candidate(batch).is_err());
        let candidate = CandidateInference::solve(hir).unwrap();
        let call = candidate.source_call(0).unwrap();
        let mut state = candidate.solved.data.candidate_calls.clone();
        state.formals[0].native_root = Some(call.native_demand());
        assert!(
            crate::candidate_call::observe(
                &candidate.solved.data.hir,
                &candidate.solved.data.store,
                &state,
                0,
            )
            .is_err()
        );
        state.formals[0].native_root = Some(call.native_invocation_effect());
        assert!(
            crate::candidate_call::observe(
                &candidate.solved.data.hir,
                &candidate.solved.data.store,
                &state,
                0,
            )
            .is_err()
        );
        state.formals[0].native_root = None;
        assert!(
            crate::candidate_call::observe(
                &candidate.solved.data.hir,
                &candidate.solved.data.store,
                &state,
                0,
            )
            .is_err()
        );
        assert!(
            candidate
                .source_call(0)
                .unwrap()
                .native_registered_root()
                .is_some()
        );
    }
    #[test]
    fn candidate_apply_fact_observation_rejects_copied_call() {
        let candidate =
            CandidateValueObservation::solve(module("my id x = x; my first = id 1")).unwrap();
        let [call] = candidate.calls() else {
            panic!("one Apply")
        };
        assert!(candidate.apply_fact(call).is_some());
        let copied = CandidateCall {
            occurrence: call.occurrence.clone(),
            callee: call.callee.clone(),
            argument: call.argument.clone(),
            unresolved: call.unresolved,
        };
        assert!(candidate.apply_fact(&copied).is_none());
    }

    #[test]
    fn candidate_apply_fact_observation_fails_closed_on_missing_or_ambiguous_inputs() {
        // Each mutation starts from an independently solved, valid observation.
        for scenario in 0..6 {
            let mut candidate =
                CandidateValueObservation::solve(module("my id x = x; my first = id 1")).unwrap();
            let occurrence = candidate.calls[0].occurrence.clone();
            let observation = candidate.apply_fact(&candidate.calls[0]).unwrap();
            let edge = observation.edge().clone();
            let fact = observation.fact().clone();
            match scenario {
                0 => candidate.apply_recipe_occurrences.clear(),
                1 => candidate.apply_recipe_occurrences.push(occurrence.clone()),
                2 => candidate
                    .solved
                    .store
                    .provenance
                    .retain(|retained| retained != &edge),
                3 => candidate.solved.store.provenance.push(edge),
                4 => candidate
                    .solved
                    .store
                    .facts
                    .retain(|retained| retained.id() != fact.id()),
                5 => candidate.solved.store.facts.push(fact),
                _ => unreachable!(),
            }
            assert!(
                candidate.apply_fact(&candidate.calls[0]).is_none(),
                "scenario {scenario}"
            );
        }
    }

    #[test]
    fn candidate_direct_chain_keeps_direction_and_bounded_shared_diagonal() {
        fn positive(value: &F5cPositive<'_>, qs: &mut HashSet<u32>) -> bool {
            match value {
                F5cPositive::Quantified(q) => {
                    qs.insert(*q);
                    false
                }
                F5cPositive::Int => true,
                F5cPositive::Union(parts) => parts
                    .iter()
                    .fold(false, |int, part| positive(part, qs) || int),
                _ => false,
            }
        }
        fn negative(value: &F5cNegative<'_>, qs: &mut HashSet<u32>) {
            match value {
                F5cNegative::Quantified(q) => {
                    qs.insert(*q);
                }
                F5cNegative::Intersection(parts) => {
                    for part in parts.iter() {
                        negative(part, qs);
                    }
                }
                _ => {}
            }
        }
        for case in [0, 1, 2] {
            let meter = DraftHeapMeter::default();
            let batch = ConstraintBatch::collect_mode(module("my f = 1"), true).unwrap();
            let mut session = InferenceSession::new(batch);
            let definition = session.batch.definitions[0].definition.clone();
            let root = session.batch.definitions[0].root.clone();
            let root_row = session.live_components
                [session.batch.root_component_positions[&root].component]
                .ordinal;
            let a = session.fresh_value_at_level(1).unwrap();
            let b = session.fresh_value_at_level(1).unwrap();
            let c = session.fresh_value_at_level(1).unwrap();
            for (lower, upper) in [(a, b), (b, c)] {
                session.bounds[lower as usize].direct_upper_rows.push(upper);
                session.bounds[upper as usize].direct_lower_rows.push(lower);
            }
            let (argument, result) = match case {
                0 => (a, c),
                1 => (c, a),
                _ => (a, a),
            };
            if case == 2 {
                session.bounds[a as usize]
                    .exact_non_variable_lowers
                    .push(ValueEndpointKey::IntPositive);
            }
            let argument = session
                .live_value_term(Polarity::Negative, argument)
                .unwrap();
            let result = session.live_value_term(Polarity::Positive, result).unwrap();
            let function = session
                .positive_function_term(
                    argument,
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    result,
                )
                .unwrap();
            session.bounds[root_row as usize]
                .exact_non_variable_lowers
                .push(ValueEndpointKey::PositiveFunction(function));
            let draft = session.generalization_draft(&meter, &definition).unwrap();
            let F5cPositive::Function {
                argument, result, ..
            } = &draft.predicate
            else {
                panic!("Function")
            };
            if case == 1 {
                assert_eq!(**argument, F5cNegative::Top);
                assert_eq!(**result, F5cPositive::Bottom);
            } else {
                let mut argument_qs = HashSet::new();
                let mut result_qs = HashSet::new();
                negative(argument, &mut argument_qs);
                let has_int = positive(result, &mut result_qs);
                assert!(argument_qs.intersection(&result_qs).next().is_some());
                if case == 2 {
                    assert!(has_int);
                }
            }
        }
    }
    #[test]
    fn candidate_boxed_and_flat_sessions_preserve_whole_scheme_parity() {
        for text in [
            "my id x = x; my wrap y = id y; pub out = wrap 1",
            "my id x = x; my wrap y = id (id y); pub out = wrap 1",
            "my self x = x x",
        ] {
            let hir = module(text);
            let mut results = Vec::new();
            for flat in [false, true] {
                let batch = ConstraintBatch::collect_mode(hir.clone(), true).unwrap();
                let mut session = InferenceSession::new(batch);
                session.flat_candidate_enabled = flat;
                results.push(session.run());
            }
            match (&results[0], &results[1]) {
                (Ok(boxed), Ok(flat)) => {
                    for item in hir.items() {
                        let HirItem::Binding(binding) = item else {
                            continue;
                        };
                        assert!(
                            boxed
                                .shadow_closed_schemes()
                                .for_root(binding.definition_root())
                                .unwrap()
                                .endpoints()
                                .alpha_eq(
                                    flat.shadow_closed_schemes()
                                        .for_root(binding.definition_root())
                                        .unwrap()
                                        .endpoints()
                                )
                        );
                    }
                }
                (Err(left), Err(right)) => assert_eq!(left, right),
                _ => panic!("boxed/flat availability differs"),
            }
        }
    }
    #[test]
    fn candidate_self_application_keeps_active_admission_invariant() {
        let hir = module("my self x = x x");
        let batch = ConstraintBatch::collect_mode(hir, true).unwrap();
        let mut session = InferenceSession::new(batch);
        session.admit_all_collected_facts().unwrap();
        let root = session.batch.definitions[0].root.clone();
        let row = session.live_components[session.batch.root_component_positions[&root].component]
            .ordinal;
        let meter = DraftHeapMeter::default();
        let mut generalizer = F5cGeneralizer::with_source_meter(&session, &meter);
        generalizer.assert_admission_invariant = true;
        // This checks safe generalizer execution, never source acceptance or R meaning.
        let _ = generalizer.build_component(row);
    }
    #[test]
    fn parameter_references_reuse_actual_startup_row() {
        let hir = module("my repeated f = f f");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda {
            parameter, body, ..
        } = binding.value()
        else {
            panic!("lambda")
        };
        let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
        let capture = candidate.solved.shadow_fresh_capture.as_ref().unwrap();
        let rows = capture.parameter_rows.as_ref().unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(&rows[0].0, parameter);
        let row = rows[0].1;
        assert!(
            capture.routes.is_empty(),
            "formals have no definition-use substitution"
        );
        let cause =
            CauseId::for_occurrence(ConstraintOccurrenceId::new(body.occurrence().clone(), 0));
        let fact_id = candidate
            .solved
            .store
            .provenance()
            .iter()
            .find(|edge| edge.cause() == &cause)
            .expect("Apply provenance")
            .fact();
        let fact = candidate
            .solved
            .store
            .facts()
            .iter()
            .find(|fact| fact.id() == fact_id)
            .expect("Apply demand");
        let TermView::LiveVariable(callee) =
            candidate.solved.store.term_view(fact.lower()).unwrap()
        else {
            panic!("direct formal callee")
        };
        assert_eq!(callee.ordinal(), row);
        let TermView::NegativeFunction { argument, .. } =
            candidate.solved.store.term_view(fact.upper()).unwrap()
        else {
            panic!("demand")
        };
        let TermView::LiveVariable(argument) = candidate.solved.store.term_view(argument).unwrap()
        else {
            panic!("direct formal argument")
        };
        assert_eq!(argument.ordinal(), row);
        let batch = ConstraintBatch::collect_mode(hir.clone(), true).unwrap();
        assert_eq!(batch.parameter_recipes.len(), 1);
        assert!(batch.definition_uses.is_empty());
        assert!(batch.components.iter().all(|component| !matches!(component,
            ComponentId::Occurrence { occurrence, kind: ComponentKind::Value } if occurrence != body.occurrence())));
    }
    #[test]
    fn preflight_depth_counts_both_apply_children() {
        let hir = module("my f x = x 1");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda { body, .. } = binding.value() else {
            panic!("lambda")
        };
        for callee_side in [true, false] {
            for (groups, accepted) in [(125, true), (126, false)] {
                let mut tree = binding.value().clone();
                let ResolvedExpr::Lambda { body: apply, .. } = &mut tree else {
                    unreachable!()
                };
                let ResolvedExpr::Apply {
                    callee, argument, ..
                } = apply.as_mut()
                else {
                    panic!("apply")
                };
                let child = if callee_side { callee } else { argument };
                for _ in 0..groups {
                    **child = ResolvedExpr::Group {
                        occurrence: body.occurrence().clone(),
                        range: body.range().clone(),
                        inner: Box::new(child.as_ref().clone()),
                    };
                }
                assert_eq!(
                    preflight_expression(&tree, Some(&mut Vec::new()), &mut HashSet::new()).is_ok(),
                    accepted
                );
                assert_eq!(
                    preflight_expression(&tree, None, &mut HashSet::new()).is_ok(),
                    accepted
                );
            }
        }
    }
    #[test]
    fn preflight_depth_counts_root_lambda_and_every_group_child() {
        let hir = module("my f x = 1");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda {
            occurrence,
            parameter,
            body,
            range,
        } = binding.value()
        else {
            panic!("lambda")
        };
        for (groups, accepted) in [(126, true), (127, false)] {
            let mut inner = body.as_ref().clone();
            for _ in 0..groups {
                inner = ResolvedExpr::Group {
                    occurrence: body.occurrence().clone(),
                    range: range.clone(),
                    inner: Box::new(inner),
                };
            }
            let tree = ResolvedExpr::Lambda {
                occurrence: occurrence.clone(),
                parameter: parameter.clone(),
                body: Box::new(inner),
                range: range.clone(),
            };
            let result = preflight_expression(&tree, Some(&mut Vec::new()), &mut HashSet::new());
            assert_eq!(result.is_ok(), accepted);
            assert_eq!(
                preflight_expression(&tree, None, &mut HashSet::new()).is_ok(),
                accepted
            );
        }
    }
}
