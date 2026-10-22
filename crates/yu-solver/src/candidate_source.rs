//! Private, sequential source inference. Planning does not admit constraints.
use crate::*;
use crate::shadow_apply::{CandidateEndpoint, CandidateRelation};
use yu_hir::shadow::{LocalSource, LocalSourceForm, LocalSourceStatement, LocalSourceResolution, SourceAnnotationValue};
use yu_hir::HirLocalId;

#[derive(Clone, Debug, Default)]
pub(super) struct Plan {
    pub scoped_experiment: bool,
    pub operation_v1: bool,
    pub scoped_work_used: usize,
    pub scoped_scratch_envelope: usize,
    pub regions: Vec<SourceRegion>,
    pub definition_regions: HashMap<DefinitionRootId, SourceRegionId>,
    pub occurrence_regions: HashMap<HirOccurrenceId, SourceRegionId>,
    pub local_regions: HashMap<HirLocalId, SourceRegionId>,
    pub computation_scopes: HashMap<HirOccurrenceId, candidate_scope::EffectScopeId>,
    pub scope_regions: Vec<SourceRegionId>,
    pub scope_occurrences: Vec<HirOccurrenceId>,
    pub active: bool,
    pub references: candidate_value_graph::Graph,
    pub schedules: HashMap<DefinitionRootId, Vec<Action>>,
    pub expressions: Vec<ExpressionSchedule>,
    /// Source-owned member bodies stay separate from ordinary module roots.
    pub members: Vec<MemberSchedule>,
    /// Imported operator owners joined to their exact provider expression
    /// roots. These are source identities, not binding/DefId substitutes.
    pub operator_provider_roots: Vec<OperatorProviderRoot>,
    /// Infix occurrences consumed by source-position two-Apply actions.
    pub operator_uses: Vec<OperatorUse>,
    /// Authenticated implementation targets and exact member overrides for
    /// imported role members used by this source world.
    pub role_implementation_members: HashMap<
        yu_hir::shadow::SourceRoleMemberId,
        Vec<yu_hir::shadow::SourceRoleImplementationMemberCandidate>,
    >,
    pub source_owners: HashMap<HirOccurrenceId, SourceRootId>,
    pub loose: Vec<Action>,
    pub component_levels: HashMap<usize, u32>,
    pub parameter_levels: HashMap<usize, u32>,
    pub locals: Vec<HirLocalId>,
    pub omitted_formals: HashMap<HirOccurrenceId, Arc<OmittedFormal>>,
}
#[derive(Clone, Debug)]
pub(super) struct ExpressionSchedule {
    pub root: ExpressionRootId,
    pub components: ComponentPositions,
    pub value: CandidateEndpoint,
    pub actions: Vec<Action>,
}
#[derive(Clone, Debug)]
pub(super) struct MemberSchedule {
    pub root: yu_hir::SourceMemberRootId,
    /// Exact source role-member key when this root is a role default. An
    /// implementation body stays separately identified by its own root.
    pub role_member: Option<yu_hir::shadow::SourceRoleMemberId>,
    /// Exact implementation-body member identity. This remains distinct from
    /// the role member that the implementation may satisfy.
    pub implementation_member: Option<yu_hir::shadow::SourceImplementationMemberId>,
    pub header: yu_hir::SourceMemberHeader,
    /// Receiver input and body output remain distinct candidate endpoints;
    /// a later selected use must freshen the body before linking these rows.
    pub receiver: CandidateEndpoint,
    pub occurrence: HirOccurrenceId,
    pub components: ComponentPositions,
    pub value: CandidateEndpoint,
    pub actions: Vec<Action>,
}
#[derive(Clone, Debug)]
pub(super) struct OperatorProviderRoot {
    pub owner: yu_hir::SourceOperatorOwner,
    pub root: yu_hir::ExpressionRootId,
}
#[derive(Clone, Debug)]
pub(super) struct OperatorUse {
    pub owner: SourceRootId,
    pub operator_owner: yu_hir::SourceOperatorOwner,
    pub occurrence: HirOccurrenceId,
    pub operator_source: yu_hir::shadow::SourceNodeKey,
    pub provider: usize,
    pub left: CandidateEndpoint,
    pub left_effect: usize,
    pub right: Option<(CandidateEndpoint, usize)>,
    pub result: usize,
    pub result_effect: usize,
}
impl Plan {
    /// Resolve only an exact role-default source key. Missing and duplicate
    /// schedules both fail closed; implementation dispatch needs receiver
    /// evidence and is intentionally not handled here.
    pub(super) fn unique_role_member_schedule(
        &self,
        member: &yu_hir::shadow::SourceRoleMemberId,
    ) -> Option<usize> {
        let mut found = None;
        for (index, schedule) in self.members.iter().enumerate() {
            if schedule.role_member.as_ref() != Some(member) { continue; }
            if found.replace(index).is_some() { return None; }
        }
        found
    }

    /// Resolve an implementation body only by its parse-owned declaration
    /// identity. Missing, stale, and duplicate schedules remain unavailable.
    pub(super) fn unique_implementation_member_schedule(
        &self,
        member: &yu_hir::shadow::SourceImplementationMemberId,
    ) -> Option<usize> {
        let mut found = None;
        for (index, schedule) in self.members.iter().enumerate() {
            if schedule.implementation_member.as_ref() != Some(member) { continue; }
            if found.replace(index).is_some() { return None; }
        }
        found
    }
}
/// Source ownership is constructed before solving; numeric solver levels never
/// determine whether a scope belongs to a captured source region.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct SourceRegionId(pub usize);
#[derive(Clone, Debug)]
pub(super) struct SourceRegion {
    pub parent: Option<SourceRegionId>,
    pub children: Vec<SourceRegionId>,
    pub scopes: Vec<candidate_scope::EffectScopeId>,
    pub inputs: Vec<candidate_scope::InputRouteId>,
}
impl Plan {
    #[track_caller]
    fn charge_scoped_work(&mut self, work: usize) -> Result<(), CollectionAvailabilityError> {
        let next = self.scoped_work_used.checked_add(work).ok_or_else(unavailable)?;
        if next > SCOPED_WORK_LIMIT { return Err(unavailable()); }
        self.scoped_work_used = next; Ok(())
    }
    #[track_caller]
    fn note_guard_stack(&mut self, capacity: usize) -> Result<(), CollectionAvailabilityError> {
        let bytes = capacity.checked_mul(std::mem::size_of::<usize>()).ok_or_else(unavailable)?;
        self.scoped_scratch_envelope = self.scoped_scratch_envelope.max(bytes); Ok(())
    }
    #[track_caller]
    fn region(&mut self, parent: Option<SourceRegionId>) -> Result<SourceRegionId, CollectionAvailabilityError> {
        if !self.scoped_experiment { return Ok(SourceRegionId(usize::MAX)); }
        if self.regions.len() >= SCOPED_RECORD_LIMIT { return Err(unavailable()); }
        self.charge_scoped_work(1)?;
        self.regions.try_reserve(1).map_err(|_| unavailable())?;
        if let Some(parent) = parent {
            self.regions[parent.0].children.try_reserve(1).map_err(|_| unavailable())?;
        }
        let id = SourceRegionId(self.regions.len());
        self.regions.push(SourceRegion { parent, children: Vec::new(), scopes: Vec::new(), inputs: Vec::new() });
        if let Some(parent) = parent { self.regions[parent.0].children.push(id); }
        Ok(id)
    }
    #[track_caller]
    fn computation_scope(&mut self, occurrence: &HirOccurrenceId, region: SourceRegionId) -> Result<(), CollectionAvailabilityError> {
        if !self.scoped_experiment { return Ok(()); }
        self.charge_scoped_work(1)?;
        self.occurrence_regions.try_reserve(1).map_err(|_| unavailable())?;
        self.computation_scopes.try_reserve(1).map_err(|_| unavailable())?;
        if self.scope_regions.len() >= SCOPED_RECORD_LIMIT { return Err(unavailable()); }
        self.scope_regions.try_reserve(1).map_err(|_| unavailable())?;
        self.scope_occurrences.try_reserve(1).map_err(|_| unavailable())?;
        self.regions[region.0].scopes.try_reserve(1).map_err(|_| unavailable())?;
        let scope = candidate_scope::EffectScopeId(u32::try_from(self.scope_regions.len()).map_err(|_| unavailable())?);
        self.scope_regions.push(region);
        self.scope_occurrences.push(occurrence.clone());
        self.regions[region.0].scopes.push(scope);
        self.occurrence_regions.insert(occurrence.clone(), region);
        self.computation_scopes.insert(occurrence.clone(), scope);
        Ok(())
    }
}
/// Runtime copy of the sealed source inventory. Fresh source instances extend
/// this forest without mutating the collected source plan.
#[derive(Debug, Default)]
pub(super) struct ScopeInventory {
    nested_bytes: usize,
    pub scope_occurrences: Vec<HirOccurrenceId>,
    pub work_used: usize,
    pub scratch_peak_bytes: usize,
    pub scope_origins: Vec<candidate_scope::EffectScopeId>,
    pub input_origins: Vec<candidate_scope::InputRouteId>,
    pub copies: Vec<ScopeCopyStatistics>,
    pub regions: Vec<SourceRegion>,
    pub scope_regions: Vec<SourceRegionId>,
    pub input_regions: Vec<SourceRegionId>,
}
#[derive(Debug, Default)]
pub(super) struct ScopeRemap {
    pub regions: HashMap<SourceRegionId, SourceRegionId>,
    pub scopes: HashMap<candidate_scope::EffectScopeId, candidate_scope::EffectScopeId>,
    pub inputs: HashMap<candidate_scope::InputRouteId, candidate_scope::InputRouteId>,
}
/// Private experiment availability limits, never a language input boundary.
pub(super) const SCOPED_RECORD_LIMIT: usize = 4096;
pub(super) const SCOPED_WORK_LIMIT: usize = 65536;
#[derive(Clone, Copy, Debug)]
pub struct ScopeCopyStatistics {
    pub regions: usize, pub scopes: usize, pub inputs: usize,
    pub graph_nodes: usize, pub graph_bounds: usize,
}
fn scope_unavailable() -> SolveAvailabilityError { SolveAvailabilityError::IdentityExhausted }
fn scope_copy<T: Copy>(values: &[T]) -> Result<Vec<T>, SolveAvailabilityError> {
    let mut out = Vec::new(); out.try_reserve_exact(values.len()).map_err(|_| scope_unavailable())?;
    out.extend_from_slice(values); Ok(out)
}
impl ScopeRemap {
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        checked_fixed_capacity_bytes([
            (self.regions.capacity(), std::mem::size_of::<(SourceRegionId, SourceRegionId)>()),
            (self.scopes.capacity(), std::mem::size_of::<(candidate_scope::EffectScopeId, candidate_scope::EffectScopeId)>()),
            (self.inputs.capacity(), std::mem::size_of::<(candidate_scope::InputRouteId, candidate_scope::InputRouteId)>()),
        ])
    }
}
impl ScopeInventory {
    pub fn charge(&mut self, work: usize) -> Result<(), SolveAvailabilityError> {
        let next = self.work_used.checked_add(work).ok_or_else(scope_unavailable)?;
        if next > SCOPED_WORK_LIMIT { return Err(scope_unavailable()); }
        self.work_used = next; Ok(())
    }
    pub fn note_scratch(&mut self, bytes: usize) { self.scratch_peak_bytes = self.scratch_peak_bytes.max(bytes); }
    pub fn from_plan(plan: &Plan) -> Result<Self, SolveAvailabilityError> {
        if plan.regions.len() > SCOPED_RECORD_LIMIT || plan.scope_regions.len() > SCOPED_RECORD_LIMIT { return Err(scope_unavailable()); }
        let mut regions = Vec::new(); regions.try_reserve_exact(plan.regions.len()).map_err(|_| scope_unavailable())?;
        let mut input_regions = Vec::new();
        let count: usize = plan.regions.iter().map(|r| r.inputs.len()).sum();
        if count > SCOPED_RECORD_LIMIT { return Err(scope_unavailable()); }
        input_regions.try_reserve_exact(count).map_err(|_| scope_unavailable())?;
        input_regions.resize(count, SourceRegionId(usize::MAX));
        for (index, region) in plan.regions.iter().enumerate() {
            for input in &region.inputs { input_regions[input.0 as usize] = SourceRegionId(index); }
            regions.push(SourceRegion { parent: region.parent, children: scope_copy(&region.children)?, scopes: scope_copy(&region.scopes)?, inputs: scope_copy(&region.inputs)? });
        }
        let mut scope_occurrences = Vec::new(); scope_occurrences.try_reserve_exact(plan.scope_occurrences.len()).map_err(|_| scope_unavailable())?;
        scope_occurrences.extend(plan.scope_occurrences.iter().cloned());
        let mut scope_origins = Vec::new(); scope_origins.try_reserve_exact(plan.scope_regions.len()).map_err(|_| scope_unavailable())?;
        for index in 0..plan.scope_regions.len() { scope_origins.push(candidate_scope::EffectScopeId(u32::try_from(index).map_err(|_| scope_unavailable())?)); }
        let mut input_origins = Vec::new(); input_origins.try_reserve_exact(count).map_err(|_| scope_unavailable())?;
        for index in 0..count { input_origins.push(candidate_scope::InputRouteId(u32::try_from(index).map_err(|_| scope_unavailable())?)); }
        let nested_bytes = regions.iter().try_fold(0usize, |n, r| n.checked_add(Self::region_bytes(r)?).ok_or_else(scope_unavailable))?;
        let mut inventory = Self { regions, scope_regions: scope_copy(&plan.scope_regions)?, input_regions, scope_origins, input_origins, scope_occurrences, nested_bytes,
            work_used: plan.scoped_work_used, scratch_peak_bytes: plan.scoped_scratch_envelope, ..Self::default() };
        inventory.charge(plan.regions.len().checked_add(plan.scope_regions.len()).and_then(|n| n.checked_add(count)).ok_or_else(scope_unavailable)?)?;
        Ok(inventory)
    }
    fn region_bytes(region: &SourceRegion) -> Result<usize, SolveAvailabilityError> {
        checked_fixed_capacity_bytes([
            (region.children.capacity(), std::mem::size_of::<SourceRegionId>()),
            (region.scopes.capacity(), std::mem::size_of::<candidate_scope::EffectScopeId>()),
            (region.inputs.capacity(), std::mem::size_of::<candidate_scope::InputRouteId>()),
        ])
    }
    fn fixed_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        checked_fixed_capacity_bytes([
            (self.regions.capacity(), std::mem::size_of::<SourceRegion>()),
            (self.scope_regions.capacity(), std::mem::size_of::<SourceRegionId>()),
            (self.input_regions.capacity(), std::mem::size_of::<SourceRegionId>()),
            (self.scope_origins.capacity(), std::mem::size_of::<candidate_scope::EffectScopeId>()),
            (self.input_origins.capacity(), std::mem::size_of::<candidate_scope::InputRouteId>()),
            (self.copies.capacity(), std::mem::size_of::<ScopeCopyStatistics>()),
            (self.scope_occurrences.capacity(), std::mem::size_of::<HirOccurrenceId>()),
        ])
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.fixed_bytes()?.checked_add(self.nested_bytes).ok_or_else(scope_unavailable)
    }
    #[cfg(test)]
    pub fn enumerated_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.regions.iter().try_fold(self.fixed_bytes()?, |n, r| n.checked_add(Self::region_bytes(r)?).ok_or_else(scope_unavailable))
    }
    /// Parent-before-child closure of an explicitly supplied capture forest.
    /// Work is proportional to that forest, including dormant source handles.
    pub fn owned(&mut self, roots: &[SourceRegionId]) -> Result<Vec<SourceRegionId>, SolveAvailabilityError> {
        self.charge(roots.len())?;
        let mut out = Vec::new(); let mut seen = HashSet::new();
        seen.try_reserve(roots.len()).map_err(|_| scope_unavailable())?;
        for &root in roots { if seen.insert(root) { out.try_reserve(1).map_err(|_| scope_unavailable())?; out.push(root); } }
        let mut cursor = 0;
        while cursor < out.len() {
            let child_count = self.regions.get(out[cursor].0).ok_or_else(scope_unavailable)?.children.len();
            self.charge(child_count.checked_add(1).ok_or_else(scope_unavailable)?)?;
            if out.len().checked_add(child_count).is_none_or(|n| n > SCOPED_RECORD_LIMIT) { return Err(scope_unavailable()); }
            let region = &self.regions[out[cursor].0];
            seen.try_reserve(region.children.len()).map_err(|_| scope_unavailable())?;
            out.try_reserve(region.children.len()).map_err(|_| scope_unavailable())?;
            for &child in &region.children { if seen.insert(child) { out.push(child); } }
            cursor += 1;
        }
        self.note_scratch(checked_fixed_capacity_bytes([
            (out.capacity(), std::mem::size_of::<SourceRegionId>()),
            (seen.capacity(), std::mem::size_of::<SourceRegionId>()),
        ])?);
        Ok(out)
    }
    pub fn fresh(&mut self, owned: &[SourceRegionId], caller: SourceRegionId, graph_nodes: usize, graph_bounds: usize) -> Result<ScopeRemap, SolveAvailabilityError> {
        self.regions.get(caller.0).ok_or_else(scope_unavailable)?;
        self.charge(owned.len())?;
        let (mut scopes_to_copy, mut inputs_to_copy) = (0usize, 0usize);
        for &id in owned {
            let region = self.regions.get(id.0).ok_or_else(scope_unavailable)?;
            scopes_to_copy = scopes_to_copy.checked_add(region.scopes.len()).ok_or_else(scope_unavailable)?;
            inputs_to_copy = inputs_to_copy.checked_add(region.inputs.len()).ok_or_else(scope_unavailable)?;
        }
        if self.regions.len().checked_add(owned.len()).is_none_or(|n| n > SCOPED_RECORD_LIMIT)
            || self.scope_regions.len().checked_add(scopes_to_copy).is_none_or(|n| n > SCOPED_RECORD_LIMIT)
            || self.input_regions.len().checked_add(inputs_to_copy).is_none_or(|n| n > SCOPED_RECORD_LIMIT)
            || self.copies.len() >= SCOPED_RECORD_LIMIT { return Err(scope_unavailable()); }
        self.charge(owned.len().checked_mul(3).and_then(|n| n.checked_add(scopes_to_copy)).and_then(|n| n.checked_add(inputs_to_copy)).ok_or_else(scope_unavailable)?)?;
        self.scope_origins.try_reserve(scopes_to_copy).map_err(|_| scope_unavailable())?;
        self.input_origins.try_reserve(inputs_to_copy).map_err(|_| scope_unavailable())?;
        self.copies.try_reserve(1).map_err(|_| scope_unavailable())?;
        let mut map = ScopeRemap::default();
        map.regions.try_reserve(owned.len()).map_err(|_| scope_unavailable())?;
        self.regions.try_reserve(owned.len()).map_err(|_| scope_unavailable())?;
        // Reserve identities first, so an owned parent is recognized regardless
        // of which root in a multi-definition forest was supplied first.
        let base = self.regions.len();
        for (offset, &old) in owned.iter().enumerate() { map.regions.insert(old, SourceRegionId(base.checked_add(offset).ok_or_else(scope_unavailable)?)); }
        for &old in owned {
            let original = self.regions.get(old.0).ok_or_else(scope_unavailable)?;
            let parent = original.parent.and_then(|p| map.regions.get(&p).copied()).unwrap_or(caller);
            let scope_count = original.scopes.len();
            let input_count = original.inputs.len();
            let id = map.regions[&old];
            let mut scopes = Vec::new(); scopes.try_reserve_exact(scope_count).map_err(|_| scope_unavailable())?;
            let mut inputs = Vec::new(); inputs.try_reserve_exact(input_count).map_err(|_| scope_unavailable())?;
            map.scopes.try_reserve(scope_count).map_err(|_| scope_unavailable())?;
            map.inputs.try_reserve(input_count).map_err(|_| scope_unavailable())?;
            self.scope_regions.try_reserve(scope_count).map_err(|_| scope_unavailable())?;
            self.input_regions.try_reserve(input_count).map_err(|_| scope_unavailable())?;
            for index in 0..scope_count {
                let old_scope = self.regions[old.0].scopes[index];
                let fresh = candidate_scope::EffectScopeId(u32::try_from(self.scope_regions.len()).map_err(|_| scope_unavailable())?);
                self.scope_origins.push(self.scope_origins[old_scope.0 as usize]);
                self.scope_regions.push(id); scopes.push(fresh); map.scopes.insert(old_scope, fresh);
            }
            for index in 0..input_count {
                let old_input = self.regions[old.0].inputs[index];
                let fresh = candidate_scope::InputRouteId(u32::try_from(self.input_regions.len()).map_err(|_| scope_unavailable())?);
                self.input_origins.push(self.input_origins[old_input.0 as usize]);
                self.input_regions.push(id); inputs.push(fresh); map.inputs.insert(old_input, fresh);
            }
            let region = SourceRegion { parent: Some(parent), children: Vec::new(), scopes, inputs };
            self.nested_bytes = self.nested_bytes.checked_add(Self::region_bytes(&region)?).ok_or_else(scope_unavailable)?;
            self.regions.push(region);
        }
        for &old in owned {
            let id = map.regions[&old]; let parent = self.regions[id.0].parent.ok_or_else(scope_unavailable)?;
            let before = self.regions[parent.0].children.capacity();
            self.regions[parent.0].children.try_reserve(1).map_err(|_| scope_unavailable())?;
            let growth = self.regions[parent.0].children.capacity() - before;
            self.nested_bytes = self.nested_bytes.checked_add(growth.checked_mul(std::mem::size_of::<SourceRegionId>()).ok_or_else(scope_unavailable)?).ok_or_else(scope_unavailable)?;
            self.regions[parent.0].children.push(id);
        }
        self.copies.push(ScopeCopyStatistics { regions: owned.len(), scopes: scopes_to_copy, inputs: inputs_to_copy, graph_nodes, graph_bounds });
        Ok(map)
    }
}
// Source construction only: no effect-position or receiver-role judgment.
#[derive(Clone, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "omission evidence has no semantic consumer"))]
pub(super) struct OmittedFormal {
    pub owner: SourceRootId,
    pub lambda: HirOccurrenceId,
    pub formal: yu_hir::HirParameterId,
    pub position: yu_hir::shadow::SourceNodeKey,
    pub scope: candidate_effect::AnnotationScope,
}
#[derive(Clone, Debug)]
pub(super) struct RecordParameterField {
    pub label: Box<str>,
    pub parameter: usize,
    pub default: Option<CandidateEndpoint>,
}
#[derive(Clone, Debug)]
pub(super) enum Action {
    Ascription { annotation: Arc<yu_hir::shadow::SourceAnnotation>, endpoint: CandidateEndpoint, computation_effect: usize, occurrence: HirOccurrenceId, level: u32, scope: candidate_effect::AnnotationScope },
    LocalAnnotation { annotation: Arc<yu_hir::shadow::SourceAnnotation>, slot: usize, endpoint: CandidateEndpoint, computation_effect: usize, occurrence: HirOccurrenceId, level: u32, boundary: u32 },
    FormalAnnotation { annotation: Arc<yu_hir::shadow::SourceAnnotation>, parameter: usize, occurrence: HirOccurrenceId, scope: candidate_effect::AnnotationScope },
    UnitParameter { parameter: usize, occurrence: HirOccurrenceId },
    RecordParameter { parameter: usize, fields: Vec<RecordParameterField>, occurrence: HirOccurrenceId },
    FormalEntry { registration: usize, annotation: Arc<yu_hir::shadow::SourceAnnotation>, occurrence: HirOccurrenceId, scope: candidate_effect::AnnotationScope },
    FormalNameEffect { registration: usize, occurrence: HirOccurrenceId, effect: usize },
    Fact(usize),
    Link { occurrence: HirOccurrenceId, endpoint: CandidateEndpoint, target: usize },
    ValueConstraint { occurrence: HirOccurrenceId, slot: u8, endpoint: CandidateEndpoint, upper: Term },
    Candidate(usize),
    Operator(usize),
    Lambda(usize),
    BeginLambda,
    EndLambda,
    Module(HirOccurrenceId),
    Local { slot: usize, occurrence: HirOccurrenceId, value: usize, level: u32 },
    BeginLocal { slot: usize },
    Install { slot: usize, initializer: CandidateEndpoint, boundary: u32 },
    Operation { declaration: Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: SourceRootId, occurrence: HirOccurrenceId, target: usize, level: u32 },
    Primitive { operation: yu_hir::shadow::PinnedPrimitiveOp, owner: SourceRootId, position: yu_hir::shadow::SourceNodeKey, occurrence: HirOccurrenceId, target: usize, level: u32 },
    CatchOperation { declaration: Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: SourceRootId, occurrence: HirOccurrenceId, payload: Option<usize>, continuation: Option<usize>, original: CandidateEndpoint, effect: usize, level: u32, h_arg: Option<HandlerContinuationArgumentV1> },
    FieldBoundV1 { declaration: Arc<yu_hir::shadow::SourceOperationDeclaration>, h_arg: HandlerContinuationArgumentV1 },
    Annotation { annotation: Arc<yu_hir::shadow::SourceAnnotation>, endpoint: CandidateEndpoint, computation_effect: usize, target: usize, occurrence: HirOccurrenceId, level: u32 },
    WhereClause { source: yu_hir::shadow::LocalSourceWhereClause, scope: candidate_effect::AnnotationScope },
}
#[derive(Clone, Debug)]
pub(super) struct HandlerContinuationArgumentV1 {
    pub owner: SourceRootId,
    pub request: HirOccurrenceId,
    pub catch_occurrence: HirOccurrenceId,
    pub arm_source: yu_hir::shadow::SourceNodeKey,
    pub declaration: yu_hir::shadow::SourceOperationId,
    pub continuation: yu_hir::shadow::LocalSourceCatchBinderId,
    pub apply_occurrence: HirOccurrenceId,
    pub argument_occurrence: HirOccurrenceId,
    pub response_definition: HirLocalId,
    pub response_annotation: Arc<yu_hir::shadow::SourceAnnotation>,
    pub declaration_field_position: yu_hir::shadow::SourceNodeKey,
    pub response_field_position: yu_hir::shadow::SourceNodeKey,
    pub field_family: yu_hir::shadow::SourceEffectId,
    pub callback_apply_occurrence: HirOccurrenceId,
    pub callback_argument_occurrence: HirOccurrenceId,
    pub callback_operation_occurrence: HirOccurrenceId,
    pub callback_operation: Arc<yu_hir::shadow::SourceOperationDeclaration>,
}
#[derive(Clone, Debug)]
pub(super) struct LicensedOperationFieldV1 {
    pub owner_request: HirOccurrenceId,
    pub declaration: Arc<yu_hir::shadow::SourceOperationDeclaration>,
    pub field_position: yu_hir::shadow::SourceNodeKey,
    pub family: yu_hir::shadow::SourceEffectId,
    pub negative_port: u32,
    pub handler_argument: HandlerContinuationArgumentV1,
}
#[derive(Clone, Debug)]
pub(super) struct CallbackFieldRealizationV1 {
    pub response_definition: HirLocalId,
    pub response_annotation: Arc<yu_hir::shadow::SourceAnnotation>,
    pub apply_occurrence: HirOccurrenceId,
    pub operation_occurrence: HirOccurrenceId,
    pub operation: Arc<yu_hir::shadow::SourceOperationDeclaration>,
    pub handler_argument: HandlerContinuationArgumentV1,
}
// The plan remains immutable while this frame is live. Root positions select
// the original schedule, so resume never reconstructs actions from graph edges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Schedule { Loose, Root(usize), Expression(usize), Member(usize) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Stage { Execute, PublishLocal { slot: usize, exposed: Term, boundary: u32 } }
// Synthetic source-boundary token, not a certificate or readiness witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Wait { pub generation: u64, pub dependency: usize }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Frame {
    pub schedule: Schedule,
    pub next: usize,
    pub stage: Stage,
    pub wait: Option<Wait>,
    pub registration: Option<candidate_context::SourceSupportId>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CandidateRun<T> { Complete(T), Suspended(Wait) }
// Only the test adapter supplies a wait here; a production lifecycle owner
// must supply authenticated support before this can be connected to certificates.
#[derive(Clone, Copy, Debug)]
pub(super) struct Support { pub wait: Option<Wait> }
impl Support { pub const READY: Self = Self { wait: None }; }

impl Plan {
    pub fn bytes(&self) -> usize {
        checked_usize_sum([
            self.references.bytes(),
            checked_capacity_bytes::<SourceRegion>(self.regions.capacity(), "source regions"),
            checked_usize_sum(self.regions.iter().map(|region| checked_usize_sum([
                checked_capacity_bytes::<SourceRegionId>(region.children.capacity(), "source region children"),
                checked_capacity_bytes::<candidate_scope::EffectScopeId>(region.scopes.capacity(), "source region scopes"),
                checked_capacity_bytes::<candidate_scope::InputRouteId>(region.inputs.capacity(), "source region inputs"),
            ], "source region inventory")), "source region forest"),
            checked_capacity_bytes::<(DefinitionRootId, SourceRegionId)>(self.definition_regions.capacity(), "source definition regions"),
            checked_capacity_bytes::<(HirOccurrenceId, SourceRegionId)>(self.occurrence_regions.capacity(), "source occurrence regions"),
            checked_capacity_bytes::<(HirLocalId, SourceRegionId)>(self.local_regions.capacity(), "source local regions"),
            checked_capacity_bytes::<(HirOccurrenceId, candidate_scope::EffectScopeId)>(self.computation_scopes.capacity(), "source computation scopes"),
            checked_capacity_bytes::<SourceRegionId>(self.scope_regions.capacity(), "source scope owners"),
            checked_capacity_bytes::<HirOccurrenceId>(self.scope_occurrences.capacity(), "source scope occurrences"),
            checked_capacity_bytes::<(DefinitionRootId, Vec<Action>)>(self.schedules.capacity(), "source schedules"),
            checked_usize_sum(self.schedules.values().map(|actions| checked_capacity_bytes::<Action>(actions.capacity(), "source actions")), "source action storage"),
            checked_capacity_bytes::<Action>(self.loose.capacity(), "source loose actions"),
            checked_capacity_bytes::<ExpressionSchedule>(self.expressions.capacity(), "expression schedules"),
            checked_usize_sum(self.expressions.iter().map(|schedule| checked_capacity_bytes::<Action>(schedule.actions.capacity(), "expression actions")), "expression action storage"),
            checked_capacity_bytes::<MemberSchedule>(self.members.capacity(), "member schedules"),
            checked_usize_sum(self.members.iter().map(|schedule| checked_capacity_bytes::<Action>(schedule.actions.capacity(), "member actions")), "member action storage"),
            checked_capacity_bytes::<OperatorProviderRoot>(self.operator_provider_roots.capacity(), "operator provider roots"),
            checked_usize_sum(self.operator_provider_roots.iter().map(|provider| provider.owner.spelling().len()), "operator provider owner spellings"),
            checked_capacity_bytes::<OperatorUse>(self.operator_uses.capacity(), "operator use routes"),
            checked_usize_sum(self.operator_uses.iter().map(|use_| use_.operator_owner.spelling().len()), "operator use owner spellings"),
            checked_capacity_bytes::<(yu_hir::shadow::SourceRoleMemberId, Vec<yu_hir::shadow::SourceRoleImplementationMemberCandidate>)>(self.role_implementation_members.capacity(), "role implementation member inventory"),
            checked_usize_sum(self.role_implementation_members.values().map(|candidates| checked_capacity_bytes::<yu_hir::shadow::SourceRoleImplementationMemberCandidate>(candidates.capacity(), "role implementation candidates")), "role implementation candidate storage"),
            checked_usize_sum(self.role_implementation_members.values().flat_map(|candidates| candidates.iter()).map(|candidate| candidate.target.text.len()), "implementation target source text"),
            checked_usize_sum(self.role_implementation_members.values().flat_map(|candidates| candidates.iter()).map(|candidate| candidate.target.shape.as_ref().map_or(0, yu_hir::shadow::SourceImplementationTypeShape::retained_bytes)), "implementation target shape storage"),
            checked_usize_sum(self.role_implementation_members.values().flat_map(|candidates| candidates.iter()).map(|candidate| checked_capacity_bytes::<Option<yu_hir::shadow::SourceImplementationWhereClause>>(candidate.where_clauses.capacity(), "implementation where-clause inventory")), "implementation where-clause inventory storage"),
            checked_usize_sum(self.role_implementation_members.values().flat_map(|candidates| candidates.iter()).flat_map(|candidate| candidate.where_clauses.iter().flatten()).map(|where_clause| where_clause.subject.text.len() + where_clause.role.text.len() + where_clause.subject.shape.as_ref().map_or(0, yu_hir::shadow::SourceImplementationTypeShape::retained_bytes) + where_clause.role.shape.as_ref().map_or(0, yu_hir::shadow::SourceImplementationTypeShape::retained_bytes)), "implementation where-clause source storage"),
            checked_usize_sum(self.role_implementation_members.values().flat_map(|candidates| candidates.iter()).map(|candidate| checked_capacity_bytes::<Option<yu_hir::shadow::SourceRoleId>>(candidate.where_roles.capacity(), "implementation where-role identity inventory")), "implementation where-role identity storage"),
            checked_usize_sum(self.members.iter().map(|schedule| {
                let header = &schedule.header;
                header.receiver.spelling.len() + header.method.spelling.len()
                    + header.annotation.as_ref().map_or(0, |annotation| annotation.text.len())
            }), "member header source text"),
            checked_capacity_bytes::<(HirOccurrenceId, SourceRootId)>(self.source_owners.capacity(), "source occurrence owners"),
            checked_usize_sum(self.schedules.values().flat_map(|actions| actions.iter()).chain(self.loose.iter()).chain(self.expressions.iter().flat_map(|schedule| schedule.actions.iter())).chain(self.members.iter().flat_map(|schedule| schedule.actions.iter())).map(|action| {
                if let Action::RecordParameter { fields, .. } = action {
                    checked_capacity_bytes::<RecordParameterField>(fields.capacity(), "record parameter fields")
                        + checked_usize_sum(fields.iter().map(|field| field.label.len()), "record parameter labels")
                } else if let Action::Ascription { annotation, .. } | Action::LocalAnnotation { annotation, .. } | Action::Annotation { annotation, .. } | Action::FormalAnnotation { annotation, .. } = action { std::mem::size_of::<yu_hir::shadow::SourceAnnotation>() + annotation.retained_arena_bytes() } else if let Action::WhereClause { source, .. } = action { std::mem::size_of::<yu_hir::shadow::LocalSourceWhereClause>() + source.text.len() + source.subject.text.len() + source.role.text.len() } else if let Action::FieldBoundV1 { declaration, h_arg } = action { std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>() + declaration.retained_arena_bytes() + std::mem::size_of::<yu_hir::shadow::SourceAnnotation>() + h_arg.response_annotation.retained_arena_bytes() } else if let Action::Operation { declaration, .. } = action { std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>() + declaration.retained_arena_bytes() } else if let Action::CatchOperation { declaration, h_arg, .. } = action { std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>() + declaration.retained_arena_bytes() + h_arg.as_ref().map_or(0, |link| std::mem::size_of::<yu_hir::shadow::SourceAnnotation>() + link.response_annotation.retained_arena_bytes()) } else { 0 }
            }), "source annotation storage"),
            checked_capacity_bytes::<(usize, u32)>(self.component_levels.capacity(), "source component levels"),
            checked_capacity_bytes::<(usize, u32)>(self.parameter_levels.capacity(), "source parameter levels"),
            checked_capacity_bytes::<HirLocalId>(self.locals.capacity(), "source local identities"),
            checked_capacity_bytes::<(HirOccurrenceId, Arc<OmittedFormal>)>(self.omitted_formals.capacity(), "omitted formal source identities"),
            checked_capacity_bytes::<OmittedFormal>(self.omitted_formals.len(), "omitted formal source records"),
        ], "candidate source plan")
    }
}
// Result callees have no direct formal-name supplier. Until that supplier is
// retained, admit only a source-grounded result whose entire Apply spine has
// no parameter/local/binder alias or unresolved join. This is opt-in deferral.
fn scoped_result_callee(source: &LocalSource, root: usize, plan: &mut Plan) -> Result<(), CollectionAvailabilityError> {
    let mut work = Vec::new(); work.try_reserve(1).map_err(|_| unavailable())?;
    plan.note_guard_stack(work.capacity())?; work.push(root);
    let mut steps = 0usize;
    while let Some(index) = work.pop() {
        plan.charge_scoped_work(1)?;
        steps = steps.checked_add(1).ok_or_else(unavailable)?;
        if steps > SCOPED_RECORD_LIMIT { return Err(unavailable()); }
        match &source.expressions().get(index).ok_or_else(invalid)?.form {
            LocalSourceForm::Apply { callee, argument, .. } => {
                work.try_reserve(2).map_err(|_| unavailable())?;
                plan.note_guard_stack(work.capacity())?;
                work.push(callee.ordinal() as usize); work.push(argument.ordinal() as usize);
            }
            LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. } => { work.try_reserve(1).map_err(|_| unavailable())?; plan.note_guard_stack(work.capacity())?; work.push(inner.ordinal() as usize); }
            LocalSourceForm::Block { bindings, final_expression } if bindings.is_empty() => { work.try_reserve(1).map_err(|_| unavailable())?; plan.note_guard_stack(work.capacity())?; work.push(final_expression.ordinal() as usize); }
            LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }
            | LocalSourceForm::Operation { .. } | LocalSourceForm::Integer(_) | LocalSourceForm::Unit
            | LocalSourceForm::Boolean(_) | LocalSourceForm::String(_) | LocalSourceForm::DecodedString(_) => {}
            _ => return Err(unavailable()),
        }
    }
    Ok(())
}
#[track_caller]
fn unavailable() -> CollectionAvailabilityError {
    if std::env::var_os("YU_SCOPED_COLLECTION_DIAGNOSTIC").is_some() {
        let caller = std::panic::Location::caller();
        eprintln!("candidate_collection.unavailable branch={}:{}:{}", caller.file(), caller.line(), caller.column());
    }
    CollectionAvailabilityError::ComponentIdentityExhausted
}
fn invalid() -> CollectionAvailabilityError {
    CollectionAvailabilityError::MissingDefinitionEndpoint
}
#[track_caller]
fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), CollectionAvailabilityError> {
    values.try_reserve(1).map_err(|_| unavailable())?;
    values.push(value);
    Ok(())
}
pub(super) fn preflight(source: &LocalSource, operation_v1: bool) -> Result<(), shadow_apply::CandidateError> {
    preflight_with_imports(source, operation_v1, &HashMap::new())
}

pub(super) fn preflight_with_imports(
    source: &LocalSource,
    operation_v1: bool,
    imported_definitions: &HashMap<yu_hir::SourceExportId, yu_hir::DefId>,
) -> Result<(), shadow_apply::CandidateError> {
    preflight_with_imports_and_roles(source, operation_v1, imported_definitions, &std::collections::HashSet::new())
}

pub(super) fn preflight_with_imports_and_roles(
    source: &LocalSource,
    operation_v1: bool,
    imported_definitions: &HashMap<yu_hir::SourceExportId, yu_hir::DefId>,
    authenticated_roles: &std::collections::HashSet<Box<str>>,
) -> Result<(), shadow_apply::CandidateError> {
    let mut referenced_catch_binders = std::collections::HashSet::new();
    if source.where_clauses().iter().any(|clause|
        !authenticated_roles.contains(clause.role.text.trim())) {

        // Only exact imported role identities may enter candidate collection;
        // the retained obligation must still be discharged by a same-row
        // selected implementation before the result can be published.
        return Err(shadow_apply::CandidateError::Unsupported);
    }
    for expr in source.expressions() {
        if let LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(id), .. } = &expr.form {
            referenced_catch_binders.try_reserve(1).map_err(|_| shadow_apply::CandidateError::Collection(unavailable()))?;
            referenced_catch_binders.insert(id);
        }
    }
    if source.annotation().is_some_and(|annotation| !preflight_annotation(&annotation.ty, true)) {
        return Err(shadow_apply::CandidateError::Unsupported);
    }
    for binding in source.bindings() {
        if binding.annotation.as_ref().is_some_and(|a| !preflight_local_annotation(&a.ty)) {
            return Err(shadow_apply::CandidateError::Unsupported);
        }
    }
    for expr in source.expressions() {
        if matches!(
            &expr.form,
            LocalSourceForm::Primitive { operation: yu_hir::shadow::PinnedPrimitiveOp::Unsupported(_) }
                | LocalSourceForm::InterpolatedString { lowered: None, .. },
        ) {
            return Err(shadow_apply::CandidateError::Unsupported);
        }
        if matches!(&expr.form, LocalSourceForm::Case { arms, .. }
            if arms.iter().any(|arm| matches!(arm.pattern, yu_hir::shadow::LocalSourceCasePattern::Variant { .. }))
                && !arms.iter().all(|arm| matches!(arm.pattern, yu_hir::shadow::LocalSourceCasePattern::Variant { .. }))) {
            return Err(shadow_apply::CandidateError::Unsupported);
        }
        if let LocalSourceForm::Ascription { annotation, .. } = &expr.form {
            if !preflight_local_annotation(&annotation.ty) {
                return Err(shadow_apply::CandidateError::Unsupported);
            }
        }
        if let LocalSourceForm::Lambda { parameter, .. } = &expr.form {
            if parameter.annotation.as_ref().is_some_and(|a| a.ty.effects.as_ref().is_some_and(|row| row.variables.len() > 1) || !preflight_formal_value(&a.ty.value, false)) {
                return Err(shadow_apply::CandidateError::Unsupported);
            }
        }
        if let LocalSourceForm::Operation { resolution } = &expr.form {
            match resolution {
                yu_hir::shadow::SourceOperationResolution::Resolved(declaration) if declaration.signature.effects.is_none() && matches!(declaration.signature.value, yu_hir::shadow::SourceAnnotationValue::Function { .. }) && operation_signature_values_supported(&declaration.signature) && preflight_annotation(&declaration.signature, true) => {},
                _ => return Err(shadow_apply::CandidateError::Unsupported),
            }
        }
        if let LocalSourceForm::Catch { arms, .. } = &expr.form {
            for arm in arms {
                if let yu_hir::shadow::LocalSourceCatchPattern::Operation { resolution, payloads, continuation, .. } = &arm.pattern {
                    match resolution {
                        yu_hir::shadow::SourceOperationResolution::Resolved(declaration)
                            if payloads.len() == 1 && declaration.signature.effects.is_none()
                            && matches!(declaration.signature.value, yu_hir::shadow::SourceAnnotationValue::Function { .. })
                            && monomorphic_signature(&declaration.signature)
                            && (preflight_catch_signature(&declaration.signature, payloads, continuation, &referenced_catch_binders)
                                || (operation_v1 && operation_v1_catch_source(source, expr, declaration, continuation)
                                    .is_some_and(|link| preflight_catch_signature_v1(&declaration.signature, payloads, continuation, &referenced_catch_binders, &link)))) => {},
                        _ => return Err(shadow_apply::CandidateError::Unsupported),
                    }
                }
            }
        }
        if let LocalSourceForm::Name { resolution, .. } = &expr.form {
            match resolution {
                LocalSourceResolution::Unresolved | LocalSourceResolution::Ambiguous => return Err(shadow_apply::CandidateError::Unsupported),
                LocalSourceResolution::Imported(id) if !imported_definitions.contains_key(id) => return Err(shadow_apply::CandidateError::Unsupported),
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(all(test, feature = "shadow-apply-candidate"))]
mod where_clause_source_tests {
    use super::*;

    #[test]
    fn candidate_preflight_does_not_drop_retained_declaration_prerequisites() {
        let text = "my display(value: 'a) =\n    where 'a: Display\n    value";
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "where-clause-source",
                "source.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        )
        .expect("HIR retains the declaration prerequisite");
        let binding = hir.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) => Some(binding),
            _ => None,
        }).expect("binding");
        let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
        assert_eq!(source.where_clauses().len(), 1);
        assert_eq!(source.where_clauses()[0].subject.text.trim(), "'a");
        assert_eq!(source.where_clauses()[0].role.text.trim(), "Display");
        assert!(matches!(
            preflight(source, false),
            Err(shadow_apply::CandidateError::Unsupported)
        ));
    }
}
pub(super) fn preflight_local_annotation(ty: &yu_hir::shadow::SourceAnnotationType) -> bool {
    preflight_annotation(ty, true)
}
fn preflight_formal(ty: &yu_hir::shadow::SourceAnnotationType, positive: bool) -> bool {
    ty.effects.as_ref().is_none_or(|row| if positive {
        row.variables.len() <= 1
    } else {
        (row.concrete.is_empty() && row.variables.len() == 1)
            || (!row.concrete.is_empty() && row.variables.is_empty())
    }) && preflight_formal_value(&ty.value, positive)
}
fn preflight_formal_value(value: &yu_hir::shadow::SourceAnnotationValue, positive: bool) -> bool {
    match value {
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } => preflight_formal(argument, !positive) && preflight_formal(result, positive),
        yu_hir::shadow::SourceAnnotationValue::Tuple(elements) => !elements.is_empty() && elements.iter()
            .all(|element| element.effects.is_none() && preflight_formal_value(&element.value, positive)),
        _ => true,
    }
}

#[cfg(all(test, feature = "shadow-apply-candidate"))]
mod formal_concrete_negative_source_tests {
    use super::*;

    fn parse_and_lower(text: &str) -> Result<Arc<yu_hir::HirModule>, yu_hir::HirAvailabilityError> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty(), "source must parse structurally: {text}");
        yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "formal-concrete-negative-source", "source.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).map(Arc::new)
    }

    fn source_for(formal: &str) -> String {
        format!("act io\nmy receive (f: {formal}) = f")
    }

    fn solve_formal(formal: &str) -> Result<crate::shadow_apply::CandidateInference, String> {
        let hir = parse_and_lower(&source_for(formal))
            .unwrap_or_else(|error| panic!("previously admitted `{formal}` failed HIR lowering: {error:?}"));
        crate::shadow_apply::CandidateInference::solve(hir)
            .map_err(|error| format!("solver: {error:?}"))
    }

    #[test]
    fn source_entry_admits_only_nonempty_concrete_negative_formal_rows() {
        let target = parse_and_lower(&source_for("((int -> [io] ()) -> ()) -> (() -> (int -> [io] ()))")).unwrap();
        let binding = target.items().iter().find_map(|item| match item {
            yu_hir::HirItem::Binding(binding) if binding.name().spelling() == "receive" => Some(binding),
            _ => None,
        }).expect("receive binding");
        let local_source = target.local_source(binding.definition_root()).unwrap().unwrap();
        let parameter = local_source.expressions().iter().find_map(|expression| match &expression.form {
            LocalSourceForm::Lambda { parameter, .. } => Some(parameter),
            _ => None,
        }).expect("annotated source lambda");
        let annotation = parameter.annotation.as_ref().expect("source formal annotation");
        let yu_hir::shadow::SourceAnnotationValue::Function { argument: outer_argument, .. } = &annotation.ty.value else { panic!("outer function"); };
        let yu_hir::shadow::SourceAnnotationValue::Function { argument: middle_argument, .. } = &outer_argument.value else { panic!("outer argument function"); };
        let yu_hir::shadow::SourceAnnotationValue::Function { result: row_owner, .. } = &middle_argument.value else { panic!("nested result function"); };
        let row = row_owner.effects.as_ref().expect("negative concrete effect row");
        assert!(row.variables.is_empty());
        assert_eq!(row.concrete, vec![target.source_effect_declarations()[0].id.clone()]);
        assert!(target.local_source_for(&annotation.owner).unwrap().is_some());

        let candidate = crate::shadow_apply::CandidateInference::solve(target.clone()).unwrap();
        assert!(candidate.observes_hir(&target));
        assert!(candidate.candidate_conflicts().is_empty());

        for formal in [
            "() -> (() -> int)",
            "() -> (() -> ['e] int)",
            "(() -> [io] int) -> ()",
        ] {
            let candidate = solve_formal(formal).unwrap_or_else(|error| panic!("previously admitted `{formal}` refused: {error:?}"));
            assert!(candidate.candidate_conflicts().is_empty(), "{formal}");
        }

        for formal in [
            "() -> (() -> [] int)",
            "() -> (() -> ['e, io] int)",
        ] {
            let hir = parse_and_lower(&source_for(formal))
                .unwrap_or_else(|error| panic!("expected HIR-supported refusal `{formal}`, got {error:?}"));
            let result = crate::shadow_apply::CandidateInference::solve(hir);
            assert!(result.is_err(), "neighboring negative row admitted: {formal}");
        }
        let multiple_symbol = parse_and_lower(&source_for("() -> (() -> ['e, 'f] int)"));
        assert!(matches!(multiple_symbol, Err(yu_hir::HirAvailabilityError::StructuralProjection)));
    }
}
fn preflight_annotation(ty: &yu_hir::shadow::SourceAnnotationType, positive: bool) -> bool {
    if let Some(row) = &ty.effects {
        if row.variables.len() > 1 || (!positive && !row.concrete.is_empty()) { return false; }
    }
    preflight_value(&ty.value, positive)
}
// Value construction ignores its own computation row. Function children each
// contribute their complete annotation according to their port variance.
fn preflight_value(value: &yu_hir::shadow::SourceAnnotationValue, positive: bool) -> bool {
    match value {
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } =>
            preflight_annotation(argument, !positive) && preflight_annotation(result, positive),
        yu_hir::shadow::SourceAnnotationValue::Tuple(elements) => !elements.is_empty() && elements.iter()
            .all(|element| element.effects.is_none() && preflight_value(&element.value, positive)),
        _ => true,
    }
}

fn preflight_catch_signature(
    ty: &yu_hir::shadow::SourceAnnotationType,
    payloads: &[yu_hir::shadow::LocalSourceCatchPayloadPattern],
    continuation: &yu_hir::shadow::LocalSourceCatchValuePattern,
    referenced: &std::collections::HashSet<&yu_hir::shadow::LocalSourceCatchBinderId>,
) -> bool {
    use yu_hir::shadow::{LocalSourceCatchPayloadPattern as Payload, LocalSourceCatchValuePattern as Value};
    let yu_hir::shadow::SourceAnnotationValue::Function { argument, result } = &ty.value else { return false; };
    let used = |pattern: &Value| matches!(pattern, Value::Binder(binder) if referenced.contains(&binder.id));
    let payload_used = payloads.iter().any(|payload| matches!(payload, Payload::Value(pattern) if used(pattern)));
    (!payload_used || (preflight_value(&argument.value, true) && preflight_value(&argument.value, false)))
        && (!used(continuation) || (preflight_value(&result.value, true) && preflight_value(&result.value, false)))
}
fn preflight_catch_signature_v1(
    ty: &yu_hir::shadow::SourceAnnotationType,
    payloads: &[yu_hir::shadow::LocalSourceCatchPayloadPattern],
    continuation: &yu_hir::shadow::LocalSourceCatchValuePattern,
    referenced: &std::collections::HashSet<&yu_hir::shadow::LocalSourceCatchBinderId>,
    link: &HandlerContinuationArgumentV1,
) -> bool {
    let mut masked = ty.clone();
    let SourceAnnotationValue::Function { result: callback, .. } = &mut masked.value else { return false; };
    let SourceAnnotationValue::Function { result: callback_result, .. } = &mut callback.value else { return false; };
    let Some(row) = callback_result.effects.as_ref() else { return false; };
    if row.position != link.declaration_field_position || row.concrete.len() != 1 || row.concrete[0] != link.field_family || !row.variables.is_empty() { return false; }
    callback_result.effects = None;
    preflight_catch_signature(&masked, payloads, continuation, referenced)
}

// This provisional matcher admits only a unique same-source handler argument
// and its uniquely linked callback-body operation. Missing or ambiguous edges
// preserve Unsupported; this is source evidence, not runtime request selection.
fn operation_v1_catch_source(
    source: &LocalSource,
    catch: &yu_hir::shadow::LocalSourceExpr,
    declaration: &Arc<yu_hir::shadow::SourceOperationDeclaration>,
    continuation: &yu_hir::shadow::LocalSourceCatchValuePattern,
) -> Option<HandlerContinuationArgumentV1> {
    use yu_hir::shadow::{LocalSourceCatchPattern as Pattern, LocalSourceCatchValuePattern as Value};
    let LocalSourceForm::Catch { scrutinee, arms } = &catch.form else { return None; };
    let Value::Binder(k) = continuation else { return None; };
    let mut matching_arms = arms.iter().filter(|arm| matches!(&arm.pattern,
        Pattern::Operation { resolution: yu_hir::shadow::SourceOperationResolution::Resolved(found), continuation: Value::Binder(b), .. }
            if found.id == declaration.id && b.id == k.id));
    let arm = matching_arms.next()?;
    if matching_arms.next().is_some() { return None; }
    fn children(source: &LocalSource, index: usize) -> Option<Vec<usize>> {
        use yu_hir::shadow::LocalSourceForm as F;
        let expression = source.expressions().get(index)?;
        let mut result = Vec::new();
        let capacity = match &expression.form {
            F::Catch { arms, .. } => 1usize.checked_add(arms.len())?,
            F::If { arms, else_branch } => arms.len().checked_mul(2)?.checked_add(usize::from(else_branch.is_some()))?,
            F::Sequence { items } => items.len(),
            F::Apply { .. } => 2,
            F::Block { bindings, .. } => bindings.len().checked_add(1)?,
            F::Group { .. } | F::Ascription { .. } | F::Lambda { .. } => 1,
            _ => 0,
        };
        result.try_reserve_exact(capacity).ok()?;
        match &expression.form {
            F::Catch { scrutinee, arms } => { result.push(scrutinee.ordinal() as usize); result.extend(arms.iter().map(|arm| arm.body.ordinal() as usize)); }
            F::If { arms, else_branch } => { for (condition, body) in arms { result.push(condition.ordinal() as usize); result.push(body.ordinal() as usize); } if let Some(branch)=else_branch { result.push(branch.ordinal() as usize); } }
            F::Sequence { items } => result.extend(items.iter().map(|item| item.ordinal() as usize)),
            F::Apply { callee, argument, .. } => { result.push(callee.ordinal() as usize); result.push(argument.ordinal() as usize); }
            F::Group { inner } | F::Ascription { inner, .. } => result.push(inner.ordinal() as usize),
            F::Lambda { body, .. } => result.push(body.ordinal() as usize),
            F::Block { bindings, final_expression } => { for binding in bindings { result.push(source.bindings().get(*binding as usize)?.initializer.ordinal() as usize); } result.push(final_expression.ordinal() as usize); }
            _ => {}
        }
        Some(result)
    }
    fn find(source: &LocalSource, root: usize, mut predicate: impl FnMut(usize, &yu_hir::shadow::LocalSourceExpr) -> bool) -> Option<usize> {
        let mut stack = Vec::new();
        stack.try_reserve_exact(source.expressions().len().min(32).max(1)).ok()?;
        stack.push(root);
        let mut seen = Vec::new();
        seen.try_reserve_exact(source.expressions().len()).ok()?;
        seen.resize(source.expressions().len(), false);
        let mut visited = 0usize;
        let mut found = None;
        while let Some(index) = stack.pop() {
            if index >= seen.len() || seen[index] { continue; }
            seen[index] = true;
            visited += 1;
            if visited > seen.len() { return None; }
            let expression = source.expressions().get(index)?;
            if predicate(index, expression) { if found.replace(index).is_some() { return None; } }
            for child in children(source, index)? {
                if stack.len() == stack.capacity() { stack.try_reserve(1).ok()?; }
                stack.push(child);
            }
        }
        found
    }
    let ping_apply = source.expression(scrutinee)?;
    let LocalSourceForm::Apply { callee: ping_callee, .. } = &ping_apply.form else { return None; };
    let ping = source.expression(ping_callee)?;
    if !matches!(&ping.form, LocalSourceForm::Operation { resolution: yu_hir::shadow::SourceOperationResolution::Resolved(found) } if found.id == declaration.id) { return None; }
    let apply_index = find(source, arm.body.ordinal() as usize, |_, expr| {
        let LocalSourceForm::Apply { callee, argument, .. } = &expr.form else { return false; };
        source.expression(callee).is_some_and(|callee| matches!(&callee.form, LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(found), .. } if found == &k.id))
            && source.expression(argument).is_some_and(|argument| matches!(&argument.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Local(_), .. }))
    })?;
    let apply = source.expressions().get(apply_index)?;
    let LocalSourceForm::Apply { callee, argument, .. } = &apply.form else { return None; };
    let callee = source.expression(callee)?;
    let argument = source.expression(argument)?;
    if !matches!(&callee.form, LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(found), .. } if found == &k.id) { return None; }
    let LocalSourceForm::Name { resolution: LocalSourceResolution::Local(response_definition), .. } = &argument.form else { return None; };
    let mut response_bindings = source.bindings().iter().filter(|binding| &binding.id == response_definition);
    let binding = response_bindings.next()?;
    if response_bindings.next().is_some() { return None; }
    let response_annotation = Arc::new(binding.annotation.clone()?);
    let SourceAnnotationValue::Function { result: expected_response, .. } = &declaration.signature.value else { return None; };
    if !same_source_annotation_type(&response_annotation.ty, expected_response) { return None; }
    let SourceAnnotationValue::Function { result: response_result, .. } = &expected_response.value else { return None; };
    let field_row = response_result.effects.as_ref()?;
    if field_row.concrete.len() != 1 || !field_row.variables.is_empty() { return None; }
    let LocalSourceForm::Lambda { body, .. } = &source.expression(&binding.initializer)?.form else { return None; };
    let body_apply = source.expression(body)?;
    let LocalSourceForm::Apply { callee: outer_callee, argument: callback_argument, .. } = &body_apply.form else { return None; };
    let outer_callee = source.expression(outer_callee)?;
    let LocalSourceForm::Operation { resolution: yu_hir::shadow::SourceOperationResolution::Resolved(callback_operation) } = &outer_callee.form else { return None; };
    if callback_operation.id.family != field_row.concrete[0] { return None; }
    let SourceAnnotationValue::Function { result: response_annotation_result, .. } = &response_annotation.ty.value else { return None; };
    let response_field_position = response_annotation_result.effects.as_ref()?.position.clone();
    Some(HandlerContinuationArgumentV1 {
        owner: source.source_root().clone(), request: ping.occurrence.clone(),
        catch_occurrence: catch.occurrence.clone(), arm_source: arm.source.clone(), declaration: declaration.id.clone(),
        continuation: k.id.clone(), apply_occurrence: apply.occurrence.clone(),
        argument_occurrence: argument.occurrence.clone(), response_definition: response_definition.clone(),
        response_annotation, declaration_field_position: field_row.position.clone(),
        response_field_position, field_family: field_row.concrete[0].clone(),
        callback_apply_occurrence: body_apply.occurrence.clone(), callback_argument_occurrence: source.expression(callback_argument)?.occurrence.clone(),
        callback_operation_occurrence: outer_callee.occurrence.clone(), callback_operation: Arc::clone(callback_operation),
    })
}
fn same_source_annotation_type(a: &yu_hir::shadow::SourceAnnotationType, b: &yu_hir::shadow::SourceAnnotationType) -> bool {
    let rows_match = match (&a.effects, &b.effects) {
        (None, None) => true,
        (Some(a), Some(b)) => a.concrete == b.concrete && a.variables == b.variables,
        _ => false,
    };
    rows_match && match (&a.value, &b.value) {
        (SourceAnnotationValue::Unit, SourceAnnotationValue::Unit) | (SourceAnnotationValue::Int, SourceAnnotationValue::Int)
        | (SourceAnnotationValue::Bool, SourceAnnotationValue::Bool) | (SourceAnnotationValue::Str, SourceAnnotationValue::Str) => true,
        (SourceAnnotationValue::Variable(a), SourceAnnotationValue::Variable(b)) => a == b,
        (SourceAnnotationValue::Hole(a), SourceAnnotationValue::Hole(b)) => a == b,
        (SourceAnnotationValue::Tuple(a), SourceAnnotationValue::Tuple(b)) => a.len() == b.len()
            && a.iter().zip(b).all(|(a, b)| same_source_annotation_type(a, b)),
        (SourceAnnotationValue::Function { argument: aa, result: ar }, SourceAnnotationValue::Function { argument: ba, result: br }) =>
            same_source_annotation_type(aa, ba) && same_source_annotation_type(ar, br),
        _ => false,
    }
}
// Generic arms require rigid existential opening (charter §§19–20).
fn monomorphic_signature(ty: &yu_hir::shadow::SourceAnnotationType) -> bool {
    ty.effects.as_ref().is_none_or(|row| row.variables.is_empty()) && match &ty.value {
        yu_hir::shadow::SourceAnnotationValue::Variable(_) | yu_hir::shadow::SourceAnnotationValue::Hole(_)
            | yu_hir::shadow::SourceAnnotationValue::Tuple(_) => false,
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } => monomorphic_signature(argument) && monomorphic_signature(result),
        _ => true,
    }
}
fn annotation_contains_unit(ty: &yu_hir::shadow::SourceAnnotationType) -> bool {
    match &ty.value {
        yu_hir::shadow::SourceAnnotationValue::Unit => true,
        yu_hir::shadow::SourceAnnotationValue::Tuple(elements) => elements.iter().any(annotation_contains_unit),
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } =>
            annotation_contains_unit(argument) || annotation_contains_unit(result),
        _ => false,
    }
}
fn operation_signature_values_supported(ty: &yu_hir::shadow::SourceAnnotationType) -> bool {
    match &ty.value {
        yu_hir::shadow::SourceAnnotationValue::Hole(_) | yu_hir::shadow::SourceAnnotationValue::Tuple(_) => false,
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } =>
            operation_signature_values_supported(argument) && operation_signature_values_supported(result),
        _ => true,
    }
}

pub(super) fn retain_placeholder_errors(expr: &ResolvedExpr, permitted: &mut HashSet<yu_hir::HirErrorId>) -> Result<(), shadow_apply::CandidateError> {
    // The HIR carrier owns this unsupported legacy placeholder. Its successful
    // source formation is checked separately; unrelated diagnostics stay visible.
    let mut current = expr;
    loop {
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            ResolvedExpr::Error { errors, .. } => {
                permitted.try_reserve(errors.len()).map_err(|_| shadow_apply::CandidateError::Unsupported)?;
                permitted.extend(errors.iter().copied());
                break;
            }
            _ => break,
        }
    }
    Ok(())
}
#[derive(Clone, Copy)]
enum Work {
    Visit(usize, u32, SourceRegionId),
    Finish(usize, u32),
    Install(usize, usize, u32),
    Initializer(usize, u32, SourceRegionId),
    CatchArms(usize, u32, SourceRegionId),
    CaseArms(usize, u32, SourceRegionId),
    CaseArmBody(usize, usize, u32, SourceRegionId),
    RestoreCaseGuards(usize),
}
impl ConstraintBatch {
    fn prepare_source_annotation_primitives(&mut self, ty: &yu_hir::shadow::SourceAnnotationType) -> Result<(), CollectionAvailabilityError> {
        match &ty.value {
            yu_hir::shadow::SourceAnnotationValue::Tuple(elements) => {
                for element in elements { self.prepare_source_annotation_primitives(element)?; }
            }
            yu_hir::shadow::SourceAnnotationValue::Bool => { self.term_for_leaf(Leaf::BoolPositive)?; self.term_for_leaf(Leaf::BoolNegative)?; }
            yu_hir::shadow::SourceAnnotationValue::Str => { self.term_for_leaf(Leaf::StrPositive)?; self.term_for_leaf(Leaf::StrNegative)?; }
            yu_hir::shadow::SourceAnnotationValue::Function { argument, result } => {
                self.prepare_source_annotation_primitives(argument)?;
                self.prepare_source_annotation_primitives(result)?;
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn emit_candidate_source<'a>(
        &mut self,
        source: &'a LocalSource,
        parent: &SourceReceiver,
        hir: &Arc<HirModule>,
        hir_index: usize,
        imported_definitions: &'a HashMap<yu_hir::SourceExportId, DefId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        let owner = source.source_root();
        let original = hir.local_source_for(owner).map_err(|_| invalid())?.ok_or_else(invalid)?;
        if !std::ptr::eq(source, original) { return Err(invalid()); }
        match (parent, owner) {
            (SourceReceiver::Definition(id), SourceRootId::Definition(root))
                if self.definitions.get(id.ordinal() as usize).is_some_and(|record| &record.definition == id && &record.root == root) => {},
            (SourceReceiver::Expression(root), SourceRootId::Expression(actual)) if root == actual => {},
            (SourceReceiver::Member(root), SourceRootId::Member(actual)) if root == actual => {},
            _ => return Err(invalid()),
        }
        self.candidate_source.source_owners.try_reserve(source.expressions().len()).map_err(|_| unavailable())?;
        self.occurrence_hir_positions.try_reserve(source.expressions().len()).map_err(|_| unavailable())?;
        for expr in source.expressions() {
            if !hir.owns_occurrence(&expr.occurrence) { return Err(invalid()); }
            if self.occurrence_hir_positions.insert(expr.occurrence.clone(), hir_index).is_some_and(|previous| previous != hir_index) { return Err(invalid()); }
            if self.candidate_source.source_owners.insert(expr.occurrence.clone(), owner.clone()).is_some_and(|previous| &previous != owner) {
                return Err(invalid());
            }
        }
        self.candidate_source.references.retain_source(source)?;
        let mut positions = Vec::new();
        positions.try_reserve_exact(source.expressions().len()).map_err(|_| unavailable())?;
        let mut parameters = HashMap::new();
        let mut local_slots = HashMap::new();
        let mut lambdas = HashMap::new();
        let mut formal_registrations = HashMap::new();
        let mut parameter_scopes = HashMap::new();
        let mut catch_arm_scopes = HashMap::new();
        for parameter in source.root_parameters() {
            let position = self.parameter_recipes.len();
            push(&mut self.parameter_recipes, parameter.id.clone())?;
            parameters.try_reserve(1).map_err(|_| unavailable())?;
            parameters.insert(parameter.id.clone(), position);
            self.candidate_source.parameter_levels.try_reserve(1).map_err(|_| unavailable())?;
            self.candidate_source.parameter_levels.insert(position, 1);
        }
        for binding in source.bindings() {
            parameter_scopes.try_reserve(binding.parameters.len()).map_err(|_| unavailable())?;
            for parameter in &binding.parameters {
                parameter_scopes.insert(parameter.id.clone(), candidate_effect::AnnotationScope::Local(binding.id.clone()));
            }
        }
        for (index, expr) in source.expressions().iter().enumerate() {
            positions.push(self.candidate_component(&expr.occurrence)?);
            if let LocalSourceForm::Catch { arms, .. } = &expr.form {
                catch_arm_scopes.try_reserve(arms.len()).map_err(|_| unavailable())?;
                for arm in arms { catch_arm_scopes.insert(arm.source.clone(), candidate_effect::AnnotationScope::Expression(arm.body.clone())); }
            }
            if let LocalSourceForm::Lambda { parameter, .. } = &expr.form {
                let position = self.parameter_recipes.len();
                push(&mut self.parameter_recipes, parameter.id.clone())?;
                parameters.try_reserve(1).map_err(|_| unavailable())?;
                parameters.insert(parameter.id.clone(), position);
                let registration = self.candidate_calls.formals.len();
                push(&mut self.candidate_calls.formals, candidate_call::FormalRegistrationInput {
                    owner: owner.clone(), lambda: index,
                    parameter: parameter.id.clone(), recipe_position: position, native_root: None,
                    role: if parameter.annotation.as_ref().is_some_and(|a| a.ty.effects.is_some()) { candidate_call::FormalRole::Computation } else { candidate_call::FormalRole::Value },
                    entry_effect: None, receiver_body: None,
                    scope: parameter_scopes.get(&parameter.id).cloned().unwrap_or_else(|| candidate_effect::AnnotationScope::for_source(owner.clone())),
                })?;
                formal_registrations.try_reserve(1).map_err(|_| unavailable())?;
                formal_registrations.insert(parameter.id.clone(), registration);
                for field in parameter.record_pattern.iter().flatten() {
                    let position = self.parameter_recipes.len();
                    push(&mut self.parameter_recipes, field.binder.clone())?;
                    parameters.try_reserve(1).map_err(|_| unavailable())?;
                    if parameters.insert(field.binder.clone(), position).is_some() { return Err(invalid()); }
                }
            }
        }
        for binding in source.bindings() {
            let slot = self.candidate_source.locals.len();
            push(&mut self.candidate_source.locals, binding.id.clone())?;
            local_slots.try_reserve(1).map_err(|_| unavailable())?;
            local_slots.insert(binding.id.clone(), slot);
        }
        let mut endpoints = Vec::new();
        endpoints.try_reserve_exact(positions.len()).map_err(|_| unavailable())?;
        for (index, expr) in source.expressions().iter().enumerate() {
            let endpoint = match &expr.form {
                LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(parameter), .. } =>
                    CandidateEndpoint::Parameter(*parameters.get(parameter).ok_or_else(invalid)?),
                _ => CandidateEndpoint::Component(positions[index].value),
            };
            endpoints.push(endpoint);
        }
        let mut ascription_children = HashMap::new();
        // Resolve aliases before recursive initializer links capture endpoints.
        // Group facades stay intact; only an ascription peels parentheses.
        for (index, expr) in source.expressions().iter().enumerate() {
            if let LocalSourceForm::Ascription { inner, .. } = &expr.form {
                let mut child = inner.ordinal() as usize;
                loop {
                    match &source.expressions()[child].form {
                        LocalSourceForm::Ascription { inner, .. } | LocalSourceForm::Group { inner } => child = inner.ordinal() as usize,
                        _ => break,
                    }
                }
                ascription_children.try_reserve(1).map_err(|_| unavailable())?;
                ascription_children.insert(index, child);
                positions[index] = positions[child];
                *self.occurrence_component_positions.get_mut(&expr.occurrence).ok_or_else(invalid)? = positions[child];
                endpoints[index] = endpoints[child];
            }
        }
        let mut formal_names = Vec::new();
        formal_names.try_reserve_exact(positions.len()).map_err(|_| unavailable())?;
        formal_names.resize(positions.len(), None);
        for (index, expr) in source.expressions().iter().enumerate() {
            if let LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(parameter), .. } = &expr.form {
                // Member receivers are source parameters too, but are not lambda
                // formals and therefore have no candidate-call registration.
                if let Some(&registration) = formal_registrations.get(parameter) {
                    let name = self.candidate_calls.names.len();
                    push(&mut self.candidate_calls.names, candidate_call::FormalNameInput {
                        owner: owner.clone(), expression: index,
                        registration,
                    })?;
                    formal_names[index] = Some(name);
                }
            }
        }
        let mut catch_positions = HashMap::new();
        let mut case_positions = HashMap::new();
        for (index, expr) in source.expressions().iter().enumerate() {
            if let LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(id), .. } = &expr.form {
                catch_positions.try_reserve(1).map_err(|_| unavailable())?;
                catch_positions.entry(id.clone()).or_insert(positions[index].value);
            }
            if let LocalSourceForm::Name { resolution: LocalSourceResolution::CaseBinder(id), .. } = &expr.form {
                case_positions.try_reserve(1).map_err(|_| unavailable())?;
                case_positions.entry(id.clone()).or_insert(positions[index].value);
            }
        }
        let mut catch_binders = HashMap::new();
        let mut case_binders = HashMap::new();
        let mut case_guards = Vec::new();
        let mut actions = Vec::new();
        let mut field_bound_v1 = Vec::new();
        let mut work = Vec::new();
        // Only currently forming function initializers use an open monomorphic
        // root. Published locals continue through the ordinary scheme route.
        let mut active_initializers = HashMap::new();
        active_initializers.try_reserve(source.bindings().len()).map_err(|_| unavailable())?;
        let definition_region = self.candidate_source.region(None)?;
        if self.candidate_source.scoped_experiment {
            self.candidate_source.definition_regions.try_reserve(1).map_err(|_| unavailable())?;
            if let SourceRootId::Definition(definition) = owner {
                self.candidate_source.definition_regions.insert(definition.clone(), definition_region);
            }
        }
        push(&mut work, Work::Visit(source.body().ordinal() as usize, 1, definition_region))?;
        while let Some(next) = work.pop() {
            match next {
                Work::Visit(index, level, region) => {
                    self.candidate_source.computation_scope(&source.expressions()[index].occurrence, region)?;
                    let expr = source.expressions().get(index).ok_or_else(invalid)?;
                    if let LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(binder), .. } = &expr.form {
                        endpoints[index] = *catch_binders.get(binder).ok_or_else(invalid)?;
                    }
                    if let LocalSourceForm::Name { resolution: LocalSourceResolution::CaseBinder(binder), .. } = &expr.form {
                        endpoints[index] = *case_binders.get(binder).ok_or_else(invalid)?;
                    }
                    let pos = positions[index];
                    self.candidate_source.component_levels.try_reserve(2).map_err(|_| unavailable())?;
                    // A Catch binder's representative is introduced at the arm level;
                    // its first Name can occur inside a deeper initializer.
                    self.candidate_source.component_levels.entry(pos.value).or_insert(level);
                    self.candidate_source.component_levels.insert(pos.effect, level);
                    push(&mut work, Work::Finish(index, level))?;
                    match &expr.form {
                        LocalSourceForm::Catch { scrutinee, .. } => {
                            push(&mut work, Work::CatchArms(index, level, region))?;
                            push(&mut work, Work::Visit(scrutinee.ordinal() as usize, level, region))?;
                        }
                        LocalSourceForm::Case { scrutinee, .. } => {
                            // LIFO must visit the scrutinee before CaseArms copies its
                            // endpoint into arm binders. CaseArms owns the only visits
                            // of the arm patterns and bodies.
                            push(&mut work, Work::CaseArms(index, level, region))?;
                            push(&mut work, Work::Visit(scrutinee.ordinal() as usize, level, region))?;
                        }
                        LocalSourceForm::If { arms, else_branch } => {
                            if let Some(else_branch) = else_branch {
                                push(&mut work, Work::Visit(else_branch.ordinal() as usize, level, region))?;
                            }
                            for (condition, body) in arms.iter().rev() {
                                push(&mut work, Work::Visit(body.ordinal() as usize, level, region))?;
                                push(&mut work, Work::Visit(condition.ordinal() as usize, level, region))?;
                            }
                        }
                        LocalSourceForm::Sequence { items } => {
                            for item in items.iter().rev() {
                                push(&mut work, Work::Visit(item.ordinal() as usize, level, region))?;
                            }
                        }
                        LocalSourceForm::Variant { payloads, .. } => {
                            for payload in payloads.iter().rev() { push(&mut work, Work::Visit(payload.ordinal() as usize, level, region))?; }
                        }
                        LocalSourceForm::InterpolatedString { lowered: None, .. } => return Err(unavailable()),
                        LocalSourceForm::Record { fields } => {
                            for field in fields.iter().rev() { push(&mut work, Work::Visit(field.value.ordinal() as usize, level, region))?; }
                        }
                        LocalSourceForm::Tuple { elements } => {
                            for element in elements.iter().rev() {
                                push(&mut work, Work::Visit(element.ordinal() as usize, level, region))?;
                            }
                        }
                        LocalSourceForm::FieldTail { receiver, .. } | LocalSourceForm::GeneratedFormatSelection { receiver, .. } => {
                            push(&mut work, Work::Visit(receiver.ordinal() as usize, level, region))?;
                        }
                        LocalSourceForm::Apply { callee, argument, .. } => {
                            push(&mut work, Work::Visit(argument.ordinal() as usize, level, region))?;
                            push(&mut work, Work::Visit(callee.ordinal() as usize, level, region))?;
                        }
                        LocalSourceForm::OperatorApplication { left, right, .. } => {
                            if let Some(right) = right { push(&mut work, Work::Visit(right.ordinal() as usize, level, region))?; }
                            push(&mut work, Work::Visit(left.ordinal() as usize, level, region))?;
                        }
                        LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. }
                        | LocalSourceForm::InterpolatedString { lowered: Some(inner), .. } => push(&mut work, Work::Visit(inner.ordinal() as usize, level, region))?,
                        LocalSourceForm::Lambda { parameter, body } => {
                            push(&mut actions, Action::BeginLambda)?;
                            let position = *parameters.get(&parameter.id).ok_or_else(invalid)?;
                            self.candidate_source.parameter_levels.try_reserve(1).map_err(|_| unavailable())?;
                            self.candidate_source.parameter_levels.insert(position, level);
                            lambdas.try_reserve(1).map_err(|_| unavailable())?;
                            lambdas.insert(index, position);
                            if parameter.annotation.is_none() && !parameter.unit_pattern && parameter.record_pattern.is_none() {
                                self.candidate_source.omitted_formals.try_reserve(1).map_err(|_| unavailable())?;
                                self.candidate_source.omitted_formals.insert(expr.occurrence.clone(), Arc::new(OmittedFormal {
                                    owner: owner.clone(), lambda: expr.occurrence.clone(),
                                    formal: parameter.id.clone(), position: parameter.source.clone(),
                                    scope: self.candidate_calls.formals[*formal_registrations.get(&parameter.id).ok_or_else(invalid)?].scope.clone(),
                                }));
                            }
                            if let Some(fields) = &parameter.record_pattern {
                                let mut recipe_fields = Vec::new();
                                recipe_fields.try_reserve_exact(fields.len()).map_err(|_| unavailable())?;
                                self.candidate_source.parameter_levels.try_reserve(fields.len()).map_err(|_| unavailable())?;
                                let mut count = 2usize;
                                for field in fields {
                                    let field_position = *parameters.get(&field.binder).ok_or_else(invalid)?;
                                    self.candidate_source.parameter_levels.insert(field_position, level);
                                    if field.default.is_some() { count = count.checked_add(2).ok_or_else(unavailable)?; }
                                    recipe_fields.push(RecordParameterField { label: field.label.clone(), parameter: field_position,
                                        default: field.default.as_ref().map(|default| endpoints[default.ordinal() as usize]) });
                                }
                                push(&mut actions, Action::RecordParameter { parameter: position, fields: recipe_fields, occurrence: expr.occurrence.clone() })?;
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(count).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(count).ok_or_else(unavailable)?;
                            }
                            if parameter.unit_pattern {
                                if parameter.annotation.is_some() { return Err(unavailable()); }
                                self.term_for_leaf(Leaf::UnitPositive)?;
                                self.term_for_leaf(Leaf::UnitNegative)?;
                                push(&mut actions, Action::UnitParameter { parameter: position, occurrence: expr.occurrence.clone() })?;
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2).ok_or_else(unavailable)?;
                            }
                            if let Some(annotation) = &parameter.annotation {
                                let annotation = Arc::new(annotation.clone());
                                if annotation.ty.effects.is_some() {
                                    let registration = *formal_registrations.get(&parameter.id).ok_or_else(invalid)?;
                                    push(&mut actions, Action::FormalEntry { registration, annotation: Arc::clone(&annotation), occurrence: expr.occurrence.clone(), scope: self.candidate_calls.formals[registration].scope.clone() })?;
                                    if annotation.ty.effects.as_ref().is_some_and(|row| !row.variables.is_empty()) {
                                        self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2).ok_or_else(unavailable)?;
                                        self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2).ok_or_else(unavailable)?;
                                    }
                                }
                                for leaf in [Leaf::IntPositive, Leaf::IntNegative] { self.term_for_leaf(leaf)?; }
                                self.prepare_source_annotation_primitives(&annotation.ty)?;
                                if annotation_contains_unit(&annotation.ty) {
                                    self.term_for_leaf(Leaf::UnitPositive)?;
                                    self.term_for_leaf(Leaf::UnitNegative)?;
                                }
                                push(&mut actions, Action::FormalAnnotation { annotation: Arc::clone(&annotation), parameter: position, occurrence: expr.occurrence.clone(), scope: parameter_scopes.get(&parameter.id).cloned().unwrap_or_else(|| candidate_effect::AnnotationScope::for_source(owner.clone())) })?;
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2).ok_or_else(unavailable)?;
                            }
                            let body_region = self.candidate_source.region(Some(region))?;
                            if self.candidate_source.scoped_experiment {
                                let registration = *formal_registrations.get(&parameter.id).ok_or_else(invalid)?;
                                self.candidate_calls.formals[registration].receiver_body = Some((
                                    source.expressions()[body.ordinal() as usize].occurrence.clone(), body_region));
                            }
                            push(&mut work, Work::Visit(body.ordinal() as usize, level, body_region))?;
                            for field in parameter.record_pattern.iter().flatten().rev() {
                                if let Some(default) = &field.default {
                                    push(&mut work, Work::Visit(default.ordinal() as usize, level, body_region))?;
                                }
                            }
                        }
                        LocalSourceForm::StatementBlock { statements, final_expression } => {
                            push(&mut work, Work::Visit(final_expression.ordinal() as usize, level, region))?;
                            let child = level.checked_add(1).ok_or_else(unavailable)?;
                            for statement in statements.iter().rev() {
                                match statement {
                                    LocalSourceStatement::Expression(expression) =>
                                        push(&mut work, Work::Visit(expression.ordinal() as usize, level, region))?,
                                    LocalSourceStatement::Binding(binding) => {
                                        source.bindings().get(*binding as usize).ok_or_else(invalid)?;
                                        push(&mut work, Work::Install(*binding as usize, index, level))?;
                                        push(&mut work, Work::Initializer(*binding as usize, child, region))?;
                                    }
                                }
                            }
                        }
                        LocalSourceForm::Block { bindings, final_expression } => {
                            push(&mut work, Work::Visit(final_expression.ordinal() as usize, level, region))?;
                            let child = level.checked_add(1).ok_or_else(unavailable)?;
                            for &binding in bindings.iter().rev() {
                                source.bindings().get(binding as usize).ok_or_else(invalid)?;
                                push(&mut work, Work::Install(binding as usize, index, level))?;
                                push(&mut work, Work::Initializer(binding as usize, child, region))?;
                            }
                        }
                        _ => {}
                    }
                }
                Work::CatchArms(index, level, region) => {
                    let LocalSourceForm::Catch { scrutinee, arms } = &source.expressions()[index].form else { return Err(invalid()); };
                    for arm in arms {
                        use yu_hir::shadow::{LocalSourceCatchPattern as Pattern, LocalSourceCatchPayloadPattern as Payload, LocalSourceCatchValuePattern as Value};
                        match &arm.pattern {
                            Pattern::Value(Value::Binder(binder)) => {
                                catch_binders.try_reserve(1).map_err(|_| unavailable())?;
                                catch_binders.insert(binder.id.clone(), endpoints[scrutinee.ordinal() as usize]);
                            }
                            Pattern::Value(Value::Wildcard) => {},
                            Pattern::Operation { resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration), payloads, continuation: continuation_pattern, .. } => {
                                let h_arg = if self.candidate_source.operation_v1 { operation_v1_catch_source(source, &source.expressions()[index], declaration, continuation_pattern) } else { None };
                                let mut retain = |pattern: &Value| -> Result<Option<usize>, CollectionAvailabilityError> {
                                    let Value::Binder(binder) = pattern else { return Ok(None); };
                                    let position = catch_positions.get(&binder.id).copied();
                                    if let Some(position) = position {
                                        catch_binders.try_reserve(1).map_err(|_| unavailable())?;
                                        catch_binders.insert(binder.id.clone(), CandidateEndpoint::Component(position));
                                        self.candidate_source.component_levels.try_reserve(1).map_err(|_| unavailable())?;
                                        self.candidate_source.component_levels.insert(position, level);
                                    }
                                    Ok(position)
                                };
                                let payload = match &payloads[0] { Payload::Value(pattern) => retain(pattern)?, Payload::Unit { .. } => None };
                                let continuation = retain(continuation_pattern)?;
                                self.term_for_leaf(Leaf::IntPositive)?;
                                self.term_for_leaf(Leaf::IntNegative)?;
                                self.prepare_source_annotation_primitives(&declaration.signature)?;
                                if annotation_contains_unit(&declaration.signature) {
                                    self.term_for_leaf(Leaf::UnitPositive)?;
                                    self.term_for_leaf(Leaf::UnitNegative)?;
                                }
                                self.term_for_leaf(Leaf::EffectBottomPositive)?;
                                self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                                let count = 2 * usize::from(payload.is_some()) + 4 * usize::from(continuation.is_some()) + 2 * usize::from(h_arg.is_some());
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(count).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(count).ok_or_else(unavailable)?;
                                if let Some(link) = &h_arg { field_bound_v1.try_reserve(1).map_err(|_| unavailable())?; field_bound_v1.push((Arc::clone(declaration), link.clone())); }
                                push(&mut actions, Action::CatchOperation { declaration: Arc::clone(declaration), owner: owner.clone(), occurrence: source.expressions()[arm.body.ordinal() as usize].occurrence.clone(), payload, continuation, original: endpoints[scrutinee.ordinal() as usize], effect: positions[scrutinee.ordinal() as usize].effect, level, h_arg })?;
                            }
                            _ => return Err(invalid()),
                        }
                    }
                    for arm in arms.iter().rev() { push(&mut work, Work::Visit(arm.body.ordinal() as usize, level, region))?; }
                }
                Work::CaseArms(index, level, region) => {
                    let LocalSourceForm::Case { scrutinee, arms } = &source.expressions()[index].form else { return Err(invalid()); };
                    let mut variant_alternatives = Vec::new();
                    for (arm_index, arm) in arms.iter().enumerate() {
                        match &arm.pattern {
                            yu_hir::shadow::LocalSourceCasePattern::Binder(binder) => {
                                case_binders.try_reserve(1).map_err(|_| unavailable())?;
                                case_binders.insert(binder.id.clone(), endpoints[scrutinee.ordinal() as usize]);
                                if let Some(position) = case_positions.get(&binder.id).copied() {
                                    self.candidate_source.component_levels.try_reserve(1).map_err(|_| unavailable())?;
                                    self.candidate_source.component_levels.insert(position, level);
                                }
                            }
                            yu_hir::shadow::LocalSourceCasePattern::Tuple { source: pattern_source, elements, .. } => {
                                let mut tuple_elements = Vec::new();
                                tuple_elements.try_reserve_exact(elements.len()).map_err(|_| unavailable())?;
                                for element in elements {
                                    match element {
                                        yu_hir::shadow::LocalSourceCasePatternElement::Binder(binder) => {
                                            let component = case_positions.get(&binder.id).copied();
                                            if let Some(position) = component {
                                                self.candidate_source.component_levels.try_reserve(1).map_err(|_| unavailable())?;
                                                self.candidate_source.component_levels.insert(position, level);
                                                case_binders.try_reserve(1).map_err(|_| unavailable())?;
                                                case_binders.insert(binder.id.clone(), CandidateEndpoint::Component(position));
                                            }
                                            tuple_elements.push(component.map(CandidateEndpoint::Component));
                                        }
                                        yu_hir::shadow::LocalSourceCasePatternElement::Wildcard => tuple_elements.push(None),
                                    }
                                }
                                let occurrence = source.expressions()[index].occurrence.clone();
                                let local_slot = u32::try_from(arm_index).map_err(|_| unavailable())?;
                                let recipe = self.candidate_recipes.len();
                                self.retain_candidate_relation(&occurrence, CandidateRelation::TuplePattern {
                                    source: pattern_source.clone(),
                                    local_slot,
                                    scrutinee: endpoints[scrutinee.ordinal() as usize],
                                    elements: tuple_elements,
                                    level,
                                })?;
                                push(&mut actions, Action::Candidate(recipe))?;
                            }
                            yu_hir::shadow::LocalSourceCasePattern::Variant { tag, elements, .. } => {
                                let mut payloads = Vec::new();
                                payloads.try_reserve_exact(elements.len()).map_err(|_| unavailable())?;
                                for element in elements {
                                    let component = match element {
                                        yu_hir::shadow::LocalSourceCasePatternElement::Binder(binder) => {
                                            let component = case_positions.get(&binder.id).copied();
                                            if let Some(position) = component {
                                                self.candidate_source.component_levels.try_reserve(1).map_err(|_| unavailable())?;
                                                self.candidate_source.component_levels.insert(position, level);
                                                case_binders.try_reserve(1).map_err(|_| unavailable())?;
                                                case_binders.insert(binder.id.clone(), CandidateEndpoint::Component(position));
                                            }
                                            component.map(CandidateEndpoint::Component)
                                        }
                                        yu_hir::shadow::LocalSourceCasePatternElement::Wildcard => None,
                                    };
                                    payloads.push(component);
                                }
                                variant_alternatives.try_reserve(1).map_err(|_| unavailable())?;
                                variant_alternatives.push(VariantAlternative { tag: tag.clone(), payloads: payloads.into_boxed_slice() });
                            }
                            yu_hir::shadow::LocalSourceCasePattern::Integer(_) | yu_hir::shadow::LocalSourceCasePattern::Wildcard => {}
                        }
                    }
                    if !variant_alternatives.is_empty() {
                        if variant_alternatives.len() != arms.len() { return Err(unavailable()); }
                        let recipe = self.candidate_recipes.len();
                        self.retain_candidate_relation(&source.expressions()[index].occurrence, CandidateRelation::VariantCase {
                            scrutinee: endpoints[scrutinee.ordinal() as usize], alternatives: variant_alternatives, level,
                        })?;
                        push(&mut actions, Action::Candidate(recipe))?;
                    }
                    for (arm_index, arm) in arms.iter().enumerate().rev() {
                        push(&mut work, Work::CaseArmBody(index, arm_index, level, region))?;
                        if let yu_hir::shadow::LocalSourceCasePattern::Integer(pattern) = &arm.pattern {
                            push(&mut work, Work::Visit(pattern.ordinal() as usize, level, region))?;
                        }
                    }
                }
                Work::RestoreCaseGuards(length) => { case_guards.truncate(length); }
                Work::CaseArmBody(index, arm_index, level, region) => {
                    let expr = &source.expressions()[index];
                    let LocalSourceForm::Case { scrutinee, arms } = &expr.form else { return Err(invalid()); };
                    let arm = arms.get(arm_index).ok_or_else(invalid)?;
                    if let yu_hir::shadow::LocalSourceCasePattern::Variant { tag, elements, .. } = &arm.pattern {
                        push(&mut work, Work::RestoreCaseGuards(case_guards.len()))?;
                        push(&mut case_guards, candidate_scheme::SourceCaseGuard {
                            case: expr.occurrence.clone(), arm: arm_index, tag: tag.clone(), arity: elements.len(),
                            input: endpoints[scrutinee.ordinal() as usize],
                        })?;
                    }
                    push(&mut work, Work::Visit(arm.body.ordinal() as usize, level, region))?;
                }
                Work::Initializer(binding, level, parent_region) => {
                    let region = self.candidate_source.region(Some(parent_region))?;
                    if self.candidate_source.scoped_experiment {
                        self.candidate_source.local_regions.try_reserve(1).map_err(|_| unavailable())?;
                        self.candidate_source.local_regions.insert(source.bindings()[binding].id.clone(), region);
                    }
                    let binding = &source.bindings()[binding];
                    push(&mut actions, Action::BeginLocal { slot: local_slots[&binding.id] })?;
                    if !binding.parameters.is_empty() {
                        active_initializers.insert(binding.id.clone(), endpoints[binding.initializer.ordinal() as usize]);
                    }
                    push(&mut work, Work::Visit(binding.initializer.ordinal() as usize, level, region))?;
                }
                Work::Install(binding, block, boundary) => {
                    let binding = &source.bindings()[binding];
                    active_initializers.remove(&binding.id);
                    let init = positions[binding.initializer.ordinal() as usize];
                    let occurrence = &source.expressions()[binding.initializer.ordinal() as usize].occurrence;
                    // Initialization effects are one-shot computation, outside
                    // the generalized value interface and every later fresh use.
                    let start = self.occurrences.len();
                    self.emit(occurrence.clone(), 20, self.component_term_at(init.effect), self.component_term_at(positions[block].effect))?;
                    self.append_source_facts(start, &mut actions)?;
                    if let Some(annotation) = &binding.annotation {
                        for leaf in [Leaf::IntPositive, Leaf::IntNegative] { self.term_for_leaf(leaf)?; }
                        self.prepare_source_annotation_primitives(&annotation.ty)?;
                        if annotation_contains_unit(&annotation.ty) {
                            self.term_for_leaf(Leaf::UnitPositive)?;
                            self.term_for_leaf(Leaf::UnitNegative)?;
                        }
                        push(&mut actions, Action::LocalAnnotation { annotation: Arc::new(annotation.clone()), slot: local_slots[&binding.id], endpoint: endpoints[binding.initializer.ordinal() as usize], computation_effect: init.effect, occurrence: occurrence.clone(), level: boundary.checked_add(1).ok_or_else(unavailable)?, boundary })?;
                        self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2 + usize::from(annotation.ty.effects.is_some())).ok_or_else(unavailable)?;
                        self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2 + usize::from(annotation.ty.effects.is_some())).ok_or_else(unavailable)?;
                    } else {
                        push(&mut actions, Action::Install { slot: local_slots[&binding.id], initializer: endpoints[binding.initializer.ordinal() as usize], boundary })?;
                    }
                }
                Work::Finish(index, level) => {
                    let expr = &source.expressions()[index];
                    let pos = positions[index];
                    let occurrence = &expr.occurrence;
                    let start = self.occurrences.len();
                    match &expr.form {
                        LocalSourceForm::Integer(_) | LocalSourceForm::Unit | LocalSourceForm::Boolean(_) | LocalSourceForm::String(_) | LocalSourceForm::DecodedString(_) => {
                            let (positive_leaf, negative_leaf) = match &expr.form {
                                LocalSourceForm::Unit => (Leaf::UnitPositive, Leaf::UnitNegative),
                                LocalSourceForm::Boolean(_) => (Leaf::BoolPositive, Leaf::BoolNegative),
                                LocalSourceForm::String(_) | LocalSourceForm::DecodedString(_) => (Leaf::StrPositive, Leaf::StrNegative),
                                _ => (Leaf::IntPositive, Leaf::IntNegative),
                            };
                            let positive = self.term_for_leaf(positive_leaf)?;
                            let negative = self.term_for_leaf(negative_leaf)?;
                            self.emit(occurrence.clone(), 0, positive, self.component_term_at(pos.value))?;
                            self.emit(occurrence.clone(), 1, self.component_term_at(pos.value), negative)?;
                            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                            self.emit(occurrence.clone(), 2, bottom, self.component_term_at(pos.effect))?;
                            self.emit(occurrence.clone(), 3, self.component_term_at(pos.effect), empty)?;
                        }
                        LocalSourceForm::Catch { scrutinee, arms } => {
                            let result = self.component_term_at(pos.value);
                            let result_effect = self.component_term_at(pos.effect);
                            let scrutinee_index = scrutinee.ordinal() as usize;
                            self.emit(source.expressions()[scrutinee_index].occurrence.clone(), 51, self.component_term_at(positions[scrutinee_index].effect), result_effect)?;
                            if !arms.iter().any(|arm| matches!(arm.pattern, yu_hir::shadow::LocalSourceCatchPattern::Value(_))) {
                                push(&mut actions, Action::ValueConstraint { occurrence: occurrence.clone(), slot: 52, endpoint: endpoints[scrutinee_index], upper: result })?;
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
                            }
                            for arm in arms {
                                let body = arm.body.ordinal() as usize;
                                let occurrence = &source.expressions()[body].occurrence;
                                push(&mut actions, Action::ValueConstraint { occurrence: occurrence.clone(), slot: 50, endpoint: endpoints[body], upper: result })?;
                                self.emit(occurrence.clone(), 51, self.component_term_at(positions[body].effect), result_effect)?;
                            }
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(arms.len()).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(arms.len()).ok_or_else(unavailable)?;
                        }
                        LocalSourceForm::Case { scrutinee, arms } => {
                            let scrutinee_index = scrutinee.ordinal() as usize;
                            let scrutinee_occurrence = &source.expressions()[scrutinee_index].occurrence;
                            let result = self.component_term_at(pos.value);
                            let result_effect = self.component_term_at(pos.effect);
                            self.emit(scrutinee_occurrence.clone(), 51, self.component_term_at(positions[scrutinee_index].effect), result_effect)?;
                            let int_negative = self.term_for_leaf(Leaf::IntNegative)?;
                            let mut value_constraints = 0usize;
                            for arm in arms {
                                match &arm.pattern {
                                    yu_hir::shadow::LocalSourceCasePattern::Integer(pattern) => {
                                        let pattern_index = pattern.ordinal() as usize;
                                        let pattern_occurrence = &source.expressions()[pattern_index].occurrence;
                                        push(&mut actions, Action::ValueConstraint {
                                            occurrence: pattern_occurrence.clone(), slot: 52,
                                            endpoint: endpoints[pattern_index], upper: self.component_term_at(positions[scrutinee_index].value),
                                        })?;
                                        push(&mut actions, Action::ValueConstraint {
                                            occurrence: pattern_occurrence.clone(), slot: 53,
                                            endpoint: endpoints[scrutinee_index], upper: int_negative,
                                        })?;
                                        value_constraints = value_constraints.checked_add(2).ok_or_else(unavailable)?;
                                    }
                                    yu_hir::shadow::LocalSourceCasePattern::Binder(_) => {}
                                    yu_hir::shadow::LocalSourceCasePattern::Wildcard => {}
                                    yu_hir::shadow::LocalSourceCasePattern::Tuple { .. } => {}
                                    yu_hir::shadow::LocalSourceCasePattern::Variant { .. } => {}
                                }
                                let body_index = arm.body.ordinal() as usize;
                                let body_occurrence = &source.expressions()[body_index].occurrence;
                                push(&mut actions, Action::ValueConstraint {
                                    occurrence: body_occurrence.clone(), slot: 50,
                                    endpoint: endpoints[body_index], upper: result,
                                })?;
                                self.emit(body_occurrence.clone(), 51, self.component_term_at(positions[body_index].effect), result_effect)?;
                            }
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(value_constraints + arms.len()).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(value_constraints + arms.len()).ok_or_else(unavailable)?;
                        }
                        LocalSourceForm::If { arms, else_branch } => {
                            // Direct children have unique source occurrences in the HIR tree.
                            // Their parent constraints use slots separate from their own constructors.
                            let boolean = self.term_for_leaf(Leaf::BoolNegative)?;
                            let result = self.component_term_at(pos.value);
                            let result_effect = self.component_term_at(pos.effect);
                            for (condition, body) in arms {
                                let condition_index = condition.ordinal() as usize;
                                let body_index = body.ordinal() as usize;
                                let condition_occurrence = &source.expressions()[condition_index].occurrence;
                                let body_occurrence = &source.expressions()[body_index].occurrence;
                                push(&mut actions, Action::ValueConstraint { occurrence: condition_occurrence.clone(), slot: 50, endpoint: endpoints[condition_index], upper: boolean })?;
                                if else_branch.is_some() {
                                    push(&mut actions, Action::ValueConstraint { occurrence: body_occurrence.clone(), slot: 50, endpoint: endpoints[body_index], upper: result })?;
                                }
                                self.emit(condition_occurrence.clone(), 51, self.component_term_at(positions[condition_index].effect), result_effect)?;
                                self.emit(body_occurrence.clone(), 51, self.component_term_at(positions[body_index].effect), result_effect)?;
                            }
                            let value_count = if let Some(else_branch) = else_branch {
                                let else_index = else_branch.ordinal() as usize;
                                let else_occurrence = &source.expressions()[else_index].occurrence;
                                push(&mut actions, Action::ValueConstraint { occurrence: else_occurrence.clone(), slot: 50, endpoint: endpoints[else_index], upper: result })?;
                                self.emit(else_occurrence.clone(), 51, self.component_term_at(positions[else_index].effect), result_effect)?;
                                arms.len().checked_mul(2).and_then(|n| n.checked_add(1)).ok_or_else(unavailable)?
                            } else {
                                // No-else bodies are checked and evaluated, but their values
                                // are discarded. The actual conditional occurrence returns Unit.
                                let unit = self.term_for_leaf(Leaf::UnitPositive)?;
                                self.emit(occurrence.clone(), 0, unit, result)?;
                                arms.len()
                            };
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(value_count).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(value_count).ok_or_else(unavailable)?;
                        }
                        LocalSourceForm::Sequence { items } => {
                            let result = self.component_term_at(pos.value);
                            let result_effect = self.component_term_at(pos.effect);
                            for (ordinal, item) in items.iter().enumerate() {
                                let item_index = item.ordinal() as usize;
                                let item_occurrence = &source.expressions()[item_index].occurrence;
                                if ordinal + 1 == items.len() {
                                    push(&mut actions, Action::ValueConstraint {
                                        occurrence: item_occurrence.clone(), slot: 50,
                                        endpoint: endpoints[item_index], upper: result,
                                    })?;
                                }
                                self.emit(item_occurrence.clone(), 51, self.component_term_at(positions[item_index].effect), result_effect)?;
                            }
                            let facts = items.len();
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(facts).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(facts).ok_or_else(unavailable)?;
                        }
                        LocalSourceForm::Operation { resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration) } => {
                            self.term_for_leaf(Leaf::IntPositive)?;
                            self.term_for_leaf(Leaf::IntNegative)?;
                            self.prepare_source_annotation_primitives(&declaration.signature)?;
                            if annotation_contains_unit(&declaration.signature) {
                                self.term_for_leaf(Leaf::UnitPositive)?;
                                self.term_for_leaf(Leaf::UnitNegative)?;
                            }
                            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                            self.emit(occurrence.clone(), 1, bottom, self.component_term_at(pos.effect))?;
                            self.emit(occurrence.clone(), 2, self.component_term_at(pos.effect), empty)?;
                            self.append_source_facts(start, &mut actions)?;
                            push(&mut actions, Action::Operation { declaration: Arc::clone(declaration), owner: owner.clone(), occurrence: occurrence.clone(), target: pos.value, level })?;
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
                            continue;
                        }
                        LocalSourceForm::Operation { .. } => return Err(invalid()),
                        LocalSourceForm::Primitive { operation } => {
                            let (argument_negative, result_positive) = match operation {
                                yu_hir::shadow::PinnedPrimitiveOp::IntAdd | yu_hir::shadow::PinnedPrimitiveOp::IntSub
                                | yu_hir::shadow::PinnedPrimitiveOp::IntMul => (Leaf::IntNegative, Leaf::IntPositive),
                                yu_hir::shadow::PinnedPrimitiveOp::IntToString => (Leaf::IntNegative, Leaf::StrPositive),
                                yu_hir::shadow::PinnedPrimitiveOp::StringConcat => (Leaf::StrNegative, Leaf::StrPositive),
                                yu_hir::shadow::PinnedPrimitiveOp::Unsupported(_) => return Err(invalid()),
                            };
                            for leaf in [argument_negative, result_positive] {
                                self.term_for_leaf(leaf)?;
                            }
                            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                            self.emit(occurrence.clone(), 1, bottom, self.component_term_at(pos.effect))?;
                            self.emit(occurrence.clone(), 2, self.component_term_at(pos.effect), empty)?;
                            self.append_source_facts(start, &mut actions)?;
                            push(&mut actions, Action::Primitive { operation: operation.clone(), owner: owner.clone(), position: expr.source.clone(), occurrence: occurrence.clone(), target: pos.value, level })?;
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
                            continue;
                        }
                        LocalSourceForm::Name { resolution, .. } => {
                            let computation = match resolution {
                                LocalSourceResolution::Parameter(parameter) => formal_registrations.get(parameter)
                                    .copied()
                                    .filter(|registration| self.candidate_calls.formals[*registration].role == candidate_call::FormalRole::Computation),
                                _ => None,
                            };
                            if let Some(registration) = computation {
                                push(&mut actions, Action::FormalNameEffect { registration, occurrence: occurrence.clone(), effect: pos.effect })?;
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2).ok_or_else(unavailable)?;
                            } else {
                                let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                                let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                                self.emit(occurrence.clone(), 1, bottom, self.component_term_at(pos.effect))?;
                                self.emit(occurrence.clone(), 2, self.component_term_at(pos.effect), empty)?;
                                self.append_source_facts(start, &mut actions)?;
                            }
                            match resolution {
                                LocalSourceResolution::ModuleDef(target) => {
                                    push(uses, PendingDefinitionUse { parent: parent.clone(), target, occurrence: occurrence.clone() })?;
                                    push(&mut actions, Action::Module(occurrence.clone()))?;
                                }
                                LocalSourceResolution::Imported(export) => {
                                    let target = imported_definitions.get(export).ok_or_else(invalid)?;
                                    push(uses, PendingDefinitionUse { parent: parent.clone(), target, occurrence: occurrence.clone() })?;
                                    push(&mut actions, Action::Module(occurrence.clone()))?;
                                }
                                LocalSourceResolution::Parameter(_) | LocalSourceResolution::CatchBinder(_) | LocalSourceResolution::CaseBinder(_) => {}
                                LocalSourceResolution::Local(local) => {
                                    if let Some(&endpoint) = active_initializers.get(local) {
                                        push(&mut actions, Action::Link { occurrence: occurrence.clone(), endpoint, target: pos.value })?;
                                        self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                                        self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
                                    } else {
                                        push(&mut actions, Action::Local { slot: *local_slots.get(local).ok_or_else(invalid)?, occurrence: occurrence.clone(), value: pos.value, level })?;
                                    }
                                }
                                _ => return Err(invalid()),
                            }
                            continue;
                        }
                        LocalSourceForm::Apply { callee, argument, .. } => {
                            let mut local_callee = None;
                            if self.candidate_source.scoped_experiment {
                                let mut argument_index = argument.ordinal() as usize;
                                loop {
                                    self.candidate_source.charge_scoped_work(1)?;
                                    match &source.expressions()[argument_index].form {
                                        LocalSourceForm::Group { inner } | LocalSourceForm::Ascription { inner, .. } => argument_index = inner.ordinal() as usize,
                                        LocalSourceForm::If { .. } | LocalSourceForm::Sequence { .. } | LocalSourceForm::StatementBlock { .. } | LocalSourceForm::Catch { .. } | LocalSourceForm::Case { .. } => return Err(unavailable()),
                                        LocalSourceForm::Block { bindings, final_expression } => {
                                            if !bindings.is_empty() { return Err(unavailable()); }
                                            argument_index = final_expression.ordinal() as usize;
                                        }
                                        _ => break,
                                    }
                                }
                                let mut callee_index = callee.ordinal() as usize;
                                let mut crossed_ascription = false;
                                let mut crossed_nonempty_block = false;
                                let mut callee_steps = 0usize;
                                loop {
                                    self.candidate_source.charge_scoped_work(1)?;
                                    callee_steps = callee_steps.checked_add(1).ok_or_else(unavailable)?;
                                    if callee_steps > SCOPED_RECORD_LIMIT { return Err(unavailable()); }
                                    match &source.expressions()[callee_index].form {
                                        LocalSourceForm::Group { inner } => callee_index = inner.ordinal() as usize,
                                        LocalSourceForm::Ascription { inner, .. } => { crossed_ascription = true; callee_index = inner.ordinal() as usize; },
                                        LocalSourceForm::Block { bindings, final_expression } => {
                                            crossed_nonempty_block |= !bindings.is_empty();
                                            callee_index = final_expression.ordinal() as usize;
                                        }
                                        LocalSourceForm::Apply { .. } => { scoped_result_callee(source, callee_index, &mut self.candidate_source)?; break; }
                                        LocalSourceForm::If { .. } | LocalSourceForm::Sequence { .. } | LocalSourceForm::StatementBlock { .. } | LocalSourceForm::Catch { .. }
                                        | LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(_) | LocalSourceResolution::CaseBinder(_), .. } => return Err(unavailable()),
                                        LocalSourceForm::Name { resolution: LocalSourceResolution::Local(local), .. } => {
                                            if crossed_ascription || crossed_nonempty_block || local.source_root() != source.source_root() { return Err(unavailable()); }
                                            let mut binding_work = 0usize;
                                            let mut annotated = false;
                                            for binding in source.bindings() {
                                                self.candidate_source.charge_scoped_work(1)?;
                                                binding_work = binding_work.checked_add(1).ok_or_else(unavailable)?;
                                                if binding_work > SCOPED_RECORD_LIMIT { return Err(unavailable()); }
                                                if &binding.id == local { annotated = binding.annotation.is_some(); break; }
                                            }
                                            if annotated { return Err(unavailable()); }
                                            let expression = source.expressions().get(callee_index).ok_or_else(invalid)?;
                                            let authentication_work = callee_steps.checked_add(binding_work).and_then(|n| n.checked_add(1)).ok_or_else(unavailable)?;
                                            self.candidate_source.charge_scoped_work(authentication_work.checked_mul(2).ok_or_else(unavailable)?)?;
                                            local_callee = Some(candidate_call::LocalCalleeRoute {
                                                expression: callee_index, occurrence: expression.occurrence.clone(),
                                                local: local.clone(), slot: *local_slots.get(local).ok_or_else(invalid)?,
                                            });
                                            break;
                                        }
                                        _ => break,
                                    }
                                }
                            }
                            let c = positions[callee.ordinal() as usize];
                            let a = positions[argument.ordinal() as usize];
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Apply { callee: endpoints[callee.ordinal() as usize], callee_effect: c.effect, argument: endpoints[argument.ordinal() as usize], argument_effect: a.effect, result: pos.value, result_effect: pos.effect })?;
                            let source_input = self.candidate_calls.calls.len();
                            let formal_name = formal_names[callee.ordinal() as usize];
                            if self.candidate_source.scoped_experiment {
                                self.candidate_calls.by_occurrence.try_reserve(1).map_err(|_| unavailable())?;
                                if self.candidate_calls.by_occurrence.insert(occurrence.clone(), source_input).is_some() {
                                    return Err(invalid());
                                }
                            }
                            if let Some(name_index) = formal_name {
                                let name = self.candidate_calls.names.get(name_index).ok_or_else(invalid)?;
                                self.candidate_calls.formals.get(name.registration).ok_or_else(invalid)?;
                                let encoded_registration = u32::try_from(name.registration).ok()
                                    .and_then(|index| index.checked_add(1)).and_then(std::num::NonZeroU32::new)
                                    .ok_or_else(unavailable)?;
                                self.candidate_calls.formal_use_by_occurrence.try_reserve(1).map_err(|_| unavailable())?;
                                self.candidate_calls.formal_use_by_occurrence.push((occurrence.ordinal(), encoded_registration));
                            }
                            if self.candidate_source.scoped_experiment {
                                if source_input >= SCOPED_RECORD_LIMIT { return Err(unavailable()); }
                                self.candidate_source.charge_scoped_work(1)?;
                                let region = self.candidate_source.occurrence_regions[occurrence];
                                let input_route = candidate_scope::InputRouteId(u32::try_from(source_input).map_err(|_| unavailable())?);
                                self.candidate_source.regions[region.0].inputs.try_reserve(1).map_err(|_| unavailable())?;
                                self.candidate_source.regions[region.0].inputs.push(input_route);
                            }
                            let receiver_attachment = if self.candidate_source.scoped_experiment {
                                if let Some(name) = formal_name {
                                    let registration_index = self.candidate_calls.names[name].registration;
                                    let registration = &self.candidate_calls.formals[registration_index];
                                    let lambda = &source.expressions()[registration.lambda];
                                    if self.candidate_source.omitted_formals.contains_key(&lambda.occurrence) {
                                        let (receiver_body, receiver_region) = registration.receiver_body.as_ref().ok_or_else(invalid)?;
                                        Some(candidate_call::ReceiverBoundaryAttachment {
                                            registration: registration_index, receiver_lambda: lambda.occurrence.clone(),
                                            receiver_body: receiver_body.clone(), receiver_region: *receiver_region,
                                            lexical_region: self.candidate_source.occurrence_regions[occurrence],
                                            scope: self.candidate_source.computation_scopes[occurrence],
                                        })
                                    } else { None }
                                } else { None }
                            } else { None };
                            let checking = ConstraintOccurrenceId::new(occurrence.clone(), 0);
                            push(&mut self.candidate_calls.calls, candidate_call::ApplySourceInput {
                                owner: owner.clone(), expression: index,
                                callee: callee.clone(), argument: argument.clone(), level, recipe,
                                callee_value: endpoints[callee.ordinal() as usize], callee_effect: c.effect,
                                argument_value: endpoints[argument.ordinal() as usize], argument_effect: a.effect,
                                result: pos.value, application_effect: pos.effect,
                                cause: CauseId::for_occurrence(checking.clone()), checking,
                                formal_name, local_callee,
                                native: None, introduction: None, receiver_attachment,
                            })?;
                            self.candidate_recipes[recipe].source_input = Some(source_input);
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::Ascription { inner, annotation } => {
                            if self.candidate_source.scoped_experiment {
                                let child_occurrence = &source.expressions()[inner.ordinal() as usize].occurrence;
                                let child_scope = self.candidate_source.computation_scopes[child_occurrence];
                                self.candidate_source.computation_scopes.insert(occurrence.clone(), child_scope);
                            }
                            formal_names[index] = formal_names[inner.ordinal() as usize];
                            // The retained canonical peeled child avoids rescanning wrappers
                            // when arm binder aliases become available during Visit.
                            endpoints[index] = endpoints[*ascription_children.get(&index).ok_or_else(invalid)?];
                            let scope = match &expr.scope {
                                yu_hir::shadow::LocalSourceScope::ModuleExpression(root) => candidate_effect::AnnotationScope::Source(SourceRootId::Expression(root.clone())),
                                yu_hir::shadow::LocalSourceScope::Definition(owner) => candidate_effect::AnnotationScope::Definition(owner.clone()),
                                yu_hir::shadow::LocalSourceScope::SourceMember(root) => candidate_effect::AnnotationScope::Source(SourceRootId::Member(root.clone())),
                                yu_hir::shadow::LocalSourceScope::LocalInitializer(local) => candidate_effect::AnnotationScope::Local(local.clone()),
                                yu_hir::shadow::LocalSourceScope::Parameter(parameter) => parameter_scopes.get(parameter).cloned().unwrap_or_else(|| candidate_effect::AnnotationScope::for_source(owner.clone())),
                                yu_hir::shadow::LocalSourceScope::CatchArm { arm, .. } => catch_arm_scopes.get(arm).cloned().ok_or_else(invalid)?,
                                yu_hir::shadow::LocalSourceScope::Expression(expression) => candidate_effect::AnnotationScope::Expression(expression.clone()),
                            };
                            // An expression annotation constrains the child's
                            // computation directly, without a fresh facade.
                            for leaf in [Leaf::IntPositive, Leaf::IntNegative, Leaf::EffectBottomPositive, Leaf::EmptyEffectNegative] {
                                self.term_for_leaf(leaf)?;
                            }
                            self.prepare_source_annotation_primitives(&annotation.ty)?;
                            if annotation_contains_unit(&annotation.ty) {
                                self.term_for_leaf(Leaf::UnitPositive)?;
                                self.term_for_leaf(Leaf::UnitNegative)?;
                            }
                            push(&mut actions, Action::Ascription {
                                annotation: Arc::new(annotation.clone()), endpoint: endpoints[index],
                                computation_effect: pos.effect, occurrence: occurrence.clone(), level, scope,
                            })?;
                            let count = 2 + usize::from(annotation.ty.effects.is_some());
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(count).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(count).ok_or_else(unavailable)?;
                        }
                        LocalSourceForm::Variant { tag, payloads, .. } => {
                            let mut values = Vec::new();
                            let mut effects = Vec::new();
                            values.try_reserve_exact(payloads.len()).map_err(|_| unavailable())?;
                            effects.try_reserve_exact(payloads.len()).map_err(|_| unavailable())?;
                            for payload in payloads {
                                let i = payload.ordinal() as usize;
                                values.push(endpoints[i]);
                                effects.push(positions[i].effect);
                            }
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Variant {
                                tag: tag.clone(), payloads: values, element_effects: effects, result: pos.value, result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::InterpolatedString { lowered: None, .. } => return Err(unavailable()),
                        LocalSourceForm::Record { fields } => {
                            let mut values = Vec::new();
                            let mut effects = Vec::new();
                            values.try_reserve_exact(fields.len()).map_err(|_| unavailable())?;
                            effects.try_reserve_exact(fields.len()).map_err(|_| unavailable())?;
                            for field in fields {
                                let i = field.value.ordinal() as usize;
                                values.push((field.label.clone(), endpoints[i]));
                                effects.push(positions[i].effect);
                            }
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Record {
                                fields: values, element_effects: effects, result: pos.value, result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::Tuple { elements } => {
                            let mut tuple_elements = Vec::new();
                            tuple_elements.try_reserve_exact(elements.len()).map_err(|_| unavailable())?;
                            let mut element_effects = Vec::new();
                            element_effects.try_reserve_exact(elements.len()).map_err(|_| unavailable())?;
                            for element in elements {
                                let element = element.ordinal() as usize;
                                tuple_elements.push(endpoints[element]);
                                element_effects.push(positions[element].effect);
                            }
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Tuple {
                                elements: tuple_elements,
                                element_effects,
                                result: pos.value,
                                result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        // Retain the source-owned lookup obligation. Admission
                        // stays deferred until an exact role/member and a
                        // receiver implementation are available.
                        LocalSourceForm::FieldTail { receiver, member, .. } | LocalSourceForm::GeneratedFormatSelection { receiver, member } => {
                            let receiver_index = receiver.ordinal() as usize;
                            let mut role_member_candidates = Vec::new();
                            if let Some(imports) = hir.source_imports() {
                                role_member_candidates.try_reserve(imports.names().len()).map_err(|_| unavailable())?;
                                for role_name in imports.names().keys() {
                                    if let Some(member_id) = imports.role_member_id(role_name, member) {
                                        if !role_member_candidates.contains(member_id) {
                                            role_member_candidates.push(member_id.clone());
                                        }
                                    }
                                }
                            }
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::DeferredFieldTail {
                                source: expr.source.clone(),
                                case_guards: case_guards.clone(),
                                member: member.clone(),
                                role_member_candidates,
                                receiver: endpoints[receiver_index],
                                receiver_effect: positions[receiver_index].effect,
                                result: pos.value,
                                result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::OperatorApplication { operator_source, operator, left, right } => {
                            if !matches!(operator.provenance().declaration().origin(), yu_syntax::OperatorOrigin::Imported(_)) {
                                return Err(unavailable());
                            }
                            let imports = hir.source_imports().ok_or_else(unavailable)?;
                            let fixity = match operator.fixity() {
                                yu_hir::OperatorFixity::Prefix => yu_syntax::OperatorFixity::Prefix,
                                yu_hir::OperatorFixity::Infix => yu_syntax::OperatorFixity::Infix,
                                yu_hir::OperatorFixity::Suffix => yu_syntax::OperatorFixity::Suffix,
                            };
                            let operator_owner = imports.operator_owner_for_use(
                                operator.provenance(), operator.provenance().declaration().range(),
                                operator.spelling(), fixity,
                            ).ok_or_else(unavailable)?;
                            let mut provider = None;
                            for (provider_index, candidate) in self.candidate_source.operator_provider_roots.iter().enumerate() {
                                if candidate.owner != operator_owner { continue; }
                                if provider.replace(provider_index).is_some() { return Err(invalid()); }
                            }
                            let provider = provider.ok_or_else(unavailable)?;
                            let left = left.ordinal() as usize;
                            let right = right.as_ref().map(|right| right.ordinal() as usize);
                            let use_index = self.candidate_source.operator_uses.len();
                            push(&mut self.candidate_source.operator_uses, OperatorUse {
                                owner: owner.clone(),
                                operator_owner,
                                occurrence: occurrence.clone(),
                                operator_source: operator_source.clone(),
                                provider,
                                left: endpoints[left],
                                left_effect: positions[left].effect,
                                right: right.map(|index| (endpoints[index], positions[index].effect)),
                                result: pos.value,
                                result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Operator(use_index))?;
                        }
                        LocalSourceForm::Group { inner } | LocalSourceForm::InterpolatedString { lowered: Some(inner), .. } => {
                            if self.candidate_source.scoped_experiment {
                                let child_occurrence = &source.expressions()[inner.ordinal() as usize].occurrence;
                                let child_scope = self.candidate_source.computation_scopes[child_occurrence];
                                self.candidate_source.computation_scopes.insert(occurrence.clone(), child_scope);
                            }
                            formal_names[index] = formal_names[inner.ordinal() as usize];
                            let child = positions[inner.ordinal() as usize];
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Group { child: endpoints[inner.ordinal() as usize], child_effect: child.effect, result: pos.value, result_effect: pos.effect })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::Lambda { parameter, body } => {
                            self.candidate_local_lambda_effect(occurrence, pos.effect)?;
                            self.append_source_facts(start, &mut actions)?;
                            let body_index = body.ordinal() as usize;
                            let body = positions[body_index];
                            let recipe = self.lambda_recipes.len();
                            self.lambda_recipes.try_reserve(1).map_err(|_| unavailable())?;
                            self.lambda_recipes.push(LambdaRecipe {
                                occurrence: occurrence.clone(), parameter_position: lambdas[&index],
                                formal_registration: Some(*formal_registrations.get(&parameter.id).ok_or_else(invalid)?),
                                root_component: pos.value, body_value_endpoint: endpoints[body_index], body_effect_component: body.effect, lambda_effect_component: pos.effect,
                                default_effect_components: parameter.record_pattern.iter().flatten().filter_map(|field|
                                    field.default.as_ref().map(|default| positions[default.ordinal() as usize].effect)).collect(),
                                after_collected_fact: self.occurrences.len(),
                            });
                            let count = (if self.candidate_calls.formals[*formal_registrations.get(&parameter.id).ok_or_else(invalid)?].role == candidate_call::FormalRole::Value { 3usize } else { 2 })
                                .checked_add(self.lambda_recipes[recipe].default_effect_components.len()).ok_or_else(unavailable)?;
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(count).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(count).ok_or_else(unavailable)?;
                            push(&mut actions, Action::Lambda(recipe))?;
                            push(&mut actions, Action::EndLambda)?;
                            continue;
                        }
                        LocalSourceForm::Block { final_expression, .. }
                        | LocalSourceForm::StatementBlock { final_expression, .. } => {
                            if let LocalSourceForm::StatementBlock { statements, .. } = &expr.form {
                                for statement in statements {
                                    if let LocalSourceStatement::Expression(expression) = statement {
                                        let prefix = expression.ordinal() as usize;
                                        self.emit(source.expressions()[prefix].occurrence.clone(), 51,
                                            self.component_term_at(positions[prefix].effect), self.component_term_at(pos.effect))?;
                                        self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                                        self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
                                    }
                                }
                            }
                            if self.candidate_source.scoped_experiment {
                                let child_occurrence = &source.expressions()[final_expression.ordinal() as usize].occurrence;
                                let child_scope = self.candidate_source.computation_scopes[child_occurrence];
                                self.candidate_source.computation_scopes.insert(occurrence.clone(), child_scope);
                            }
                            formal_names[index] = formal_names[final_expression.ordinal() as usize];
                            let child = positions[final_expression.ordinal() as usize];
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Group {
                                child: endpoints[final_expression.ordinal() as usize], child_effect: child.effect,
                                result: pos.value, result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                    }
                    self.append_source_facts(start, &mut actions)?;
                }
            }
        }
        for (declaration, h_arg) in field_bound_v1 { push(&mut actions, Action::FieldBoundV1 { declaration, h_arg })?; }
        let body = source.body().ordinal() as usize;
        if let SourceRootId::Definition(definition) = owner {
            let root = self.root_component_positions[definition].component;
            if let Some(annotation) = source.annotation() {
                // Prepare the annotation constructor's primitives before sealing,
                // including bodies whose source expressions contain no literals.
                for leaf in [Leaf::IntPositive, Leaf::IntNegative, Leaf::EffectBottomPositive, Leaf::EmptyEffectNegative] {
                    self.term_for_leaf(leaf)?;
                }
                self.prepare_source_annotation_primitives(&annotation.ty)?;
                if annotation_contains_unit(&annotation.ty) {
                    self.term_for_leaf(Leaf::UnitPositive)?;
                    self.term_for_leaf(Leaf::UnitNegative)?;
                }
                let named_group = source.named_groups().iter().find(|group|
                    group.owner == yu_hir::shadow::LocalSourceNamedGroupOwner::Definition(definition.clone())
                );
                if source.named_groups().iter().filter(|group|
                    group.owner == yu_hir::shadow::LocalSourceNamedGroupOwner::Definition(definition.clone())
                ).count() > 1 {
                    return Err(invalid());
                }
                if let Some(group) = named_group.filter(|group| !group.formals.is_empty()) {
                    let outer = source.expressions().get(body).ok_or_else(invalid)?;
                    let outer_is_group_lambda = matches!(
                        &outer.form,
                        LocalSourceForm::Lambda { .. }
                    ) && group.formals.first().is_some_and(|formal| formal.lambda.ordinal() as usize == body);
                    if !outer_is_group_lambda { return Err(invalid()); }
                    let result = group.terminal_body.ordinal() as usize;
                    if result >= positions.len() { return Err(invalid()); }
                    let result_position = positions[result];
                    // A named header's binding annotation is the result
                    // annotation of its curried function. Apply it to the
                    // terminal body, then retain the outer Lambda constructor
                    // as the definition's function value.
                    push(&mut actions, Action::Annotation {
                        annotation: Arc::new(annotation.clone()),
                        endpoint: endpoints[result],
                        computation_effect: result_position.effect,
                        target: result_position.value,
                        occurrence: outer.occurrence.clone(),
                        level: self.candidate_source.component_levels[&result_position.value],
                    })?;
                    push(&mut actions, Action::Link {
                        occurrence: outer.occurrence.clone(),
                        endpoint: endpoints[body],
                        target: root,
                    })?;
                    let additional = 3 + usize::from(annotation.ty.effects.is_some());
                    self.counters.emitted_facts = self.counters.emitted_facts.checked_add(additional).ok_or_else(unavailable)?;
                    self.counters.generated_work_items = self.counters.generated_work_items.checked_add(additional).ok_or_else(unavailable)?;
                } else {
                    push(&mut actions, Action::Annotation { annotation: Arc::new(annotation.clone()), endpoint: endpoints[body], computation_effect: positions[body].effect, target: root, occurrence: source.expressions()[body].occurrence.clone(), level: self.candidate_source.component_levels[&positions[body].value] })?;
                    self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2 + usize::from(annotation.ty.effects.is_some())).ok_or_else(unavailable)?;
                    self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2 + usize::from(annotation.ty.effects.is_some())).ok_or_else(unavailable)?;
                }
            } else {
                push(&mut actions, Action::Link { occurrence: source.expressions()[body].occurrence.clone(), endpoint: endpoints[body], target: root })?;
                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
            }
            let obligation_scope = candidate_effect::AnnotationScope::for_source(source.source_root().clone());
            for clause in source.where_clauses() {
                push(&mut actions, Action::WhereClause { source: clause.clone(), scope: obligation_scope.clone() })?;
            }
            self.candidate_source.schedules.try_reserve(1).map_err(|_| unavailable())?;
            self.candidate_source.schedules.insert(definition.clone(), actions);
        } else if let SourceRootId::Expression(root) = owner {
            self.candidate_source.expressions.try_reserve(1).map_err(|_| unavailable())?;
            self.candidate_source.expressions.push(ExpressionSchedule {
                root: root.clone(), components: positions[body], value: endpoints[body], actions,
            });
        } else if let SourceRootId::Member(root) = owner {
            let [receiver_parameter] = source.root_parameters() else { return Err(invalid()); };
            let header = source.member_header().ok_or_else(invalid)?;
            if header.receiver.source != receiver_parameter.source
                || header.receiver.spelling != receiver_parameter.spelling
            { return Err(invalid()); }
            let receiver = CandidateEndpoint::Parameter(
                *parameters.get(&receiver_parameter.id).ok_or_else(invalid)?,
            );
            self.candidate_source.members.try_reserve(1).map_err(|_| unavailable())?;
            self.candidate_source.members.push(MemberSchedule {
                root: root.clone(), occurrence: source.expressions()[body].occurrence.clone(),
                role_member: match root.kind() {
                    yu_hir::SourceMemberKind::Role => Some(yu_hir::shadow::SourceRoleMemberId {
                        role: yu_hir::shadow::SourceRoleId {
                            module: Arc::new(root.module().clone()),
                            declaration: root.declaration_source_key().clone(),
                        },
                        declaration: root.member_source_key().clone(),
                    }),
                    yu_hir::SourceMemberKind::Implementation => None,
                },
                implementation_member: match root.kind() {
                    yu_hir::SourceMemberKind::Role => None,
                    yu_hir::SourceMemberKind::Implementation => Some(
                        yu_hir::shadow::SourceImplementationMemberId {
                            implementation: yu_hir::shadow::SourceImplementationId {
                                module: Arc::new(root.module().clone()),
                                declaration: root.declaration_source_key().clone(),
                            },
                            declaration: root.member_source_key().clone(),
                        },
                    ),
                },
                header: header.clone(),
                receiver, components: positions[body], value: endpoints[body], actions,
            });
        }
        self.candidate_source.active = true;
        Ok(())
    }
    fn append_source_facts(&self, start: usize, actions: &mut Vec<Action>) -> Result<(), CollectionAvailabilityError> {
        for index in start..self.occurrences.len() { push(actions, Action::Fact(index))?; }
        Ok(())
    }
    pub(super) fn candidate_legacy_actions(&self, start: usize, end: usize, candidate_start: usize, lambda_start: usize) -> Result<Vec<Action>, CollectionAvailabilityError> {
        let mut actions = Vec::new();
        let mut routed = HashSet::new();
        let mut candidate = candidate_start;
        let mut lambda = lambda_start;
        for index in start..=end {
            while self.candidate_recipes.get(candidate).is_some_and(|r| r.after_collected_fact == index) {
                push(&mut actions, Action::Candidate(candidate))?;
                candidate += 1;
            }
            while self.lambda_recipes.get(lambda).is_some_and(|r| r.after_collected_fact == index) {
                push(&mut actions, Action::Lambda(lambda))?;
                lambda += 1;
            }
            if index < end {
                let occurrence = self.occurrences[index].id.occurrence();
                routed.try_reserve(1).map_err(|_| unavailable())?;
                if routed.insert(occurrence.clone()) { push(&mut actions, Action::Module(occurrence.clone()))?; }
                push(&mut actions, Action::Fact(index))?;
            }
        }
        Ok(actions)
    }

}
impl InferenceSession {
    pub(super) fn initialize_candidate_source_levels(&mut self) -> Result<(), SolveAvailabilityError> {
        for (&component, &level) in &self.batch.candidate_source.component_levels {
            let endpoint = self.live_components[component];
            match endpoint.kind {
                ComponentKind::Value => self.value_levels[endpoint.ordinal as usize] = level,
                ComponentKind::Effect => self.effect_levels[endpoint.ordinal as usize] = level,
            }
        }
        for (&parameter, &level) in &self.batch.candidate_source.parameter_levels {
            self.value_levels[self.parameter_live_base as usize + parameter] = level;
        }
        for index in 0..self.batch.candidate_calls.formals.len() {
            let registration = &self.batch.candidate_calls.formals[index];
            if self
                .batch
                .parameter_recipes
                .get(registration.recipe_position)
                != Some(&registration.parameter)
                || registration.native_root.is_some()
            {
                return Err(SolveAvailabilityError::IdentityExhausted);
            }
            let parameter = registration.recipe_position;
            let role = registration.role;
            let root = self.candidate_endpoint(
                CandidateEndpoint::Parameter(parameter),
                Polarity::Positive,
            )?;
            let entry = if role == candidate_call::FormalRole::Computation {
                let level = *self.batch.candidate_source.parameter_levels.get(&parameter).ok_or(SolveAvailabilityError::IdentityExhausted)?;
                Some(self.fresh_effect_at_level(level)?)
            } else { None };
            self.batch.candidate_calls.formals[index].native_root = Some(root);
            self.batch.candidate_calls.formals[index].entry_effect = entry;
        }
        Ok(())
    }
    pub(super) fn execute_candidate_expression(&mut self, index: usize) -> Result<(), SolveAvailabilityError> {
        let schedule = self.batch.candidate_source.expressions.get(index).ok_or(SolveAvailabilityError::ReceiptMismatch)?;
        if self.batch.candidate_source.source_owners.get(schedule.root.occurrence()) != Some(&SourceRootId::Expression(schedule.root.clone()))
            || self.batch.candidate_source.component_levels.get(&schedule.components.value) != Some(&1)
            || self.batch.candidate_source.component_levels.get(&schedule.components.effect) != Some(&1)
        { return Err(SolveAvailabilityError::ReceiptMismatch); }
        let value = schedule.value;
        self.candidate_endpoint(value, Polarity::Positive)?;
        self.execute_candidate_source_schedule(Schedule::Expression(index))
    }
    pub(super) fn execute_candidate_member(&mut self, index: usize) -> Result<(), SolveAvailabilityError> {
        let schedule = self.batch.candidate_source.members.get(index).ok_or(SolveAvailabilityError::ReceiptMismatch)?;
        let owner = SourceRootId::Member(schedule.root.clone());
        let CandidateEndpoint::Parameter(receiver) = schedule.receiver else { return Err(SolveAvailabilityError::ReceiptMismatch); };
        if self.batch.candidate_source.source_owners.get(&schedule.occurrence) != Some(&owner)
            || self.batch.parameter_recipes.get(receiver).is_none_or(|parameter| parameter.source_root() != &owner)
            || self.batch.candidate_source.parameter_levels.get(&receiver).is_none()
            || !self.batch.candidate_source.component_levels.contains_key(&schedule.components.value)
            || !self.batch.candidate_source.component_levels.contains_key(&schedule.components.effect)
        { return Err(SolveAvailabilityError::ReceiptMismatch); }
        self.execute_candidate_source_schedule(Schedule::Member(index))
    }
    pub(super) fn execute_candidate_loose(&mut self) -> Result<(), SolveAvailabilityError> {
        self.execute_candidate_source_schedule(Schedule::Loose)
    }
    pub(super) fn execute_candidate_source_root(&mut self, root: &DefinitionRootId) -> Result<(), SolveAvailabilityError> {
        let position = *self.batch.root_definition_positions.get(root).ok_or(SolveAvailabilityError::IdentityExhausted)?;
        self.execute_candidate_source_schedule(Schedule::Root(position))
    }
    fn execute_candidate_source_schedule(&mut self, schedule: Schedule) -> Result<(), SolveAvailabilityError> {
        self.begin_candidate_source(schedule)?;
        // Completed-result callers never attach invalidatable synthetic support.
        debug_assert!(self.candidate_graph.as_ref().unwrap().source.unwrap().registration.is_none());
        let result = self.drive_candidate_source(Support::READY);
        if result.is_err() { self.candidate_graph.as_mut().unwrap().source = None; }
        match result? {
            CandidateRun::Complete(()) => Ok(()),
            CandidateRun::Suspended(_) => unreachable!("synchronous source caller supplies supported execution"),
        }
    }
    pub(super) fn begin_candidate_source(&mut self, schedule: Schedule) -> Result<(), SolveAvailabilityError> {
        let state = self.candidate_graph.as_mut().ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if state.source.is_some() || !state.local_capture_stack.is_empty() || state.source_lambda_depth != 0 {
            return Err(SolveAvailabilityError::IdentityExhausted);
        }
        state.source = Some(Frame { schedule, next: 0, stage: Stage::Execute, wait: None, registration: None });
        if let Err(error) = self.sample_f4_resources(ResourceBoundary::SourceDrafts) {
            self.candidate_graph.as_mut().unwrap().source = None;
            return Err(error);
        }
        Ok(())
    }
    // This private driver retains the session in `self`. Until inner operations
    // have retained outcomes, support may only change at completed action or
    // construction boundaries. Production certificate creation remains disabled.
    #[cfg(test)]
    pub(super) fn supply_synthetic_source_support(&mut self, watched: &[candidate_context::RelationId]) -> Result<candidate_context::SourceSupportId, SolveAvailabilityError> {
        let graph = self.candidate_graph.as_mut().ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if !graph.source.is_some_and(|frame| matches!(frame.stage, Stage::PublishLocal { .. })) { return Err(SolveAvailabilityError::IdentityExhausted); }
        let id = graph.intrusion.effect_algebra.context.synthetic_source_support(watched)?;
        graph.source.as_mut().unwrap().registration = Some(id);
        graph.source.as_mut().unwrap().wait = None;
        Ok(id)
    }
    pub(super) fn drive_candidate_source(&mut self, support: Support) -> Result<CandidateRun<()>, SolveAvailabilityError> {
        loop {
            match self.step_candidate_source(support)? {
                CandidateRun::Complete(true) => return Ok(CandidateRun::Complete(())),
                CandidateRun::Complete(false) => {},
                CandidateRun::Suspended(wait) => return Ok(CandidateRun::Suspended(wait)),
            }
        }
    }
    pub(super) fn step_candidate_source(&mut self, support: Support) -> Result<CandidateRun<bool>, SolveAvailabilityError> {
        let frame = self.candidate_graph.as_ref().and_then(|state| state.source).ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if let Some(registration) = frame.registration {
            if let Some(wait) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.source_support_wait(registration)? {
                self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().wait = Some(wait);
                return Ok(CandidateRun::Suspended(wait));
            }
        }
        if let Some(wait) = support.wait {
            self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().wait = Some(wait);
            return Ok(CandidateRun::Suspended(wait));
        }
        self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().wait = None;
        if let Stage::PublishLocal { slot, exposed, boundary } = frame.stage {
            self.install_candidate_local_term(slot, exposed, boundary)?;
            let current = self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap();
            current.stage = Stage::Execute;
            current.registration = None;
            current.next += 1;
            return Ok(CandidateRun::Complete(false));
        }
        let actions = match frame.schedule {
            Schedule::Loose => &self.batch.candidate_source.loose,
            Schedule::Expression(index) => &self.batch.candidate_source.expressions.get(index).ok_or(SolveAvailabilityError::ReceiptMismatch)?.actions,
            Schedule::Member(index) => &self.batch.candidate_source.members.get(index).ok_or(SolveAvailabilityError::ReceiptMismatch)?.actions,
            Schedule::Root(position) => {
                let root = &self.batch.definitions.get(position).ok_or(SolveAvailabilityError::IdentityExhausted)?.root;
                self.batch.candidate_source.schedules.get(root).ok_or(SolveAvailabilityError::IdentityExhausted)?
            }
        };
        let Some(action) = actions.get(frame.next).cloned() else {
            let state = self.candidate_graph.as_ref().unwrap();
            if !state.local_capture_stack.is_empty() || state.source_lambda_depth != 0 {
                return Err(SolveAvailabilityError::ReceiptMismatch);
            }
            self.candidate_graph.as_mut().unwrap().source = None;
            return Ok(CandidateRun::Complete(true));
        };
        match &action {
            Action::Install { slot, initializer, boundary } => {
                let exposed = self.candidate_endpoint(*initializer, Polarity::Positive)?;
                self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().stage = Stage::PublishLocal { slot: *slot, exposed, boundary: *boundary };
                return Ok(CandidateRun::Complete(false));
            }
            Action::LocalAnnotation { annotation, slot, endpoint, computation_effect, occurrence, level, boundary } => {
                let exposed = self.construct_candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *computation_effect)?;
                self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().stage = Stage::PublishLocal { slot: *slot, exposed, boundary: *boundary };
                return Ok(CandidateRun::Complete(false));
            }
            _ => {},
        }
        self.execute_candidate_action(&action)?;
        self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().next += 1;
        Ok(CandidateRun::Complete(false))
    }
    pub(super) fn execute_candidate_action(&mut self, action: &Action) -> Result<(), SolveAvailabilityError> {
            match action {
                Action::Ascription { annotation, endpoint, computation_effect, occurrence, level, scope } => self.candidate_expression_ascription(annotation, *endpoint, occurrence, *level, *computation_effect, scope)?,
                Action::FormalAnnotation { annotation, parameter, occurrence, scope } => self.candidate_formal_annotation(annotation, *parameter, occurrence, scope)?,
                Action::UnitParameter { parameter, occurrence } => self.candidate_unit_parameter(*parameter, occurrence)?,
                Action::RecordParameter { parameter, fields, occurrence } => self.candidate_record_parameter(*parameter, fields, occurrence)?,
                Action::FormalEntry { registration, annotation, occurrence, scope } => self.candidate_formal_entry_annotation(*registration, annotation, occurrence, scope)?,
                Action::FormalNameEffect { registration, occurrence, effect } => {
                    let entry = self.batch.candidate_calls.formals[*registration].entry_effect.ok_or(SolveAvailabilityError::IdentityExhausted)?;
                    let name = self.live_components[*effect].ordinal;
                    self.candidate_formal_effect_equal(occurrence, 1, entry, name)?;
                }
                Action::Fact(index) => self.admit_collected_fact(*index)?,
                Action::Link { occurrence, endpoint, target } => {
                    let lower = self.candidate_endpoint(*endpoint, Polarity::Positive)?;
                    let upper = self.batch.component_term_at(*target);
                    self.admit_candidate_value_link(occurrence, 30, lower, upper)?;
                }
                Action::ValueConstraint { occurrence, slot, endpoint, upper } => {
                    let lower = self.candidate_endpoint(*endpoint, Polarity::Positive)?;
                    self.admit_candidate_value_link(occurrence, *slot, lower, *upper)?;
                }
                Action::Candidate(index) => { let recipe = self.batch.candidate_recipes[*index].clone(); self.admit_candidate_fact(&recipe)?; }
                Action::Operator(index) => self.execute_candidate_operator_use(*index)?,
                Action::Lambda(index) => { let recipe = self.batch.lambda_recipes[*index].clone(); self.admit_lambda_fact(&recipe)?; }
                Action::BeginLambda => {
                    let state = self.candidate_graph.as_mut().ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                    state.source_lambda_depth = state.source_lambda_depth.checked_add(1).ok_or(SolveAvailabilityError::IdentityExhausted)?;
                }
                Action::EndLambda => {
                    let state = self.candidate_graph.as_mut().ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                    state.source_lambda_depth = state.source_lambda_depth.checked_sub(1).ok_or(SolveAvailabilityError::ReceiptMismatch)?;
                }
                Action::Module(occurrence) => {
                    let id = DefinitionUseId::new(self.batch.collection_artifact.clone(), occurrence.clone());
                    if self.batch.definition_use_positions.contains_key(&id) {
                        if self.candidate_graph.as_ref().is_some_and(|state| state.intrusion.active_uses.contains(&id)) { self.route_candidate_open_use(&id)?; }
                        else { self.route_incoming(&id)?; }
                    }
                }
                Action::LocalAnnotation { annotation, slot, endpoint, computation_effect, occurrence, level, boundary } => self.candidate_local_annotation(annotation, *slot, *endpoint, occurrence, *level, *boundary, *computation_effect)?,
                Action::Local { slot, occurrence, value, level } => self.route_candidate_local(*slot, occurrence, *value, *level)?,
                Action::BeginLocal { slot } => self.begin_candidate_local_capture(*slot)?,
                Action::Install { slot, initializer, boundary } => self.install_candidate_local(*slot, *initializer, *boundary)?,
                Action::CatchOperation { declaration, owner, occurrence, payload, continuation, original, effect, level, h_arg } => self.candidate_catch_operation(declaration, owner, occurrence, *payload, *continuation, *original, *effect, *level, h_arg.as_ref())?,
                Action::FieldBoundV1 { declaration, h_arg } => self.candidate_field_bound_v1(declaration, h_arg)?,
                Action::Operation { declaration, owner, occurrence, target, level } => self.candidate_operation(declaration, owner, occurrence, *target, *level)?,
                Action::Primitive { operation, owner, position, occurrence, target, level } => self.candidate_pinned_primitive(operation.clone(), owner, position, occurrence, *target, *level)?,
                Action::Annotation { annotation, endpoint, computation_effect, target, occurrence, level } => self.candidate_annotation(annotation, *endpoint, *target, occurrence, *level, *computation_effect)?,
                Action::WhereClause { source, scope } => self.candidate_register_source_role_obligation(source, scope)?,
            }
        Ok(())
    }
}

#[cfg(test)]
mod local_self_recursion_tests {
    use super::*;

    fn hir() -> Arc<yu_hir::HirModule> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(
            "my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }",
        );
        let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "local-self-recursion-kernel", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap())
    }

    #[test]
    fn nested_recursive_link_targets_the_outer_initializer_before_installation() {
        let hir = hir();
        let yu_hir::HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding"); };
        let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
        let local = source.bindings().iter().find(|local| local.spelling.as_ref() == "loop").unwrap();
        let batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
        let slot = batch.candidate_source.locals.iter().position(|id| id == &local.id).unwrap();
        let actions = &batch.candidate_source.schedules[binding.definition_root()];
        let (install, initializer) = actions.iter().enumerate().find_map(|(index, action)| match action {
            Action::Install { slot: target, initializer, .. } if *target == slot => Some((index, initializer)),
            _ => None,
        }).unwrap();
        let occurrences: Vec<_> = source.expressions().iter().filter(|expression| matches!(&expression.form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Local(id), .. } if id == &local.id))
            .map(|expression| &expression.occurrence).collect();
        assert_eq!(occurrences.len(), 3);
        let mut links = 0;
        let mut fresh_uses = 0;
        for occurrence in occurrences {
            for (index, action) in actions.iter().enumerate() {
                match action {
                    Action::Link { occurrence: actual, endpoint, .. } if actual == occurrence => {
                        assert!(index < install);
                        assert!(matches!((endpoint, initializer),
                            (CandidateEndpoint::Component(a), CandidateEndpoint::Component(b)) if a == b));
                        links += 1;
                    }
                    Action::Local { occurrence: actual, slot: target, .. } if actual == occurrence => {
                        assert_eq!(*target, slot);
                        assert!(index > install);
                        fresh_uses += 1;
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(links, 2, "direct and nested recursive occurrences both link to the installed initializer endpoint");
        assert_eq!(fresh_uses, 1);
    }

    #[test]
    fn failed_recursive_publication_drops_session_and_rebuilds_from_same_hir() {
        let hir = hir();
        let mut batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
        let actions = batch.candidate_source.schedules.values_mut().next().unwrap();
        let position = actions.iter().rposition(|action| matches!(action, Action::Install { .. })).unwrap();
        assert!(actions[..position].iter().any(|action| matches!(action, Action::Link { .. })));
        assert!(actions[..position].iter().any(|action| matches!(action, Action::Candidate(_))));
        let Action::Install { slot, .. } = &mut actions[position] else { unreachable!(); };
        *slot = usize::MAX; // Exercise a failed destination after recursive intrinsic actions.
        let session = InferenceSession::try_new_candidate(batch).unwrap();
        assert!(matches!(session.run_candidate(), Err(SolveAvailabilityError::IdentityExhausted)));
        let candidate = crate::shadow_apply::CandidateInference::solve(hir).unwrap();
        assert!(candidate.candidate_conflicts().is_empty());
    }

    #[test]
    fn conditional_constraints_use_distinct_direct_child_occurrences() {
        for with_else in [true, false] {
            let mut text = String::from("my example = if true: 1");
            for _ in 0..60 { text.push_str(" elsif false: 2"); }
            text.push_str(" elsif false: \"str\"");
            if with_else { text.push_str(" else: ()"); }
            let source: Arc<yu_syntax::SourceText> = Arc::from(text);
            let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)),
                Arc::new(yu_syntax::SyntaxEnvironment::empty()));
            let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "conditional-child-constraints", "source.yu"))),
                &parsed, yu_hir::SemanticImports::empty(),
            ).unwrap());
            let yu_hir::HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding"); };
            let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
            let expression = &source.expressions()[source.body().ordinal() as usize];
            let LocalSourceForm::If { arms, else_branch } = &expression.form else { panic!("conditional"); };
            let children: HashSet<_> = arms.iter().flat_map(|(condition, body)| [condition, body])
                .chain(else_branch.iter())
                .map(|index| source.expressions()[index.ordinal() as usize].occurrence.clone()).collect();
            assert_eq!(children.len(), arms.len() * 2 + usize::from(with_else));
            let batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
            let actions = &batch.candidate_source.schedules[binding.definition_root()];
            let values: Vec<_> = actions.iter().filter_map(|action| match action {
                Action::ValueConstraint { occurrence, slot: 50, .. } => Some(occurrence.clone()),
                _ => None,
            }).collect();
            let effects: Vec<_> = batch.occurrences.iter()
                .filter(|fact| fact.id.local_slot() == 51)
                .map(|fact| fact.id.occurrence().clone()).collect();
            let value_children: HashSet<_> = if with_else { children.clone() } else {
                arms.iter().map(|(condition, _)| source.expressions()[condition.ordinal() as usize].occurrence.clone()).collect()
            };
            assert_eq!(values.len(), value_children.len());
            assert_eq!(effects.len(), children.len());
            assert_eq!(values.into_iter().collect::<HashSet<_>>(), value_children);
            assert_eq!(effects.into_iter().collect::<HashSet<_>>(), children);
            assert!(!children.contains(&expression.occurrence));
        }
    }


    #[test]
    fn receiver_attachment_exposes_the_existing_argument_release_collision() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "act signal:\n    our ping: () -> int\n\nmy id x = x\nmy g h = catch id (h 0) { signal::ping(), _ -> 1, v -> v }\nmy callback i = signal::ping()\nmy answer = g callback",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "receiver-release-collision", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap();
        let (call_index, call) = batch.candidate_calls.calls.iter().enumerate()
            .find(|(_, call)| call.receiver_attachment.is_some()).unwrap();
        let attachment = call.receiver_attachment.as_ref().unwrap().clone();
        let source = batch.hir.local_source_for(&call.owner).unwrap().unwrap();
        let id_call = batch.candidate_calls.calls.iter().find(|other| {
            other.owner == call.owner && source.expression(&other.callee).is_some_and(|callee| matches!(&callee.form,
                LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "id"))
        }).unwrap();
        let argument = source.expression(&id_call.argument).unwrap();
        assert_eq!(batch.candidate_source.computation_scopes[&argument.occurrence], attachment.scope,
            "the actual id argument reuses h's protection scope inside its receiver");
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.execute().unwrap();
        let context = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let copied_demands: Vec<_> = context.observed_relations().filter_map(|(_, pair, flow)| {
            let demand = flow.demand?;
            if demand.original_call != call_index || demand.use_instance == 0 { return None; }
            if !matches!(pair, TypedPairKey::Value(CanonicalValuePairKey {
                upper: ValueEndpointKey::NegativeFunction(root), .. }) if *root == demand.root) { return None; }
            let inventory = &context.scope_inventory;
            assert_eq!(inventory.scope_origins[demand.output_scope.0 as usize], attachment.scope);
            assert_eq!(inventory.input_origins[demand.input.0 as usize], candidate_scope::InputRouteId(call_index as u32));
            assert_ne!(demand.output_scope, attachment.scope);
            assert_ne!(demand.input, candidate_scope::InputRouteId(call_index as u32));
            Some(demand)
        }).collect();
        assert!(!copied_demands.is_empty(), "an authenticated nonidentity FreshUse demand must activate");
        assert!(copied_demands.iter().any(|demand| {
            let release = candidate_scope::ScopeTransformer::release(demand.output_scope).unwrap();
            let protection = candidate_scope::ScopeTransformer::protect_body(demand.output_scope, demand.input).unwrap();
            context.observed_relations().any(|(_, _, flow)| context.scope_transformer(flow.transformer)
                .is_ok_and(|transformer| transformer == &release))
                && context.observed_relations().any(|(_, _, flow)| context.scope_transformer(flow.transformer)
                    .is_ok_and(|transformer| transformer == &protection))
        }), "the same authenticated copied scope/input must supply both native protection and argument release");
    }


    #[test]
    fn captured_receiver_attachment_does_not_reown_fresh_scope_instances() {
        let text: Arc<yu_syntax::SourceText> = Arc::from(
            "my g h x = h x\nmy callback i = i\nmy first = g callback 0\nmy second = g callback 1",
        );
        let parsed = yu_syntax::parse_file(text.clone(), Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "receiver-capture-owner", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode_scoped(hir, true, true, true).unwrap();
        let (call_index, attachment) = batch.candidate_calls.calls.iter().enumerate()
            .filter_map(|(index, call)| call.receiver_attachment.as_ref().map(|attachment| (index, attachment)))
            .find(|(_, attachment)| attachment.receiver_region != attachment.lexical_region).unwrap();
        let attachment = attachment.clone();
        let receiver_scope = batch.candidate_source.computation_scopes[&attachment.receiver_body];
        assert_eq!(batch.candidate_source.scope_regions[attachment.scope.0 as usize], attachment.lexical_region);
        assert_eq!(batch.candidate_source.scope_regions[receiver_scope.0 as usize], attachment.receiver_region);
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.execute().unwrap();
        let context = &session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let inventory = &context.scope_inventory;
        let receiver_regions: HashSet<_> = inventory.scope_origins.iter().enumerate()
            .filter(|(_, original)| **original == receiver_scope)
            .map(|(actual, _)| inventory.scope_regions[actual]).collect();
        let copied_scopes: HashSet<_> = context.observed_relations().filter_map(|(_, pair, flow)| {
            let demand = flow.demand?;
            if demand.original_call != call_index || demand.use_instance == 0 { return None; }
            if !matches!(pair, TypedPairKey::Value(CanonicalValuePairKey {
                upper: ValueEndpointKey::NegativeFunction(root), .. }) if *root == demand.root) { return None; }
            assert_eq!(inventory.scope_origins[demand.output_scope.0 as usize], attachment.scope);
            assert_eq!(inventory.input_origins[demand.input.0 as usize], candidate_scope::InputRouteId(call_index as u32));
            assert_ne!(demand.output_scope, attachment.scope);
            assert_ne!(demand.input, candidate_scope::InputRouteId(call_index as u32));
            Some(demand.output_scope)
        }).collect();
        assert!(copied_scopes.len() >= 2, "two distinct authenticated nonidentity FreshUse images of the captured h scope are required");
        let demand_regions: Vec<_> = copied_scopes.iter()
            .map(|scope| inventory.scope_regions[scope.0 as usize]).collect();
        assert!(demand_regions.iter().all(|region| !receiver_regions.contains(region)),
            "diagnostic attachment leaves every actual copied binder at its lexical owner");
    }

}

#[cfg(test)]
mod expression_receiver_tests {
    use super::*;

    fn module(text: &str) -> Arc<HirModule> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(source.clone(), Arc::new(yu_syntax::scan_header(source)), Arc::new(yu_syntax::SyntaxEnvironment::empty()));
        Arc::new(yu_hir::lower_module(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new("expression-receiver", "source.yu"))),
            &parsed, yu_hir::SemanticImports::empty(),
        ).unwrap())
    }

    #[test]
    fn expression_uses_keep_original_receivers_levels_and_definition_scc_domain() {
        let hir = module("{ my local = target; local }; target; my target = 1");
        let batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
        assert_eq!(batch.definitions.len(), 1);
        assert_eq!(batch.root_order.len(), 1);
        assert_eq!(batch.candidate_source.expressions.len(), 2);
        assert_eq!(batch.definition_uses.len(), 2);
        let expected_roots: Vec<_> = hir.items().iter().filter_map(|item| match item {
            HirItem::Expression(expr) => hir.expression_root(expr.occurrence()).unwrap().cloned(), _ => None,
        }).collect();
        assert_eq!(batch.candidate_source.expressions.iter().map(|schedule| &schedule.root).collect::<Vec<_>>(), expected_roots.iter().collect::<Vec<_>>());
        for (record, (root, level)) in batch.definition_uses.iter().zip(expected_roots.iter().zip([2, 1])) {
            assert_eq!(record.parent(), &SourceReceiver::Expression(root.clone()));
            assert_eq!(record.use_level, level);
            assert_eq!(record.id().occurrence(), record.occurrence());
            assert_eq!(record.cause().id(), record.id());
            assert_eq!(record.target(), &batch.definitions[0].definition);
        }
        for component in batch.scc_plan().components_in_dependency_first_order() {
            assert!(batch.scc_plan().internal_uses(component).unwrap().is_empty());
            assert!(batch.scc_plan().incoming_uses(component).unwrap().is_empty());
        }
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        session.execute().unwrap();
        let state = session.candidate_graph.as_ref().unwrap();
        assert_eq!(state.graphs.len(), 1);
        assert!(state.graphs[0].is_some());
        assert_eq!(state.routes.len(), 2);
        for record in &session.batch.definition_uses {
            assert_eq!(state.routes.iter().filter(|route| &route.use_id == record.id()).count(), 1);
        }
    }

    #[test]
    fn source_planner_refuses_foreign_or_mismatched_expression_receivers_before_actions() {
        let hir = module("1; 2");
        let foreign = module("1; 2");
        let root = |module: &HirModule, index| {
            let HirItem::Expression(expr) = &module.items()[index] else { panic!("expression"); };
            module.expression_root(expr.occurrence()).unwrap().unwrap().clone()
        };
        let owner = SourceRootId::Expression(root(&hir, 0));
        let source = hir.local_source_for(&owner).unwrap().unwrap();
        let mut batch = ConstraintBatch::collect(hir.clone()).unwrap();
        let source_hir = batch.hir.clone();
        let no_imports = HashMap::new();
        let mut uses = Vec::new();
        for receiver in [SourceReceiver::Expression(root(&hir, 1)), SourceReceiver::Expression(root(&foreign, 0))] {
            assert!(matches!(batch.emit_candidate_source(source, &receiver, &source_hir, 0, &no_imports, &mut uses), Err(CollectionAvailabilityError::MissingDefinitionEndpoint)));
            assert!(batch.candidate_source.expressions.is_empty());
            assert!(uses.is_empty());
        }
        let foreign_owner = SourceRootId::Expression(root(&foreign, 0));
        let foreign_source = foreign.local_source_for(&foreign_owner).unwrap().unwrap();
        assert!(matches!(batch.emit_candidate_source(foreign_source, &SourceReceiver::Expression(root(&foreign, 0)), &foreign, 1, &no_imports, &mut uses), Err(CollectionAvailabilityError::MissingDefinitionEndpoint)));
    }
}

#[cfg(test)]
mod member_source_tests {
    use super::*;

    #[test]
    fn member_sources_form_separate_candidate_roots_with_receiver_inputs() {
        let source: Arc<yu_syntax::SourceText> = Arc::from(
            "role Echo:\n    our receiver.echo: int = receiver.other\nimpl int: Echo:\n    our value.echo: int = value.other\n1",
        );
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "candidate-member-root", "members.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode(hir.clone(), true, true).unwrap();
        assert_eq!(batch.candidate_source.members.len(), 2);
        for (schedule_index, (schedule, (owner, outcome))) in batch.candidate_source.members.iter()
            .zip(hir.source_member_carrier_outcomes()).enumerate()
        {
            let yu_hir::SourceCarrierOutcome::Supported(source) = outcome else { panic!("supported fixture"); };
            let member = owner.member_root().unwrap();
            assert_eq!(&schedule.root, member);
            assert_eq!(schedule.header.receiver.source, source.root_parameters()[0].source);
            assert_eq!(schedule.header.method.spelling.as_ref(), "echo");
            assert_eq!(schedule.header.annotation.as_ref().unwrap().text.as_ref(), "int");
            assert_eq!(schedule.occurrence, source.expressions()[0].occurrence);
            assert_eq!(batch.candidate_source.source_owners.get(&schedule.occurrence), Some(owner));
            match member.kind() {
                yu_hir::SourceMemberKind::Role => {
                    assert_eq!(schedule.role_member.as_ref().unwrap().role.declaration, *member.declaration_source_key());
                    assert_eq!(schedule.role_member.as_ref().unwrap().declaration, *member.member_source_key());
                    assert_eq!(schedule.role_member.as_ref().unwrap().role.module.as_ref(), member.module());
                    assert_eq!(batch.candidate_source.unique_role_member_schedule(schedule.role_member.as_ref().unwrap()), Some(schedule_index));
                }
                yu_hir::SourceMemberKind::Implementation => assert!(schedule.role_member.is_none()),
            }
            match member.kind() {
                yu_hir::SourceMemberKind::Role => assert!(schedule.implementation_member.is_none()),
                yu_hir::SourceMemberKind::Implementation => {
                    let implementation_member = schedule.implementation_member.as_ref().unwrap();
                    assert_eq!(implementation_member.implementation.module.as_ref(), member.module());
                    assert_eq!(implementation_member.implementation.declaration, *member.declaration_source_key());
                    assert_eq!(implementation_member.declaration, *member.member_source_key());
                    assert_eq!(batch.candidate_source.unique_implementation_member_schedule(implementation_member), Some(schedule_index));
                }
            }
            let parameter = &source.root_parameters()[0];
            let position = batch.parameter_recipes.iter().position(|id| id == &parameter.id).unwrap();
            assert!(matches!(schedule.receiver, CandidateEndpoint::Parameter(actual) if actual == position));
            assert!(matches!(schedule.value, CandidateEndpoint::Component(_)),
                "member body FieldTail has its own result endpoint");
            assert_eq!(batch.candidate_source.parameter_levels.get(&position), Some(&1));
            assert!(batch.candidate_source.references.value_component(
                &candidate_value_graph::Value::Parameter(parameter.id.clone()),
            ).is_some());
        }
        assert!(batch.candidate_source.schedules.is_empty());
        assert!(batch.definitions.is_empty(), "member roots do not become ordinary definitions");
        let role_member = batch.candidate_source.members.iter()
            .find_map(|schedule| schedule.role_member.as_ref()).unwrap();
        let implementation_member = batch.candidate_source.members.iter()
            .find_map(|schedule| schedule.implementation_member.as_ref()).unwrap();
        let mut stale = role_member.clone();
        stale.declaration = batch.candidate_source.members[1].root.member_source_key().clone();
        assert_eq!(batch.candidate_source.unique_role_member_schedule(&stale), None);
        let mut stale_implementation = implementation_member.clone();
        stale_implementation.declaration = role_member.declaration.clone();
        assert_eq!(batch.candidate_source.unique_implementation_member_schedule(&stale_implementation), None);
        let mut ambiguous = batch.candidate_source.clone();
        ambiguous.members.push(ambiguous.members[0].clone());
        assert_eq!(ambiguous.unique_role_member_schedule(role_member), None);
        let implementation_index = ambiguous.members.iter().position(|schedule|
            schedule.implementation_member.as_ref() == Some(implementation_member)).unwrap();
        ambiguous.members.push(ambiguous.members[implementation_index].clone());
        assert_eq!(ambiguous.unique_implementation_member_schedule(implementation_member), None);
        let roots: Vec<_> = batch.candidate_source.members.iter().map(|schedule| schedule.root.clone()).collect();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        assert!(matches!(session.execute(), Err(SolveAvailabilityError::DeferredSelectionUnavailable)),
            "the final deferred-selection gate runs after all source schedules");
        let expression = &session.batch.candidate_source.expressions[0];
        let value = session.candidate_endpoint(expression.value, Polarity::Positive).unwrap();
        let TermView::LiveVariable(value) = session.store.term_view(value).unwrap() else {
            panic!("the direct integer expression keeps its live Value endpoint");
        };
        assert!(session.bounds[value.ordinal() as usize].exact_non_variable_lowers
            .contains(&ValueEndpointKey::IntPositive),
            "the integer expression's candidate action ran before pending member FieldTails were reported");
        let state = session.candidate_graph.as_ref().unwrap();
        assert!(state.has_pending_field_tail_selection(),
            "captured nested FieldTail remains pending without a stable selection consumer");
        assert_eq!(state.member_graphs.len(), 2, "member templates have source-rooted candidate graphs");
        for root in roots {
            let member = state.member_graphs.get(&root).expect("exact member graph");
            assert!(member.graph.rows.iter().any(|row| row.key == member.receiver), "receiver input is explicitly retained");
            assert!(member.graph.rows.iter().any(|row| row.key == member.result), "body result is retained");
            assert!(member.graph.rows.iter().any(|row| row.key == member.result_effect), "body effect is retained");
            assert!(matches!(member.receiver, crate::candidate_scheme::RowKey::Value(_)));
            assert!(matches!(member.result, crate::candidate_scheme::RowKey::Value(_)));
            assert!(matches!(member.result_effect, crate::candidate_scheme::RowKey::Effect(_)));
            assert_eq!(member.graph.source_field_tail_obligations.len(), 1,
                "nested member lookup remains in its member graph");
            assert_eq!(member.graph.source_field_tail_obligations[0].owner,
                yu_hir::SourceRootId::Member(root.clone()));
        }
        let layouts = state.captured_member_field_tail_layouts().unwrap();
        assert_eq!(layouts.len(), 2,
            "each captured member FieldTail has one row layout consumed by FreshUse");
        for layout in layouts {
            let member = state.member_graphs.get(&layout.member).expect("layout keeps its exact member graph root");
            let obligation = member.graph.source_field_tail_obligations.iter()
                .find(|obligation| obligation.occurrence == layout.obligation.occurrence)
                .expect("layout occurrence remains in its exact graph");
            assert_eq!(layout.obligation.source, obligation.source);
            assert_eq!(layout.obligation.owner, yu_hir::SourceRootId::Member(layout.member.clone()));
            let keys = [obligation.receiver_row, obligation.receiver_effect,
                obligation.result_row, obligation.result_effect];
            let indexes = keys.map(|key| member.graph.rows.iter().position(|row| row.key == key).unwrap());
            assert_eq!(layout.freshuse_row_indexes, indexes,
                "the readback and prepare_candidate_fresh_use share one row-index constructor");
            assert!(indexes.iter().all(|index| *index < layout.graph_row_count));
            assert_eq!(layout.freshuse_row_local,
                indexes.map(|index| member.graph.rows[index].local));
        }
    }

    #[test]
    fn post_schedule_readback_recovers_receiver_tuple_shape() {
        let source: Arc<yu_syntax::SourceText> = Arc::from(
            "role Echo:\n    our receiver.echo = receiver\nimpl int: Echo:\n    our value.echo = value\nmy pair = (1, \"x\")\npair.echo",
        );
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "receiver-tuple-readback", "receiver.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        assert!(matches!(session.execute(), Err(SolveAvailabilityError::DeferredSelectionUnavailable)));
        let state = session.candidate_graph.as_ref().unwrap();
        let receiver = state.source_field_tail_obligations.values().flatten()
            .find(|obligation| matches!(obligation.owner, SourceRootId::Expression(_)))
            .map(|obligation| obligation.receiver_row)
            .expect("pair.echo retains its receiver row");
        let crate::candidate_scheme::RowKey::Value(receiver) = receiver else {
            panic!("FieldTail receiver is a Value row");
        };
        assert_eq!(session.candidate_receiver_positive_shape(receiver), Some(
            crate::shadow_apply::CandidateReceiverShape::Tuple(vec![
                crate::shadow_apply::CandidateReceiverShape::Int,
                crate::shadow_apply::CandidateReceiverShape::Str,
            ]),
        ), "all source schedules drain before ordered receiver bounds are read back");
    }

    #[test]
    fn generic_definition_fieldtail_receives_concrete_apply_argument() {
        let source: Arc<yu_syntax::SourceText> = Arc::from(
            "role Echo:\n    our receiver.echo = receiver\nimpl int: Echo:\n    our value.echo = value\nmy apply x = x.echo\napply 1",
        );
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        let hir = Arc::new(yu_hir::shadow::lower_module_with_local_source(
            yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                "generic-fieldtail-apply", "generic.yu",
            ))),
            &parsed,
            yu_hir::SemanticImports::empty(),
        ).unwrap());
        let batch = ConstraintBatch::collect_candidate_mode(hir, true, true).unwrap();
        let mut session = InferenceSession::try_new_candidate(batch).unwrap();
        let result = session.execute();
        let readbacks = session.candidate_field_tail_receiver_readbacks().unwrap();
        assert!(result.is_ok(), "generic application should finish after FieldTail dispatch: {result:?}");
        assert!(readbacks.iter().any(|readback|
            readback.member.as_ref() == "echo"
                && readback.positive_shape == Some(crate::shadow_apply::CandidateReceiverShape::Int)
        ), "the concrete actual argument must reach the generic definition's FieldTail receiver");
    }
}
