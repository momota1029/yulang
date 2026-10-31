//! Bounded, private A0–A7 source-use experiment. No generic scheme is produced.
use crate::*;
use yu_hir::shadow::{
    LocalSource, LocalSourceCatchPattern as Pattern,
    LocalSourceCatchPayloadPattern as PayloadPattern, LocalSourceCatchValuePattern as ValuePattern,
    LocalSourceForm as Form, LocalSourceIndex, LocalSourceResolution as Resolution,
    SourceAnnotationValue as AnnotationValue, SourceOperationDeclaration,
    SourceOperationResolution, SourceNodeKey,
};
#[cfg(feature = "shadow-apply-candidate")]
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReceivingResidualOutcome {
    Suppress,
    Forward,
}

/// Owns the unpublished native graph, including the unfiltered scrutinee.
/// This is neither a module result nor an exported relay interface.
pub struct ReceivingResidualExperiment {
    session: InferenceSession,
    schema: Assembly,
    outcomes: Vec<(EffectEndpointKey, ReceivingResidualOutcome)>,
    #[cfg(feature = "shadow-apply-candidate")]
    publication_observation: Option<WholePublicationObservation>,
    result_row: u32,
}
#[cfg(feature = "shadow-apply-candidate")]
struct PendingResidualFold {
    fact: ConstraintOccurrence,
    upper: EffectEndpointKey,
    terminals: Vec<EffectEndpointKey>,
    result_row: u32,
}
#[cfg(feature = "shadow-apply-candidate")]
struct LowerPathSearch<'a> {
    endpoint: EffectEndpointKey,
    steps: Vec<LowerPathStep<'a>>,
    seen: HashSet<EffectEndpointKey>,
    use_root: Option<candidate_context::RelationId>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
pub(super) enum LowerPathStep<'a> {
    Physical(candidate_context::CheckedPhysicalLowerEdge<'a>),
    SupportMember {
        support: EffectEndpointKey,
        member: EffectEndpointKey,
        view_index: u32,
        member_index: u32,
        view: &'a candidate_effect::View,
        family: &'a yu_hir::shadow::SourceEffectId,
        closed_tail: bool,
    },
}
#[cfg(feature = "shadow-apply-candidate")]
fn certified_lower_paths<'a>(
    bounds: &'a [EffectBounds],
    context: &'a candidate_context::State,
    views: &'a [candidate_effect::View],
    root: EffectEndpointKey,
    target: EffectEndpointKey,
    entry: Option<&'a ReceivingResidualExperiment>,
) -> Result<Vec<Vec<LowerPathStep<'a>>>, candidate_context::CurrentEmissionGap> {
    let mut initial_seen = HashSet::new();
    initial_seen.try_reserve(1).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
    initial_seen.insert(root);
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
    pending.push(LowerPathSearch { endpoint: root, steps: Vec::new(), seen: initial_seen, use_root: None });
    let mut results = Vec::new();
    let mut work = 0usize;
    while let Some(path) = pending.pop() {
        work = work.checked_add(path.steps.len().checked_add(path.seen.len()).and_then(|n| n.checked_add(1))
            .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?)
            .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?;
        if work > candidate_source::SCOPED_WORK_LIMIT {
            return Err(candidate_context::CurrentEmissionGap::SearchLimit);
        }
        if path.endpoint == target {
            results.try_reserve(1).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
            results.push(path.steps);
            if results.len() > 1 {
                return Err(candidate_context::CurrentEmissionGap::AmbiguousPath);
            }
            continue;
        }
        if let EffectEndpointKey::Support(view_index) = path.endpoint {
            let view = views.get(view_index as usize)
                .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
            if view.tail.is_some() {
                return Err(candidate_context::CurrentEmissionGap::MissingCommonEndpoint);
            }
            for (member_index, family) in view.allowed.iter().enumerate() {
                work = work.checked_add(1).ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?;
                if work > candidate_source::SCOPED_WORK_LIMIT {
                    return Err(candidate_context::CurrentEmissionGap::SearchLimit);
                }
                let member = EffectEndpointKey::AnnotationMember(
                    view_index,
                    u32::try_from(member_index).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?,
                );
                if path.seen.contains(&member) { continue; }
                let mut steps = Vec::new();
                steps.try_reserve(path.steps.len().checked_add(1)
                    .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?)
                    .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                steps.extend_from_slice(&path.steps);
                steps.push(LowerPathStep::SupportMember {
                    support: path.endpoint,
                    member,
                    view_index,
                    member_index: u32::try_from(member_index)
                        .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?,
                    view,
                    family,
                    closed_tail: view.tail.is_none(),
                });
                let mut seen = HashSet::new();
                seen.try_reserve(path.seen.len().checked_add(1)
                    .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?)
                    .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                seen.extend(path.seen.iter().copied());
                seen.insert(member);
                pending.try_reserve(1).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                pending.push(LowerPathSearch { endpoint: member, steps, seen, use_root: path.use_root });
            }
            continue;
        }
        let EffectEndpointKey::EffectRow(row) = path.endpoint else { continue; };
        let row_bounds = bounds.get(row as usize).ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
        for (lane, length) in [
            (candidate_context::BoundLane::EffectLowerRow, row_bounds.direct_lower_rows.len()),
            (candidate_context::BoundLane::EffectLowerAtom, row_bounds.exact_non_variable_lowers.len()),
        ] {
            for index in 0..length {
                work = work.checked_add(1).ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?;
                if work > candidate_source::SCOPED_WORK_LIMIT {
                    return Err(candidate_context::CurrentEmissionGap::SearchLimit);
                }
                let target_endpoint = match lane {
                    candidate_context::BoundLane::EffectLowerRow => EffectEndpointKey::EffectRow(
                        *row_bounds.direct_lower_rows.get(index).ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?,
                    ),
                    candidate_context::BoundLane::EffectLowerAtom => *row_bounds.exact_non_variable_lowers
                        .get(index).ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?,
                    _ => unreachable!(),
                };
                if path.seen.contains(&target_endpoint) {
                    continue;
                }
                let slot = candidate_context::PhysicalBoundSlot {
                    owner: candidate_scheme::RowKey::Effect(row), lane, index,
                };
                let bound = crate::candidate_effect::BoundKey(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(target_endpoint),
                );
                let edge = context.checked_physical_lower_edge(slot, bound)?;
                let use_root = match (entry, path.use_root, path.steps.is_empty()) {
                    (Some(experiment), None, true) => {
                        let internal = experiment.current_internal_emission(edge.id.0)?;
                        if internal.emission.id != edge.id
                            || internal.emission.admission_id != edge.admission_id
                            || internal.emission.emission.physical != slot
                            || internal.emission.emission.bound != bound {
                            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
                        }
                        Some(internal.emission.use_root)
                    }
                    (Some(_), Some(root), false) => {
                        context.require_relation_ancestry(edge.relation, root)?;
                        Some(root)
                    }
                    (None, _, _) => None,
                    _ => return Err(candidate_context::CurrentEmissionGap::MissingUseAncestry),
                };
                let mut steps = Vec::new();
                steps.try_reserve(path.steps.len().checked_add(1)
                    .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?)
                    .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                steps.extend_from_slice(&path.steps);
                steps.push(LowerPathStep::Physical(edge));
                let mut seen = HashSet::new();
                seen.try_reserve(path.seen.len().checked_add(1)
                    .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?)
                    .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                seen.extend(path.seen.iter().copied());
                seen.insert(target_endpoint);
                pending.try_reserve(1).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                pending.push(LowerPathSearch { endpoint: target_endpoint, steps, seen, use_root });
            }
        }
    }
    Ok(results)
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Debug)]
pub(super) struct CurrentInternalEmission<'a> {
    pub incidence: InternalFormalPermissionIncidence<'a>,
    pub emission: candidate_context::CheckedBoundEmission<'a>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Debug)]
pub(super) struct ProviderEntryCertificate<'a> {
    pub internal: CurrentInternalEmission<'a>,
    pub catch_fact: &'a ConstraintOccurrence,
    pub endpoint: EffectEndpointKey,
    pub operation_view: &'a candidate_effect::View,
    pub entry_path: Vec<LowerPathStep<'a>>,
    pub catch_path: Vec<LowerPathStep<'a>>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ProviderFactOwner {
    BatchOccurrence(usize),
    SemanticStore(usize),
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "composes the actual R47/R48 readers with the exact R55 source/Internal owner")]
pub(super) struct ProviderNativeContextProjection<'a> {
    pub(super) source_internal: SourceInternalProjection<'a>,
    pub(super) provider: ProviderEntryCertificate<'a>,
    /// Complete owner inventory used by provider candidate enumeration.
    pub(super) views: Vec<(usize, &'a candidate_effect::View)>,
    /// Tagged separately from SemanticStore indexes: the numeric namespaces
    /// can collide while naming different fact owners.
    pub(super) catch_fact_owner: ProviderFactOwner,
    pub(super) provider_view_index: usize,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
struct SelectedCatchArmEvidence {
    catch: HirOccurrenceId,
    arm_ordinal: u32,
    arm_source: SourceNodeKey,
    arm_range: (usize, usize),
    operation_source: SourceNodeKey,
    operation: Arc<SourceOperationDeclaration>,
    operation_identity: yu_hir::shadow::SourceOperationId,
    unit_payload_source: SourceNodeKey,
    unit_payload_range: (usize, usize),
    continuation_is_wildcard: bool,
}
#[cfg(feature = "shadow-apply-candidate")]
impl SelectedCatchArmEvidence {
    fn is_authenticated_source(&self, schema: &Assembly) -> bool {
        self.catch == schema.catch
            && self.continuation_is_wildcard
            && self.arm_ordinal == 0
            && self.operation_identity == self.operation.id
            && self.arm_range.0 < self.arm_range.1
            && self.unit_payload_range.0 < self.unit_payload_range.1
    }
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceOperationMatch {
    Match,
    KnownUnmatched,
    Unavailable,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
enum LowerPathSnapshot {
    Physical {
        emission: candidate_context::BoundEmissionId,
        admission: candidate_context::BoundAdmissionId,
        slot: candidate_context::PhysicalBoundSlot,
        bound: candidate_effect::BoundKey,
        relation: candidate_context::RelationId,
    },
    SupportMember {
        view_index: u32,
        member_index: u32,
        family: yu_hir::shadow::SourceEffectId,
        closed_tail: bool,
    },
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
struct AuthenticatedSuppression {
    endpoint: EffectEndpointKey,
    provider_occurrence: HirOccurrenceId,
    provider_source: SourceNodeKey,
    provider_source_range: (usize, usize),
    provider_identity: yu_hir::shadow::SourceOperationId,
    entry_effect: u32,
    emission: candidate_context::BoundEmissionId,
    admission: candidate_context::BoundAdmissionId,
    catch_fact: ConstraintOccurrenceId,
    catch_occurrence: HirOccurrenceId,
    arm_ordinal: u32,
    arm_source: SourceNodeKey,
    arm_range: (usize, usize),
    operation_source: SourceNodeKey,
    operation: yu_hir::shadow::SourceOperationId,
    unit_payload_source: SourceNodeKey,
    unit_payload_range: (usize, usize),
    continuation_is_wildcard: bool,
    entry_path: Vec<LowerPathSnapshot>,
    catch_path: Vec<LowerPathSnapshot>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
struct ResidualDecision {
    endpoint: EffectEndpointKey,
    outcome: ReceivingResidualOutcome,
    suppression: Option<AuthenticatedSuppression>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Copy, Debug)]
struct ResidualPublicationPlan {
    plan_index: usize,
    endpoint: EffectEndpointKey,
    bound: candidate_effect::BoundKey,
    slot: candidate_context::PhysicalBoundSlot,
    already_present: bool,
    prior_slot_emissions: usize,
}
#[cfg(feature = "shadow-apply-candidate")]
struct CompleteResidualPlan {
    decisions: Vec<ResidualDecision>,
}
#[cfg(feature = "shadow-apply-candidate")]
struct PreparedNativePublicationPlan {
    decisions: Vec<ResidualPublicationPlan>,
    initial_lower_rows: Vec<u32>,
    initial_lower_atoms: Vec<EffectEndpointKey>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ResidualPublicationIdentity(usize);
#[cfg(feature = "shadow-apply-candidate")]
static NEXT_RESIDUAL_PUBLICATION_ID: AtomicUsize = AtomicUsize::new(1);
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Copy, Debug)]
struct ResidualCallCut {
    origin_cut: usize,
    completion_cut: usize,
    emission_cut: usize,
    pre_call_slot: Option<EffectEndpointKey>,
    prior_slot_emissions: usize,
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
#[allow(dead_code, reason = "retained private source/native publication observation")]
enum NativeResidualBoundEvidence {
    AlreadyPresent {
        slot: candidate_context::PhysicalBoundSlot,
        prior_emission_count: usize,
    },
    NewlyEmitted {
        slot: candidate_context::PhysicalBoundSlot,
        emission: candidate_context::BoundEmissionId,
        admission: candidate_context::BoundAdmissionId,
        relation: candidate_context::RelationId,
        readback: candidate_context::PhysicalBoundReadback,
    },
}
#[cfg(feature = "shadow-apply-candidate")]
#[derive(Clone, Debug)]
#[allow(dead_code, reason = "retained private source/native publication observation")]
struct ResidualPublicationObservation {
        identity: ResidualPublicationIdentity,
        plan_index: usize,
        endpoint: EffectEndpointKey,
        upper: EffectEndpointKey,
        occurrence: ConstraintOccurrenceId,
        cause: CauseId,
        origin_cut: usize,
        origin_end: usize,
        completion_cut: usize,
        completion_end: usize,
        completion_index: usize,
        emission_cut: usize,
        emission_end: usize,
        returned: bool,
        pre_call_slot: Option<EffectEndpointKey>,
        prior_slot_emissions: usize,
        source_origin_index: usize,
        source_relation: candidate_context::RelationId,
        source_drain: candidate_context::SourceDrainReceipt,
        native_bound: NativeResidualBoundEvidence,
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "whole publication source/native observation is a private query")]
pub(super) struct WholePublicationObservation {
    identity: ResidualPublicationIdentity,
    relay_owner: DefinitionRootId,
    answer_owner: DefinitionRootId,
    catch_occurrence: HirOccurrenceId,
    edge_scrutinee: HirOccurrenceId,
    original_fact: ConstraintOccurrence,
    upper: EffectEndpointKey,
    result_row: u32,
    plan: CompleteResidualPlan,
    calls: Vec<ResidualPublicationObservation>,
    initial_lower_rows: Vec<u32>,
    initial_lower_atoms: Vec<EffectEndpointKey>,
    final_lower_rows: Vec<u32>,
    final_lower_atoms: Vec<EffectEndpointKey>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "sealed borrowed owner interpretation for the R54 source/native bridge")]
pub(super) struct OwnedResidualProjection<'a> {
    pub(super) owner: &'a ReceivingResidualExperiment,
    pub(super) schema: &'a Assembly,
    pub(super) batch: &'a ConstraintBatch,
    pub(super) session: &'a InferenceSession,
    pub(super) live_state: &'a candidate_context::State,
    pub(super) whole: &'a WholePublicationObservation,
    pub(super) raw_lower_endpoint: EffectEndpointKey,
    pub(super) canonical_lower_endpoint: EffectEndpointKey,
    pub(super) raw_upper_endpoint: EffectEndpointKey,
    pub(super) canonical_upper_endpoint: EffectEndpointKey,
    pub(super) publications: Vec<(usize, &'a WholePublicationObservation)>,
    pub(super) calls: Vec<(usize, &'a ResidualPublicationObservation)>,
    pub(super) facts: Vec<(usize, &'a ConstraintOccurrence)>,
    pub(super) value_rows: Vec<(usize, &'a VariableBounds)>,
    pub(super) value_row_representatives: Vec<(usize, ValueEndpointKey)>,
    pub(super) rows: Vec<(usize, &'a EffectBounds)>,
    pub(super) effect_row_representatives: Vec<(usize, EffectEndpointKey)>,
    pub(super) relations: Vec<(usize, &'a candidate_context::Relation)>,
    pub(super) dependencies: Vec<(usize, &'a candidate_context::Dependency)>,
    pub(super) origins: Vec<(usize, &'a candidate_context::Origin)>,
    pub(super) source_drains: Vec<Option<&'a candidate_context::SourceDrainReceipt>>,
    pub(super) completions: Vec<(usize, &'a candidate_context::SourceDrainReceipt)>,
    pub(super) admissions: Vec<(usize, &'a candidate_context::BoundAdmission)>,
    pub(super) emissions: Vec<(usize, &'a candidate_context::BoundEmission)>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "bounded source/Internal fragment owned by R55")]
pub(super) struct OwnedLocalSource<'a> {
    pub(super) registration_owner: &'a SourceRootId,
    pub(super) hir: &'a Arc<HirModule>,
    pub(super) source: &'a LocalSource,
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "bounded source/Internal fragment owned by R55")]
pub(super) struct SourceInternalProjection<'a> {
    pub(super) native: OwnedResidualProjection<'a>,
    pub(super) local_sources: Vec<OwnedLocalSource<'a>>,
    pub(super) catch_source: &'a LocalSource,
    pub(super) catch_expression: &'a yu_hir::shadow::LocalSourceExpr,
    pub(super) catch_scrutinee: &'a yu_hir::shadow::LocalSourceExpr,
    pub(super) catch_arms: &'a [yu_hir::shadow::LocalSourceCatchArm],
    pub(super) resolved_operations: Vec<(usize, &'a SourceNodeKey, &'a Arc<SourceOperationDeclaration>)>,
    pub(super) formal_registrations: Vec<(usize, &'a candidate_call::FormalRegistrationInput)>,
    pub(super) formal_names: Vec<(usize, &'a candidate_call::FormalNameInput)>,
    pub(super) calls: Vec<(usize, &'a candidate_call::ApplySourceInput)>,
    pub(super) parameter_recipes: Vec<(usize, &'a HirParameterId)>,
    pub(super) lambda_recipes: Vec<(usize, &'a LambdaRecipe)>,
    /// The registration's parameter native root and the R45 registered root
    /// are different coordinates. The former addresses the formal parameter;
    /// the latter is joined through the unique LambdaRecipe and its root
    /// component for this exact Internal use.
    pub(super) internal_root_join: InternalRegisteredRootJoin,
    pub(super) internal_function_witness: InternalFunctionWitness,
    pub(super) formal_entry_permissions: Vec<(usize, &'a candidate_effect::FormalEntryPermission)>,
    pub(super) lambda_origins: Vec<(usize, &'a candidate_context::LambdaArgumentEffectOrigin)>,
    pub(super) definition_uses: Vec<(usize, &'a DefinitionUse)>,
    pub(super) routed_uses: Vec<(usize, &'a RoutedUseProvenance)>,
    pub(super) schedules: Vec<(&'a DefinitionRootId, &'a Vec<candidate_source::Action>)>,
    pub(super) source_owners: Vec<(&'a HirOccurrenceId, &'a SourceRootId)>,
    pub(super) component_terms: Vec<(usize, &'a ComponentId, Term)>,
    pub(super) semantic_facts: Vec<(usize, &'a SemanticFact)>,
    pub(super) internal_incidence: InternalFormalPermissionIncidence<'a>,
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "keeps parameter-root and Internal registered-root coordinates distinct")]
pub(super) struct InternalRegisteredRootJoin {
    pub(super) registration: usize,
    pub(super) recipe_index: usize,
    pub(super) root_component: usize,
    pub(super) parameter_native_root: Option<Term>,
    pub(super) registered_root: Term,
}
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "retains the actual positive Function child used by the Internal incidence")]
pub(super) struct InternalFunctionWitness {
    pub(super) function: Term,
    pub(super) argument_effect: Term,
    pub(super) entry_effect: u32,
}
#[cfg(feature = "shadow-apply-candidate")]
fn collect_owned_borrowed_inventory<'a, T>(
    items: impl Iterator<Item = (usize, &'a T)>,
) -> Option<Vec<(usize, &'a T)>> {
    let (lower_bound, upper_bound) = items.size_hint();
    let mut inventory = Vec::new();
    if upper_bound == Some(lower_bound) {
        inventory.try_reserve_exact(lower_bound).ok()?;
    }
    for (owner_index, item) in items {
        if owner_index != inventory.len() { return None; }
        inventory.try_reserve(1).ok()?;
        inventory.push((owner_index, item));
    }
    Some(inventory)
}
#[cfg(feature = "shadow-apply-candidate")]
fn snapshot_path(
    path: &[LowerPathStep<'_>],
    terminal: EffectEndpointKey,
) -> Result<Vec<LowerPathSnapshot>, candidate_context::CurrentEmissionGap> {
    let mut snapshot = Vec::new();
    snapshot.try_reserve(path.len()).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
    let mut terminal_member = false;
    for step in path {
        match step {
            LowerPathStep::Physical(edge) => snapshot.push(LowerPathSnapshot::Physical {
                emission: edge.id,
                admission: edge.admission_id,
                slot: edge.slot,
                bound: edge.bound,
                relation: edge.relation,
            }),
            LowerPathStep::SupportMember {
                support, member, view_index, member_index, view, family, closed_tail,
            } => {
                let exact = *support == EffectEndpointKey::Support(*view_index)
                    && *member == EffectEndpointKey::AnnotationMember(*view_index, *member_index)
                    && view.tail.is_none()
                    && *closed_tail
                    && view.allowed.get(*member_index as usize) == Some(*family);
                if !exact {
                    return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
                }
                terminal_member |= *member == terminal;
                snapshot.push(LowerPathSnapshot::SupportMember {
                    view_index: *view_index,
                    member_index: *member_index,
                    family: (*family).clone(),
                    closed_tail: *closed_tail,
                });
            }
        }
    }
    if !terminal_member {
        return Err(candidate_context::CurrentEmissionGap::MissingCommonEndpoint);
    }
    Ok(snapshot)
}
impl ReceivingResidualExperiment {
    pub fn outcomes(&self) -> impl Iterator<Item = ReceivingResidualOutcome> + '_ {
        self.outcomes.iter().map(|(_, outcome)| *outcome)
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "source/native publication evidence is a private observation query")]
    pub(super) fn native_publication_observations(&self) -> Option<&[ResidualPublicationObservation]> {
        self.publication_observation.as_ref().map(|publication| publication.calls.as_slice())
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "private identity for the per-call observation query")]
    pub(super) fn native_publication_identity(&self) -> Option<ResidualPublicationIdentity> {
        self.publication_observation.as_ref().map(|publication| publication.identity)
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "whole publication source/native observation query")]
    pub(super) fn native_whole_publication_observation(&self) -> Option<&WholePublicationObservation> {
        self.publication_observation.as_ref()
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "private R54 owner-preserving observation projection")]
    pub(super) fn native_owned_projection(&self) -> Option<OwnedResidualProjection<'_>> {
        OwnedResidualProjection::capture(self)
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "private R55 source/Internal owner projection")]
    pub(super) fn source_internal_projection(&self) -> Option<SourceInternalProjection<'_>> {
        SourceInternalProjection::capture(self)
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "private R57 composition of owner-derived R47/R48/R49 evidence")]
    pub(super) fn provider_native_context_projection(
        &self,
    ) -> Result<ProviderNativeContextProjection<'_>, candidate_context::CurrentEmissionGap> {
        ProviderNativeContextProjection::capture(self)
    }
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "selected by the private proof correspondence query")]
    pub(super) fn native_publication_call(
        &self,
        identity: ResidualPublicationIdentity,
        plan_index: usize,
    ) -> Option<&ResidualPublicationObservation> {
        let observations = self.publication_observation.as_ref()?.calls.as_slice();
        let mut selected = observations.iter().filter(|observation| {
            observation.identity == identity && observation.plan_index == plan_index
        });
        let call = selected.next()?;
        (selected.next().is_none() && call.returned).then_some(call)
    }
    /// Reconstruct the private Internal-specific permission incidence from
    /// this experiment's already-admitted complete use. This does not borrow
    /// or substitute any candidate_scheme FreshRoute.
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "source evidence remains provisional and has no permission consumer")]
    pub(super) fn internal_formal_permission_incidence(
        &self,
    ) -> Option<InternalFormalPermissionIncidence<'_>> {
        let [use_record] = self.session.batch.definition_uses() else {
            return None;
        };
        let incidence = self.session
            .internal_formal_permission_incidence(use_record.id())?;
        (incidence.target_owner == &self.schema.relay
            && incidence.receiving_owner == &self.schema.answer)
            .then_some(incidence)
    }
    /// Authenticate one retained emission against the same Internal use's
    /// raw entry row and a fresh read of its addressed physical slot.
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "current emission evidence is provisional and has no consumer")]
    pub(super) fn current_internal_emission(
        &self,
        index: usize,
    ) -> Result<CurrentInternalEmission<'_>, candidate_context::CurrentEmissionGap> {
        let [use_record] = self.session.batch.definition_uses() else {
            return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
        };
        let incidence = self.session
            .internal_formal_permission_incidence(use_record.id())
            .ok_or(candidate_context::CurrentEmissionGap::MissingInternalCertificate)?;
        if incidence.target_owner != &self.schema.relay
            || incidence.receiving_owner != &self.schema.answer {
            return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
        }
        let entry_effect = incidence.permission.entry_effect;
        let state = &self.session.candidate_graph.as_ref()
            .ok_or(candidate_context::CurrentEmissionGap::MissingInternalCertificate)?
            .intrusion.effect_algebra.context;
        let (_, emission) = state.observed_bound_emission(index)
            .ok_or(candidate_context::CurrentEmissionGap::MissingEmission)?;
        let physical = emission.physical;
        if physical.owner != candidate_scheme::RowKey::Effect(entry_effect)
            || !matches!(physical.lane,
                candidate_context::BoundLane::EffectLowerRow
                    | candidate_context::BoundLane::EffectLowerAtom)
        {
            return Err(candidate_context::CurrentEmissionGap::WrongEntrySlot);
        }
        let current = match (physical.owner, physical.lane) {
            (candidate_scheme::RowKey::Effect(row), candidate_context::BoundLane::EffectLowerRow) => {
                let item = *self.session.effect_bounds.get(row as usize)
                    .and_then(|bounds| bounds.direct_lower_rows.get(physical.index))
                    .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
                crate::candidate_effect::BoundKey(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(item)),
                )
            }
            (candidate_scheme::RowKey::Effect(row), candidate_context::BoundLane::EffectLowerAtom) => {
                let item = *self.session.effect_bounds.get(row as usize)
                    .and_then(|bounds| bounds.exact_non_variable_lowers.get(physical.index))
                    .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
                crate::candidate_effect::BoundKey(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(item),
                )
            }
            _ => return Err(candidate_context::CurrentEmissionGap::WrongEntrySlot),
        };
        let occurrence = ConstraintOccurrenceId::new(use_record.occurrence.clone(), 0);
        let fact = incidence.internal_fact;
        let root_pair = TypedPairKey::Value(CanonicalValuePairKey {
            lower: self.session.value_endpoint(fact.lower(), Polarity::Positive),
            upper: self.session.value_endpoint(fact.upper(), Polarity::Negative),
        });
        let emission = state.checked_emission_for_internal_use(
            index, current, entry_effect, &occurrence, root_pair,
        )?;
        Ok(CurrentInternalEmission { incidence, emission })
    }
    /// Build a read-only common-endpoint certificate from the exact Internal
    /// entry and the original Catch input fact. Every traversed lower edge is
    /// read at its physical slot and carries its own retained producer record.
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "provider arrival evidence is provisional and has no consumer")]
    pub(super) fn provider_entry_certificate(
        &self,
    ) -> Result<ProviderEntryCertificate<'_>, candidate_context::CurrentEmissionGap> {
        let [use_record] = self.session.batch.definition_uses() else {
            return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
        };
        let incidence = self.session.internal_formal_permission_incidence(use_record.id())
            .ok_or(candidate_context::CurrentEmissionGap::MissingInternalCertificate)?;
        if incidence.target_owner != &self.schema.relay
            || incidence.receiving_owner != &self.schema.answer {
            return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
        }
        let facts = self.session.batch.occurrences.iter().filter(|fact|
            fact.id().occurrence() == &self.schema.edge_scrutinee
                && fact.id().local_slot() == 51);
        let mut facts = facts;
        let catch_fact = facts.next().ok_or(candidate_context::CurrentEmissionGap::MissingCatchFact)?;
        if facts.next().is_some() {
            return Err(candidate_context::CurrentEmissionGap::AmbiguousCatchFact);
        }
        let context = &self.session.candidate_graph.as_ref()
            .ok_or(candidate_context::CurrentEmissionGap::MissingInternalCertificate)?
            .intrusion.effect_algebra.context;
        let algebra = &self.session.candidate_graph.as_ref().unwrap().intrusion.effect_algebra;
        let mut terminals = Vec::new();
        let mut provider_scan_work = 0usize;
        for (view_index, view) in algebra.views.iter().enumerate() {
            provider_scan_work = provider_scan_work.checked_add(view.allowed.len().checked_add(1)
                .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?)
                .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?;
            if provider_scan_work > candidate_source::SCOPED_WORK_LIMIT {
                return Err(candidate_context::CurrentEmissionGap::SearchLimit);
            }
            let candidate_effect::ViewOrigin::Operation(origin) = &view.provenance else { continue; };
            if origin.occurrence != self.schema.provider
                || !Arc::ptr_eq(&origin.declaration, &self.schema.operation) {
                continue;
            }
            for (member, family) in view.allowed.iter().enumerate() {
                if family == &self.schema.operation.id.family {
                    terminals.try_reserve(1)
                        .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
                    terminals.push((
                        EffectEndpointKey::AnnotationMember(
                            u32::try_from(view_index).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?,
                            u32::try_from(member).map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?,
                        ),
                        view,
                    ));
                    if terminals.len() > 1 {
                        return Err(candidate_context::CurrentEmissionGap::AmbiguousProviderOrigin);
                    }
                }
            }
        }
        if terminals.is_empty() {
            return Err(candidate_context::CurrentEmissionGap::MissingProviderOrigin);
        }
        if terminals.len() != 1 {
            return Err(candidate_context::CurrentEmissionGap::AmbiguousProviderOrigin);
        }
        let (endpoint, operation_view) = terminals[0];
        let root_entry = EffectEndpointKey::EffectRow(incidence.permission.entry_effect);
        let root_catch = self.session.effect_endpoint(catch_fact.lower(), Polarity::Positive);
        let catch_paths = certified_lower_paths(
            &self.session.effect_bounds, context, &algebra.views, root_catch, endpoint, None,
        )?;
        let entry_paths = certified_lower_paths(
            &self.session.effect_bounds, context, &algebra.views, root_entry, endpoint, Some(self),
        )?;
        let [catch_path] = catch_paths.as_slice() else {
            return Err(if catch_paths.is_empty() {
                candidate_context::CurrentEmissionGap::MissingCommonEndpoint
            } else { candidate_context::CurrentEmissionGap::AmbiguousPath });
        };
        let [entry_path] = entry_paths.as_slice() else {
            return Err(if entry_paths.is_empty() {
                candidate_context::CurrentEmissionGap::MissingCommonEndpoint
            } else { candidate_context::CurrentEmissionGap::AmbiguousPath });
        };
        let first = entry_path.iter().find_map(|step| match step {
            LowerPathStep::Physical(edge) => Some(edge),
            LowerPathStep::SupportMember { .. } => None,
        }).ok_or(candidate_context::CurrentEmissionGap::MissingCommonEndpoint)?;
        let internal = self.current_internal_emission(first.id.0)?;
        if internal.emission.id != first.id || internal.emission.admission_id != first.admission_id
            || internal.emission.emission.physical != first.slot
            || internal.emission.emission.bound != first.bound {
            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
        }
        let mut retained_entry_path = Vec::new();
        retained_entry_path.try_reserve_exact(entry_path.len())
            .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
        retained_entry_path.extend_from_slice(entry_path);
        let mut retained_catch_path = Vec::new();
        retained_catch_path.try_reserve_exact(catch_path.len())
            .map_err(|_| candidate_context::CurrentEmissionGap::SearchLimit)?;
        retained_catch_path.extend_from_slice(catch_path);
        Ok(ProviderEntryCertificate {
            internal,
            catch_fact,
            endpoint,
            operation_view,
            entry_path: retained_entry_path,
            catch_path: retained_catch_path,
        })
    }
    pub fn catch_occurrence(&self) -> &HirOccurrenceId {
        &self.schema.catch
    }
    pub fn scrutinee_occurrence(&self) -> &HirOccurrenceId {
        &self.schema.scrutinee
    }
    /// Actual retained native lower operands, after residual admission.
    pub fn result_lower_operand_count(&self) -> usize {
        self.session.effect_bounds[self.result_row as usize]
            .exact_non_variable_lowers
            .len()
    }
    /// Families in the actual canonical native Catch-result lower graph.
    /// An unresolved row leaf or symbolic support tail makes this observation
    /// unavailable; neither the source certificate nor recorded outcomes is read.
    pub fn result_families(
        &self,
    ) -> Result<Vec<yu_hir::shadow::SourceEffectId>, SolveAvailabilityError> {
        let mut pending = vec![EffectEndpointKey::EffectRow(self.result_row)];
        let mut seen = HashSet::new();
        let mut families = Vec::new();
        let algebra = &self
            .session
            .candidate_graph
            .as_ref()
            .ok_or_else(native_unavailable)?
            .intrusion
            .effect_algebra;
        let mut work = 0usize;
        while let Some(endpoint) = pending.pop() {
            work = work.checked_add(1).ok_or_else(native_unavailable)?;
            if work > candidate_source::SCOPED_WORK_LIMIT {
                return Err(native_unavailable());
            }
            let endpoint = self.session.canonical_effect(endpoint);
            if !seen.insert(endpoint) {
                continue;
            }
            match endpoint {
                EffectEndpointKey::BottomPositive => {}
                EffectEndpointKey::EffectRow(row) => {
                    let bounds = &self.session.effect_bounds[row as usize];
                    if bounds.direct_lower_rows.is_empty()
                        && bounds.exact_non_variable_lowers.is_empty()
                        && !bounds.has_bottom_lower
                    {
                        return Err(native_unavailable());
                    }
                    pending.extend(
                        bounds
                            .direct_lower_rows
                            .iter()
                            .copied()
                            .map(EffectEndpointKey::EffectRow),
                    );
                    pending.extend(bounds.exact_non_variable_lowers.iter().copied());
                }
                EffectEndpointKey::Support(view) => {
                    let view = &algebra.views[view as usize];
                    if view.tail.is_some() {
                        return Err(native_unavailable());
                    }
                    for family in &view.allowed {
                        if !families.contains(family) {
                            families.push(family.clone());
                        }
                    }
                }
                EffectEndpointKey::AnnotationMember(view, member) => {
                    let family = algebra.views[view as usize]
                        .allowed
                        .get(member as usize)
                        .ok_or_else(native_unavailable)?;
                    if !families.contains(family) {
                        families.push(family.clone());
                    }
                }
                EffectEndpointKey::Contribution(id) => {
                    let family = &algebra.contributions[id as usize].effect;
                    if !families.contains(family) {
                        families.push(family.clone());
                    }
                }
                EffectEndpointKey::EmptyNegative | EffectEndpointKey::Allowance(_) => {
                    return Err(native_unavailable());
                }
            }
        }
        Ok(families)
    }
}

/// Immutable references to original constructors. Symbolic invocation/receipt/
/// observation binders are justified by the validated A0–A7 sequence, never by
/// ScopeState, inferred family membership, or a previous receiver activation.
pub(super) struct Assembly {
    relay: DefinitionRootId,
    answer: DefinitionRootId,
    catch: HirOccurrenceId,
    scrutinee: HirOccurrenceId,
    edge_scrutinee: HirOccurrenceId,
    provider: HirOccurrenceId,
    provider_source: SourceNodeKey,
    provider_source_range: (usize, usize),
    operation: Arc<SourceOperationDeclaration>,
    provider_identity: yu_hir::shadow::SourceOperationId,
    selected_arm: SelectedCatchArmEvidence,
}
#[cfg(feature = "shadow-apply-candidate")]
fn source_operation_match(schema: &Assembly) -> SourceOperationMatch {
    // Both IDs are captured only from resolved LocalSource operations. Keep
    // their source occurrence/key and declaration identity together; pointer
    // inequality, spelling, or family inequality alone cannot mean mismatch.
    let provider_authenticated = schema.provider_identity == schema.operation.id
        && schema.provider_source_range.0 < schema.provider_source_range.1;
    let handler_authenticated = schema.selected_arm.is_authenticated_source(schema);
    if !provider_authenticated || !handler_authenticated {
        return SourceOperationMatch::Unavailable;
    }
    if schema.selected_arm.operation_identity == schema.provider_identity {
        SourceOperationMatch::Match
    } else {
        SourceOperationMatch::KnownUnmatched
    }
}
fn unavailable() -> shadow_apply::CandidateError {
    shadow_apply::CandidateError::Unsupported
}
fn native_unavailable() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}

fn peel<'a>(
    source: &'a LocalSource,
    mut index: &'a LocalSourceIndex,
    visited: &mut HashSet<u32>,
) -> Result<&'a yu_hir::shadow::LocalSourceExpr, shadow_apply::CandidateError> {
    loop {
        if !visited.insert(index.ordinal()) {
            return Err(unavailable());
        }
        let expression = source.expression(index).ok_or_else(unavailable)?;
        match &expression.form {
            Form::Group { inner } => index = inner,
            _ => return Ok(expression),
        }
    }
}
fn source<'a>(
    hir: &'a HirModule,
    root: &DefinitionRootId,
) -> Result<&'a LocalSource, shadow_apply::CandidateError> {
    hir.local_source(root)
        .map_err(|_| unavailable())?
        .ok_or_else(unavailable)
}
fn unit_operation(declaration: &SourceOperationDeclaration) -> bool {
    let signature = &declaration.signature;
    let AnnotationValue::Function { argument, result } = &signature.value else {
        return false;
    };
    signature.effects.is_none()
        && argument.effects.is_none()
        && result.effects.is_none()
        && matches!(argument.value, AnnotationValue::Unit)
        && matches!(result.value, AnnotationValue::Int)
}
fn assemble(
    hir: &HirModule,
    answer: &DefinitionRootId,
) -> Result<Assembly, shadow_apply::CandidateError> {
    // The complete private inventory is two definitions. No unrelated caller,
    // alias, initializer, expression item or unselected consumer is admitted.
    let bindings: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding),
            _ => None,
        })
        .collect();
    if bindings.len() != 2
        || hir
            .items()
            .iter()
            .any(|item| matches!(item, HirItem::Expression(_)))
    {
        return Err(unavailable());
    }
    let answer_binding = bindings
        .iter()
        .find(|binding| binding.definition_root() == answer)
        .ok_or_else(unavailable)?;
    let relay_binding = bindings
        .iter()
        .find(|binding| binding.definition_root() != answer)
        .ok_or_else(unavailable)?;
    let caller = source(hir, answer_binding.definition_root())?;
    let relay = source(hir, relay_binding.definition_root())?;
    if caller.expressions().len() > candidate_source::SCOPED_RECORD_LIMIT
        || relay.expressions().len() > candidate_source::SCOPED_RECORD_LIMIT
        || caller.annotation().is_some()
        || relay.annotation().is_some()
        || !caller.bindings().is_empty()
        || !relay.bindings().is_empty()
    {
        return Err(unavailable());
    }
    let mut visited = HashSet::new();
    let call = peel(caller, caller.body(), &mut visited)?;
    let Form::Apply {
        callee, argument, ..
    } = &call.form
    else {
        return Err(unavailable());
    };
    let callee = peel(caller, callee, &mut visited)?;
    if !matches!(&callee.form, Form::Name { resolution: Resolution::ModuleDef(id), .. } if id == relay_binding.id())
    {
        return Err(unavailable());
    }
    let provider_call = peel(caller, argument, &mut visited)?;
    let Form::Apply {
        callee, argument, ..
    } = &provider_call.form
    else {
        return Err(unavailable());
    };
    let provider = peel(caller, callee, &mut visited)?;
    let Form::Operation {
        resolution: SourceOperationResolution::Resolved(operation),
    } = &provider.form
    else {
        return Err(unavailable());
    };
    if !unit_operation(operation)
        || !matches!(peel(caller, argument, &mut visited)?.form, Form::Unit)
        || visited.len() != caller.expressions().len()
    {
        return Err(unavailable());
    }
    visited.clear();
    let lambda = peel(relay, relay.body(), &mut visited)?;
    let Form::Lambda { parameter, body } = &lambda.form else {
        return Err(unavailable());
    };
    let annotation = parameter.annotation.as_ref().ok_or_else(unavailable)?;
    let row = annotation.ty.effects.as_ref().ok_or_else(unavailable)?;
    if row.concrete.len() != 1
        || !row.variables.is_empty()
        || !matches!(annotation.ty.value, AnnotationValue::Int)
    {
        return Err(unavailable());
    }
    let catch = peel(relay, body, &mut visited)?;
    let Form::Catch { scrutinee, arms } = &catch.form else {
        return Err(unavailable());
    };
    let edge_scrutinee = relay
        .expression(scrutinee)
        .ok_or_else(unavailable)?
        .occurrence
        .clone();
    let scrutinee = peel(relay, scrutinee, &mut visited)?;
    if !matches!(&scrutinee.form, Form::Name { resolution: Resolution::Parameter(id), .. } if id == &parameter.id)
        || arms.len() != 2
    {
        return Err(unavailable());
    }
    let Pattern::Operation {
        resolution: SourceOperationResolution::Resolved(handled),
        operation_source,
        payloads,
        continuation,
    } = &arms[0].pattern
    else {
        return Err(unavailable());
    };
    if !unit_operation(handled)
        || handled.id.family != row.concrete[0]
        || payloads.len() != 1
        || !matches!(payloads[0], PayloadPattern::Unit { .. })
        || !matches!(continuation, ValuePattern::Wildcard)
        || !matches!(
            peel(relay, &arms[0].body, &mut visited)?.form,
            Form::Integer(_)
        )
    {
        return Err(unavailable());
    }
    let Pattern::Value(ValuePattern::Binder(binder)) = &arms[1].pattern else {
        return Err(unavailable());
    };
    if !matches!(&peel(relay, &arms[1].body, &mut visited)?.form,
        Form::Name { resolution: Resolution::CatchBinder(id), .. } if id == &binder.id)
        || visited.len() != relay.expressions().len()
    {
        return Err(unavailable());
    }
    let PayloadPattern::Unit { source: unit_payload_source, range: unit_payload_range } = &payloads[0]
    else { return Err(unavailable()); };
    let selected_arm = SelectedCatchArmEvidence {
        catch: catch.occurrence.clone(),
        arm_ordinal: 0,
        arm_source: arms[0].source.clone(),
        arm_range: (arms[0].range.start, arms[0].range.end),
        operation_source: operation_source.clone(),
        operation: Arc::clone(handled),
        operation_identity: handled.id.clone(),
        unit_payload_source: unit_payload_source.clone(),
        unit_payload_range: (unit_payload_range.start, unit_payload_range.end),
        continuation_is_wildcard: matches!(continuation, ValuePattern::Wildcard),
    };
    Ok(Assembly {
        relay: relay.definition_root().ok_or_else(unavailable)?.clone(),
        answer: answer.clone(),
        catch: catch.occurrence.clone(),
        scrutinee: scrutinee.occurrence.clone(),
        edge_scrutinee,
        provider: provider.occurrence.clone(),
        provider_source: provider.source.clone(),
        provider_source_range: (provider.range.start, provider.range.end),
        operation: Arc::clone(operation),
        provider_identity: operation.id.clone(),
        selected_arm,
    })
}

/// Source-shaped admission failure means this private attempt is unavailable;
/// it never rejects source from the ordinary compiler or changes its solver.
pub fn solve_receiving_residual_experiment(
    hir: Arc<HirModule>,
    answer: DefinitionRootId,
) -> Result<ReceivingResidualExperiment, shadow_apply::CandidateError> {
    let schema = assemble(&hir, &answer)?;
    let batch = ConstraintBatch::collect_candidate_mode(hir, true, true)
        .map_err(shadow_apply::CandidateError::Collection)?;
    let mut session =
        InferenceSession::try_new_candidate(batch).map_err(shadow_apply::CandidateError::Solve)?;
    let pending = session
        .execute_receiving_assembly(&schema)
        .map_err(shadow_apply::CandidateError::Solve)?;
    let mut experiment = ReceivingResidualExperiment {
        session,
        schema,
        outcomes: Vec::new(),
        #[cfg(feature = "shadow-apply-candidate")]
        publication_observation: None,
        result_row: pending.result_row,
    };
    experiment.publish_authenticated_residual(pending)
        .map_err(shadow_apply::CandidateError::Solve)?;
    Ok(experiment)
}

impl ReceivingResidualExperiment {
    fn publish_authenticated_residual(
        &mut self,
        pending: PendingResidualFold,
    ) -> Result<(), SolveAvailabilityError> {
        let plan = self.complete_residual_plan(&pending)?;
        #[cfg(feature = "shadow-apply-candidate")]
        let publication_plan = self.prepare_native_publication(&pending, &plan);
        #[cfg(feature = "shadow-apply-candidate")]
        let identity = NEXT_RESIDUAL_PUBLICATION_ID
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| next.checked_add(1))
            .ok()
            .map(ResidualPublicationIdentity);
        #[cfg(feature = "shadow-apply-candidate")]
        let mut observations = Vec::new();
        #[cfg(feature = "shadow-apply-candidate")]
        let mut observe_calls = publication_plan.as_ref().is_some_and(|publication| {
            identity.is_some() && observations.try_reserve(publication.decisions.len()).is_ok()
        });
        #[cfg(feature = "shadow-apply-candidate")]
        let mut publication_cursor = publication_plan.as_ref().map(|publication| publication.decisions.iter());
        let mut outcomes = Vec::new();
        outcomes.try_reserve(plan.decisions.len()).map_err(|_| native_unavailable())?;
        for (plan_index, decision) in plan.decisions.iter().enumerate() {
            let _validated_suppression = &decision.suppression;
            if decision.outcome == ReceivingResidualOutcome::Forward {
                #[cfg(feature = "shadow-apply-candidate")]
                let capture = if observe_calls {
                    let publication = publication_cursor.as_mut().and_then(|cursor| cursor.next()).copied();
                    let cut = publication.filter(|entry| entry.plan_index == plan_index && entry.endpoint == decision.endpoint)
                        .and_then(|entry| self.capture_native_call_cut(entry));
                    Some((publication, cut))
                } else { None };
                self.session.constrain_live_effect(
                    decision.endpoint,
                    pending.upper,
                    &pending.fact.id,
                    &pending.fact.cause,
                )?;
                #[cfg(feature = "shadow-apply-candidate")]
                if let (Some((Some(publication), Some(cut))), Some(identity)) = (capture, identity) {
                    if let Some(observation) = self.capture_native_publication_call(
                        &pending, identity, plan_index, publication, cut,
                    ) {
                        observations.push(observation);
                    } else {
                        observe_calls = false;
                        observations.clear();
                    }
                } else if observe_calls {
                    observe_calls = false;
                    observations.clear();
                }
            }
            outcomes.push((decision.endpoint, decision.outcome));
        }
        self.outcomes = outcomes;
        #[cfg(feature = "shadow-apply-candidate")]
        {
            self.publication_observation = match (observe_calls, identity, publication_plan) {
                (true, Some(identity), Some(publication)) => self.capture_native_whole_publication(
                    pending, plan, publication, identity, observations,
                ),
                _ => None,
            };
        }
        Ok(())
    }

    #[cfg(feature = "shadow-apply-candidate")]
    fn capture_native_whole_publication(
        &self,
        pending: PendingResidualFold,
        plan: CompleteResidualPlan,
        publication: PreparedNativePublicationPlan,
        identity: ResidualPublicationIdentity,
        calls: Vec<ResidualPublicationObservation>,
    ) -> Option<WholePublicationObservation> {
        let fact = &pending.fact;
        if fact.id.occurrence() != &self.schema.edge_scrutinee
            || fact.id.local_slot() != 51
            || fact.cause.occurrence() != &fact.id
            || self.schema.catch != self.schema.selected_arm.catch
            || pending.upper != EffectEndpointKey::EffectRow(pending.result_row)
            || self.result_row != pending.result_row
            || plan.decisions.len() != pending.terminals.len()
        {
            return None;
        }
        if plan.decisions.iter().zip(&pending.terminals)
            .any(|(decision, endpoint)| decision.endpoint != *endpoint)
        {
            return None;
        }
        let row = self.session.effect_bounds.get(pending.result_row as usize)?;
        let mut final_lower_rows = Vec::new();
        final_lower_rows.try_reserve_exact(row.direct_lower_rows.len()).ok()?;
        final_lower_rows.extend_from_slice(&row.direct_lower_rows);
        let mut final_lower_atoms = Vec::new();
        final_lower_atoms.try_reserve_exact(row.exact_non_variable_lowers.len()).ok()?;
        final_lower_atoms.extend(row.exact_non_variable_lowers.iter().cloned());

        let expected_call_count = plan.decisions.iter()
            .filter(|decision| decision.outcome == ReceivingResidualOutcome::Forward)
            .count();
        if expected_call_count != publication.decisions.len()
            || expected_call_count != calls.len()
            || publication.initial_lower_rows.len() > final_lower_rows.len()
            || publication.initial_lower_atoms.len() > final_lower_atoms.len()
            || final_lower_rows.get(..publication.initial_lower_rows.len())?
                != publication.initial_lower_rows.as_slice()
            || final_lower_atoms.get(..publication.initial_lower_atoms.len())?
                != publication.initial_lower_atoms.as_slice()
        {
            return None;
        }

        let mut call_index = 0usize;
        let mut next_row_suffix = 0usize;
        let mut next_atom_suffix = 0usize;
        let mut previous_origin_end = 0usize;
        let mut previous_completion_end = 0usize;
        let mut previous_emission_end = 0usize;
        for (plan_index, decision) in plan.decisions.iter().enumerate() {
            match decision.outcome {
                ReceivingResidualOutcome::Suppress => {
                    let suppression = decision.suppression.as_ref();
                    if !suppression.is_some_and(|suppression| {
                        suppression.endpoint == decision.endpoint
                            && suppression.catch_fact == fact.id
                            && suppression.catch_occurrence == self.schema.selected_arm.catch
                    })
                        || publication.decisions.get(call_index)
                            .is_some_and(|entry| entry.plan_index == plan_index)
                        || calls.get(call_index)
                            .is_some_and(|call| call.plan_index == plan_index)
                    {
                        return None;
                    }
                }
                ReceivingResidualOutcome::Forward => {
                    if decision.suppression.is_some() { return None; }
                    let prepared = publication.decisions.get(call_index)?;
                    let call = calls.get(call_index)?;
                    let expected_bound = candidate_effect::BoundKey(
                        ExtrusionEndpoint::Effect(pending.upper),
                        Polarity::Positive,
                        ExtrusionEndpoint::Effect(decision.endpoint),
                    );
                    if prepared.plan_index != plan_index
                        || prepared.endpoint != decision.endpoint
                        || prepared.bound != expected_bound
                        || call.identity != identity
                        || call.plan_index != plan_index
                        || call.endpoint != decision.endpoint
                        || call.upper != pending.upper
                        || call.occurrence != fact.id
                        || call.cause != fact.cause
                        || !call.returned
                        || call.origin_cut > call.origin_end
                        || call.completion_cut > call.completion_end
                        || call.emission_cut > call.emission_end
                        || call.source_origin_index < call.origin_cut
                        || call.source_origin_index >= call.origin_end
                        || call.completion_index < call.completion_cut
                        || call.completion_index >= call.completion_end
                        || call.origin_cut < previous_origin_end
                        || call.completion_cut < previous_completion_end
                        || call.emission_cut < previous_emission_end
                    {
                        return None;
                    }
                    match &call.native_bound {
                        NativeResidualBoundEvidence::AlreadyPresent { slot, .. } => {
                            let expected = match (slot.lane, decision.endpoint) {
                                (candidate_context::BoundLane::EffectLowerRow,
                                    EffectEndpointKey::EffectRow(lower)) => {
                                        publication.initial_lower_rows.get(slot.index)
                                            == Some(&lower)
                                    }
                                (candidate_context::BoundLane::EffectLowerAtom, endpoint) => {
                                    publication.initial_lower_atoms.get(slot.index)
                                        == Some(&endpoint)
                                }
                                _ => false,
                            };
                            if *slot != prepared.slot || !prepared.already_present
                                || slot.owner != candidate_scheme::RowKey::Effect(pending.result_row)
                                || !expected || call.pre_call_slot != Some(decision.endpoint)
                                || call.prior_slot_emissions != prepared.prior_slot_emissions
                            {
                                return None;
                            }
                        }
                        NativeResidualBoundEvidence::NewlyEmitted {
                            slot, emission, readback, ..
                        } => {
                            if *slot != prepared.slot || prepared.already_present
                                || slot.owner != candidate_scheme::RowKey::Effect(pending.result_row)
                                || readback.slot != *slot || readback.bound != expected_bound
                                || readback.phase != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
                                || emission.0 < call.emission_cut
                                || emission.0 >= call.emission_end
                                || call.pre_call_slot.is_some()
                                || call.prior_slot_emissions != 0
                            {
                                return None;
                            }
                            match (slot.lane, decision.endpoint) {
                                (candidate_context::BoundLane::EffectLowerRow,
                                    EffectEndpointKey::EffectRow(lower)) => {
                                    let index = publication.initial_lower_rows.len()
                                        .checked_add(next_row_suffix)?;
                                    if slot.index != index
                                        || final_lower_rows.get(index) != Some(&lower)
                                    {
                                        return None;
                                    }
                                    next_row_suffix = next_row_suffix.checked_add(1)?;
                                }
                                (candidate_context::BoundLane::EffectLowerAtom, endpoint) => {
                                    let index = publication.initial_lower_atoms.len()
                                        .checked_add(next_atom_suffix)?;
                                    if slot.index != index || final_lower_atoms.get(index) != Some(&endpoint) {
                                        return None;
                                    }
                                    next_atom_suffix = next_atom_suffix.checked_add(1)?;
                                }
                                _ => return None,
                            }
                        }
                    }
                    previous_origin_end = call.origin_end;
                    previous_completion_end = call.completion_end;
                    previous_emission_end = call.emission_end;
                    call_index = call_index.checked_add(1)?;
                }
            }
        }
        if call_index != calls.len()
            || call_index != publication.decisions.len()
            || publication.initial_lower_rows.len().checked_add(next_row_suffix)?
                != final_lower_rows.len()
            || publication.initial_lower_atoms.len().checked_add(next_atom_suffix)?
                != final_lower_atoms.len()
        {
            return None;
        }
        Some(WholePublicationObservation {
            identity,
            relay_owner: self.schema.relay.clone(),
            answer_owner: self.schema.answer.clone(),
            catch_occurrence: self.schema.catch.clone(),
            edge_scrutinee: self.schema.edge_scrutinee.clone(),
            original_fact: pending.fact,
            upper: pending.upper,
            result_row: pending.result_row,
            plan,
            calls,
            initial_lower_rows: publication.initial_lower_rows,
            initial_lower_atoms: publication.initial_lower_atoms,
            final_lower_rows,
            final_lower_atoms,
        })
    }

    #[cfg(feature = "shadow-apply-candidate")]
    fn capture_native_call_cut(&self, publication: ResidualPublicationPlan) -> Option<ResidualCallCut> {
        let context = &self.session.candidate_graph.as_ref()?.intrusion.effect_algebra.context;
        let pre_call_slot = match publication.slot.lane {
            candidate_context::BoundLane::EffectLowerRow => {
                let candidate_scheme::RowKey::Effect(row) = publication.slot.owner else { return None };
                self.session.effect_bounds.get(row as usize)?.direct_lower_rows
                    .get(publication.slot.index).copied().map(EffectEndpointKey::EffectRow)
            }
            candidate_context::BoundLane::EffectLowerAtom => {
                let candidate_scheme::RowKey::Effect(row) = publication.slot.owner else { return None };
                self.session.effect_bounds.get(row as usize)?.exact_non_variable_lowers
                    .get(publication.slot.index).copied()
            }
            _ => return None,
        };
        let emission_cut = context.observed_bound_emission_count();
        let prior_slot_emissions = (0..emission_cut).filter(|index| {
            context.observed_bound_emission(*index)
                .is_some_and(|(_, emission)| emission.physical == publication.slot)
        }).count();
        Some(ResidualCallCut {
            origin_cut: context.origins.len(),
            completion_cut: context.observed_source_drain_completion_count(),
            emission_cut,
            pre_call_slot,
            prior_slot_emissions,
        })
    }

    #[cfg(feature = "shadow-apply-candidate")]
    fn capture_native_publication_call(
        &self,
        pending: &PendingResidualFold,
        identity: ResidualPublicationIdentity,
        plan_index: usize,
        publication: ResidualPublicationPlan,
        cut: ResidualCallCut,
    ) -> Option<ResidualPublicationObservation> {
        let context = &self.session.candidate_graph.as_ref()?.intrusion.effect_algebra.context;
        let origin_end = context.origins.len();
        let completion_end = context.observed_source_drain_completion_count();
        let emission_end = context.observed_bound_emission_count();
        let source = context.checked_source_drain_in_cuts(
            cut.origin_cut, origin_end, cut.completion_cut, completion_end,
            &pending.fact.id, &pending.fact.cause,
            LiveConstraintTask::Effect(publication.endpoint, pending.upper),
        )?;
        let exact_physical_slot = match publication.slot.lane {
            candidate_context::BoundLane::EffectLowerRow => {
                let candidate_scheme::RowKey::Effect(row) = publication.slot.owner else { return None };
                let EffectEndpointKey::EffectRow(lower) = publication.endpoint else { return None };
                self.session.effect_bounds.get(row as usize)?.direct_lower_rows
                    .get(publication.slot.index).copied() == Some(lower)
            }
            candidate_context::BoundLane::EffectLowerAtom => {
                let candidate_scheme::RowKey::Effect(row) = publication.slot.owner else { return None };
                self.session.effect_bounds.get(row as usize)?.exact_non_variable_lowers
                    .get(publication.slot.index).copied() == Some(publication.endpoint)
            }
            _ => return None,
        };
        let physical_occurrences = match publication.slot.lane {
            candidate_context::BoundLane::EffectLowerRow => {
                let candidate_scheme::RowKey::Effect(row) = publication.slot.owner else { return None };
                let EffectEndpointKey::EffectRow(lower) = publication.endpoint else { return None };
                self.session.effect_bounds.get(row as usize)?.direct_lower_rows.iter()
                    .filter(|candidate| **candidate == lower).count()
            }
            candidate_context::BoundLane::EffectLowerAtom => {
                let candidate_scheme::RowKey::Effect(row) = publication.slot.owner else { return None };
                self.session.effect_bounds.get(row as usize)?.exact_non_variable_lowers.iter()
                    .filter(|candidate| **candidate == publication.endpoint).count()
            }
            _ => return None,
        };
        if !exact_physical_slot
            || physical_occurrences != 1
            || !matches!(publication.slot.owner, candidate_scheme::RowKey::Effect(row) if row == self.result_row)
        { return None; }
        let mut slot_emissions = (cut.emission_cut..emission_end).filter_map(|index| {
            context.observed_bound_emission(index)
                .filter(|(_, emission)| emission.physical == publication.slot)
        });
        let native_bound = if publication.already_present {
            if cut.pre_call_slot != Some(publication.endpoint)
                || cut.prior_slot_emissions != publication.prior_slot_emissions
                || slot_emissions.next().is_some()
            { return None; }
            let mut prior_count = 0usize;
            for index in 0..cut.emission_cut {
                let Some((_, emission)) = context.observed_bound_emission(index)
                    .filter(|(_, emission)| emission.physical == publication.slot) else { continue };
                prior_count = prior_count.checked_add(1)?;
                if emission.bound != publication.bound || emission.readback.bound != publication.bound
                    || emission.readback.slot != publication.slot
                    || emission.readback.phase != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
                { return None; }
                let (_, admission) = context.observed_bound_admissions()
                    .find(|(admission_index, _)| *admission_index == emission.admission.0)?;
                let relation = admission.relation?;
                if admission.bound != publication.bound
                    || context.relation_pair(relation) != Some(candidate_context::bound_pair(publication.bound))
                { return None; }
            }
            if prior_count != cut.prior_slot_emissions { return None; }
            NativeResidualBoundEvidence::AlreadyPresent {
                slot: publication.slot,
                prior_emission_count: cut.prior_slot_emissions,
            }
        } else {
            if cut.pre_call_slot.is_some() || cut.prior_slot_emissions != 0 { return None; }
            let (emission_id, emission) = slot_emissions.next()?;
            if slot_emissions.next().is_some()
                || emission_id.0 < cut.emission_cut || emission_id.0 >= emission_end
                || emission.bound != publication.bound || emission.physical != publication.slot
                || emission.readback.bound != publication.bound || emission.readback.slot != publication.slot
                || emission.readback.phase != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
            { return None; }
            let mut admissions = context.observed_bound_admissions()
                .filter(|(index, _)| *index == emission.admission.0);
            let (_, admission) = admissions.next()?;
            if admissions.next().is_some() || admission.bound != publication.bound { return None; }
            let relation = admission.relation?;
            if context.relation_pair(relation) != Some(candidate_context::bound_pair(publication.bound))
                || context.require_relation_ancestry(relation, source.relation).is_err()
            { return None; }
            NativeResidualBoundEvidence::NewlyEmitted {
                slot: publication.slot,
                emission: emission_id,
                admission: emission.admission,
                relation,
                readback: emission.readback,
            }
        };
        Some(ResidualPublicationObservation {
            identity, plan_index, endpoint: publication.endpoint, upper: pending.upper,
            occurrence: pending.fact.id.clone(), cause: pending.fact.cause.clone(),
            origin_cut: cut.origin_cut, origin_end,
            completion_cut: cut.completion_cut, completion_end,
            completion_index: source.completion_index,
            emission_cut: cut.emission_cut, emission_end, returned: true,
            pre_call_slot: cut.pre_call_slot, prior_slot_emissions: cut.prior_slot_emissions,
            source_origin_index: source.origin_index, source_relation: source.relation,
            source_drain: source.receipt.clone(), native_bound,
        })
    }

    fn complete_residual_plan(
        &self,
        pending: &PendingResidualFold,
    ) -> Result<CompleteResidualPlan, SolveAvailabilityError> {
        let algebra = &self.session.candidate_graph.as_ref()
            .ok_or_else(native_unavailable)?.intrusion.effect_algebra;
        let operation_match = source_operation_match(&self.schema);
        if operation_match == SourceOperationMatch::Unavailable {
            return Err(native_unavailable());
        }
        let mut decisions = Vec::new();
        decisions.try_reserve(pending.terminals.len()).map_err(|_| native_unavailable())?;
        for &endpoint in &pending.terminals {
            let suppression = match operation_match {
                SourceOperationMatch::KnownUnmatched => None,
                SourceOperationMatch::Unavailable => return Err(native_unavailable()),
                SourceOperationMatch::Match => {
                    if let EffectEndpointKey::AnnotationMember(view_index, member_index) = endpoint {
                        let view = algebra.views.get(view_index as usize).ok_or_else(native_unavailable)?;
                        let member = view.allowed.get(member_index as usize).ok_or_else(native_unavailable)?;
                        let provider_origin = match &view.provenance {
                            candidate_effect::ViewOrigin::Operation(origin)
                                if origin.occurrence == self.schema.provider => {
                                    if origin.declaration.id != self.schema.provider_identity {
                                        return Err(native_unavailable());
                                    }
                                    true
                                }
                            _ => false,
                        };
                        let provider_member = provider_origin
                            && view.tail.is_none()
                            && member == &self.schema.provider_identity.family;
                        if provider_member {
                            let certificate = self.provider_entry_certificate()
                                .map_err(|_| native_unavailable())?;
                            if certificate.endpoint != endpoint
                                || !std::ptr::eq(certificate.operation_view, view)
                                || certificate.catch_fact.id != pending.fact.id
                                || certificate.operation_view.allowed.get(member_index as usize) != Some(member)
                            {
                                return Err(native_unavailable());
                            }
                            Some(snapshot_suppression(&certificate, &self.schema)?)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            };
            let outcome = if suppression.is_some() {
                ReceivingResidualOutcome::Suppress
            } else {
                ReceivingResidualOutcome::Forward
            };
            decisions.push(ResidualDecision { endpoint, outcome, suppression });
        }
        if decisions.is_empty() {
            return Err(native_unavailable());
        }
        Ok(CompleteResidualPlan { decisions })
    }

    #[cfg(feature = "shadow-apply-candidate")]
    fn prepare_native_publication(
        &self,
        pending: &PendingResidualFold,
        plan: &CompleteResidualPlan,
    ) -> Option<PreparedNativePublicationPlan> {
        let initial = self.session.effect_bounds.get(pending.result_row as usize)?;
        let mut initial_lower_rows = Vec::new();
        initial_lower_rows.try_reserve_exact(initial.direct_lower_rows.len()).ok()?;
        initial_lower_rows.extend_from_slice(&initial.direct_lower_rows);
        let mut initial_lower_atoms = Vec::new();
        initial_lower_atoms.try_reserve_exact(initial.exact_non_variable_lowers.len()).ok()?;
        initial_lower_atoms.extend(initial.exact_non_variable_lowers.iter().cloned());
        let mut decisions = Vec::new();
        decisions.try_reserve(plan.decisions.len()).ok()?;
        let mut planned_row_appends = 0usize;
        let mut planned_atom_appends = 0usize;
        for (plan_index, decision) in plan.decisions.iter().enumerate() {
            if decision.outcome != ReceivingResidualOutcome::Forward { continue; }
            let mut publication = self.residual_publication_plan(
                decision.endpoint, pending, planned_row_appends, planned_atom_appends,
            )?;
            publication.plan_index = plan_index;
            if !publication.already_present {
                match publication.slot.lane {
                    candidate_context::BoundLane::EffectLowerRow => {
                        planned_row_appends = planned_row_appends.checked_add(1)?;
                    }
                    candidate_context::BoundLane::EffectLowerAtom => {
                        planned_atom_appends = planned_atom_appends.checked_add(1)?;
                    }
                    _ => return None,
                }
            }
            decisions.push(publication);
        }
        Some(PreparedNativePublicationPlan {
            decisions,
            initial_lower_rows,
            initial_lower_atoms,
        })
    }

    #[cfg(feature = "shadow-apply-candidate")]
    fn residual_publication_plan(
        &self,
        endpoint: EffectEndpointKey,
        pending: &PendingResidualFold,
        planned_row_appends: usize,
        planned_atom_appends: usize,
    ) -> Option<ResidualPublicationPlan> {
        let EffectEndpointKey::EffectRow(upper_row) = pending.upper else {
            return None;
        };
        if upper_row != pending.result_row {
            return None;
        }
        let row = self.session.effect_bounds.get(upper_row as usize)?;
        let (lane, index, occurrences) = if let EffectEndpointKey::EffectRow(lower_row) = endpoint {
            let mut first = None;
            let mut count = 0usize;
            for (index, candidate) in row.direct_lower_rows.iter().enumerate() {
                if *candidate == lower_row { first.get_or_insert(index); count += 1; }
            }
            (candidate_context::BoundLane::EffectLowerRow,
                first.unwrap_or(row.direct_lower_rows.len().checked_add(planned_row_appends)
                    ?), count)
        } else {
            let mut first = None;
            let mut count = 0usize;
            for (index, candidate) in row.exact_non_variable_lowers.iter().enumerate() {
                if *candidate == endpoint { first.get_or_insert(index); count += 1; }
            }
            (candidate_context::BoundLane::EffectLowerAtom,
                first.unwrap_or(row.exact_non_variable_lowers.len().checked_add(planned_atom_appends)
                    ?), count)
        };
        if occurrences > 1 {
            return None;
        }
        let bound = candidate_effect::BoundKey(
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(upper_row)),
            Polarity::Positive,
            ExtrusionEndpoint::Effect(endpoint),
        );
        let slot = candidate_context::PhysicalBoundSlot {
            owner: candidate_scheme::RowKey::Effect(upper_row), lane, index,
        };
        let context = &self.session.candidate_graph.as_ref()?.intrusion.effect_algebra.context;
        let prior_slot_emissions = context.observed_bound_emissions_for_slot(slot).count();
        if (occurrences == 0 && prior_slot_emissions != 0)
            || (occurrences == 1 && prior_slot_emissions > 1)
        {
            return None;
        }
        Some(ResidualPublicationPlan {
            plan_index: usize::MAX,
            endpoint,
            bound,
            slot,
            already_present: occurrences == 1,
            prior_slot_emissions,
        })
    }
}

#[cfg(feature = "shadow-apply-candidate")]
impl<'a> OwnedResidualProjection<'a> {
    fn capture(owner: &'a ReceivingResidualExperiment) -> Option<Self> {
        let whole = owner.publication_observation.as_ref()?;
        let graph = owner.session.candidate_graph.as_ref()?;
        let live_state = &graph.intrusion.effect_algebra.context;
        let raw_lower_endpoint = raw_source_effect_endpoint(
            &owner.session, whole.original_fact.lower(), Polarity::Positive,
        )?;
        let canonical_lower_endpoint = owner.session.canonical_effect(raw_lower_endpoint);
        let raw_upper_endpoint = raw_source_effect_endpoint(
            &owner.session, whole.original_fact.upper(), Polarity::Negative,
        )?;
        let canonical_upper_endpoint = owner.session.canonical_effect(raw_upper_endpoint);
        let mut publications = Vec::new();
        publications.try_reserve_exact(1).ok()?;
        publications.push((0, whole));
        let origins = collect_owned_borrowed_inventory(live_state.origins.iter().enumerate())?;
        let mut source_drains = Vec::new();
        source_drains.try_reserve_exact(origins.len()).ok()?;
        source_drains.extend(origins.iter().map(|(_, origin)| origin.source_drain_receipt.as_ref()));
        let mut value_row_representatives = Vec::new();
        value_row_representatives.try_reserve_exact(owner.session.bounds.len()).ok()?;
        for index in 0..owner.session.bounds.len() {
            let row = u32::try_from(index).ok()?;
            value_row_representatives.push((
                index,
                owner.session.canonical_value(ValueEndpointKey::ValueRow(row)),
            ));
        }
        let mut effect_row_representatives = Vec::new();
        effect_row_representatives.try_reserve_exact(owner.session.effect_bounds.len()).ok()?;
        for index in 0..owner.session.effect_bounds.len() {
            let row = u32::try_from(index).ok()?;
            effect_row_representatives.push((
                index,
                owner.session.canonical_effect(EffectEndpointKey::EffectRow(row)),
            ));
        }
        let projection = Self {
            owner,
            schema: &owner.schema,
            batch: &owner.session.batch,
            session: &owner.session,
            live_state,
            whole,
            raw_lower_endpoint,
            canonical_lower_endpoint,
            raw_upper_endpoint,
            canonical_upper_endpoint,
            publications,
            calls: collect_owned_borrowed_inventory(whole.calls.iter().enumerate())?,
            facts: collect_owned_borrowed_inventory(owner.session.batch.occurrences.iter().enumerate())?,
            value_rows: collect_owned_borrowed_inventory(owner.session.bounds.iter().enumerate())?,
            value_row_representatives,
            rows: collect_owned_borrowed_inventory(owner.session.effect_bounds.iter().enumerate())?,
            effect_row_representatives,
            relations: collect_owned_borrowed_inventory(live_state.owned_projection_relations())?,
            dependencies: collect_owned_borrowed_inventory(live_state.observed_dependencies().enumerate())?,
            origins,
            source_drains,
            completions: collect_owned_borrowed_inventory(
                live_state.owned_projection_source_drain_completions(),
            )?,
            admissions: collect_owned_borrowed_inventory(live_state.observed_bound_admissions())?,
            emissions: collect_owned_borrowed_inventory(
                live_state.owned_projection_bound_emissions()
                    .map(|(id, emission)| (id.0, emission)),
            )?,
        };
        projection.verify_owner_round_trips().then_some(projection)
    }

    fn verify_owner_round_trips(&self) -> bool {
        let Some(owner_whole) = self.owner.publication_observation.as_ref() else { return false; };
        let Some(graph) = self.owner.session.candidate_graph.as_ref() else { return false; };
        let owner_state = &graph.intrusion.effect_algebra.context;
        if self.value_row_representatives.len() != self.value_rows.len()
            || self.effect_row_representatives.len() != self.rows.len()
        {
            return false;
        }
        for (index, (row, endpoint)) in self.value_row_representatives.iter().enumerate() {
            let Ok(row_id) = u32::try_from(index) else { return false; };
            if *row != index
                || *endpoint != self.owner.session.canonical_value(ValueEndpointKey::ValueRow(row_id))
            {
                return false;
            }
        }
        for (index, (row, endpoint)) in self.effect_row_representatives.iter().enumerate() {
            let Ok(row_id) = u32::try_from(index) else { return false; };
            if *row != index
                || *endpoint != self.owner.session.canonical_effect(EffectEndpointKey::EffectRow(row_id))
            {
                return false;
            }
        }
        if !std::ptr::eq(owner_whole, self.whole)
            || !std::ptr::eq(&self.owner.schema, self.schema)
            || !std::ptr::eq(&self.owner.session.batch, self.batch)
            || !std::ptr::eq(&self.owner.session, self.session)
            || !std::ptr::eq(owner_state, self.live_state)
            || self.owner.session.canonical_effect(self.raw_lower_endpoint) != self.canonical_lower_endpoint
            || self.owner.session.canonical_effect(self.raw_upper_endpoint) != self.canonical_upper_endpoint
            || self.owner.session.effect_endpoint(
                self.whole.original_fact.lower(), Polarity::Positive,
            ) != self.canonical_lower_endpoint
            || self.owner.session.effect_endpoint(
                self.whole.original_fact.upper(), Polarity::Negative,
            ) != self.canonical_upper_endpoint
            || raw_source_effect_endpoint(
                &self.owner.session,
                self.whole.original_fact.lower(),
                Polarity::Positive,
            ) != Some(self.raw_lower_endpoint)
            || raw_source_effect_endpoint(
                &self.owner.session,
                self.whole.original_fact.upper(),
                Polarity::Negative,
            ) != Some(self.raw_upper_endpoint)
            || self.canonical_upper_endpoint != self.whole.upper
            || self.publications.len() != 1
            || self.publications[0].0 != 0
            || !std::ptr::eq(self.publications[0].1, self.whole)
        {
            return false;
        }
        if !borrowed_inventory_matches(self.whole.calls.iter().enumerate(), &self.calls)
            || !borrowed_inventory_matches(self.batch.occurrences.iter().enumerate(), &self.facts)
            || !borrowed_inventory_matches(self.owner.session.bounds.iter().enumerate(), &self.value_rows)
            || !borrowed_inventory_matches(self.owner.session.effect_bounds.iter().enumerate(), &self.rows)
            || !borrowed_inventory_matches(self.live_state.owned_projection_relations(), &self.relations)
            || !borrowed_inventory_matches(self.live_state.observed_dependencies().enumerate(), &self.dependencies)
            || !borrowed_inventory_matches(self.live_state.origins.iter().enumerate(), &self.origins)
            || !borrowed_inventory_matches(
                self.live_state.owned_projection_source_drain_completions(), &self.completions,
            )
            || !borrowed_inventory_matches(
                self.live_state.observed_bound_admissions(), &self.admissions,
            )
            || !borrowed_inventory_matches(
                self.live_state.owned_projection_bound_emissions()
                    .map(|(id, emission)| (id.0, emission)),
                &self.emissions,
            )
        {
            return false;
        }
        if self.source_drains.len() != self.origins.len()
            || self.source_drains.iter().zip(&self.origins).any(|(drain, (_, origin))| {
                match (drain, origin.source_drain_receipt.as_ref()) {
                    (Some(borrowed), Some(owner_record)) => !std::ptr::eq(*borrowed, owner_record),
                    (None, None) => false,
                    _ => true,
                }
            })
        {
            return false;
        }
        self.verify_source_fact_owner() && self.verify_live_observation_owners()
    }

    fn verify_source_fact_owner(&self) -> bool {
        let fact = &self.whole.original_fact;
        if fact.id().occurrence() != &self.whole.edge_scrutinee
            || fact.id().local_slot() != 51
            || fact.cause().occurrence() != fact.id()
            || self.whole.relay_owner != self.schema.relay
            || self.whole.answer_owner != self.schema.answer
            || self.whole.catch_occurrence != self.schema.catch
            || self.schema.catch != self.schema.selected_arm.catch
        {
            return false;
        }
        let mut found = None;
        for root in [&self.schema.relay, &self.schema.answer] {
            let Some(actions) = self.batch.candidate_source.schedules.get(root) else { return false; };
            for action in actions {
                let candidate_source::Action::Fact(fact_index) = action else { continue; };
                let Some((owner_index, source_fact)) = self.facts.get(*fact_index) else { return false; };
                if *owner_index != *fact_index
                    || source_fact.id().occurrence() != &self.whole.edge_scrutinee
                    || source_fact.id().local_slot() != 51
                {
                    continue;
                }
                if **source_fact != *fact || found.replace(*owner_index).is_some() {
                    return false;
                }
            }
        }
        found.is_some()
    }

    fn verify_live_observation_owners(&self) -> bool {
        let whole = self.whole;
        let Some((row_index, row)) = self.rows.get(whole.result_row as usize) else { return false; };
        if *row_index != whole.result_row as usize
            || self.owner.result_row != whole.result_row
            || row.direct_lower_rows != whole.final_lower_rows
            || row.exact_non_variable_lowers != whole.final_lower_atoms
            || row.direct_lower_rows.get(..whole.initial_lower_rows.len())
                != Some(whole.initial_lower_rows.as_slice())
            || row.exact_non_variable_lowers.get(..whole.initial_lower_atoms.len())
                != Some(whole.initial_lower_atoms.as_slice())
            || whole.upper != EffectEndpointKey::EffectRow(whole.result_row)
        {
            return false;
        }
        let mut call_index = 0usize;
        for (plan_index, decision) in whole.plan.decisions.iter().enumerate() {
            match decision.outcome {
                ReceivingResidualOutcome::Suppress => {
                    if self.calls.get(call_index).is_some_and(|(index, call)| {
                        *index == call_index && call.plan_index == plan_index
                    }) {
                        return false;
                    }
                }
                ReceivingResidualOutcome::Forward => {
                    let Some((candidate_index, call)) = self.calls.get(call_index) else { return false; };
                    if *candidate_index != call_index
                        || call.identity != whole.identity
                        || call.plan_index != plan_index
                        || call.endpoint != decision.endpoint
                        || call.upper != whole.upper
                        || call.occurrence != *whole.original_fact.id()
                        || call.cause != *whole.original_fact.cause()
                        || !self.verify_call_records(call)
                    {
                        return false;
                    }
                    let Some(next) = call_index.checked_add(1) else { return false; };
                    call_index = next;
                }
            }
        }
        call_index == self.calls.len()
    }

    fn verify_call_records(&self, call: &ResidualPublicationObservation) -> bool {
        if call.origin_cut > call.source_origin_index
            || call.source_origin_index >= call.origin_end
            || call.completion_cut > call.completion_index
            || call.completion_index >= call.completion_end
            || call.emission_cut > call.emission_end
        {
            return false;
        }
        let Some((origin_index, origin)) = self.origins.get(call.source_origin_index) else { return false; };
        let Some(origin_receipt) = origin.source_drain_receipt.as_ref() else { return false; };
        let Some(Some(receipt)) = self.source_drains.get(call.source_origin_index) else { return false; };
        let Some((completion_index, completion)) = self.completions.get(call.completion_index) else { return false; };
        let Some((relation_index, relation)) = self.relations.get(call.source_relation.0 as usize) else { return false; };
        if *origin_index != call.source_origin_index
            || origin.relation != call.source_relation
            || origin.occurrence != call.occurrence
            || !std::ptr::eq(*receipt, origin_receipt)
            || origin_receipt != &call.source_drain
            || receipt.origin_index != call.source_origin_index
            || receipt.completed
            || receipt.task != LiveConstraintTask::Effect(call.endpoint, call.upper)
            || receipt.cause != *self.whole.original_fact.cause()
            || *completion_index != call.completion_index
            || !completion.completed
            || completion.drain_index != receipt.drain_index
            || completion.incoming_relation != receipt.incoming_relation
            || completion.replay_ack != receipt.replay_ack
            || completion.created_seed != receipt.created_seed
            || completion.selected_relation != receipt.selected_relation
            || completion.origin_index != receipt.origin_index
            || completion.task != receipt.task
            || completion.cause != receipt.cause
            || *relation_index != call.source_relation.0 as usize
            || self.live_state.relation_pair(call.source_relation) != Some(relation.key.pair)
        {
            return false;
        }
        match &call.native_bound {
            NativeResidualBoundEvidence::AlreadyPresent { slot, prior_emission_count } => {
                let candidate_scheme::RowKey::Effect(row_id) = slot.owner else { return false; };
                let Some((row_index, row)) = self.rows.get(row_id as usize) else { return false; };
                let expected_bound = candidate_effect::BoundKey(
                    ExtrusionEndpoint::Effect(self.whole.upper),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(call.endpoint),
                );
                if *row_index != row_id as usize
                    || slot.owner != candidate_scheme::RowKey::Effect(self.whole.result_row)
                    || call.pre_call_slot != Some(call.endpoint)
                    || *prior_emission_count != call.prior_slot_emissions
                {
                    return false;
                }
                let exact_slot = match (slot.lane, call.endpoint) {
                    (candidate_context::BoundLane::EffectLowerRow, EffectEndpointKey::EffectRow(lower)) => {
                        row.direct_lower_rows.get(slot.index) == Some(&lower)
                    }
                    (candidate_context::BoundLane::EffectLowerAtom, endpoint) => {
                        row.exact_non_variable_lowers.get(slot.index) == Some(&endpoint)
                    }
                    _ => false,
                };
                if !exact_slot { return false; }
                let mut observed_prior = 0usize;
                for (index, emission) in &self.emissions {
                    if *index >= call.emission_cut && *index < call.emission_end
                        && emission.physical == *slot
                    {
                        return false;
                    }
                    if *index < call.emission_cut && emission.physical == *slot {
                        if emission.bound != expected_bound
                            || emission.readback.bound != expected_bound
                            || emission.readback.slot != *slot
                            || emission.readback.phase != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
                            || !self.verify_emission_owner(*index, emission, expected_bound)
                        {
                            return false;
                        }
                        let Some(next) = observed_prior.checked_add(1) else { return false; };
                        observed_prior = next;
                    }
                }
                observed_prior == call.prior_slot_emissions
            }
            NativeResidualBoundEvidence::NewlyEmitted { slot, emission, admission, relation, readback } => {
                let Some((emission_index, emitted)) = self.emissions.get(emission.0) else { return false; };
                let Some((admission_index, admitted)) = self.admissions.get(admission.0) else { return false; };
                let Some((native_relation_index, native_relation)) = self.relations.get(relation.0 as usize) else { return false; };
                let expected_bound = candidate_effect::BoundKey(
                    ExtrusionEndpoint::Effect(self.whole.upper),
                    Polarity::Positive,
                    ExtrusionEndpoint::Effect(call.endpoint),
                );
                let emitted_in_window = self.emissions.iter().filter(|(index, candidate)| {
                    *index >= call.emission_cut && *index < call.emission_end
                        && candidate.physical == *slot
                }).count();
                *emission_index == emission.0
                    && *admission_index == admission.0
                    && *native_relation_index == relation.0 as usize
                    && emitted_in_window == 1
                    && emitted.admission == *admission
                    && emitted.bound == expected_bound
                    && readback.bound == expected_bound
                    && emitted.physical == *slot
                    && emitted.readback == *readback
                    && admitted.bound == readback.bound
                    && admitted.relation == Some(*relation)
                    && native_relation.key.pair == admitted.origin
                    && readback.slot == *slot
                    && slot.owner == candidate_scheme::RowKey::Effect(self.whole.result_row)
                    && emission.0 >= call.emission_cut
                    && emission.0 < call.emission_end
                    && self.verify_emission_owner(emission.0, emitted, expected_bound)
            }
        }
    }

    fn verify_emission_owner(
        &self,
        emission_index: usize,
        emission: &candidate_context::BoundEmission,
        expected_bound: candidate_effect::BoundKey,
    ) -> bool {
        let Some((owner_index, owner_emission)) = self.emissions.get(emission_index) else { return false; };
        let Some((admission_index, admission)) = self.admissions.get(emission.admission.0) else { return false; };
        let Some(relation_id) = admission.relation else { return false; };
        let Some((relation_index, relation)) = self.relations.get(relation_id.0 as usize) else { return false; };
        *owner_index == emission_index
            && std::ptr::eq(*owner_emission, emission)
            && *admission_index == emission.admission.0
            && admission.bound == expected_bound
            && emission.bound == expected_bound
            && emission.readback.bound == expected_bound
            && emission.readback.slot == emission.physical
            && emission.readback.phase == candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
            && *relation_index == relation_id.0 as usize
            && relation.key.pair == admission.origin
            && self.live_state.relation_pair(relation_id) == Some(relation.key.pair)
    }
}

#[cfg(feature = "shadow-apply-candidate")]
impl<'a> SourceInternalProjection<'a> {
    fn capture(owner: &'a ReceivingResidualExperiment) -> Option<Self> {
        let native = owner.native_owned_projection()?;
        let batch = native.batch;
        let effect_state = &owner.session.candidate_graph.as_ref()?.intrusion.effect_algebra;
        let registrations = collect_owned_borrowed_inventory(batch.candidate_calls.formals.iter().enumerate())?;
        let mut local_sources = Vec::new();
        local_sources.try_reserve_exact(registrations.len()).ok()?;
        for (_, registration) in &registrations {
            if local_sources.iter().any(|source: &OwnedLocalSource<'_>| source.registration_owner == &registration.owner) {
                continue;
            }
            let hir = batch.hir_for_source_root(&registration.owner)?;
            let source = hir.local_source_for(&registration.owner).ok().flatten()?;
            if source.source_root() != &registration.owner { return None; }
            local_sources.try_reserve(1).ok()?;
            local_sources.push(OwnedLocalSource {
                registration_owner: &registration.owner,
                hir,
                source,
            });
        }
        let relay_source = local_sources.iter().find_map(|source| {
            matches!(source.registration_owner, SourceRootId::Definition(root) if root == &owner.schema.relay)
                .then_some(source.source)
        })?;
        let internal_incidence = owner.internal_formal_permission_incidence()?;
        let permission = &internal_incidence.permission;
        let registration_index = permission.registration;
        let registration = batch.candidate_calls.formals.get(registration_index)?;
        let mut matching_recipes = batch.lambda_recipes.iter().enumerate().filter(|(_, recipe)| {
            recipe.formal_registration == Some(registration_index)
        });
        let (recipe_index, recipe) = matching_recipes.next()?;
        if matching_recipes.next().is_some()
            || recipe.occurrence != internal_incidence.lambda_origin.lambda
            || recipe.root_component != internal_incidence.use_record.target_root_component
            || recipe.root_component >= batch.component_terms.len()
        {
            return None;
        }
        let registered_root = batch.component_term_at(recipe.root_component);
        if registered_root != batch.component_terms[recipe.root_component]
            || internal_incidence.lambda_fact.upper() != registered_root
            || internal_incidence.internal_fact.lower() != registered_root
        {
            return None;
        }
        let TermView::PositiveFunction { argument_effect, .. } =
            owner.session.store.term_view(internal_incidence.lambda_origin.function).ok()?
        else { return None; };
        let TermView::LiveVariable(argument_view) = owner.session.store.term_view(argument_effect).ok()?
        else { return None; };
        if argument_view.kind() != ComponentKind::Effect
            || argument_view.polarity() != Polarity::Negative
            || argument_view.ordinal() != permission.entry_effect
        {
            return None;
        }
        let internal_root_join = InternalRegisteredRootJoin {
            registration: registration_index,
            recipe_index,
            root_component: recipe.root_component,
            parameter_native_root: registration.native_root,
            registered_root,
        };
        let internal_function_witness = InternalFunctionWitness {
            function: internal_incidence.lambda_origin.function,
            argument_effect,
            entry_effect: argument_view.ordinal(),
        };
        let mut catch_expressions = relay_source.expressions().iter().filter(|expression| {
            expression.occurrence == owner.schema.catch
        });
        let catch_expression = catch_expressions.next()?;
        if catch_expressions.next().is_some() { return None; }
        let Form::Catch { scrutinee, arms } = &catch_expression.form else { return None; };
        let catch_scrutinee = relay_source.expression(scrutinee)?;
        if catch_scrutinee.occurrence != owner.schema.edge_scrutinee || arms.len() != 2 {
            return None;
        }
        let mut resolved_operations = Vec::new();
        resolved_operations.try_reserve_exact(arms.len()).ok()?;
        for (arm_index, arm) in arms.iter().enumerate() {
            if let Pattern::Operation {
                resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration),
                operation_source,
                ..
            } = &arm.pattern
            {
                resolved_operations.try_reserve(1).ok()?;
                resolved_operations.push((arm_index, operation_source, declaration));
            }
        }
        let (selected_index, selected_source, selected_declaration) = resolved_operations.iter()
            .find(|record| record.0 == owner.schema.selected_arm.arm_ordinal as usize)
            .copied()?;
        if selected_index != owner.schema.selected_arm.arm_ordinal as usize
            || selected_source != &owner.schema.selected_arm.operation_source
            || !Arc::ptr_eq(selected_declaration, &owner.schema.selected_arm.operation)
            || selected_declaration.id != owner.schema.selected_arm.operation_identity
            || selected_declaration.id.family != owner.schema.provider_identity.family
        {
            return None;
        }

        let graph = owner.session.candidate_graph.as_ref()?;
        let context = &graph.intrusion.effect_algebra.context;
        let projection = Self {
            native,
            local_sources,
            catch_source: relay_source,
            catch_expression,
            catch_scrutinee,
            catch_arms: arms,
            resolved_operations,
            formal_registrations: registrations,
            formal_names: collect_owned_borrowed_inventory(batch.candidate_calls.names.iter().enumerate())?,
            calls: collect_owned_borrowed_inventory(batch.candidate_calls.calls.iter().enumerate())?,
            parameter_recipes: collect_owned_borrowed_inventory(batch.parameter_recipes.iter().enumerate())?,
            lambda_recipes: collect_owned_borrowed_inventory(batch.lambda_recipes.iter().enumerate())?,
            internal_root_join,
            internal_function_witness,
            formal_entry_permissions: collect_owned_borrowed_inventory(
                graph.intrusion.effect_algebra.owned_projection_entry_permissions(),
            )?,
            lambda_origins: collect_owned_borrowed_inventory(context.lambda_argument_effects.iter().enumerate())?,
            definition_uses: collect_owned_borrowed_inventory(batch.definition_uses().iter().enumerate())?,
            routed_uses: collect_owned_borrowed_inventory(owner.session.routed_uses.iter().enumerate())?,
            schedules: {
                let mut inventory = Vec::new();
                inventory.try_reserve_exact(batch.candidate_source.schedules.len()).ok()?;
                inventory.extend(batch.candidate_source.schedules.iter());
                inventory
            },
            source_owners: {
                let mut inventory = Vec::new();
                inventory.try_reserve_exact(batch.candidate_source.source_owners.len()).ok()?;
                inventory.extend(batch.candidate_source.source_owners.iter());
                inventory
            },
            component_terms: {
                if batch.components.len() != batch.component_terms.len() { return None; }
                let mut inventory = Vec::new();
                inventory.try_reserve_exact(batch.components.len()).ok()?;
                inventory.extend(batch.components.iter().zip(&batch.component_terms).enumerate()
                    .map(|(index, (component, term))| (index, component, *term)));
                inventory
            },
            semantic_facts: collect_owned_borrowed_inventory(owner.session.store.facts().iter().enumerate())?,
            internal_incidence,
        };
        projection.verify_owner_round_trips().then_some(projection)
    }

    fn verify_owner_round_trips(&self) -> bool {
        let owner = self.native.owner;
        let batch = self.native.batch;
        let Some(graph) = owner.session.candidate_graph.as_ref() else { return false; };
        let effect_state = &graph.intrusion.effect_algebra;
        if !borrowed_inventory_matches(batch.candidate_calls.formals.iter().enumerate(), &self.formal_registrations)
            || !borrowed_inventory_matches(batch.candidate_calls.names.iter().enumerate(), &self.formal_names)
            || !borrowed_inventory_matches(batch.candidate_calls.calls.iter().enumerate(), &self.calls)
            || !borrowed_inventory_matches(batch.parameter_recipes.iter().enumerate(), &self.parameter_recipes)
            || !borrowed_inventory_matches(batch.lambda_recipes.iter().enumerate(), &self.lambda_recipes)
            || !borrowed_inventory_matches(effect_state.owned_projection_entry_permissions(), &self.formal_entry_permissions)
            || !borrowed_inventory_matches(effect_state.context.lambda_argument_effects.iter().enumerate(), &self.lambda_origins)
            || !borrowed_inventory_matches(batch.definition_uses().iter().enumerate(), &self.definition_uses)
            || !borrowed_inventory_matches(owner.session.routed_uses.iter().enumerate(), &self.routed_uses)
            || !borrowed_inventory_matches(owner.session.store.facts().iter().enumerate(), &self.semantic_facts)
        {
            return false;
        }
        for (index, (_, registration)) in self.formal_registrations.iter().enumerate() {
            if self.formal_registrations[..index].iter().any(|(_, prior)| {
                prior.owner == registration.owner && prior.lambda == registration.lambda
            }) {
                return false;
            }
        }
        for source in &self.local_sources {
            let Some(hir) = batch.hir_for_source_root(source.registration_owner) else { return false; };
            if !Arc::ptr_eq(hir, source.hir)
                || !hir.local_source_for(source.registration_owner).is_ok_and(|retained| {
                    retained.is_some_and(|retained| std::ptr::eq(retained, source.source))
                })
            {
                return false;
            }
        }
        if self.schedules.len() != batch.candidate_source.schedules.len()
            || self.schedules.iter().any(|(root, actions)| {
                !batch.candidate_source.schedules.get(*root).is_some_and(|current| std::ptr::eq(*actions, current))
            })
            || self.source_owners.len() != batch.candidate_source.source_owners.len()
            || self.source_owners.iter().any(|(occurrence, root)| {
                !batch.candidate_source.source_owners.get(*occurrence).is_some_and(|current| std::ptr::eq(*root, current))
            })
            || self.component_terms.len() != batch.components.len()
            || self.component_terms.iter().enumerate().any(|(index, (owner_index, component, term))| {
                *owner_index != index || !std::ptr::eq(*component, &batch.components[index])
                    || *term != batch.component_terms[index]
            })
        {
            return false;
        }
        for (registration_index, registration) in &self.formal_registrations {
            let Some(local_source) = self.local_sources.iter().find(|source| source.registration_owner == &registration.owner) else { return false; };
            let root_is_owned = match &registration.owner {
                SourceRootId::Definition(root) => local_source.hir.owns_definition_root(root),
                SourceRootId::Expression(root) => local_source.hir.owns_expression_root(root),
            };
            if !root_is_owned {
                return false;
            }
            let Some(expression) = local_source.source.expressions().get(registration.lambda) else { return false; };
            if !local_source.hir.owns_occurrence(&expression.occurrence)
                || !matches!(&expression.form, Form::Lambda { parameter, .. }
                    if parameter.id == registration.parameter && parameter.id.source_root() == &registration.owner)
                || batch.parameter_recipes.get(registration.recipe_position) != Some(&registration.parameter)
            {
                return false;
            }
            if self.source_owners.iter().filter(|(occurrence, root)| {
                **occurrence == expression.occurrence && **root == registration.owner
            }).count() != 1
                || self.source_owners.iter().find(|(occurrence, _)| **occurrence == expression.occurrence)
                    .is_none_or(|(_, root)| **root != registration.owner)
            {
                return false;
            }
            let _ = registration_index;
        }
        for (permission_index, permission) in &self.formal_entry_permissions {
            if *permission_index >= self.formal_entry_permissions.len() { return false; }
            let Some((registration_index, registration)) = self.formal_registrations.get(permission.registration) else { return false; };
            if *registration_index != permission.registration
                || registration.role != candidate_call::FormalRole::Computation
                || registration.recipe_position != permission.parameter
                || registration.parameter != permission.formal
                || registration.owner != permission.source_owner
                || registration.scope != permission.scope
                || registration.entry_effect != Some(permission.entry_effect)
            {
                return false;
            }
            let SourceRootId::Definition(root) = &permission.source_owner else { return false; };
            let Some(actions) = batch.candidate_source.schedules.get(root) else { return false; };
            let mut matching_actions = actions.iter().filter_map(|action| match action {
                candidate_source::Action::FormalEntry { registration: index, annotation, occurrence, scope }
                    if *index == permission.registration => Some((annotation, occurrence, scope)),
                _ => None,
            });
            let Some((annotation, occurrence, scope)) = matching_actions.next() else { return false; };
            if matching_actions.next().is_some()
                || annotation.owner != permission.source_owner
                || annotation.position != permission.annotation_position
                || occurrence != &permission.occurrence
                || scope != &permission.scope
                || annotation.ty.effects.as_ref().is_none_or(|row| {
                    row.position != permission.source_row || row.concrete != permission.concrete
                })
            {
                return false;
            }
            let Some(local_source) = self.local_sources.iter().find(|source| {
                source.registration_owner == &registration.owner
            }) else { return false; };
            let Some(expression) = local_source.source.expressions().get(registration.lambda) else { return false; };
            let Form::Lambda { parameter, .. } = &expression.form else { return false; };
            if parameter.id != permission.formal {
                return false;
            }
            let Some(source_annotation) = parameter.annotation.as_ref() else { return false; };
            if source_annotation.owner != permission.source_owner
                || source_annotation.position != permission.annotation_position
                || source_annotation.ty.effects.as_ref().is_none_or(|row| {
                    row.position != permission.source_row || row.concrete != permission.concrete
                })
            {
                return false;
            }
        }
        let Form::Catch { scrutinee, arms } = &self.catch_expression.form else { return false; };
        if !self.local_sources.iter().any(|source| {
            std::ptr::eq(self.catch_source, source.source)
                && matches!(source.registration_owner, SourceRootId::Definition(root) if root == &owner.schema.relay)
        })
            || self.catch_expression.occurrence != owner.schema.catch
            || !std::ptr::eq(self.catch_scrutinee, match self.catch_source.expression(scrutinee) { Some(value) => value, None => return false })
            || self.catch_scrutinee.occurrence != owner.schema.edge_scrutinee
            || !std::ptr::eq(self.catch_arms, arms.as_slice())
            || arms.len() != 2
        {
            return false;
        }
        let Some((selected_index, arm)) = arms.iter().enumerate().find(|(index, _)| *index == owner.schema.selected_arm.arm_ordinal as usize) else { return false; };
        if selected_index != owner.schema.selected_arm.arm_ordinal as usize { return false; }
        let Pattern::Operation {
            resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration),
            operation_source,
            ..
        } = &arm.pattern else { return false; };
        if operation_source != &owner.schema.selected_arm.operation_source
            || !Arc::ptr_eq(declaration, &owner.schema.selected_arm.operation)
            || declaration.id != owner.schema.selected_arm.operation_identity
        {
            return false;
        }
        let Some(definition_index) = self.definition_uses.iter().position(|(_, use_record)| {
            std::ptr::eq(*use_record, self.internal_incidence.use_record)
        }) else { return false; };
        let Some((owner_index, use_record)) = self.definition_uses.get(definition_index) else { return false; };
        if *owner_index != definition_index || !std::ptr::eq(*use_record, self.internal_incidence.use_record)
            || self.internal_incidence.target_owner != &owner.schema.relay
            || self.internal_incidence.receiving_owner != &owner.schema.answer
            || !self.routed_uses.iter().any(|(index, route)| {
                std::ptr::eq(*route, self.internal_incidence.internal_route)
                    && route.kind == RoutedUseKind::Internal
                    && route.fact == Some(self.internal_incidence.internal_fact.id())
                    && *index < self.routed_uses.len()
            })
        {
            return false;
        }
        let Ok(TermView::PositiveFunction { argument_effect, .. }) =
            owner.session.store.term_view(self.internal_function_witness.function)
        else { return false; };
        let Ok(TermView::LiveVariable(argument_view)) =
            owner.session.store.term_view(argument_effect)
        else { return false; };
        let permission = &self.internal_incidence.permission;
        if argument_effect != self.internal_function_witness.argument_effect
            || argument_view.kind() != ComponentKind::Effect
            || argument_view.polarity() != Polarity::Negative
            || argument_view.ordinal() != self.internal_function_witness.entry_effect
            || argument_view.ordinal() != permission.entry_effect
            || self.internal_function_witness.function != self.internal_incidence.lambda_origin.function
        {
            return false;
        }
        let Some((root_registration_index, root_registration)) =
            self.formal_registrations.get(self.internal_root_join.registration)
        else { return false; };
        let Some((recipe_index, recipe)) = self.lambda_recipes.get(self.internal_root_join.recipe_index)
        else { return false; };
        if *root_registration_index != self.internal_root_join.registration
            || *recipe_index != self.internal_root_join.recipe_index
            || recipe.formal_registration != Some(self.internal_root_join.registration)
            || recipe.root_component != self.internal_root_join.root_component
            || self.internal_root_join.parameter_native_root != root_registration.native_root
            || self.internal_root_join.registered_root != batch.component_term_at(recipe.root_component)
            || self.internal_incidence.lambda_fact.upper() != self.internal_root_join.registered_root
            || self.internal_incidence.internal_fact.lower() != self.internal_root_join.registered_root
        {
            return false;
        }
        let mut permissions = self.formal_entry_permissions.iter().filter(|(_, retained)| {
            retained.registration == permission.registration
        });
        let Some((_, retained_permission)) = permissions.next() else { return false; };
        if permissions.next().is_some()
            || retained_permission.formal != *permission.formal
            || retained_permission.occurrence != *permission.occurrence
            || retained_permission.source_owner != *permission.source_owner
            || retained_permission.scope != *permission.scope
            || retained_permission.annotation_position != *permission.annotation_position
            || retained_permission.source_row != *permission.source_row
            || retained_permission.entry_effect != permission.entry_effect
            || retained_permission.concrete.as_slice().as_ptr() != permission.concrete.as_ptr()
        {
            return false;
        }
        if !self.lambda_origins.iter().any(|(_, origin)| std::ptr::eq(*origin, self.internal_incidence.lambda_origin))
            || !self.semantic_facts.iter().any(|(_, fact)| std::ptr::eq(*fact, self.internal_incidence.lambda_fact))
            || !self.semantic_facts.iter().any(|(_, fact)| std::ptr::eq(*fact, self.internal_incidence.internal_fact))
        {
            return false;
        }
        true
    }
}

#[cfg(feature = "shadow-apply-candidate")]
impl<'a> ProviderNativeContextProjection<'a> {
    fn capture(
        owner: &'a ReceivingResidualExperiment,
    ) -> Result<Self, candidate_context::CurrentEmissionGap> {
        let source_internal = owner.source_internal_projection()
            .ok_or(candidate_context::CurrentEmissionGap::MissingInternalCertificate)?;
        let provider = owner.provider_entry_certificate()?;
        let Some(graph) = owner.session.candidate_graph.as_ref() else {
            return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
        };
        let effect_state = &graph.intrusion.effect_algebra;
        let views = collect_owned_borrowed_inventory(effect_state.views.iter().enumerate())
            .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?;
        let Some((emission_index, owner_emission)) = source_internal.native.emissions
            .get(provider.internal.emission.id.0)
        else { return Err(candidate_context::CurrentEmissionGap::MissingEmission); };
        let Some((admission_index, owner_admission)) = source_internal.native.admissions
            .get(provider.internal.emission.admission_id.0)
        else { return Err(candidate_context::CurrentEmissionGap::MissingAdmission); };
        if !borrowed_inventory_matches(effect_state.views.iter().enumerate(), &views)
            || !std::ptr::eq(source_internal.native.owner, owner)
            || !std::ptr::eq(provider.internal.incidence.use_record, source_internal.internal_incidence.use_record)
            || !std::ptr::eq(provider.internal.incidence.lambda_origin, source_internal.internal_incidence.lambda_origin)
            || !std::ptr::eq(provider.internal.incidence.lambda_fact, source_internal.internal_incidence.lambda_fact)
            || !std::ptr::eq(provider.internal.incidence.internal_fact, source_internal.internal_incidence.internal_fact)
            || !std::ptr::eq(provider.internal.incidence.internal_route, source_internal.internal_incidence.internal_route)
            || *emission_index != provider.internal.emission.id.0
            || !std::ptr::eq(*owner_emission, provider.internal.emission.emission)
            || *admission_index != provider.internal.emission.admission_id.0
            || !std::ptr::eq(*owner_admission, provider.internal.emission.admission)
        {
            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
        }

        let mut catch_fact_index = None;
        for (index, fact) in &source_internal.native.facts {
            if std::ptr::eq(*fact, provider.catch_fact) {
                if catch_fact_index.replace(*index).is_some() {
                    return Err(candidate_context::CurrentEmissionGap::AmbiguousCatchFact);
                }
            }
        }
        let Some(catch_fact_index) = catch_fact_index else {
            return Err(candidate_context::CurrentEmissionGap::MissingCatchFact);
        };
        if provider.catch_fact.id().occurrence() != &owner.schema.edge_scrutinee
            || provider.catch_fact.id().local_slot() != 51
        {
            return Err(candidate_context::CurrentEmissionGap::MissingCatchFact);
        }
        let EffectEndpointKey::AnnotationMember(view_index, member_index) = provider.endpoint else {
            return Err(candidate_context::CurrentEmissionGap::MissingCommonEndpoint);
        };
        let Some((owner_view_index, owner_view)) = views.get(view_index as usize) else {
            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
        };
        if *owner_view_index != view_index as usize
            || !std::ptr::eq(*owner_view, provider.operation_view)
            || provider.operation_view.tail.is_some()
            || provider.operation_view.allowed.get(member_index as usize)
                != Some(&owner.schema.operation.id.family)
        {
            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
        }
        let candidate_effect::ViewOrigin::Operation(origin) = &provider.operation_view.provenance else {
            return Err(candidate_context::CurrentEmissionGap::MissingProviderOrigin);
        };
        if origin.occurrence != owner.schema.provider
            || !Arc::ptr_eq(&origin.declaration, &owner.schema.operation)
        {
            return Err(candidate_context::CurrentEmissionGap::MissingProviderOrigin);
        }
        let result = Self {
            source_internal,
            provider,
            views,
            catch_fact_owner: ProviderFactOwner::BatchOccurrence(catch_fact_index),
            provider_view_index: view_index as usize,
        };
        if !result.verify_path_owners(&result.provider.entry_path)
            || !result.verify_path_owners(&result.provider.catch_path)
            || !result.verify_semantic_fact_owners()
        {
            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
        }
        Ok(result)
    }

    fn verify_path_owners(&self, path: &[LowerPathStep<'_>]) -> bool {
        for step in path {
            match step {
                LowerPathStep::SupportMember { view_index, member_index, view, family, closed_tail, .. } => {
                    let Some((index, owner_view)) = self.views.get(*view_index as usize) else { return false; };
                    if *index != *view_index as usize
                        || !std::ptr::eq(*owner_view, *view)
                        || !*closed_tail
                        || view.tail.is_some()
                        || !std::ptr::eq(*family, match view.allowed.get(*member_index as usize) {
                            Some(family) => family,
                            None => return false,
                        })
                    {
                        return false;
                    }
                }
                LowerPathStep::Physical(edge) => {
                    let Some((emission_index, emission)) = self.source_internal.native.emissions.get(edge.id.0) else { return false; };
                    let Some((admission_index, admission)) = self.source_internal.native.admissions.get(edge.admission_id.0) else { return false; };
                    let Some((relation_index, relation)) = self.source_internal.native.relations.get(edge.relation.0 as usize) else { return false; };
                    if *emission_index != edge.id.0
                        || !std::ptr::eq(*emission, edge.emission)
                        || *admission_index != edge.admission_id.0
                        || !std::ptr::eq(*admission, edge.admission)
                        || *relation_index != edge.relation.0 as usize
                        || relation.key.pair != admission.origin
                        || admission.relation != Some(edge.relation)
                        || emission.admission != edge.admission_id
                        || emission.physical != edge.slot
                        || emission.bound != edge.bound
                        || admission.bound != edge.bound
                    {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn verify_semantic_fact_owners(&self) -> bool {
        let facts = &self.source_internal.semantic_facts;
        let incidence = &self.source_internal.internal_incidence;
        let fact_is_unique = |fact: &SemanticFact| {
            facts.iter().filter(|(_, owner_fact)| std::ptr::eq(*owner_fact, fact)).count() == 1
        };
        fact_is_unique(incidence.lambda_fact) && fact_is_unique(incidence.internal_fact)
    }

    /// Build the concrete borrowed readers used by the R60 local-decoding
    /// correspondence. This deliberately keeps the same session and live
    /// State references as the R55/R57 projection; it does not snapshot,
    /// canonicalize, or assign a new owner identity.
    #[allow(dead_code, reason = "source-side construction for the R60 LocalDecode bridge")]
    fn local_decode_reader(&self) -> Option<LocalDecodeReader<'_, 'a>> {
        let native = &self.source_internal.native;
        let graph = native.owner.session.candidate_graph.as_ref()?;
        let effect_state = &graph.intrusion.effect_algebra;
        if !std::ptr::eq(&effect_state.context, native.live_state)
            || !self.source_internal.verify_owner_round_trips()
            || !borrowed_inventory_matches(
                native.owner.session.effect_bounds.iter().enumerate(), &native.rows,
            )
            || !borrowed_inventory_matches(effect_state.views.iter().enumerate(), &self.views)
            || !self.verify_path_owners(&self.provider.entry_path)
            || !self.verify_path_owners(&self.provider.catch_path)
        {
            return None;
        }
        Some(LocalDecodeReader { projection: self })
    }
}

/// The row and checked edge remain borrowed from one sealed projection. The
/// row borrow records which exact current vector supplied the lane/index;
/// `edge` records the matching native emission, admission and live relation.
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "source-side R60 reader result; consumed by the Lean-facing correspondence")]
pub(super) struct BorrowedPhysicalLowerRead<'a> {
    pub(super) row_index: usize,
    pub(super) owner_state: &'a candidate_context::State,
    pub(super) row: BorrowedEffectRowRead<'a>,
    pub(super) edge: candidate_context::CheckedPhysicalLowerEdge<'a>,
}

#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "source-side R60 row read retains raw bounds and their canonical representative")]
pub(super) struct BorrowedEffectRowRead<'a> {
    pub(super) index: usize,
    pub(super) owner_state: &'a candidate_context::State,
    pub(super) canonical: EffectEndpointKey,
    pub(super) bounds: &'a EffectBounds,
}

#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "source-side R60 view read retains the exact indexed owner view")]
pub(super) struct BorrowedEffectViewRead<'a> {
    pub(super) index: usize,
    pub(super) owner_state: &'a candidate_context::State,
    pub(super) view: &'a candidate_effect::View,
}

/// Read-only owner-local rows, views and physical positive effect-lower edges.
/// The constructor is private and rechecks the complete borrowed inventories;
/// callers cannot supply alternate State, row, view, admission or emission
/// tables.
#[cfg(feature = "shadow-apply-candidate")]
#[allow(dead_code, reason = "sealed R60 source-side local decoder")]
struct LocalDecodeReader<'p, 'a> {
    projection: &'p ProviderNativeContextProjection<'a>,
}

#[cfg(feature = "shadow-apply-candidate")]
impl<'p, 'a> LocalDecodeReader<'p, 'a> {
    fn rows(&self) -> &'p [(usize, &'a EffectBounds)] {
        &self.projection.source_internal.native.rows
    }

    fn row(&self, index: usize) -> Option<BorrowedEffectRowRead<'a>> {
        let (owner_index, bounds) = self.rows().get(index)?;
        let (representative_index, canonical) = self.projection.source_internal.native
            .effect_row_representatives.get(index)?;
        let row_id = u32::try_from(index).ok()?;
        let native = &self.projection.source_internal.native;
        if *owner_index != index
            || *representative_index != index
            || !std::ptr::eq(*bounds, native.session.effect_bounds.get(index)?)
            || *canonical != native.session.canonical_effect(EffectEndpointKey::EffectRow(row_id))
        {
            return None;
        }
        Some(BorrowedEffectRowRead {
            index,
            owner_state: native.live_state,
            canonical: *canonical,
            bounds: *bounds,
        })
    }

    fn views(&self) -> &'p [(usize, &'a candidate_effect::View)] {
        &self.projection.views
    }

    fn view(&self, index: usize) -> Option<BorrowedEffectViewRead<'a>> {
        let (owner_index, view) = self.views().get(index)?;
        let graph = self.projection.source_internal.native.owner.session.candidate_graph.as_ref()?;
        let effect_state = &graph.intrusion.effect_algebra;
        if *owner_index != index
            || !std::ptr::eq(&effect_state.context, self.projection.source_internal.native.live_state)
            || !std::ptr::eq(*view, effect_state.views.get(index)?)
        {
            return None;
        }
        Some(BorrowedEffectViewRead {
            index,
            owner_state: self.projection.source_internal.native.live_state,
            view: *view,
        })
    }

    /// Read exactly one current lower slot and authenticate its existing
    /// admission/emission/relation with State's checked helper. Atom lanes
    /// reject row endpoints because R47's atom-vector interpretation preserves
    /// them as atoms, while the native current-bound read interprets a row
    /// constructor as an effect-row key.
    fn physical_lower(
        &self,
        row_index: usize,
        lane: candidate_context::BoundLane,
        index: usize,
    ) -> Result<BorrowedPhysicalLowerRead<'a>, candidate_context::CurrentEmissionGap> {
        let row = self.row(row_index)
            .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
        let row_id = u32::try_from(row_index)
            .map_err(|_| candidate_context::CurrentEmissionGap::BoundMismatch)?;
        let endpoint = match lane {
            candidate_context::BoundLane::EffectLowerRow => EffectEndpointKey::EffectRow(
                *row.bounds.direct_lower_rows.get(index)
                    .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?,
            ),
            candidate_context::BoundLane::EffectLowerAtom => {
                let endpoint = *row.bounds.exact_non_variable_lowers.get(index)
                    .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
                if matches!(endpoint, EffectEndpointKey::EffectRow(_)) {
                    return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
                }
                endpoint
            }
            _ => return Err(candidate_context::CurrentEmissionGap::WrongEntrySlot),
        };
        let slot = candidate_context::PhysicalBoundSlot {
            owner: candidate_scheme::RowKey::Effect(row_id),
            lane,
            index,
        };
        let bound = candidate_effect::BoundKey(
            ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row_id)),
            Polarity::Positive,
            ExtrusionEndpoint::Effect(endpoint),
        );
        let edge = self.projection.source_internal.native.live_state
            .checked_physical_lower_edge(slot, bound)?;
        if edge.slot != slot || edge.bound != bound {
            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
        }
        Ok(BorrowedPhysicalLowerRead {
            row_index,
            owner_state: row.owner_state,
            row,
            edge,
        })
    }
}

#[cfg(feature = "shadow-apply-candidate")]
fn raw_source_effect_endpoint(
    session: &InferenceSession,
    term: Term,
    polarity: Polarity,
) -> Option<EffectEndpointKey> {
    match session.store.term_view(term).ok()? {
        TermView::Leaf(Leaf::EffectBottomPositive) => Some(EffectEndpointKey::BottomPositive),
        TermView::Leaf(Leaf::EmptyEffectNegative) => Some(EffectEndpointKey::EmptyNegative),
        TermView::Component(_) => {
            let endpoint = session.component_endpoint(term);
            (endpoint.kind == ComponentKind::Effect)
                .then_some(EffectEndpointKey::EffectRow(endpoint.ordinal))
        }
        TermView::LiveVariable(view)
            if view.kind() == ComponentKind::Effect && view.polarity() == polarity =>
        {
            Some(EffectEndpointKey::EffectRow(view.ordinal()))
        }
        _ => None,
    }
}

#[cfg(feature = "shadow-apply-candidate")]
fn borrowed_inventory_matches<'a, T>(
    source: impl Iterator<Item = (usize, &'a T)>,
    inventory: &[(usize, &'a T)],
) -> bool {
    let mut source = source;
    for (index, (owner_index, borrowed)) in inventory.iter().enumerate() {
        let Some((source_index, source_item)) = source.next() else { return false; };
        if index != *owner_index || index != source_index || !std::ptr::eq(*borrowed, source_item) {
            return false;
        }
    }
    source.next().is_none()
}

impl InferenceSession {
    fn execute_receiving_assembly(
        &mut self,
        schema: &Assembly,
    ) -> Result<PendingResidualFold, SolveAvailabilityError>
    {
        // Route the unique original module use directly. This is an assembly
        // inventory, not an SCC: do not populate intrusion active_roots/uses.
        if !self.batch.candidate_source.loose.is_empty() || self.batch.definition_uses().len() != 1
        {
            return Err(native_unavailable());
        }
        let usage = &self.batch.definition_uses()[0];
        let SourceReceiver::Definition(parent) = &usage.parent else {
            return Err(native_unavailable());
        };
        if self.batch.definitions[parent.ordinal() as usize].root != schema.answer
            || self.batch.definitions[usage.target.ordinal() as usize].root != schema.relay
        {
            return Err(native_unavailable());
        }
        let mut residual = None;
        for root in [&schema.relay, &schema.answer] {
            let actions = self
                .batch
                .candidate_source
                .schedules
                .get(root)
                .ok_or_else(native_unavailable)?
                .clone();
            for action in actions {
                if let candidate_source::Action::Fact(index) = &action {
                    let fact = &self.batch.occurrences[*index];
                    if fact.id.occurrence() == &schema.edge_scrutinee && fact.id.local_slot() == 51
                    {
                        if residual.replace(*index).is_some() {
                            return Err(native_unavailable());
                        }
                        continue;
                    }
                }
                if let candidate_source::Action::Module(occurrence) = &action {
                    let id = DefinitionUseId::new(
                        self.batch.collection_artifact.clone(),
                        occurrence.clone(),
                    );
                    self.route_internal(&id)?;
                } else {
                    self.execute_candidate_action(&action)?;
                }
            }
        }
        let fact = self.batch.occurrences[residual.ok_or_else(native_unavailable)?].clone();
        let lower = self.effect_endpoint(fact.lower, Polarity::Positive);
        let upper = self.effect_endpoint(fact.upper, Polarity::Negative);
        let EffectEndpointKey::EffectRow(result_row) = self.canonical_effect(upper) else {
            return Err(native_unavailable());
        };
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| native_unavailable())?;
        pending.push(lower);
        let mut seen = HashSet::new();
        seen.try_reserve(1).map_err(|_| native_unavailable())?;
        let mut terminals = Vec::new();
        let mut work = 0usize;
        while let Some(endpoint) = pending.pop() {
            work = work.checked_add(1).ok_or_else(native_unavailable)?;
            if work > candidate_source::SCOPED_WORK_LIMIT {
                return Err(native_unavailable());
            }
            let endpoint = self.canonical_effect(endpoint);
            seen.try_reserve(1).map_err(|_| native_unavailable())?;
            if !seen.insert(endpoint) {
                continue;
            }
            match endpoint {
                EffectEndpointKey::BottomPositive => {}
                EffectEndpointKey::EffectRow(row) => {
                    let bounds = &self.effect_bounds[row as usize];
                    // No terminal evidence is not evidence of an empty row.
                    if bounds.direct_lower_rows.is_empty()
                        && bounds.exact_non_variable_lowers.is_empty()
                        && !bounds.has_bottom_lower
                    {
                        return Err(native_unavailable());
                    }
                    let lower_count = bounds.direct_lower_rows.len()
                        .checked_add(bounds.exact_non_variable_lowers.len())
                        .ok_or_else(native_unavailable)?;
                    pending.try_reserve(lower_count).map_err(|_| native_unavailable())?;
                    pending.extend(bounds.direct_lower_rows.iter().copied().map(EffectEndpointKey::EffectRow));
                    pending.extend(bounds.exact_non_variable_lowers.iter().copied());
                }
                EffectEndpointKey::Support(view) => {
                    let view_data = self
                        .candidate_graph
                        .as_ref()
                        .ok_or_else(native_unavailable)?
                        .intrusion
                        .effect_algebra
                        .views
                        .get(view as usize)
                        .ok_or_else(native_unavailable)?;
                    // An unresolved tail is Pending; never publish a partial
                    // certificate from the concrete members beside that tail.
                    if view_data.tail.is_some() {
                        return Err(native_unavailable());
                    }
                    pending.try_reserve(view_data.allowed.len()).map_err(|_| native_unavailable())?;
                    for member in 0..view_data.allowed.len() {
                        pending.push(EffectEndpointKey::AnnotationMember(
                            view,
                            u32::try_from(member).map_err(|_| native_unavailable())?,
                        ));
                    }
                }
                _ => {
                    terminals.try_reserve(1).map_err(|_| native_unavailable())?;
                    terminals.push(endpoint);
                }
            }
        }
        if terminals.is_empty() {
            return Err(native_unavailable());
        }
        Ok(PendingResidualFold { fact, upper, terminals, result_row })
    }
}

#[cfg(feature = "shadow-apply-candidate")]
fn snapshot_suppression(
    certificate: &ProviderEntryCertificate<'_>,
    schema: &Assembly,
) -> Result<AuthenticatedSuppression, SolveAvailabilityError> {
    let entry_path = snapshot_path(&certificate.entry_path, certificate.endpoint)
        .map_err(|_| native_unavailable())?;
    let catch_path = snapshot_path(&certificate.catch_path, certificate.endpoint)
        .map_err(|_| native_unavailable())?;
    Ok(AuthenticatedSuppression {
        endpoint: certificate.endpoint,
        provider_occurrence: schema.provider.clone(),
        provider_source: schema.provider_source.clone(),
        provider_source_range: schema.provider_source_range,
        provider_identity: schema.provider_identity.clone(),
        entry_effect: certificate.internal.incidence.permission.entry_effect,
        emission: certificate.internal.emission.id,
        admission: certificate.internal.emission.admission_id,
        catch_fact: certificate.catch_fact.id.clone(),
        catch_occurrence: schema.selected_arm.catch.clone(),
        arm_ordinal: schema.selected_arm.arm_ordinal,
        arm_source: schema.selected_arm.arm_source.clone(),
        arm_range: schema.selected_arm.arm_range,
        operation_source: schema.selected_arm.operation_source.clone(),
        operation: schema.selected_arm.operation.id.clone(),
        unit_payload_source: schema.selected_arm.unit_payload_source.clone(),
        unit_payload_range: schema.selected_arm.unit_payload_range,
        continuation_is_wildcard: schema.selected_arm.continuation_is_wildcard,
        entry_path,
        catch_path,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const DECLARATIONS: &str =
        "act signal:\n    our ping: () -> int\nact write:\n    our ping: () -> int\n";
    const RELAY: &str =
        "my relay(thunk: [signal] int) = catch thunk { signal::ping(), _ -> 1, v -> v }\n";

    fn lower(text: &str) -> (Arc<HirModule>, DefinitionRootId) {
        let text: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            text.clone(),
            Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(
            parsed.structural_recoveries().is_empty(),
            "{:?}",
            parsed.structural_recoveries()
        );
        let hir = Arc::new(
            yu_hir::shadow::lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "receiving-residual",
                    "source.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .unwrap(),
        );
        let answer = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == "answer" => {
                    Some(binding.definition_root().clone())
                }
                _ => None,
            })
            .unwrap();
        (hir, answer)
    }

    fn permission_family(hir: &HirModule) -> yu_hir::shadow::SourceEffectId {
        hir.items()
            .iter()
            .find_map(|item| {
                let HirItem::Binding(binding) = item else {
                    return None;
                };
                let local = source(hir, binding.definition_root()).ok()?;
                local
                    .expressions()
                    .iter()
                    .find_map(|expression| match &expression.form {
                        Form::Lambda { parameter, .. } => parameter
                            .annotation
                            .as_ref()
                            .and_then(|annotation| annotation.ty.effects.as_ref())
                            .and_then(|row| row.concrete.first())
                            .cloned(),
                        _ => None,
                    })
            })
            .unwrap()
    }

    #[test]
    fn exact_signal_use_suppresses_actual_native_result_family() {
        let (hir, answer) = lower(&format!(
            "{DECLARATIONS}{RELAY}my answer = relay signal::ping()"
        ));
        let signal = permission_family(&hir);
        let result = solve_receiving_residual_experiment(hir, answer).unwrap();
        assert!(
            result
                .outcomes()
                .any(|outcome| outcome == ReceivingResidualOutcome::Suppress)
        );
        assert!(!result.result_families().unwrap().contains(&signal));
    }

    #[test]
    fn same_spelling_write_operation_remains_in_actual_native_result() {
        let (hir, answer) = lower(&format!(
            "{DECLARATIONS}{RELAY}my answer = relay write::ping()"
        ));
        let signal = permission_family(&hir);
        let write = source(&hir, &answer)
            .unwrap()
            .expressions()
            .iter()
            .find_map(|expression| match &expression.form {
                Form::Operation {
                    resolution: SourceOperationResolution::Resolved(operation),
                } => Some(operation.id.family.clone()),
                _ => None,
            })
            .unwrap();
        assert_ne!(signal, write);
        let result = solve_receiving_residual_experiment(hir, answer).unwrap();
        assert!(
            result
                .outcomes()
                .any(|outcome| outcome == ReceivingResidualOutcome::Forward)
        );
        let actual = result.result_families().unwrap();
        assert!(actual.contains(&write));
        assert!(!actual.contains(&signal));
    }

    #[test]
    fn grouped_scrutinee_uses_its_original_parent_edge() {
        let relay = RELAY.replace("catch thunk", "catch (thunk)");
        let (hir, answer) = lower(&format!(
            "{DECLARATIONS}{relay}my answer = relay signal::ping()"
        ));
        let signal = permission_family(&hir);
        let result = solve_receiving_residual_experiment(hir, answer).unwrap();
        assert!(
            result
                .outcomes()
                .any(|outcome| outcome == ReceivingResidualOutcome::Suppress)
        );
        assert!(!result.result_families().unwrap().contains(&signal));
    }

    #[test]
    fn private_envelope_controls_preserve_ordinary_candidate_admission() {
        let controls = [
            format!(
                "{DECLARATIONS}{RELAY}my answer = relay signal::ping()\nmy another = relay signal::ping()"
            ),
            format!("{DECLARATIONS}{RELAY}my alias = relay\nmy answer = alias signal::ping()"),
            format!(
                "{DECLARATIONS}my relay(thunk: [signal] int) = {{ my ignored = write::ping(); catch thunk {{ signal::ping(), _ -> 1, v -> v }} }}\nmy answer = relay signal::ping()"
            ),
            format!(
                "{DECLARATIONS}my relay(thunk: [signal] int) = catch thunk {{ signal::ping(), k -> k 0, v -> v }}\nmy answer = relay signal::ping()"
            ),
            format!(
                "{DECLARATIONS}my relay(thunk: [signal] int) = catch thunk {{ signal::ping(), _ -> write::ping(), v -> v }}\nmy answer = relay signal::ping()"
            ),
        ];
        for text in controls {
            let (hir, answer) = lower(&text);
            assert!(
                matches!(
                    solve_receiving_residual_experiment(hir.clone(), answer),
                    Err(shadow_apply::CandidateError::Unsupported)
                ),
                "{text}"
            );
            assert!(
                shadow_apply::CandidateInference::solve(hir).is_ok(),
                "{text}"
            );
        }
    }
}
