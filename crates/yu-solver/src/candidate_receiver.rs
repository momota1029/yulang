//! Bounded, private A0–A7 source-use experiment. No generic scheme is produced.
use crate::*;
use yu_hir::shadow::{
    LocalSource, LocalSourceCatchPattern as Pattern,
    LocalSourceCatchPayloadPattern as PayloadPattern, LocalSourceCatchValuePattern as ValuePattern,
    LocalSourceForm as Form, LocalSourceIndex, LocalSourceResolution as Resolution,
    SourceAnnotationValue as AnnotationValue, SourceOperationDeclaration,
    SourceOperationResolution, SourceNodeKey,
};

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
    publication_observation: Option<Vec<ResidualPublicationObservation>>,
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
    endpoint: EffectEndpointKey,
    bound: candidate_effect::BoundKey,
    slot: candidate_context::PhysicalBoundSlot,
    already_present: bool,
    emission_frontier: usize,
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
        endpoint: EffectEndpointKey,
        upper: EffectEndpointKey,
        occurrence: ConstraintOccurrenceId,
        cause: CauseId,
        source_origin_index: usize,
        source_relation: candidate_context::RelationId,
        source_drain: candidate_context::SourceDrainReceipt,
        native_bound: NativeResidualBoundEvidence,
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
        self.publication_observation.as_deref()
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
        Ok(ProviderEntryCertificate {
            internal,
            catch_fact,
            endpoint,
            operation_view,
            entry_path: entry_path.clone(),
            catch_path: catch_path.clone(),
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
struct Assembly {
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
        let mut outcomes = Vec::new();
        outcomes.try_reserve(plan.decisions.len()).map_err(|_| native_unavailable())?;
        for decision in &plan.decisions {
            let _validated_suppression = &decision.suppression;
            if decision.outcome == ReceivingResidualOutcome::Forward {
                self.session.constrain_live_effect(
                    decision.endpoint,
                    pending.upper,
                    &pending.fact.id,
                    &pending.fact.cause,
                )?;
            }
            outcomes.push((decision.endpoint, decision.outcome));
        }
        self.outcomes = outcomes;
        #[cfg(feature = "shadow-apply-candidate")]
        {
            self.publication_observation = publication_plan.as_ref()
                .and_then(|publication| self.capture_native_publication(&pending, &plan, publication));
        }
        Ok(())
    }

    #[cfg(feature = "shadow-apply-candidate")]
    fn capture_native_publication(
        &self,
        pending: &PendingResidualFold,
        plan: &CompleteResidualPlan,
        publication_plan: &PreparedNativePublicationPlan,
    ) -> Option<Vec<ResidualPublicationObservation>> {
        let graph = self.session.candidate_graph.as_ref()?;
        let context = &graph.intrusion.effect_algebra.context;
        let mut observations = Vec::new();
        observations.try_reserve(publication_plan.decisions.len()).ok()?;
        let row = self.session.effect_bounds.get(self.result_row as usize)?;
        if row.direct_lower_rows.as_slice().get(..publication_plan.initial_lower_rows.len())?
                != publication_plan.initial_lower_rows.as_slice()
            || row.exact_non_variable_lowers.as_slice().get(..publication_plan.initial_lower_atoms.len())?
                != publication_plan.initial_lower_atoms.as_slice()
        {
            return None;
        }
        let expected_new_rows = publication_plan.decisions.iter().filter(|publication| {
            !publication.already_present
                && publication.slot.lane == candidate_context::BoundLane::EffectLowerRow
        }).count();
        let expected_new_atoms = publication_plan.decisions.iter().filter(|publication| {
            !publication.already_present
                && publication.slot.lane == candidate_context::BoundLane::EffectLowerAtom
        }).count();
        if row.direct_lower_rows.len() != publication_plan.initial_lower_rows.len().checked_add(expected_new_rows)?
            || row.exact_non_variable_lowers.len()
                != publication_plan.initial_lower_atoms.len().checked_add(expected_new_atoms)?
        {
            return None;
        }
        let mut row_cursor = publication_plan.initial_lower_rows.len();
        let mut atom_cursor = publication_plan.initial_lower_atoms.len();
        let mut publication_cursor = publication_plan.decisions.iter();
        for decision in plan.decisions.iter()
            .filter(|decision| decision.outcome == ReceivingResidualOutcome::Forward)
        {
            let publication = publication_cursor.next()?;
            if publication.endpoint != decision.endpoint { return None; }
            if !publication.already_present {
                match publication.slot.lane {
                    candidate_context::BoundLane::EffectLowerRow => {
                        if publication.slot.index != row_cursor
                            || row.direct_lower_rows.get(row_cursor).copied()
                                != Some(match decision.endpoint {
                                    EffectEndpointKey::EffectRow(lower) => lower,
                                    _ => return None,
                                })
                        { return None; }
                        row_cursor = row_cursor.checked_add(1)?;
                    }
                    candidate_context::BoundLane::EffectLowerAtom => {
                        if publication.slot.index != atom_cursor
                            || row.exact_non_variable_lowers.get(atom_cursor).copied()
                                != Some(decision.endpoint)
                        { return None; }
                        atom_cursor = atom_cursor.checked_add(1)?;
                    }
                    _ => return None,
                }
            }
            let source = context.checked_source_drain(
                &pending.fact.id,
                &pending.fact.cause,
                LiveConstraintTask::Effect(decision.endpoint, pending.upper),
            )?;
            let exact_physical_slot = match publication.slot.lane {
                candidate_context::BoundLane::EffectLowerRow => {
                    self.session.effect_bounds.get(match publication.slot.owner {
                        candidate_scheme::RowKey::Effect(row) => row as usize,
                        _ => return None,
                    })?.direct_lower_rows.get(publication.slot.index).copied()
                        == Some(match decision.endpoint {
                            EffectEndpointKey::EffectRow(row) => row,
                            _ => return None,
                        })
                }
                candidate_context::BoundLane::EffectLowerAtom => {
                    self.session.effect_bounds.get(match publication.slot.owner {
                        candidate_scheme::RowKey::Effect(row) => row as usize,
                        _ => return None,
                    })?.exact_non_variable_lowers.get(publication.slot.index).copied()
                        == Some(decision.endpoint)
                }
                _ => return None,
            };
            let physical_occurrences = match publication.slot.lane {
                candidate_context::BoundLane::EffectLowerRow => {
                    let row = match publication.slot.owner {
                        candidate_scheme::RowKey::Effect(row) => self.session.effect_bounds.get(row as usize)?,
                        _ => return None,
                    };
                    match decision.endpoint {
                        EffectEndpointKey::EffectRow(lower) => row.direct_lower_rows.iter()
                            .filter(|candidate| **candidate == lower).count(),
                        _ => return None,
                    }
                }
                candidate_context::BoundLane::EffectLowerAtom => {
                    let row = match publication.slot.owner {
                        candidate_scheme::RowKey::Effect(row) => self.session.effect_bounds.get(row as usize)?,
                        _ => return None,
                    };
                    row.exact_non_variable_lowers.iter()
                        .filter(|candidate| **candidate == decision.endpoint).count()
                }
                _ => return None,
            };
            if !exact_physical_slot
                || physical_occurrences != 1
                || match publication.slot.owner {
                    candidate_scheme::RowKey::Effect(row) => row != self.result_row,
                    _ => true,
                }
            {
                return None;
            }
            let mut slot_emissions = context.observed_bound_emissions_for_slot(publication.slot);
            let native_bound = if publication.already_present {
                let mut count = 0usize;
                for (_, emission) in &mut slot_emissions {
                    count = count.checked_add(1)?;
                    if emission.bound != publication.bound
                        || emission.physical != publication.slot
                        || emission.readback.bound != publication.bound
                        || emission.readback.slot != publication.slot
                        || emission.readback.phase
                            != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
                    { return None; }
                    let (_, admission) = context.observed_bound_admissions()
                        .find(|(index, _)| *index == emission.admission.0)?;
                    let relation = admission.relation?;
                    if admission.bound != publication.bound
                        || context.relation_pair(relation)
                            != Some(candidate_context::bound_pair(publication.bound))
                    { return None; }
                }
                if count != publication.prior_slot_emissions {
                    return None;
                }
                NativeResidualBoundEvidence::AlreadyPresent {
                    slot: publication.slot,
                    prior_emission_count: publication.prior_slot_emissions,
                }
            } else {
                if publication.prior_slot_emissions != 0 {
                    return None;
                }
                let (emission_id, emission) = slot_emissions.next()?;
                if slot_emissions.next().is_some() {
                    return None;
                }
                if emission_id.0 < publication.emission_frontier
                    || emission.bound != publication.bound
                    || emission.physical != publication.slot
                    || emission.readback.bound != publication.bound
                    || emission.readback.slot != publication.slot
                    || emission.readback.phase
                        != candidate_context::PhysicalReadbackPhase::ConstructorAfterAppend
                {
                    return None;
                }
                let mut admissions = context.observed_bound_admissions()
                    .filter(|(index, _)| *index == emission.admission.0);
                let (_, admission) = admissions.next()?;
                if admissions.next().is_some() || admission.bound != publication.bound {
                    return None;
                }
                let relation = admission.relation?;
                if admission.bound != publication.bound
                    || context.relation_pair(relation)
                        != Some(candidate_context::bound_pair(publication.bound))
                    || context.require_relation_ancestry(relation, source.relation).is_err()
                {
                    return None;
                }
                NativeResidualBoundEvidence::NewlyEmitted {
                    slot: publication.slot,
                    emission: emission_id,
                    admission: emission.admission,
                    relation,
                    readback: emission.readback,
                }
            };
            observations.push(ResidualPublicationObservation {
                endpoint: decision.endpoint,
                upper: pending.upper,
                occurrence: pending.fact.id.clone(),
                cause: pending.fact.cause.clone(),
                source_origin_index: source.origin_index,
                source_relation: source.relation,
                source_drain: source.receipt.clone(),
                native_bound,
            });
        }
        Some(observations)
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
        let row = self.session.effect_bounds.get(pending.result_row as usize)?;
        let mut initial_lower_rows = Vec::new();
        initial_lower_rows.try_reserve_exact(row.direct_lower_rows.len()).ok()?;
        initial_lower_rows.extend_from_slice(&row.direct_lower_rows);
        let mut initial_lower_atoms = Vec::new();
        initial_lower_atoms.try_reserve_exact(row.exact_non_variable_lowers.len()).ok()?;
        initial_lower_atoms.extend_from_slice(&row.exact_non_variable_lowers);
        let mut decisions = Vec::new();
        decisions.try_reserve(plan.decisions.len()).ok()?;
        let mut planned_row_appends = 0usize;
        let mut planned_atom_appends = 0usize;
        for decision in &plan.decisions {
            if decision.outcome != ReceivingResidualOutcome::Forward { continue; }
            let publication = self.residual_publication_plan(
                decision.endpoint, pending, planned_row_appends, planned_atom_appends,
            )?;
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
        Some(PreparedNativePublicationPlan { decisions, initial_lower_rows, initial_lower_atoms })
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
            endpoint,
            bound,
            slot,
            already_present: occurrences == 1,
            emission_frontier: context.observed_bound_emission_count(),
            prior_slot_emissions,
        })
    }
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
