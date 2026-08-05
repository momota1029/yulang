use super::*;

use std::hash::{Hash, Hasher};

use crate::constraints::canonical_projection_key::{self, Key as CanonicalProjectionKey};
#[cfg(any(test, debug_assertions))]
use crate::constraints::replay_factored::ReplayFactoredOracleMismatch;
#[cfg(test)]
use crate::constraints::replay_factored::ReplayFactoredShadowStatus;
use crate::constraints::replay_factored::{
    FirstQualifiedParentSource, FirstReplayParentWitness, ReplayFactoredResult,
    ReplayFactoredShadowFailure, ReplayOccurrenceKey, ReplayParentDraft, ReplayParentDraftId,
    ReplayResultSummaryDelta,
};
use rustc_hash::FxHasher;
use smallvec::SmallVec;

#[cfg(test)]
std::thread_local! {
    static RCPF_C3B_REPLAY_PARENT_ADMISSION_PROBES: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    static RCPF_D2B_FAIL_NEXT_CLAUSE_PROJECTION: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    static RCPF_D2C_CLAUSE_LINK_REGISTRATION_PROBES: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    static RCPF_D2C_EVENT_ORACLE_PROBES: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    static RCPF_D2C_FAIL_DEFERRED_EVALUATION_AT: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
    static RCPF_D2C_PHASE_A_OWNER_INTENT_PROBES: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    static RCPF_D4_FAIL_NEXT_PRE_CONSUMER_QUERY: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
    static RCPF_E2C_FAIL_NEXT_A1_READ: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
fn rcpf_d2c_should_fail_deferred_evaluation() -> bool {
    RCPF_D2C_FAIL_DEFERRED_EVALUATION_AT.with(|fail_at| {
        let Some(remaining) = fail_at.get() else {
            return false;
        };
        if remaining == 1 {
            fail_at.set(None);
            mark_next_replay_soak_failure_as_intentional();
            true
        } else {
            fail_at.set(Some(remaining - 1));
            false
        }
    })
}

/// Snapshot of canonical replay work. Applying a replay constraint can mutate
/// the same bounds table, so replay construction must not keep borrowed bound
/// rows. Semantic queue admission remains prefiltered, while duplicate/trivial
/// pairings retain small provenance-only actions so their exact parents are not lost.
type BoundReplayActions = SmallVec<[BoundReplayAction; 4]>;
type ReplayClaimParents = SmallVec<[SideTaggedReplayClaim; 2]>;

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundReplayAction {
    constraint: SubtypeConstraintKey,
    derivation: BinaryReplayDerivation,
    // Legacy admission remains authoritative until the RCPF cutover.
    claim_parents: ReplayClaimParents,
    lower_parents: ReplayParentDraftId,
    upper_parents: ReplayParentDraftId,
    canonicalization_disposition: Option<ConstraintCanonicalizationDisposition>,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct BoundReplayPlan {
    parent_drafts: Vec<ReplayParentDraft>,
    parent_drafts_by_fingerprint: FxHashMap<u64, SmallVec<[ReplayParentDraftId; 1]>>,
    input_count: usize,
    generated: usize,
    var_var: usize,
    prefiltered: usize,
    prefilter_duplicate: ReplayDuplicateProfile,
    stats: BoundReplayApplyStats,
    actions: BoundReplayActions,
    evidence_actions: BoundReplayActions,
    duplicate_actions: BoundReplayActions,
    trivial_actions: BoundReplayActions,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct BoundReplayApplyStats {
    accepted: usize,
    duplicate: usize,
    trivial: usize,
}

#[derive(Debug, Clone, Copy)]
struct FactoredReplayParentDrafts<'plan> {
    parent_drafts: &'plan [ReplayParentDraft],
    lower: ReplayParentDraftId,
    upper: ReplayParentDraftId,
}

struct ClaimQualifiedParentAdmissionSnapshot {
    inclusion_before: FxHashMap<BoundRecordId, bool>,
}

/// A committed Phase-A clause-link mutation whose after-view has not been evaluated yet.
///
/// Factored clause projection must reach the same event boundary before this snapshot is sealed;
/// otherwise the evaluator can observe the new flat link against the previous factored view.
struct ClauseLinkBatchAdmissionSnapshot {
    lower_record: BoundRecordId,
    was_included: bool,
}

struct ClaimParentClauseLinkPreflight {
    legacy_phase_a_links: Vec<RecordProofClauseLinkAdmission>,
    factored_failure: Option<ReplayFactoredShadowFailure>,
}

#[derive(Default)]
struct ReplayAdmissionPublicationFence {
    intents: Vec<SchemeProjectionPublicationIntent>,
}

type UpperMaterializationLineages =
    FxHashMap<(BoundRecordId, UpperReplayClaimId), UpperReplayClaimLineage>;
type ClaimParentPhaseBPlan = (
    Option<UpperMaterializationLineages>,
    Option<LowerProjectionAdapterSnapshot>,
);

#[derive(Debug, Default, PartialEq, Eq)]
struct LowerProjectionAdapterSnapshot {
    claimed_roots: Vec<UpperReplayClaimId>,
    proof_keys: Vec<CanonicalProjectionKey>,
}

#[cfg(any(test, debug_assertions))]
#[derive(Debug, Default, PartialEq, Eq)]
struct LowerProjectionLogicalSnapshot {
    support_map: FxHashSet<SchemeProjectionProofSupport>,
    canonical: LowerProjectionAdapterSnapshot,
}

#[cfg(any(test, debug_assertions))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LowerProjectionPublicationClass {
    None,
    MetadataOnly,
    OwnersChanged,
}

impl ReplayAdmissionPublicationFence {
    fn try_push(&mut self, intent: SchemeProjectionPublicationIntent) -> ReplayFactoredResult<()> {
        self.intents
            .try_reserve(1)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        self.intents.push(intent);
        Ok(())
    }
}

impl<'plan> FactoredReplayParentDrafts<'plan> {
    fn resolve(
        self,
        id: ReplayParentDraftId,
    ) -> ReplayFactoredResult<Option<&'plan ReplayParentDraft>> {
        if id == ReplayParentDraftId::EMPTY {
            return Ok(None);
        }
        let index =
            id.0.checked_sub(1)
                .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentDraft(id))?;
        self.parent_drafts
            .get(index as usize)
            .map(Some)
            .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentDraft(id))
    }
}

impl BoundReplayPlan {
    /// Intern the ordered claim projection for one side. The fingerprint is only an index hint;
    /// exact draft contents decide reuse.
    fn intern_parent_draft(
        &mut self,
        claim_parents: &ReplayClaimParents,
        parent_side: ReplayClaimParentSide,
    ) -> ReplayParentDraftId {
        let mut parent_count = 0usize;
        let mut hasher = FxHasher::default();
        for parent in claim_parents
            .iter()
            .filter(|parent| parent.parent_side == parent_side)
        {
            parent.claim.hash(&mut hasher);
            parent_count += 1;
        }
        if parent_count == 0 {
            return ReplayParentDraftId::EMPTY;
        }
        parent_count.hash(&mut hasher);
        let fingerprint = hasher.finish();

        if let Some(candidates) = self.parent_drafts_by_fingerprint.get(&fingerprint) {
            for &candidate in candidates {
                let Some(draft) = self.parent_draft(candidate) else {
                    continue;
                };
                if draft.claims.iter().copied().eq(claim_parents
                    .iter()
                    .filter(|parent| parent.parent_side == parent_side)
                    .map(|parent| parent.claim))
                {
                    return candidate;
                }
            }
        }

        let id = u32::try_from(self.parent_drafts.len())
            .ok()
            .and_then(|index| index.checked_add(1))
            .map(ReplayParentDraftId)
            .expect("a replay plan cannot contain more than u32::MAX parent drafts");
        let claims = claim_parents
            .iter()
            .filter(|parent| parent.parent_side == parent_side)
            .map(|parent| parent.claim)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        self.parent_drafts.push(ReplayParentDraft { claims });
        self.parent_drafts_by_fingerprint
            .entry(fingerprint)
            .or_default()
            .push(id);
        id
    }

    fn parent_draft(&self, id: ReplayParentDraftId) -> Option<&ReplayParentDraft> {
        let index = id.0.checked_sub(1)?;
        self.parent_drafts.get(index as usize)
    }
}

enum LowerProjectionDelta {
    ClaimsOnly,
    Bound(BoundDerivation),
    Carrier(ProjectionProofCarrier),
}

impl BoundReplayApplyStats {
    fn absorb(&mut self, other: Self) {
        self.accepted += other.accepted;
        self.duplicate += other.duplicate;
        self.trivial += other.trivial;
    }
}

impl ConstraintMachine {
    pub(in crate::constraints) fn record_bound_disposition(
        &mut self,
        direction: BoundDirection,
        owner: TypeVar,
        endpoint: BoundEndpoint,
        weights: ConstraintWeights,
        derivation: Option<BoundDerivation>,
        disposition: BoundDisposition,
        tombstone: Option<BoundRecordId>,
    ) -> BoundDispositionRecordId {
        let id = BoundDispositionRecordId(self.bound_dispositions.len() as u32);
        self.bound_dispositions.push(BoundDispositionRecord {
            direction,
            owner,
            endpoint,
            weights,
            derivation,
            disposition,
        });
        #[cfg(test)]
        proof::record_bound_disposition_shadow(
            id,
            tombstone,
            self.bound_dispositions[id.0 as usize].clone(),
        );
        if let Some(bound) = tombstone {
            self.bounds.records[bound.0 as usize].disposition = Some(id);
        }
        self.timing
            .record_bound_disposition(disposition, tombstone.is_some());
        self.bump_provenance_epoch();
        id
    }

    pub(in crate::constraints) fn record_pruned_bound_dispositions(
        &mut self,
        removed: Vec<BoundRecordId>,
        survivor: BoundRecordId,
    ) {
        for removed in removed {
            let record = self.bounds.records[removed.0 as usize].clone();
            self.record_bound_disposition(
                record.direction,
                record.owner,
                record.endpoint,
                record.weights,
                None,
                BoundDisposition::SubsumedBy(survivor),
                Some(removed),
            );
        }
    }

    #[cfg(test)]
    pub(crate) fn debug_nominal_replay_witnesses(
        &self,
        source: &[String],
        target: &[String],
    ) -> Vec<DebugReplayWitness> {
        let mut witnesses = Vec::new();
        for (index, record) in self.constraint_records.iter().enumerate() {
            let (Pos::Con(record_source, _), Neg::Con(record_target, _)) = (
                self.types.pos(record.key.lower),
                self.types.neg(record.key.upper),
            ) else {
                continue;
            };
            if record_source != source || record_target != target {
                continue;
            }
            let result = ConstraintRecordId(index as u32);
            for derivation in &record.replay_derivations {
                witnesses.push(self.debug_replay_witness(result, *derivation));
            }
        }
        witnesses
    }

    #[cfg(test)]
    pub(crate) fn debug_first_shared_source_replay_witness(&self) -> Option<DebugReplayWitness> {
        for (index, record) in self.constraint_records.iter().enumerate() {
            for derivation in &record.replay_derivations {
                let witness =
                    self.debug_replay_witness(ConstraintRecordId(index as u32), *derivation);
                if witness
                    .lower
                    .source_origins
                    .iter()
                    .any(|origin| witness.upper.source_origins.contains(origin))
                {
                    return Some(witness);
                }
            }
        }
        None
    }

    #[cfg(test)]
    fn debug_replay_witness(
        &self,
        result: ConstraintRecordId,
        derivation: BinaryReplayDerivation,
    ) -> DebugReplayWitness {
        let lower_record = self
            .bounds
            .record(derivation.lower)
            .expect("replay lower parent remains stable");
        let upper_record = self
            .bounds
            .record(derivation.upper)
            .expect("replay upper parent remains stable");
        let lower_origins = self.debug_bound_origin_ids(derivation.lower);
        let upper_origins = self.debug_bound_origin_ids(derivation.upper);
        DebugReplayWitness {
            edge: ReplayDerivationEdge { result, derivation },
            lower: DebugReplayParentTrace {
                bound: derivation.lower,
                owner: lower_record.owner(),
                endpoint: lower_record.endpoint(),
                derivations: lower_record.derivations().to_vec(),
                source_origins: self.debug_source_origin_ids(&lower_origins),
                origins: lower_origins,
            },
            upper: DebugReplayParentTrace {
                bound: derivation.upper,
                owner: upper_record.owner(),
                endpoint: upper_record.endpoint(),
                derivations: upper_record.derivations().to_vec(),
                source_origins: self.debug_source_origin_ids(&upper_origins),
                origins: upper_origins,
            },
        }
    }

    #[cfg(test)]
    fn debug_source_origin_ids(&self, origins: &[OriginId]) -> Vec<OriginId> {
        origins
            .iter()
            .copied()
            .filter(|origin| self.origins[origin.0 as usize].kind.is_source())
            .collect()
    }

    #[cfg(test)]
    fn debug_bound_origin_ids(&self, start: BoundRecordId) -> Vec<OriginId> {
        let mut origins = FxHashSet::default();
        let mut visited_bounds = FxHashSet::default();
        let mut visited_constraints = FxHashSet::default();
        let mut visited_lower_filters = FxHashSet::default();
        self.debug_collect_bound_origins(
            start,
            &mut origins,
            &mut visited_bounds,
            &mut visited_constraints,
            &mut visited_lower_filters,
        );
        let mut origins = origins.into_iter().collect::<Vec<_>>();
        origins.sort_by_key(|origin| origin.0);
        origins
    }

    #[cfg(test)]
    fn debug_collect_bound_origins(
        &self,
        id: BoundRecordId,
        origins: &mut FxHashSet<OriginId>,
        visited_bounds: &mut FxHashSet<BoundRecordId>,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        visited_lower_filters: &mut FxHashSet<LowerFilterRecordId>,
    ) {
        if !visited_bounds.insert(id) {
            return;
        }
        let Some(record) = self.bounds.record(id) else {
            return;
        };
        for derivation in record.derivations() {
            match derivation {
                BoundDerivation::Origin(origin) => {
                    origins.insert(*origin);
                }
                BoundDerivation::Constraint(parent) => self.debug_collect_constraint_origins(
                    *parent,
                    origins,
                    visited_bounds,
                    visited_constraints,
                    visited_lower_filters,
                ),
                BoundDerivation::ReplayEvidence(replay) => {
                    self.debug_collect_bound_origins(
                        replay.lower,
                        origins,
                        visited_bounds,
                        visited_constraints,
                        visited_lower_filters,
                    );
                    self.debug_collect_bound_origins(
                        replay.upper,
                        origins,
                        visited_bounds,
                        visited_constraints,
                        visited_lower_filters,
                    );
                }
                BoundDerivation::Row(row) => self.debug_collect_row_origins(
                    *row,
                    origins,
                    visited_bounds,
                    visited_constraints,
                    visited_lower_filters,
                ),
                BoundDerivation::SchemeInstantiation(_) | BoundDerivation::IncompleteReplay => {}
            }
        }
    }

    #[cfg(test)]
    fn debug_collect_constraint_origins(
        &self,
        id: ConstraintRecordId,
        origins: &mut FxHashSet<OriginId>,
        visited_bounds: &mut FxHashSet<BoundRecordId>,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        visited_lower_filters: &mut FxHashSet<LowerFilterRecordId>,
    ) {
        if !visited_constraints.insert(id) {
            return;
        }
        let record = &self.constraint_records[id.0 as usize];
        origins.extend(record.root_origins.iter().copied());
        for structural in &record.structural_derivations {
            self.debug_collect_constraint_origins(
                structural.parent,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            );
        }
        for row in &record.row_derivations {
            self.debug_collect_row_origins(
                *row,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            );
        }
        for replay in &record.replay_derivations {
            self.debug_collect_bound_origins(
                replay.lower,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            );
            self.debug_collect_bound_origins(
                replay.upper,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            );
        }
    }

    #[cfg(test)]
    fn debug_collect_row_origins(
        &self,
        id: RowDerivationId,
        origins: &mut FxHashSet<OriginId>,
        visited_bounds: &mut FxHashSet<BoundRecordId>,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        visited_lower_filters: &mut FxHashSet<LowerFilterRecordId>,
    ) {
        let Some(derivation) = self.row_derivations.get(id.0 as usize) else {
            return;
        };
        for parent in &derivation.parents {
            self.debug_collect_row_parent_origins(
                *parent,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            );
        }
    }

    #[cfg(test)]
    fn debug_collect_row_parent_origins(
        &self,
        parent: RowDerivationParent,
        origins: &mut FxHashSet<OriginId>,
        visited_bounds: &mut FxHashSet<BoundRecordId>,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        visited_lower_filters: &mut FxHashSet<LowerFilterRecordId>,
    ) {
        match parent {
            RowDerivationParent::Constraint(parent) => self.debug_collect_constraint_origins(
                parent,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            ),
            RowDerivationParent::Bound(parent) => self.debug_collect_bound_origins(
                parent,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            ),
            RowDerivationParent::SubtractFact(parent) => {
                if let Some(record) = self.subtracts.record(parent) {
                    for derivation in record.derivations() {
                        match *derivation {
                            SubtractFactDerivation::Declaration(origin)
                            | SubtractFactDerivation::Import(origin)
                            | SubtractFactDerivation::Internal(origin) => {
                                origins.insert(origin);
                            }
                        }
                    }
                }
            }
            RowDerivationParent::RowDerivation(parent) => self.debug_collect_row_origins(
                parent,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            ),
            RowDerivationParent::LowerFilter(parent) => self.debug_collect_lower_filter_origins(
                parent,
                origins,
                visited_bounds,
                visited_constraints,
                visited_lower_filters,
            ),
            RowDerivationParent::Origin(origin) => {
                origins.insert(origin);
            }
        }
    }

    #[cfg(test)]
    fn debug_collect_lower_filter_origins(
        &self,
        id: LowerFilterRecordId,
        origins: &mut FxHashSet<OriginId>,
        visited_bounds: &mut FxHashSet<BoundRecordId>,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        visited_lower_filters: &mut FxHashSet<LowerFilterRecordId>,
    ) {
        if !visited_lower_filters.insert(id) {
            return;
        }
        let Some(record) = self.lower_filter_records.get(id.0 as usize) else {
            return;
        };
        for derivation in &record.derivations {
            for parent in &derivation.parents {
                self.debug_collect_row_parent_origins(
                    *parent,
                    origins,
                    visited_bounds,
                    visited_constraints,
                    visited_lower_filters,
                );
            }
        }
    }

    pub(in crate::constraints) fn add_lower_bound(
        &mut self,
        target: TypeVar,
        pos: PosId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) {
        let producer = match &derivation {
            BoundDerivation::Constraint(record) => Some(*record),
            BoundDerivation::Origin(_)
            | BoundDerivation::ReplayEvidence(_)
            | BoundDerivation::Row(_)
            | BoundDerivation::SchemeInstantiation(_)
            | BoundDerivation::IncompleteReplay => None,
        };
        let pos = self.extrude_pos(pos, self.level_of(target));
        let weights = self.check_and_erase_lower_left_filter(pos, weights, &derivation);
        if let Some(survivor) = self.lower_var_alias_replay_cycle_subsumed(target, pos, &weights) {
            self.record_bound_disposition(
                BoundDirection::Lower,
                target,
                BoundEndpoint::Lower(pos),
                weights,
                Some(derivation),
                BoundDisposition::SubsumedBy(survivor),
                None,
            );
            return;
        }
        let premise_inclusion_before = producer
            .map(|producer| self.projection_inclusion_snapshot(ProofPremise::Constraint(producer)));
        let insertion = self
            .bounds
            .add_lower(target, pos, weights.clone(), derivation.clone());
        if let Some(before) = premise_inclusion_before {
            self.publish_projection_inclusion_snapshot(before);
        }
        self.record_bound_provenance(insertion, BoundDirection::Lower, false);
        self.record_bound_disposition(
            BoundDirection::Lower,
            target,
            BoundEndpoint::Lower(pos),
            weights.clone(),
            Some(derivation.clone()),
            if insertion.semantic_changed {
                BoundDisposition::Inserted(insertion.id)
            } else {
                BoundDisposition::EquivalentTo(insertion.id)
            },
            None,
        );
        if insertion.provenance_changed {
            self.register_lower_projection_derivation(insertion.id, producer, derivation);
        }
        if !insertion.semantic_changed {
            return;
        }
        self.record_effective_bounds_mutation(target);
        let frontier_shadow = self.observe_lower_replay_frontier_shadow(target, pos, &weights);
        self.constrain_lower_bound_by_registered_filters(target, insertion.id, pos, &weights);
        self.record_pos_bound_var_neighbors(target, pos);
        self.events.push(ConstraintEvent::LowerBoundAdded {
            record: insertion.id,
            producer,
            var: target,
            bound: pos,
            weights: weights.clone(),
        });
        trace_var_bounds("after lower", target, self.bounds.of(target), &self.types);

        let incremental_routes =
            self.unweighted_row_reduction_routes_for_new_lower(target, insertion.id, pos, &weights);
        let mut replay = self.lower_bound_replay_actions(
            target,
            insertion.id,
            pos,
            &weights,
            &incremental_routes,
        );
        let mut planned_incremental_actions = FxHashSet::default();
        for route in &incremental_routes {
            let generic_replay_covers_route =
                self.bounds
                    .record(route.upper_record)
                    .is_some_and(|record| {
                        record.endpoint() == BoundEndpoint::Upper(route.upper)
                            && self.upper_record_requires_generic_replay(route.upper_record)
                    });
            let derivation = BinaryReplayDerivation {
                pivot: target,
                lower: insertion.id,
                upper: route.upper_record,
                rule: ReplayRule::LowerBoundAdded,
            };
            if generic_replay_covers_route
                || !planned_incremental_actions.insert((route.upper, derivation))
            {
                continue;
            }
            replay.input_count += 1;
            replay.generated += 1;
            if self.is_var_var_replay(pos, route.upper) {
                replay.var_var += 1;
            }
            let mut claim_parents = self.lower_record_replay_claim_parents(insertion.id);
            if let Some(claim) = route.claim {
                claim_parents.push(SideTaggedReplayClaim {
                    claim,
                    parent_side: ReplayClaimParentSide::Upper,
                });
            }
            self.push_replay_constraint_or_prefilter(
                pos,
                weights.clone(),
                route.upper,
                derivation,
                claim_parents,
                &mut replay,
            );
        }
        self.apply_prefiltered_replay_provenance_with_parent_drafts(
            replay.duplicate_actions,
            replay.trivial_actions,
            &replay.parent_drafts,
        );
        let apply = self
            .apply_bound_replay_actions_with_parent_drafts(replay.actions, &replay.parent_drafts);
        replay.stats.absorb(apply);
        let evidence_count = replay.evidence_actions.len();
        self.apply_bound_replay_evidence_actions(replay.evidence_actions);
        for route in incremental_routes {
            self.merge_unweighted_row_route_provenance(
                pos,
                weights.clone(),
                route.upper,
                route.provenance,
                route.claim,
            );
        }
        self.record_lower_replay_frontier_shadow(frontier_shadow, replay.stats.accepted);
        self.timing.record_lower_bound_added(
            replay.input_count,
            replay.generated,
            replay.var_var,
            replay.stats.accepted,
            evidence_count,
            replay.stats.duplicate,
            replay.stats.trivial,
            replay.prefiltered,
            replay.prefilter_duplicate,
        );
    }

    pub(in crate::constraints) fn merge_scheme_instantiations_into_lower_bound(
        &mut self,
        target: TypeVar,
        lower: PosId,
        derivations: Vec<SchemeInstantiationDerivation>,
    ) {
        let key = BoundSemanticKey::Lower {
            owner: target,
            endpoint: lower,
            weights: ConstraintWeights::empty(),
        };
        let Some(id) = self.bounds.canonical.get(&key).copied() else {
            return;
        };
        let considered = derivations.len();
        let mut inserted_derivations = Vec::new();
        let incoming = {
            let record = &mut self.bounds.records[id.0 as usize];
            for derivation in derivations {
                let derivation = BoundDerivation::SchemeInstantiation(derivation);
                if !record.derivations.contains(&derivation) {
                    record.derivations.push(derivation.clone());
                    #[cfg(test)]
                    proof::record_bound_shadow(id, derivation.clone());
                    inserted_derivations.push(derivation);
                }
            }
            record
                .derivations
                .iter()
                .filter(|edge| matches!(edge, BoundDerivation::SchemeInstantiation(_)))
                .count()
        };
        let inserted = inserted_derivations.len();
        let coverage = &mut self.timing.scheme_instantiations;
        coverage.edges_considered += considered;
        coverage.edges_inserted += inserted;
        coverage.edges_deduplicated += considered.saturating_sub(inserted);
        coverage.max_incoming_edges_per_record =
            coverage.max_incoming_edges_per_record.max(incoming);
        if inserted != 0 {
            self.bump_provenance_epoch();
        }
        for derivation in inserted_derivations {
            self.register_lower_projection_derivation(id, None, derivation);
        }
    }

    pub(in crate::constraints) fn add_upper_bound(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) {
        let producer = match &derivation {
            BoundDerivation::Constraint(record) => Some(*record),
            BoundDerivation::Origin(_)
            | BoundDerivation::ReplayEvidence(_)
            | BoundDerivation::Row(_)
            | BoundDerivation::SchemeInstantiation(_)
            | BoundDerivation::IncompleteReplay => None,
        };
        let neg = self.extrude_neg(neg, self.level_of(source));
        let weights = self.check_and_erase_upper_left_filter(source, weights, &derivation);
        if let Some(survivor) = self.upper_var_alias_replay_cycle_subsumed(source, neg, &weights) {
            self.record_bound_disposition(
                BoundDirection::Upper,
                source,
                BoundEndpoint::Upper(neg),
                weights,
                Some(derivation),
                BoundDisposition::SubsumedBy(survivor),
                None,
            );
            self.register_constraint_upper_replay_claims(survivor, producer);
            return;
        }
        if let Some(survivor) = self.upper_bound_subsumed_by_existing(source, neg, &weights) {
            self.record_bound_disposition(
                BoundDirection::Upper,
                source,
                BoundEndpoint::Upper(neg),
                weights,
                Some(derivation),
                BoundDisposition::SubsumedBy(survivor),
                None,
            );
            self.register_constraint_upper_replay_claims(survivor, producer);
            return;
        }
        let pruned = self.prune_upper_rows_subsumed_by(source, neg, &weights);
        let insertion = self
            .bounds
            .add_upper(source, neg, weights.clone(), derivation.clone());
        self.record_bound_provenance(insertion, BoundDirection::Upper, false);
        self.record_bound_disposition(
            BoundDirection::Upper,
            source,
            BoundEndpoint::Upper(neg),
            weights.clone(),
            Some(derivation),
            if insertion.semantic_changed {
                BoundDisposition::Inserted(insertion.id)
            } else {
                BoundDisposition::EquivalentTo(insertion.id)
            },
            None,
        );
        self.record_pruned_bound_dispositions(pruned, insertion.id);
        self.register_constraint_upper_replay_claims(insertion.id, producer);
        if !insertion.semantic_changed {
            return;
        }
        self.record_effective_bounds_mutation(source);
        let frontier_shadow = self.observe_upper_replay_frontier_shadow(source, neg, &weights);
        self.record_neg_bound_var_neighbors(source, neg);
        self.events.push(ConstraintEvent::UpperBoundAdded {
            record: insertion.id,
            producer,
            var: source,
            bound: neg,
            weights: weights.clone(),
        });
        trace_var_bounds("after upper", source, self.bounds.of(source), &self.types);

        let mut replay = self.upper_bound_replay_actions(source, insertion.id, neg, &weights);
        self.apply_prefiltered_replay_provenance_with_parent_drafts(
            replay.duplicate_actions,
            replay.trivial_actions,
            &replay.parent_drafts,
        );
        let apply = self
            .apply_bound_replay_actions_with_parent_drafts(replay.actions, &replay.parent_drafts);
        replay.stats.absorb(apply);
        let evidence_count = replay.evidence_actions.len();
        self.apply_bound_replay_evidence_actions(replay.evidence_actions);
        self.record_upper_replay_frontier_shadow(frontier_shadow, replay.stats.accepted);
        self.timing.record_upper_bound_added(
            replay.input_count,
            replay.generated,
            replay.var_var,
            replay.stats.accepted,
            evidence_count,
            replay.stats.duplicate,
            replay.stats.trivial,
            replay.prefiltered,
            replay.prefilter_duplicate,
        );
    }

    /// Publish one effective mutation of the exact projected bound vectors.
    ///
    /// This is deliberately independent of replay. Callers are the ordinary and evidence bound
    /// insertions already represented by the legacy global and per-variable epochs.
    pub(in crate::constraints) fn record_effective_bounds_mutation(&mut self, var: TypeVar) {
        if self.method_role_mutations.is_active() {
            self.method_role_mutations
                .record(DependencyKey::ConstraintBounds(var));
        }
        let epoch = self.bump_epoch();
        self.bounds.record_var_epoch(var, epoch);
    }

    pub(in crate::constraints) fn record_bound_provenance(
        &mut self,
        insertion: BoundInsertResult,
        direction: BoundDirection,
        evidence: bool,
    ) {
        if insertion.provenance_changed {
            self.bump_provenance_epoch();
        }
        self.timing.record_bound_record(
            direction,
            evidence,
            insertion.semantic_changed && !insertion.promoted,
            insertion.provenance_changed && !insertion.semantic_changed,
            insertion.promoted,
        );
    }

    pub(in crate::constraints) fn register_constraint_upper_replay_claims(
        &mut self,
        record: BoundRecordId,
        producer: Option<ConstraintRecordId>,
    ) -> Vec<UpperReplayClaimId> {
        let Some(producer) = producer else {
            return Vec::new();
        };
        #[cfg(any(test, debug_assertions))]
        self.observe_factored_upper_materialization_full(record, producer);
        let parents = self
            .bounds
            .claim_parents_by_constraint
            .get(&producer)
            .cloned()
            .unwrap_or_default();
        if let Some(lower_record) = self.lower_record_for_constraint(producer) {
            self.register_claim_parent_clause_links_after_factored_projection(
                producer,
                lower_record,
                &parents,
                None,
            );
        }
        let mut claims: Vec<UpperReplayClaimId> = Vec::new();
        for parent in parents {
            let parent_claim = parent.parent_claim();
            let coverage_root =
                self.bounds.upper_replay_claims[parent_claim.0 as usize].coverage_root;
            // The exact route carrier remains in `claim_parents_by_constraint`, while the
            // materialized upper claim is canonical per record and coverage root. Replaying the
            // second carrier would only count the same proof as a claim cycle.
            if matches!(
                parent,
                ClaimQualifiedParent::ReductionRouteConstraint { .. }
            ) && claims.iter().any(|claim| {
                self.bounds.upper_replay_claims[claim.0 as usize].coverage_root == coverage_root
            }) {
                continue;
            }
            let claim =
                self.materialize_constraint_upper_replay_claim(record, producer, parent, None);
            if !claims.contains(&claim) {
                claims.push(claim);
            }
        }
        if claims.is_empty() {
            let registration = self.bounds.original_upper_replay_claim(
                record,
                producer,
                UpperReplayClaimKind::Direct,
            );
            self.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
            claims.push(registration.claim);
        }
        #[cfg(any(test, debug_assertions))]
        self.observe_factored_replay_event_boundary(producer);
        claims
    }

    fn register_constraint_upper_replay_claims_delta(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
        replay_clause_work_precommitted: bool,
        mut publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) -> Vec<UpperReplayClaimId> {
        if let Some(lower_record) = self.lower_record_for_constraint(producer) {
            if !replay_clause_work_precommitted {
                self.register_claim_parent_clause_links_after_factored_projection(
                    producer,
                    lower_record,
                    parents,
                    publication_fence.as_deref_mut(),
                );
            }
        }
        let mut claims = Vec::new();
        for parent in parents.iter().copied() {
            let coverage_root =
                self.bounds.upper_replay_claims[parent.parent_claim().0 as usize].coverage_root;
            // Materialization is canonical per (record, root), not per exact carrier. The caller
            // has already recorded every newly admitted key and qualified parent unconditionally.
            if self
                .bounds
                .derived_claim_by_record_and_root
                .contains_key(&(record, coverage_root))
            {
                continue;
            }
            let claim = self.materialize_constraint_upper_replay_claim(
                record,
                producer,
                parent,
                publication_fence.as_deref_mut(),
            );
            if !claims.contains(&claim) {
                claims.push(claim);
            }
        }
        claims
    }

    fn materialize_constraint_upper_replay_claim(
        &mut self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        parent: ClaimQualifiedParent,
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) -> UpperReplayClaimId {
        let parent_claim = parent.parent_claim();
        let registration = match parent {
            ClaimQualifiedParent::ReplayConstraint {
                parent_side,
                replay,
                ..
            } => self
                .bounds
                .derived_upper_replay_claim(record, parent_claim, producer, |depth| {
                    UpperReplayClaimLineage::ReplayConstraint {
                        parent_claim,
                        parent_side,
                        result: producer,
                        replay,
                        depth,
                    }
                }),
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => self
                .bounds
                .derived_upper_replay_claim(record, parent_claim, producer, |depth| {
                    UpperReplayClaimLineage::StructuralConstraint {
                        parent_claim,
                        result: producer,
                        derivation,
                        depth,
                    }
                }),
            ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => self
                .bounds
                .derived_upper_replay_claim(record, parent_claim, producer, |depth| {
                    UpperReplayClaimLineage::ReductionRouteConstraint {
                        parent_claim,
                        result: producer,
                        derivation,
                        depth,
                    }
                }),
        };
        if let Some(fence) = publication_fence {
            self.defer_scheme_projection_mutation(fence, registration.scheme_projection_mutation);
        } else {
            self.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
        }
        registration.claim
    }

    fn try_insert_upper_materialization_lineage(
        &self,
        lineages: &mut UpperMaterializationLineages,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        root: UpperReplayClaimId,
        replay_parent: Option<ClaimQualifiedParent>,
        unmaterialized_only: bool,
    ) -> ReplayFactoredResult<()> {
        let parent = match self
            .replay_result_summary
            .first_qualified_parent_source(producer, root)?
            .ok_or(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex)?
        {
            FirstQualifiedParentSource::Replay => {
                replay_parent.ok_or(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex)?
            }
            FirstQualifiedParentSource::NonReplay(parent) => parent,
        };
        let parent_claim = parent.parent_claim();
        let actual_root = self.bounds.canonical_coverage_root(parent_claim).ok_or(
            ReplayFactoredShadowFailure::UnknownReplayParentClaim(parent_claim),
        )?;
        if actual_root != root {
            return Err(
                ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot {
                    claim: parent_claim,
                    root,
                },
            );
        }
        self.try_insert_upper_materialization_lineage_from_parent(
            lineages,
            record,
            producer,
            parent,
            unmaterialized_only,
        )
    }

    fn try_insert_upper_materialization_lineage_from_parent(
        &self,
        lineages: &mut UpperMaterializationLineages,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        parent: ClaimQualifiedParent,
        unmaterialized_only: bool,
    ) -> ReplayFactoredResult<()> {
        let parent_claim = parent.parent_claim();
        let parent_record = self
            .bounds
            .upper_replay_claims
            .get(parent_claim.0 as usize)
            .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(
                parent_claim,
            ))?;
        let root = parent_record.coverage_root;
        let root_record = self
            .bounds
            .upper_replay_claims
            .get(root.0 as usize)
            .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(root))?;
        if unmaterialized_only
            && (root_record.current_record == record
                || self
                    .bounds
                    .derived_claim_by_record_and_root
                    .contains_key(&(record, root)))
        {
            return Ok(());
        }
        let key = (record, root);
        if lineages.contains_key(&key) {
            return Ok(());
        }
        let depth = parent_record.lineage.depth().saturating_add(1);
        let lineage = if root_record.current_record == record {
            UpperReplayClaimLineage::Original
        } else {
            match parent {
                ClaimQualifiedParent::ReplayConstraint {
                    parent_side,
                    replay,
                    ..
                } => UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim,
                    parent_side,
                    result: producer,
                    replay,
                    depth,
                },
                ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                    UpperReplayClaimLineage::StructuralConstraint {
                        parent_claim,
                        result: producer,
                        derivation,
                        depth,
                    }
                }
                ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => {
                    UpperReplayClaimLineage::ReductionRouteConstraint {
                        parent_claim,
                        result: producer,
                        derivation,
                        depth,
                    }
                }
            }
        };
        lineages
            .try_reserve(1)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        lineages.insert(key, lineage);
        Ok(())
    }

    fn try_upper_materialization_lineages_from_parents(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        parents: impl IntoIterator<Item = ClaimQualifiedParent>,
        unmaterialized_only: bool,
    ) -> ReplayFactoredResult<UpperMaterializationLineages> {
        let mut lineages = FxHashMap::default();
        for parent in parents {
            self.try_insert_upper_materialization_lineage_from_parent(
                &mut lineages,
                record,
                producer,
                parent,
                unmaterialized_only,
            )?;
        }
        Ok(lineages)
    }

    fn try_factored_upper_materialization(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        witnesses: impl IntoIterator<
            Item = ReplayFactoredResult<(UpperReplayClaimId, FirstReplayParentWitness)>,
        >,
        include_non_replay: bool,
        unmaterialized_only: bool,
    ) -> ReplayFactoredResult<UpperMaterializationLineages> {
        let mut roots = FxHashSet::default();
        let mut replay_parents = FxHashMap::default();
        for witness in witnesses {
            let (root, witness) = witness?;
            let occurrence = self.replay_occurrence(witness.occurrence)?;
            if occurrence.result != producer {
                return Err(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex);
            }
            let parent = ClaimQualifiedParent::ReplayConstraint {
                parent_claim: witness.parent_claim,
                parent_side: witness.parent_side,
                replay: occurrence.carrier,
            };
            let parent_root = self
                .bounds
                .upper_replay_claims
                .get(witness.parent_claim.0 as usize)
                .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(
                    witness.parent_claim,
                ))?
                .coverage_root;
            if parent_root != root {
                return Err(
                    ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot {
                        claim: witness.parent_claim,
                        root,
                    },
                );
            }
            roots
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            replay_parents
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            roots.insert(root);
            if replay_parents.insert(root, parent).is_some() {
                return Err(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex);
            }
        }
        if include_non_replay {
            for parent in self.non_replay_claim_parents_for_result(producer) {
                let claim = parent.parent_claim();
                let root = self
                    .bounds
                    .canonical_coverage_root(claim)
                    .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(claim))?;
                roots
                    .try_reserve(1)
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                roots.insert(root);
            }
        }
        let mut lineages = UpperMaterializationLineages::default();
        for root in roots {
            self.try_insert_upper_materialization_lineage(
                &mut lineages,
                record,
                producer,
                root,
                replay_parents.get(&root).copied(),
                unmaterialized_only,
            )?;
        }
        Ok(lineages)
    }

    fn try_factored_upper_materialization_full(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
    ) -> ReplayFactoredResult<UpperMaterializationLineages> {
        let witnesses = self
            .replay_result_summary
            .roots_for_result(producer)
            .map(|root| {
                self.replay_result_summary
                    .first_parent_witness(producer, root)
                    .and_then(|witness| {
                        witness
                            .copied()
                            .map(|witness| (root, witness))
                            .ok_or(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex)
                    })
            });
        self.try_factored_upper_materialization(record, producer, witnesses, true, false)
    }

    fn try_factored_upper_materialization_delta(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        delta: &ReplayResultSummaryDelta,
    ) -> ReplayFactoredResult<UpperMaterializationLineages> {
        self.try_factored_upper_materialization(
            record,
            producer,
            delta.entries.iter().copied().map(Ok),
            false,
            true,
        )
    }

    #[allow(
        dead_code,
        reason = "RCPF-D4-2 preflights the authoritative derived-read plan"
    )]
    fn try_authoritative_upper_materialization_full(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
    ) -> ReplayFactoredResult<UpperMaterializationLineages> {
        match self.replay_read_authority() {
            ReplayReadAuthority::Factored => {
                self.try_factored_upper_materialization_full(record, producer)
            }
            ReplayReadAuthority::LegacyRollback(_) => self
                .try_upper_materialization_lineages_from_parents(
                    record,
                    producer,
                    self.bounds
                        .claim_parents_by_constraint
                        .get(&producer)
                        .into_iter()
                        .flatten()
                        .copied(),
                    false,
                ),
        }
    }

    #[allow(
        dead_code,
        reason = "RCPF-D4-2 preflights the authoritative derived-read plan"
    )]
    fn try_authoritative_upper_materialization_replay_delta(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        legacy_parents: &[ClaimQualifiedParent],
        delta: &ReplayResultSummaryDelta,
    ) -> ReplayFactoredResult<UpperMaterializationLineages> {
        match self.replay_read_authority() {
            ReplayReadAuthority::Factored => {
                self.try_factored_upper_materialization_delta(record, producer, delta)
            }
            ReplayReadAuthority::LegacyRollback(_) => self
                .try_upper_materialization_lineages_from_parents(
                    record,
                    producer,
                    legacy_parents.iter().copied(),
                    true,
                ),
        }
    }

    #[cfg(any(test, debug_assertions))]
    fn observe_factored_upper_materialization_full(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
    ) {
        if !self.replay_factored_writes_enabled()
            || !self.replay_result_summary.event_oracle_enabled()
        {
            return;
        }
        let legacy = self.try_upper_materialization_lineages_from_parents(
            record,
            producer,
            self.bounds
                .claim_parents_by_constraint
                .get(&producer)
                .into_iter()
                .flatten()
                .copied(),
            false,
        );
        let factored = self.try_factored_upper_materialization_full(record, producer);
        self.observe_factored_upper_materialization(legacy, factored);
    }

    #[cfg(any(test, debug_assertions))]
    fn observe_factored_upper_materialization_delta(
        &self,
        record: BoundRecordId,
        producer: ConstraintRecordId,
        legacy_parents: &[ClaimQualifiedParent],
        delta: &ReplayResultSummaryDelta,
    ) {
        if !self.replay_factored_writes_enabled()
            || !self.replay_result_summary.event_oracle_enabled()
        {
            return;
        }
        let legacy = self.try_upper_materialization_lineages_from_parents(
            record,
            producer,
            legacy_parents.iter().copied(),
            true,
        );
        let factored = self.try_factored_upper_materialization_delta(record, producer, delta);
        self.observe_factored_upper_materialization(legacy, factored);
    }

    #[cfg(any(test, debug_assertions))]
    fn observe_factored_upper_materialization(
        &self,
        legacy: ReplayFactoredResult<UpperMaterializationLineages>,
        factored: ReplayFactoredResult<UpperMaterializationLineages>,
    ) {
        let legacy = match legacy {
            Ok(legacy) => legacy,
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Oracle,
                );
                return;
            }
        };
        let factored = match factored {
            Ok(factored) => factored,
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Oracle,
                );
                return;
            }
        };
        if legacy != factored {
            self.mark_replay_factored_failure(
                ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::DerivedReplayLineage,
                ),
                ReplayFactoredFailureOperation::Oracle,
            );
        }
    }

    fn try_lower_projection_root(
        &self,
        claim: UpperReplayClaimId,
    ) -> ReplayFactoredResult<UpperReplayClaimId> {
        self.bounds
            .canonical_coverage_root(claim)
            .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(claim))
    }

    fn try_factored_lower_projection(
        &self,
        producer: ConstraintRecordId,
        witnesses: impl IntoIterator<
            Item = ReplayFactoredResult<(UpperReplayClaimId, FirstReplayParentWitness)>,
        >,
        include_non_replay: bool,
        independent_supports: impl IntoIterator<Item = ProjectionProofCarrier>,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        let mut roots = FxHashSet::default();
        let mut replay_roots = FxHashSet::default();
        for witness in witnesses {
            let (root, witness) = witness?;
            let occurrence = self.replay_occurrence(witness.occurrence)?;
            if occurrence.result != producer {
                return Err(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex);
            }
            let actual_root = self.try_lower_projection_root(witness.parent_claim)?;
            if actual_root != root {
                return Err(
                    ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot {
                        claim: witness.parent_claim,
                        root,
                    },
                );
            }
            roots
                .try_reserve(1)
                .and_then(|_| replay_roots.try_reserve(1))
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            roots.insert(root);
            if !replay_roots.insert(root) {
                return Err(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex);
            }
        }
        if include_non_replay {
            for parent in self.non_replay_claim_parents_for_result(producer) {
                let claim = parent.parent_claim();
                let root = self.try_lower_projection_root(claim)?;
                roots
                    .try_reserve(1)
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                roots.insert(root);
            }
        }

        let mut claimed_roots = Vec::new();
        claimed_roots
            .try_reserve(roots.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for root in roots {
            match self
                .replay_result_summary
                .first_qualified_parent_source(producer, root)?
                .ok_or(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex)?
            {
                FirstQualifiedParentSource::Replay if !replay_roots.contains(&root) => {
                    return Err(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex);
                }
                FirstQualifiedParentSource::Replay => {}
                FirstQualifiedParentSource::NonReplay(parent) => {
                    let claim = parent.parent_claim();
                    let actual_root = self.try_lower_projection_root(claim)?;
                    if actual_root != root {
                        return Err(
                            ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot {
                                claim,
                                root,
                            },
                        );
                    }
                }
            }
            claimed_roots.push(root);
        }
        Self::try_lower_projection_adapter_snapshot(claimed_roots, independent_supports)
    }

    fn try_lower_projection_adapter_snapshot(
        mut claimed_roots: Vec<UpperReplayClaimId>,
        independent_supports: impl IntoIterator<Item = ProjectionProofCarrier>,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        claimed_roots.sort_by(|left, right| {
            canonical_projection_key::cmp(
                &CanonicalProjectionKey::Claimed(*left),
                &CanonicalProjectionKey::Claimed(*right),
            )
        });

        let mut proof_keys = Vec::new();
        proof_keys
            .try_reserve(claimed_roots.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        proof_keys.extend(
            claimed_roots
                .iter()
                .copied()
                .map(CanonicalProjectionKey::Claimed),
        );
        for carrier in independent_supports {
            proof_keys
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            proof_keys.push(CanonicalProjectionKey::Independent(carrier));
        }
        proof_keys.sort_by(canonical_projection_key::cmp);
        proof_keys.dedup();
        Ok(LowerProjectionAdapterSnapshot {
            claimed_roots,
            proof_keys,
        })
    }

    fn try_factored_lower_projection_full(
        &self,
        producer: ConstraintRecordId,
        independent_supports: impl IntoIterator<Item = ProjectionProofCarrier>,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        let witnesses = self
            .replay_result_summary
            .roots_for_result(producer)
            .map(|root| {
                self.replay_result_summary
                    .first_parent_witness(producer, root)
                    .and_then(|witness| {
                        witness
                            .copied()
                            .map(|witness| (root, witness))
                            .ok_or(ReplayFactoredShadowFailure::CorruptReplayResultSummaryIndex)
                    })
            });
        self.try_factored_lower_projection(producer, witnesses, true, independent_supports)
    }

    #[allow(
        dead_code,
        reason = "RCPF-D3b-1 retains the producer-local delta adapter"
    )]
    fn try_factored_lower_projection_delta(
        &self,
        producer: ConstraintRecordId,
        delta: &ReplayResultSummaryDelta,
        independent_supports: impl IntoIterator<Item = ProjectionProofCarrier>,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        self.try_factored_lower_projection(
            producer,
            delta.entries.iter().copied().map(Ok),
            false,
            independent_supports,
        )
    }

    fn try_lower_projection_from_parents(
        &self,
        parents: impl IntoIterator<Item = ClaimQualifiedParent>,
        independent_supports: impl IntoIterator<Item = ProjectionProofCarrier>,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        let mut roots = FxHashSet::default();
        for parent in parents {
            roots
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            roots.insert(self.try_lower_projection_root(parent.parent_claim())?);
        }
        Self::try_lower_projection_adapter_snapshot(
            roots.into_iter().collect(),
            independent_supports,
        )
    }

    #[allow(
        dead_code,
        reason = "RCPF-D4-2 preflights the authoritative derived-read plan"
    )]
    fn try_authoritative_lower_projection_full(
        &self,
        producer: ConstraintRecordId,
        legacy_parents: &[ClaimQualifiedParent],
        independent_supports: &[ProjectionProofCarrier],
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        match self.replay_read_authority() {
            ReplayReadAuthority::Factored => self
                .try_factored_lower_projection_full(producer, independent_supports.iter().copied()),
            ReplayReadAuthority::LegacyRollback(_) => self.try_lower_projection_from_parents(
                legacy_parents.iter().copied(),
                independent_supports.iter().copied(),
            ),
        }
    }

    #[allow(
        dead_code,
        reason = "RCPF-D4-2 preflights the authoritative derived-read plan"
    )]
    fn try_authoritative_lower_projection_replay_delta(
        &self,
        producer: ConstraintRecordId,
        legacy_parents: &[ClaimQualifiedParent],
        delta: &ReplayResultSummaryDelta,
        independent_supports: &[ProjectionProofCarrier],
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        match self.replay_read_authority() {
            ReplayReadAuthority::Factored => self.try_factored_lower_projection_delta(
                producer,
                delta,
                independent_supports.iter().copied(),
            ),
            ReplayReadAuthority::LegacyRollback(_) => self.try_lower_projection_from_parents(
                legacy_parents.iter().copied(),
                independent_supports.iter().copied(),
            ),
        }
    }

    fn try_d4_pre_consumer_query(&self) -> ReplayFactoredResult<()> {
        #[cfg(test)]
        if RCPF_D4_FAIL_NEXT_PRE_CONSUMER_QUERY.with(|fail| fail.replace(false)) {
            mark_next_replay_soak_failure_as_intentional();
            return Err(ReplayFactoredShadowFailure::AllocationFailed);
        }
        Ok(())
    }

    fn try_authoritative_claim_parent_full_plan(
        &self,
        producer: ConstraintRecordId,
        target_record: Option<BoundRecordId>,
        legacy_parents: &[ClaimQualifiedParent],
        independent_supports: &[ProjectionProofCarrier],
    ) -> ReplayFactoredResult<ClaimParentPhaseBPlan> {
        self.try_d4_pre_consumer_query()?;
        let upper = target_record
            .map(|record| self.try_authoritative_upper_materialization_full(record, producer))
            .transpose()?;
        let lower = self
            .lower_record_for_constraint(producer)
            .map(|_| {
                self.try_authoritative_lower_projection_full(
                    producer,
                    legacy_parents,
                    independent_supports,
                )
            })
            .transpose()?;
        Ok((upper, lower))
    }

    fn try_authoritative_replay_delta_plan(
        &self,
        producer: ConstraintRecordId,
        target_record: Option<BoundRecordId>,
        legacy_parents: &[ClaimQualifiedParent],
        delta: &ReplayResultSummaryDelta,
        carrier: ProjectionProofCarrier,
    ) -> ReplayFactoredResult<ClaimParentPhaseBPlan> {
        self.try_d4_pre_consumer_query()?;
        let upper = target_record
            .filter(|_| !legacy_parents.is_empty())
            .map(|record| {
                self.try_authoritative_upper_materialization_replay_delta(
                    record,
                    producer,
                    legacy_parents,
                    delta,
                )
            })
            .transpose()?;
        let lower = if let Some(lower_record) = self.lower_record_for_constraint(producer) {
            let independent_supports = self
                .projection_carrier_is_independent(lower_record, carrier)
                .then_some(carrier)
                .into_iter()
                .collect::<Vec<_>>();
            if self
                .bounds
                .projection_proofs_by_lower_record
                .contains_key(&lower_record)
            {
                Some(self.try_authoritative_lower_projection_replay_delta(
                    producer,
                    legacy_parents,
                    delta,
                    &independent_supports,
                )?)
            } else {
                let all_parents = self
                    .bounds
                    .claim_parents_by_constraint
                    .get(&producer)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                Some(self.try_authoritative_lower_projection_full(
                    producer,
                    all_parents,
                    &independent_supports,
                )?)
            }
        } else {
            None
        };
        Ok((upper, lower))
    }

    #[cfg(any(test, debug_assertions))]
    fn try_legacy_lower_projection(
        &self,
        lower_record: BoundRecordId,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        let claims = self
            .bounds
            .scheme_projection_claims_by_lower_record
            .get(&lower_record)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let proofs = self
            .bounds
            .projection_proofs_by_lower_record
            .get(&lower_record)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut snapshot = LowerProjectionAdapterSnapshot::default();
        snapshot
            .claimed_roots
            .try_reserve(claims.len())
            .and_then(|_| snapshot.proof_keys.try_reserve(proofs.len()))
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for &claim in claims {
            snapshot
                .claimed_roots
                .push(self.try_lower_projection_root(claim)?);
        }
        for proof in proofs {
            if proof.lower_record != lower_record {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::DerivedReplayLineage,
                ));
            }
            snapshot.proof_keys.push(match proof.support {
                SchemeProjectionProofSupport::Claimed(claim) => {
                    CanonicalProjectionKey::Claimed(self.try_lower_projection_root(claim)?)
                }
                SchemeProjectionProofSupport::Independent(carrier) => {
                    CanonicalProjectionKey::Independent(carrier)
                }
            });
        }
        Ok(snapshot)
    }

    #[cfg(any(test, debug_assertions))]
    #[allow(
        dead_code,
        reason = "RCPF-D3b-1 retains the producer-local delta oracle"
    )]
    fn try_legacy_lower_projection_delta(
        &self,
        lower_record: BoundRecordId,
        delta: &ReplayResultSummaryDelta,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        let mut snapshot = self.try_legacy_lower_projection(lower_record)?;
        let mut roots = FxHashSet::default();
        roots
            .try_reserve(delta.entries.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        roots.extend(delta.entries.iter().map(|(root, _)| *root));
        snapshot.claimed_roots.retain(|root| roots.contains(root));
        snapshot.proof_keys.retain(|key| match key {
            CanonicalProjectionKey::Claimed(root) => roots.contains(root),
            CanonicalProjectionKey::Independent(_) => true,
        });
        Ok(snapshot)
    }

    #[cfg(any(test, debug_assertions))]
    #[allow(dead_code, reason = "RCPF-D3b-1 retains the qualified-parent oracle")]
    fn try_legacy_qualified_lower_projection(
        &self,
        lower_record: BoundRecordId,
        producer: ConstraintRecordId,
    ) -> ReplayFactoredResult<LowerProjectionAdapterSnapshot> {
        let mut snapshot = self.try_legacy_lower_projection(lower_record)?;
        let parents = self
            .bounds
            .claim_parents_by_constraint
            .get(&producer)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut roots = FxHashSet::default();
        roots
            .try_reserve(parents.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for parent in parents {
            roots.insert(self.try_lower_projection_root(parent.parent_claim())?);
        }
        // A lower record can also carry direct claims owned outside the qualified-parent
        // relation. D3b-1 compares the D1/C1/§9 relation without disturbing raw canonical order;
        // D3b-2's logical-support map will cover the complete record-wide sequence.
        snapshot.claimed_roots.retain(|root| roots.contains(root));
        snapshot.proof_keys.retain(|key| match key {
            CanonicalProjectionKey::Claimed(root) => roots.contains(root),
            CanonicalProjectionKey::Independent(_) => true,
        });
        Ok(snapshot)
    }

    #[cfg(any(test, debug_assertions))]
    fn try_lower_projection_logical_snapshot(
        support_map: FxHashSet<SchemeProjectionProofSupport>,
    ) -> ReplayFactoredResult<LowerProjectionLogicalSnapshot> {
        let mut canonical = LowerProjectionAdapterSnapshot::default();
        canonical
            .claimed_roots
            .try_reserve(support_map.len())
            .and_then(|_| canonical.proof_keys.try_reserve(support_map.len()))
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for support in support_map.iter().copied() {
            match support {
                SchemeProjectionProofSupport::Claimed(root) => {
                    canonical.claimed_roots.push(root);
                    canonical
                        .proof_keys
                        .push(CanonicalProjectionKey::Claimed(root));
                }
                SchemeProjectionProofSupport::Independent(carrier) => canonical
                    .proof_keys
                    .push(CanonicalProjectionKey::Independent(carrier)),
            }
        }
        canonical.claimed_roots.sort_by(|left, right| {
            canonical_projection_key::cmp(
                &CanonicalProjectionKey::Claimed(*left),
                &CanonicalProjectionKey::Claimed(*right),
            )
        });
        canonical.proof_keys.sort_by(canonical_projection_key::cmp);
        Ok(LowerProjectionLogicalSnapshot {
            support_map,
            canonical,
        })
    }

    #[cfg(any(test, debug_assertions))]
    #[allow(dead_code, reason = "RCPF-D3b-2b wires the record-wide oracle")]
    fn try_factored_record_lower_projection(
        &self,
        lower_record: BoundRecordId,
    ) -> ReplayFactoredResult<LowerProjectionLogicalSnapshot> {
        let record =
            self.bounds
                .record(lower_record)
                .ok_or(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::DerivedReplayLineage,
                ))?;
        let links = self
            .bounds
            .record_proof_clause_links_by_lower_record
            .get(&lower_record)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut support_map = FxHashSet::default();
        support_map
            .try_reserve(record.derivations().len().saturating_add(links.len()))
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;

        for derivation in record.derivations() {
            let BoundDerivation::Constraint(producer) = derivation else {
                continue;
            };
            if let Some(claim) = self
                .bounds
                .root_claim_by_producer_constraint
                .get(producer)
                .copied()
            {
                support_map
                    .try_reserve(1)
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                support_map.insert(SchemeProjectionProofSupport::Claimed(
                    self.try_lower_projection_root(claim)?,
                ));
            }
            for root in self
                .try_factored_lower_projection_full(*producer, [])?
                .claimed_roots
            {
                support_map
                    .try_reserve(1)
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                support_map.insert(SchemeProjectionProofSupport::Claimed(root));
            }
        }
        for link in links {
            if let SchemeProjectionProofSupport::Independent(carrier) = link.support {
                support_map
                    .try_reserve(1)
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                support_map.insert(SchemeProjectionProofSupport::Independent(carrier));
            }
        }
        Self::try_lower_projection_logical_snapshot(support_map)
    }

    #[cfg(any(test, debug_assertions))]
    #[allow(dead_code, reason = "RCPF-D3b-2b wires the record-wide oracle")]
    fn try_legacy_record_lower_projection(
        &self,
        lower_record: BoundRecordId,
    ) -> ReplayFactoredResult<LowerProjectionLogicalSnapshot> {
        let canonical = self.try_legacy_lower_projection(lower_record)?;
        let mut support_map = FxHashSet::default();
        support_map
            .try_reserve(canonical.proof_keys.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for key in canonical.proof_keys.iter().copied() {
            support_map.insert(match key {
                CanonicalProjectionKey::Claimed(root) => {
                    SchemeProjectionProofSupport::Claimed(root)
                }
                CanonicalProjectionKey::Independent(carrier) => {
                    SchemeProjectionProofSupport::Independent(carrier)
                }
            });
        }
        Ok(LowerProjectionLogicalSnapshot {
            support_map,
            canonical,
        })
    }

    #[cfg(any(test, debug_assertions))]
    fn validate_lower_projection_reverse_index(
        &self,
        lower_record: BoundRecordId,
        roots: &[UpperReplayClaimId],
    ) -> ReplayFactoredResult<()> {
        for &root in roots {
            let has_membership = self
                .bounds
                .scheme_projection_lower_record_memberships
                .contains(&(root, lower_record));
            let count = self
                .bounds
                .scheme_projection_lower_records_by_root
                .get(&root)
                .map_or(0, |records| {
                    records
                        .iter()
                        .filter(|record| **record == lower_record)
                        .count()
                });
            if !has_membership || count != 1 {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::DerivedReplayLineage,
                ));
            }
        }
        Ok(())
    }

    #[cfg(any(test, debug_assertions))]
    fn try_compare_factored_record_lower_projection(
        &self,
        lower_record: BoundRecordId,
        pending_independent_supports: &[ProjectionProofCarrier],
    ) -> ReplayFactoredResult<LowerProjectionLogicalSnapshot> {
        let legacy = self.try_legacy_record_lower_projection(lower_record)?;
        let mut factored = self.try_factored_record_lower_projection(lower_record)?;
        if !pending_independent_supports.is_empty() {
            factored
                .support_map
                .try_reserve(pending_independent_supports.len())
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            factored.support_map.extend(
                pending_independent_supports
                    .iter()
                    .copied()
                    .map(SchemeProjectionProofSupport::Independent),
            );
            factored = Self::try_lower_projection_logical_snapshot(factored.support_map)?;
        }
        if legacy != factored {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::DerivedReplayLineage,
            ));
        }
        self.validate_lower_projection_reverse_index(
            lower_record,
            &factored.canonical.claimed_roots,
        )?;
        Ok(factored)
    }

    #[cfg(any(test, debug_assertions))]
    fn try_lower_projection_proofs_from_snapshot(
        lower_record: BoundRecordId,
        snapshot: &LowerProjectionLogicalSnapshot,
    ) -> ReplayFactoredResult<Vec<SchemeProjectionProof>> {
        let mut proofs = Vec::new();
        proofs
            .try_reserve(snapshot.canonical.proof_keys.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        proofs.extend(snapshot.canonical.proof_keys.iter().map(|key| {
            let support = match key {
                CanonicalProjectionKey::Claimed(root) => {
                    SchemeProjectionProofSupport::Claimed(*root)
                }
                CanonicalProjectionKey::Independent(carrier) => {
                    SchemeProjectionProofSupport::Independent(*carrier)
                }
            };
            SchemeProjectionProof {
                lower_record,
                support,
            }
        }));
        Ok(proofs)
    }

    #[cfg(any(test, debug_assertions))]
    fn lower_projection_publication_class(
        intent: &SchemeProjectionPublicationIntent,
    ) -> LowerProjectionPublicationClass {
        match intent {
            SchemeProjectionPublicationIntent::None => LowerProjectionPublicationClass::None,
            SchemeProjectionPublicationIntent::MetadataOnly => {
                LowerProjectionPublicationClass::MetadataOnly
            }
            SchemeProjectionPublicationIntent::OwnersChanged(_) => {
                LowerProjectionPublicationClass::OwnersChanged
            }
        }
    }

    #[cfg(any(test, debug_assertions))]
    fn try_factored_lower_projection_publication_class(
        &self,
        lower_record: BoundRecordId,
        previous_proofs: Option<&[SchemeProjectionProof]>,
        current_proofs: &[SchemeProjectionProof],
    ) -> ReplayFactoredResult<LowerProjectionPublicationClass> {
        let evaluator = SchemeProjectionEvaluator::new(self);
        let was_fail_open = evaluator.flat_fail_open(lower_record, previous_proofs);
        let is_fail_open = evaluator.flat_fail_open(lower_record, Some(current_proofs));
        if was_fail_open == is_fail_open {
            return Ok(LowerProjectionPublicationClass::MetadataOnly);
        }
        let intent = if was_fail_open {
            let is_included = SchemeProjectionEvaluator::new(self)
                .with_proof_override(lower_record, Some(current_proofs))
                .eval_record(lower_record)?;
            self.try_evaluate_record_inclusion_publication(lower_record, true, is_included, true)?
        } else {
            let was_included = SchemeProjectionEvaluator::new(self)
                .with_proof_override(lower_record, previous_proofs)
                .eval_record(lower_record)?;
            self.try_evaluate_record_inclusion_publication(lower_record, was_included, true, true)?
        };
        Ok(Self::lower_projection_publication_class(&intent))
    }

    #[cfg(any(test, debug_assertions))]
    fn try_factored_lower_projection_mutation_oracle(
        &self,
        lower_record: BoundRecordId,
        mutation: &SchemeProjectionMutation,
        pending_independent_supports: &[ProjectionProofCarrier],
    ) -> ReplayFactoredResult<()> {
        let factored = self.try_compare_factored_record_lower_projection(
            lower_record,
            pending_independent_supports,
        )?;
        let legacy_intent = self.try_evaluate_scheme_projection_mutation(mutation.clone())?;
        let legacy_class = Self::lower_projection_publication_class(&legacy_intent);
        let factored_class = match mutation {
            SchemeProjectionMutation::None => LowerProjectionPublicationClass::None,
            SchemeProjectionMutation::ProofsChanged {
                previous_proofs, ..
            } => {
                let current_proofs =
                    Self::try_lower_projection_proofs_from_snapshot(lower_record, &factored)?;
                self.try_factored_lower_projection_publication_class(
                    lower_record,
                    previous_proofs.as_deref(),
                    &current_proofs,
                )?
            }
        };
        if legacy_class != factored_class {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::DerivedReplayLineage,
            ));
        }
        Ok(())
    }

    #[cfg(any(test, debug_assertions))]
    fn observe_factored_lower_projection_result(&self, result: ReplayFactoredResult<()>) {
        if let Err(failure) = result {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Oracle,
            );
        }
    }

    #[cfg(any(test, debug_assertions))]
    fn observe_factored_lower_projection_full(
        &self,
        lower_record: BoundRecordId,
        _producer: ConstraintRecordId,
    ) {
        if !self.replay_factored_writes_enabled()
            || !self.replay_result_summary.event_oracle_enabled()
        {
            return;
        }
        self.observe_factored_lower_projection_result(
            self.try_compare_factored_record_lower_projection(lower_record, &[])
                .map(drop),
        );
    }

    #[cfg(any(test, debug_assertions))]
    fn observe_factored_lower_projection_delta(
        &self,
        lower_record: BoundRecordId,
        _producer: ConstraintRecordId,
        delta: &ReplayResultSummaryDelta,
    ) {
        if !self.replay_factored_writes_enabled()
            || !self.replay_result_summary.event_oracle_enabled()
            || delta.entries.is_empty()
        {
            return;
        }
        self.observe_factored_lower_projection_result(
            self.try_compare_factored_record_lower_projection(lower_record, &[])
                .map(drop),
        );
    }

    #[cfg(test)]
    fn register_claim_parent_clause_links(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
    ) {
        let snapshot =
            self.commit_claim_parent_clause_links_mutation(result, lower_record, parents);
        self.seal_record_proof_clause_link_batch(snapshot, None);
    }

    fn commit_claim_parent_clause_links_mutation(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
    ) -> Option<ClauseLinkBatchAdmissionSnapshot> {
        #[cfg(test)]
        RCPF_D2C_CLAUSE_LINK_REGISTRATION_PROBES.with(|probes| {
            probes.set(probes.get().saturating_add(1));
        });
        let preflight = self.preflight_claim_parent_clause_links(result, lower_record, parents);
        let snapshot = self.commit_record_proof_clause_link_batch_mutation(
            lower_record,
            preflight.legacy_phase_a_links,
        );
        if let Some(failure) = preflight.factored_failure {
            self.mark_replay_factored_failure(failure, ReplayFactoredFailureOperation::Read);
        }
        snapshot
    }

    fn preflight_claim_parent_clause_links(
        &self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
    ) -> ClaimParentClauseLinkPreflight {
        let mut pending_links = Vec::new();
        let mut batch_link_keys = FxHashSet::default();
        let mut factored_failure = None;
        for parent in parents.iter().copied() {
            let Some(root) = self.bounds.canonical_coverage_root(parent.parent_claim()) else {
                continue;
            };
            let (clause, attribution_source) = match parent {
                ClaimQualifiedParent::ReplayConstraint { replay, .. } => (
                    RecordProofClause::ReplayConjunction {
                        carrier: replay,
                        lower_premise: replay.lower,
                        upper_premise: replay.upper,
                    },
                    ClaimedAttributionSource::CanonicalReplay,
                ),
                ClaimQualifiedParent::StructuralConstraint { derivation, .. } => (
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(derivation),
                        premise: ProofPremise::Constraint(derivation.parent),
                    },
                    ClaimedAttributionSource::FlatRetained,
                ),
                ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => (
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::ReductionRoute(derivation),
                        premise: ProofPremise::RootCoverage(root),
                    },
                    ClaimedAttributionSource::FlatRetained,
                ),
            };
            let support = SchemeProjectionProofSupport::Claimed(root);
            let already_registered = if factored_failure.is_some() {
                self.bounds
                    .record_proof_clause_link_is_registered(lower_record, support, clause)
            } else {
                match self.try_authoritative_claim_parent_clause_link_is_registered(
                    result,
                    lower_record,
                    parent,
                    support,
                    clause,
                ) {
                    Ok(already_registered) => already_registered,
                    Err(failure) => {
                        factored_failure = Some(failure);
                        // The failed attempt is discarded, but Phase A remains a complete legacy
                        // oracle for the clean LegacyRollback retry.
                        self.bounds.record_proof_clause_link_is_registered(
                            lower_record,
                            support,
                            clause,
                        )
                    }
                }
            };
            if already_registered {
                continue;
            }
            let batch_link_key = (
                TypeBounds::record_proof_clause_key(lower_record, clause),
                support,
            );
            if !batch_link_keys.insert(batch_link_key) {
                continue;
            }
            pending_links.push(RecordProofClauseLinkAdmission::claimed(
                root,
                clause,
                attribution_source,
            ));
        }
        ClaimParentClauseLinkPreflight {
            legacy_phase_a_links: pending_links,
            factored_failure,
        }
    }

    fn register_claim_parent_clause_links_after_factored_projection(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        // Phase A is unconditional. Only after Phase B has made the factored occurrence/link view
        // current may the pending after-view be evaluated and published.
        let snapshot =
            self.commit_claim_parent_clause_links_mutation(result, lower_record, parents);
        self.observe_factored_replay_clause_projection(result, lower_record, parents);
        if self.replay_factored_terminal_failure().is_none() {
            self.seal_record_proof_clause_link_batch(snapshot, publication_fence);
        }
    }

    fn observe_factored_replay_clause_projection(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
    ) {
        if !self.replay_factored_writes_enabled() {
            return;
        }
        if let Err(failure) =
            self.try_project_factored_replay_clause_parents(result, lower_record, parents)
        {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Write,
            );
        }
    }

    fn try_project_factored_replay_clause_parents(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
    ) -> ReplayFactoredResult<()> {
        #[cfg(test)]
        if RCPF_D2B_FAIL_NEXT_CLAUSE_PROJECTION.with(|fail| fail.replace(false)) {
            mark_next_replay_soak_failure_as_intentional();
            return Err(ReplayFactoredShadowFailure::AllocationFailed);
        }
        self.replay_clause_projection.try_project_replay_parents(
            result,
            lower_record,
            parents,
            &self.replay_parent_sets,
            &self.replay_occurrences,
            &self.bounds,
        )
    }

    fn try_factored_replay_clause_link_is_registered(
        &self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        root: UpperReplayClaimId,
        replay: BinaryReplayDerivation,
        clause: RecordProofClause,
    ) -> ReplayFactoredResult<bool> {
        #[cfg(test)]
        if RCPF_E2C_FAIL_NEXT_A1_READ.with(|fail| fail.replace(false)) {
            mark_next_replay_soak_failure_as_intentional();
            return Err(ReplayFactoredShadowFailure::AllocationFailed);
        }
        let Some(occurrence_id) = self.replay_occurrences.occurrence_id(ReplayOccurrenceKey {
            result,
            carrier: replay,
        }) else {
            return Ok(false);
        };
        let clause_key = TypeBounds::record_proof_clause_key(lower_record, clause);
        let Some(clause_id) = self
            .bounds
            .record_proof_clause_by_key
            .get(&clause_key)
            .copied()
        else {
            return Ok(false);
        };
        self.replay_clause_projection.try_has_exact_replay_link(
            lower_record,
            occurrence_id,
            root,
            clause_id,
            &self.replay_parent_sets,
            &self.replay_occurrences,
        )
    }

    fn try_authoritative_claim_parent_clause_link_is_registered(
        &self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parent: ClaimQualifiedParent,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) -> ReplayFactoredResult<bool> {
        match (self.replay_read_authority(), parent, support) {
            (
                ReplayReadAuthority::Factored,
                ClaimQualifiedParent::ReplayConstraint { replay, .. },
                SchemeProjectionProofSupport::Claimed(root),
            ) => self.try_factored_replay_clause_link_is_registered(
                result,
                lower_record,
                root,
                replay,
                clause,
            ),
            _ => Ok(self.bounds.record_proof_clause_link_is_registered(
                lower_record,
                support,
                clause,
            )),
        }
    }

    #[cfg(any(test, debug_assertions))]
    #[allow(
        dead_code,
        reason = "debug consumers opt in explicitly; release builds remove this API"
    )]
    pub(in crate::constraints) fn enable_replay_factored_event_oracle(&mut self) {
        if !self.replay_factored_writes_enabled() {
            return;
        }
        self.replay_result_summary.enable_event_oracle();
    }

    #[cfg(any(test, debug_assertions))]
    #[allow(
        dead_code,
        reason = "debug consumers opt in explicitly; release builds remove this API"
    )]
    pub(in crate::constraints) fn enable_replay_factored_evaluator_oracle(&mut self) {
        if !self.replay_factored_writes_enabled() {
            return;
        }
        self.replay_result_summary.enable_evaluator_oracle();
    }

    #[cfg(any(test, debug_assertions))]
    fn try_compare_first_qualified_parent_sources(
        &self,
        result: ConstraintRecordId,
    ) -> ReplayFactoredResult<()> {
        let parents = self
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut legacy = FxHashMap::default();
        legacy
            .try_reserve(parents.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for &parent in parents {
            let claim = parent.parent_claim();
            let root = self
                .bounds
                .canonical_coverage_root(claim)
                .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(claim))?;
            let source = match parent {
                ClaimQualifiedParent::ReplayConstraint { .. } => FirstQualifiedParentSource::Replay,
                ClaimQualifiedParent::StructuralConstraint { .. }
                | ClaimQualifiedParent::ReductionRouteConstraint { .. } => {
                    FirstQualifiedParentSource::NonReplay(parent)
                }
            };
            legacy.entry(root).or_insert(source);
        }
        for (root, source) in legacy {
            if self
                .replay_result_summary
                .first_qualified_parent_source(result, root)?
                != Some(source)
            {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::DerivedReplayLineage,
                ));
            }
        }
        Ok(())
    }

    /// Run the expensive dual-write comparison only at a complete admission boundary. A
    /// mismatch quarantines the observer exactly like a shadow allocation failure; legacy state
    /// has already committed and never depends on this result.
    #[cfg(any(test, debug_assertions))]
    fn observe_factored_replay_event_boundary(&mut self, result: ConstraintRecordId) {
        #[cfg(test)]
        RCPF_D2C_EVENT_ORACLE_PROBES.with(|probes| {
            probes.set(probes.get().saturating_add(1));
        });
        if !self.replay_factored_writes_enabled()
            || !self.replay_result_summary.event_oracle_enabled()
        {
            return;
        }
        if let Err(failure) = self.try_compare_factored_replay_event_boundary(result) {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Oracle,
            );
        }
    }

    #[cfg(any(test, debug_assertions))]
    fn try_compare_factored_replay_event_boundary(
        &self,
        result: ConstraintRecordId,
    ) -> ReplayFactoredResult<()> {
        if !self.replay_result_summary.event_oracle_enabled() {
            return Ok(());
        }

        self.try_compare_factored_claimed_attribution_union()?;

        type ParentKey = (
            UpperReplayClaimId,
            ReplayClaimParentSide,
            BinaryReplayDerivation,
        );
        type WitnessValue = (
            UpperReplayClaimId,
            ReplayClaimParentSide,
            BinaryReplayDerivation,
        );

        let legacy_parents = self
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut legacy_exact = FxHashMap::<ParentKey, UpperReplayClaimId>::default();
        let mut legacy_carriers = FxHashSet::<BinaryReplayDerivation>::default();
        let mut legacy_witnesses = FxHashMap::<UpperReplayClaimId, WitnessValue>::default();
        legacy_exact
            .try_reserve(legacy_parents.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        legacy_carriers
            .try_reserve(legacy_parents.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        legacy_witnesses
            .try_reserve(legacy_parents.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for &parent in legacy_parents {
            let ClaimQualifiedParent::ReplayConstraint {
                parent_claim,
                parent_side,
                replay,
            } = parent
            else {
                continue;
            };
            let root = self.bounds.canonical_coverage_root(parent_claim).ok_or(
                ReplayFactoredShadowFailure::UnknownReplayParentClaim(parent_claim),
            )?;
            if legacy_exact
                .insert((root, parent_side, replay), parent_claim)
                .is_some()
            {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::ExactParentRelation,
                ));
            }
            legacy_carriers.insert(replay);
            legacy_witnesses
                .entry(root)
                .or_insert((parent_claim, parent_side, replay));
        }

        let result_occurrences = self
            .replay_occurrences
            .by_result
            .get(&result)
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        let mut factored_parent_count = 0usize;
        for &occurrence_id in result_occurrences {
            let occurrence = self.replay_occurrences.occurrence(occurrence_id)?;
            for version in [occurrence.lower_parents, occurrence.upper_parents] {
                factored_parent_count = factored_parent_count
                    .checked_add(self.replay_parent_sets.iter(version)?.len())
                    .ok_or(ReplayFactoredShadowFailure::ParentSetLengthOverflow)?;
            }
        }
        let mut factored_exact = FxHashMap::<ParentKey, UpperReplayClaimId>::default();
        let mut factored_carriers = FxHashSet::<BinaryReplayDerivation>::default();
        factored_exact
            .try_reserve(factored_parent_count)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        factored_carriers
            .try_reserve(result_occurrences.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for &occurrence_id in result_occurrences {
            let occurrence = self.replay_occurrences.occurrence(occurrence_id)?;
            if occurrence.result != result || !factored_carriers.insert(occurrence.carrier) {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::QualifiedReplayCarriers,
                ));
            }
            for (side, version) in [
                (ReplayClaimParentSide::Lower, occurrence.lower_parents),
                (ReplayClaimParentSide::Upper, occurrence.upper_parents),
            ] {
                for entry in self.replay_parent_sets.iter(version)? {
                    if factored_exact
                        .insert(
                            (entry.coverage_root, side, occurrence.carrier),
                            entry.representative_claim,
                        )
                        .is_some()
                    {
                        return Err(ReplayFactoredShadowFailure::OracleMismatch(
                            ReplayFactoredOracleMismatch::ExactParentRelation,
                        ));
                    }
                }
            }
        }
        if legacy_exact != factored_exact {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ExactParentRelation,
            ));
        }

        let indexed_carrier_count = self
            .bounds
            .qualified_carrier_index
            .get(&result)
            .map(FxHashSet::len)
            .unwrap_or(0);
        let mut indexed_legacy_carriers = FxHashSet::default();
        indexed_legacy_carriers
            .try_reserve(indexed_carrier_count)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for carrier in self
            .bounds
            .qualified_carrier_index
            .get(&result)
            .into_iter()
            .flatten()
        {
            if let QualifiedCarrier::Replay(replay) = carrier {
                indexed_legacy_carriers.insert(*replay);
            }
        }
        if legacy_carriers != indexed_legacy_carriers || legacy_carriers != factored_carriers {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::QualifiedReplayCarriers,
            ));
        }

        let mut factored_witnesses = FxHashMap::<UpperReplayClaimId, WitnessValue>::default();
        let factored_witness_count = self
            .replay_result_summary
            .first_parent_by_root
            .keys()
            .filter(|(witness_result, _)| *witness_result == result)
            .count();
        factored_witnesses
            .try_reserve(factored_witness_count)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for (&(witness_result, root), &witness) in &self.replay_result_summary.first_parent_by_root
        {
            if witness_result != result {
                continue;
            }
            let occurrence = self.replay_occurrences.occurrence(witness.occurrence)?;
            if occurrence.result != result
                || occurrence.first_admission_ordinal > witness.admission_ordinal
                || factored_witnesses
                    .insert(
                        root,
                        (
                            witness.parent_claim,
                            witness.parent_side,
                            occurrence.carrier,
                        ),
                    )
                    .is_some()
            {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::FirstReplayWitness,
                ));
            }
        }
        if legacy_witnesses != factored_witnesses {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::FirstReplayWitness,
            ));
        }
        self.try_compare_first_qualified_parent_sources(result)?;

        let mut legacy_clauses = FxHashMap::default();
        legacy_clauses
            .try_reserve(result_occurrences.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        if let Some(lower_record) = self.lower_record_for_constraint(result) {
            for &occurrence_id in result_occurrences {
                let occurrence = self.replay_occurrences.occurrence(occurrence_id)?;
                let clause = RecordProofClause::ReplayConjunction {
                    carrier: occurrence.carrier,
                    lower_premise: occurrence.carrier.lower,
                    upper_premise: occurrence.carrier.upper,
                };
                let Some(clause_id) = self
                    .bounds
                    .record_proof_clause_by_key
                    .get(&TypeBounds::record_proof_clause_key(lower_record, clause))
                    .copied()
                else {
                    continue;
                };
                let has_exact_link = legacy_exact.iter().any(|(&(root, _, replay), _)| {
                    replay == occurrence.carrier
                        && self.bounds.record_proof_clause_link_keys.contains(
                            &TypeBounds::record_proof_clause_link_key(
                                lower_record,
                                SchemeProjectionProofSupport::Claimed(root),
                                clause_id,
                            ),
                        )
                });
                if has_exact_link {
                    legacy_clauses.insert((lower_record, occurrence.carrier), clause_id);
                }
            }
        }
        let mut factored_clauses = FxHashMap::default();
        factored_clauses
            .try_reserve(
                self.replay_clause_projection
                    .clause_by_record_and_occurrence
                    .len(),
            )
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for (&(record, occurrence_id), &clause) in &self
            .replay_clause_projection
            .clause_by_record_and_occurrence
        {
            let occurrence = self.replay_occurrences.occurrence(occurrence_id)?;
            if occurrence.result == result
                && factored_clauses
                    .insert((record, occurrence.carrier), clause)
                    .is_some()
            {
                return Err(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::ClauseMapping,
                ));
            }
        }
        if legacy_clauses != factored_clauses {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ClauseMapping,
            ));
        }

        let total_legacy_parents = self
            .bounds
            .claim_parents_by_constraint
            .values()
            .try_fold(0usize, |total, parents| total.checked_add(parents.len()))
            .ok_or(ReplayFactoredShadowFailure::ParentSetLengthOverflow)?;
        let mut legacy_exact_links = FxHashSet::default();
        legacy_exact_links
            .try_reserve(total_legacy_parents)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for (&link_result, parents) in &self.bounds.claim_parents_by_constraint {
            let Some(lower_record) = self.lower_record_for_constraint(link_result) else {
                continue;
            };
            for &parent in parents {
                let ClaimQualifiedParent::ReplayConstraint {
                    parent_claim,
                    replay,
                    ..
                } = parent
                else {
                    continue;
                };
                let root = self.bounds.canonical_coverage_root(parent_claim).ok_or(
                    ReplayFactoredShadowFailure::UnknownReplayParentClaim(parent_claim),
                )?;
                let clause = RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: replay.lower,
                    upper_premise: replay.upper,
                };
                let Some(clause_id) = self
                    .bounds
                    .record_proof_clause_by_key
                    .get(&TypeBounds::record_proof_clause_key(lower_record, clause))
                    .copied()
                else {
                    continue;
                };
                if self.bounds.record_proof_clause_link_keys.contains(
                    &TypeBounds::record_proof_clause_link_key(
                        lower_record,
                        SchemeProjectionProofSupport::Claimed(root),
                        clause_id,
                    ),
                ) {
                    legacy_exact_links.insert((lower_record, root, clause_id));
                }
            }
        }
        let factored_exact_link_iter = self
            .replay_clause_projection
            .try_exact_links(&self.replay_parent_sets, &self.replay_occurrences)?;
        let mut factored_exact_links = FxHashSet::default();
        factored_exact_links
            .try_reserve(factored_exact_link_iter.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        factored_exact_links.extend(factored_exact_link_iter);
        if legacy_exact_links != factored_exact_links {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ExactClauseLinks,
            ));
        }

        let mut legacy_attributed_roots = FxHashSet::default();
        legacy_attributed_roots
            .try_reserve(legacy_exact_links.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        legacy_attributed_roots.extend(
            legacy_exact_links
                .iter()
                .map(|&(record, root, _)| (record, root)),
        );
        if legacy_attributed_roots
            != self
                .replay_clause_projection
                .replay_attributed_claim_supports
        {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::AttributedRoots,
            ));
        }

        let mut expected_dependency_edges = FxHashSet::default();
        expected_dependency_edges
            .try_reserve(factored_clauses.len().saturating_mul(2))
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for (&(record, replay), _) in &factored_clauses {
            expected_dependency_edges.insert((ProofPremise::Record(replay.lower), record));
            expected_dependency_edges.insert((ProofPremise::Record(replay.upper), record));
        }
        let mut registered_dependency_edges = FxHashSet::default();
        registered_dependency_edges
            .try_reserve(expected_dependency_edges.len())
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        for &(premise, record) in &expected_dependency_edges {
            if self
                .bounds
                .dependent_records_by_premise
                .get(&premise)
                .is_some_and(|records| records.contains(&record))
            {
                registered_dependency_edges.insert((premise, record));
            }
        }
        if expected_dependency_edges != registered_dependency_edges {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ReplayDependencyEdges,
            ));
        }

        if let Some(target_record) = self.var_var_upper_record_for_constraint(result)
            && self.bounds.record(target_record).is_some_and(|record| {
                record
                    .derivations()
                    .contains(&BoundDerivation::Constraint(result))
            })
        {
            for (&root, &(parent_claim, parent_side, replay)) in &factored_witnesses {
                let root_claim = self
                    .bounds
                    .upper_replay_claims
                    .get(root.0 as usize)
                    .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(root))?;
                if root_claim.current_record == target_record {
                    continue;
                }
                let Some(derived_claim) = self
                    .bounds
                    .derived_claim_by_record_and_root
                    .get(&(target_record, root))
                    .and_then(|claim| self.bounds.upper_replay_claims.get(claim.0 as usize))
                else {
                    return Err(ReplayFactoredShadowFailure::OracleMismatch(
                        ReplayFactoredOracleMismatch::DerivedReplayLineage,
                    ));
                };
                if derived_claim.current_record != target_record
                    || derived_claim.coverage_root != root
                {
                    return Err(ReplayFactoredShadowFailure::OracleMismatch(
                        ReplayFactoredOracleMismatch::DerivedReplayLineage,
                    ));
                }
                if let UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: actual_parent,
                    parent_side: actual_side,
                    result: actual_result,
                    replay: actual_replay,
                    ..
                } = derived_claim.lineage
                    && (actual_parent != parent_claim
                        || actual_side != parent_side
                        || actual_result != result
                        || actual_replay != replay)
                {
                    return Err(ReplayFactoredShadowFailure::OracleMismatch(
                        ReplayFactoredOracleMismatch::DerivedReplayLineage,
                    ));
                }
            }
        }
        Ok(())
    }

    /// The legacy attribution set stays all-source during RCPF-E, while the Factored consumer
    /// view is partitioned at writer boundaries. Two-way membership proves exact set equality
    /// without allocating a temporary union in this debug/test-only event oracle.
    #[cfg(any(test, debug_assertions))]
    fn try_compare_factored_claimed_attribution_union(&self) -> ReplayFactoredResult<()> {
        let legacy = &self.bounds.attributed_claim_supports;
        let replay = &self
            .replay_clause_projection
            .replay_attributed_claim_supports;
        let flat_retained = &self.bounds.flat_retained_attributed_claim_supports;
        let legacy_is_covered = legacy
            .iter()
            .all(|key| replay.contains(key) || flat_retained.contains(key));
        let union_is_legacy = replay
            .iter()
            .chain(flat_retained)
            .all(|key| legacy.contains(key));
        if !legacy_is_covered || !union_is_legacy {
            return Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ClaimedAttributionUnion,
            ));
        }
        Ok(())
    }

    fn register_replay_evidence_clause_link(
        &mut self,
        lower_record: BoundRecordId,
        parent_claim: UpperReplayClaimId,
        replay: BinaryReplayDerivation,
    ) {
        let Some(root) = self.bounds.canonical_coverage_root(parent_claim) else {
            return;
        };
        self.register_record_proof_clause_link(
            lower_record,
            RecordProofClauseLinkAdmission::claimed(
                root,
                RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: replay.lower,
                    upper_premise: replay.upper,
                },
                ClaimedAttributionSource::FlatRetained,
            ),
        );
    }

    fn register_record_proof_clause_link(
        &mut self,
        lower_record: BoundRecordId,
        admission: RecordProofClauseLinkAdmission,
    ) {
        let support = admission.support;
        let clause = admission.clause;
        if self
            .bounds
            .record_proof_clause_link_is_registered(lower_record, support, clause)
        {
            return;
        }
        self.commit_record_proof_clause_link_batch(lower_record, [admission]);
    }

    fn commit_record_proof_clause_link_batch(
        &mut self,
        lower_record: BoundRecordId,
        links: impl IntoIterator<Item = RecordProofClauseLinkAdmission>,
    ) {
        self.commit_record_proof_clause_link_batch_with_fence(lower_record, links, None);
    }

    fn commit_record_proof_clause_link_batch_with_fence(
        &mut self,
        lower_record: BoundRecordId,
        links: impl IntoIterator<Item = RecordProofClauseLinkAdmission>,
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        let Some(snapshot) =
            self.commit_record_proof_clause_link_batch_mutation(lower_record, links)
        else {
            return;
        };
        self.seal_record_proof_clause_link_batch(Some(snapshot), publication_fence);
    }

    fn seal_record_proof_clause_link_batch(
        &mut self,
        snapshot: Option<ClauseLinkBatchAdmissionSnapshot>,
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        let Some(snapshot) = snapshot else {
            return;
        };
        if let Some(fence) = publication_fence {
            let intent = match self.try_evaluate_record_proof_clause_link_batch(&snapshot) {
                Ok(intent) => intent,
                Err(failure) => {
                    self.mark_replay_factored_failure(
                        failure,
                        ReplayFactoredFailureOperation::Read,
                    );
                    return;
                }
            };
            self.defer_replay_admission_publication(fence, intent);
        } else {
            self.publish_record_proof_clause_link_batch(snapshot);
        }
    }

    fn commit_record_proof_clause_link_batch_mutation(
        &mut self,
        lower_record: BoundRecordId,
        links: impl IntoIterator<Item = RecordProofClauseLinkAdmission>,
    ) -> Option<ClauseLinkBatchAdmissionSnapshot> {
        let mut links = links.into_iter().peekable();
        if links.peek().is_none() {
            return None;
        }
        let was_included = self.scheme_projection_record_is_included(lower_record);
        let mut any_link_inserted = false;
        let mut inserted_clauses = Vec::new();
        for admission in links {
            let clause = admission.clause;
            let (_, clause_inserted, link_inserted) = self
                .bounds
                .register_record_proof_clause_link(lower_record, admission);
            debug_assert!(
                link_inserted,
                "clause-link batch preflight must agree with exact-key insertion"
            );
            if !link_inserted {
                continue;
            }
            any_link_inserted = true;
            if clause_inserted {
                inserted_clauses.push(clause);
            }
        }
        if !any_link_inserted {
            return None;
        }
        for clause in inserted_clauses {
            match clause {
                RecordProofClause::Standalone { .. } => {}
                RecordProofClause::DerivedUnary { premise, .. } => {
                    let mut visited_constraints = FxHashSet::default();
                    self.register_premise_dependency_chain(
                        premise,
                        lower_record,
                        &mut visited_constraints,
                    );
                }
                RecordProofClause::ReplayConjunction {
                    lower_premise,
                    upper_premise,
                    ..
                } => {
                    self.bounds.insert_dependent_record_edge(
                        ProofPremise::Record(lower_premise),
                        lower_record,
                    );
                    self.bounds.insert_dependent_record_edge(
                        ProofPremise::Record(upper_premise),
                        lower_record,
                    );
                }
            }
        }
        Some(ClauseLinkBatchAdmissionSnapshot {
            lower_record,
            was_included,
        })
    }

    fn publish_record_proof_clause_link_batch(
        &mut self,
        snapshot: ClauseLinkBatchAdmissionSnapshot,
    ) {
        let intent = match self.try_evaluate_record_proof_clause_link_batch(&snapshot) {
            Ok(intent) => intent,
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Read,
                );
                return;
            }
        };
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        self.publish_scheme_projection_intent(intent);
    }

    fn try_evaluate_record_proof_clause_link_batch(
        &self,
        snapshot: &ClauseLinkBatchAdmissionSnapshot,
    ) -> ReplayFactoredResult<SchemeProjectionPublicationIntent> {
        let is_included =
            SchemeProjectionEvaluator::new(self).eval_record(snapshot.lower_record)?;
        self.try_evaluate_record_inclusion_publication(
            snapshot.lower_record,
            snapshot.was_included,
            is_included,
            false,
        )
    }

    fn register_premise_dependency_chain(
        &mut self,
        premise: ProofPremise,
        dependent: BoundRecordId,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
    ) {
        // Factored occurrence lookup is fallible, so finish the whole graph-local read before
        // publishing any dependency edge from this chain.
        let visited_before = visited_constraints.clone();
        let mut authoritative_visited = visited_before.clone();
        let mut pending_premises = FxHashSet::default();
        if let Err(failure) = self.try_collect_premise_dependency_chain(
            premise,
            self.replay_read_authority(),
            &mut authoritative_visited,
            &mut pending_premises,
        ) {
            self.mark_replay_factored_failure(failure, ReplayFactoredFailureOperation::Read);
            return;
        }

        #[cfg(any(test, debug_assertions))]
        if self.replay_factored_writes_enabled()
            && self.replay_result_summary.event_oracle_enabled()
        {
            let mut legacy_visited = visited_before;
            let mut legacy_premises = FxHashSet::default();
            let legacy_authority = ReplayReadAuthority::LegacyRollback(
                ReplayFactoredShadowFailure::AllocationFailed,
            );
            let legacy = self.try_collect_premise_dependency_chain(
                premise,
                legacy_authority,
                &mut legacy_visited,
                &mut legacy_premises,
            );
            if legacy.is_err() || legacy_premises != pending_premises {
                self.mark_replay_factored_failure(
                    ReplayFactoredShadowFailure::OracleMismatch(
                        ReplayFactoredOracleMismatch::ReplayDependencyEdges,
                    ),
                    ReplayFactoredFailureOperation::Oracle,
                );
                return;
            }
        }

        *visited_constraints = authoritative_visited;
        for pending in pending_premises {
            self.bounds.insert_dependent_record_edge(pending, dependent);
        }
    }

    fn try_collect_premise_dependency_chain(
        &self,
        premise: ProofPremise,
        authority: ReplayReadAuthority,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        pending_premises: &mut FxHashSet<ProofPremise>,
    ) -> ReplayFactoredResult<()> {
        pending_premises.insert(premise);
        let ProofPremise::Constraint(constraint) = premise else {
            return Ok(());
        };
        // Record nodes publish their own inclusion changes, so only record-free constraint chains
        // are expanded here. The pass-local set bounds structural cycles without evaluating them.
        if !visited_constraints.insert(constraint) {
            return Ok(());
        }
        if let Some(lower_record) = self.lower_record_for_constraint(constraint) {
            pending_premises.insert(ProofPremise::Record(lower_record));
        }
        match authority {
            ReplayReadAuthority::Factored => {
                let occurrence_ids = self.replay_occurrences_for_result(constraint);
                let mut replay_carriers = Vec::new();
                replay_carriers
                    .try_reserve(occurrence_ids.size_hint().0)
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                for occurrence_id in occurrence_ids {
                    let occurrence = self.replay_occurrence(occurrence_id)?;
                    if occurrence.result != constraint {
                        return Err(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex);
                    }
                    replay_carriers.push(occurrence.carrier);
                }

                for replay in replay_carriers {
                    pending_premises.insert(ProofPremise::Record(replay.lower));
                    pending_premises.insert(ProofPremise::Record(replay.upper));
                }
                for parent in self.non_replay_claim_parents_for_result(constraint) {
                    self.try_collect_claim_parent_dependency_chain(
                        parent,
                        authority,
                        visited_constraints,
                        pending_premises,
                    )?;
                }
            }
            ReplayReadAuthority::LegacyRollback(_) => {
                let parents = self
                    .bounds
                    .claim_parents_by_constraint
                    .get(&constraint)
                    .cloned()
                    .unwrap_or_default();
                for parent in parents {
                    self.try_collect_claim_parent_dependency_chain(
                        parent,
                        authority,
                        visited_constraints,
                        pending_premises,
                    )?;
                }
            }
        }
        if let Some(root_claim) = self
            .bounds
            .root_claim_by_producer_constraint
            .get(&constraint)
            .copied()
            && let Some(root) = self.bounds.canonical_coverage_root(root_claim)
        {
            pending_premises.insert(ProofPremise::RootCoverage(root));
        }
        Ok(())
    }

    fn try_collect_claim_parent_dependency_chain(
        &self,
        parent: ClaimQualifiedParent,
        authority: ReplayReadAuthority,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        pending_premises: &mut FxHashSet<ProofPremise>,
    ) -> ReplayFactoredResult<()> {
        match parent {
            ClaimQualifiedParent::ReplayConstraint { replay, .. } => {
                pending_premises.insert(ProofPremise::Record(replay.lower));
                pending_premises.insert(ProofPremise::Record(replay.upper));
            }
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                self.try_collect_premise_dependency_chain(
                    ProofPremise::Constraint(derivation.parent),
                    authority,
                    visited_constraints,
                    pending_premises,
                )?;
            }
            ClaimQualifiedParent::ReductionRouteConstraint { parent_claim, .. } => {
                if let Some(root) = self.bounds.canonical_coverage_root(parent_claim) {
                    pending_premises.insert(ProofPremise::RootCoverage(root));
                }
            }
        }
        Ok(())
    }

    fn register_claim_parent_dependency_chain(
        &mut self,
        parent: ClaimQualifiedParent,
        dependent: BoundRecordId,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
    ) {
        match parent {
            ClaimQualifiedParent::ReplayConstraint { replay, .. } => {
                self.bounds
                    .insert_dependent_record_edge(ProofPremise::Record(replay.lower), dependent);
                self.bounds
                    .insert_dependent_record_edge(ProofPremise::Record(replay.upper), dependent);
            }
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                self.register_premise_dependency_chain(
                    ProofPremise::Constraint(derivation.parent),
                    dependent,
                    visited_constraints,
                );
            }
            ClaimQualifiedParent::ReductionRouteConstraint { parent_claim, .. } => {
                if let Some(root) = self.bounds.canonical_coverage_root(parent_claim) {
                    self.bounds
                        .insert_dependent_record_edge(ProofPremise::RootCoverage(root), dependent);
                }
            }
        }
    }

    pub(in crate::constraints) fn register_new_constraint_premise_route_edges(
        &mut self,
        constraint: ConstraintRecordId,
        parent: ClaimQualifiedParent,
    ) {
        // A late route extends every edge already rooted at this Constraint premise before the
        // caller compares and publishes the dependent records' inclusion states.
        let dependents = self
            .bounds
            .dependent_records_by_premise
            .get(&ProofPremise::Constraint(constraint))
            .cloned()
            .unwrap_or_default();
        for dependent in dependents {
            let mut visited_constraints = FxHashSet::from_iter([constraint]);
            self.register_claim_parent_dependency_chain(
                parent,
                dependent,
                &mut visited_constraints,
            );
        }
    }

    #[cfg(test)]
    pub(in crate::constraints) fn admit_claim_qualified_parent(
        &mut self,
        constraint: ConstraintRecordId,
        parent: ClaimQualifiedParent,
    ) {
        let snapshot = self.commit_claim_qualified_parent_mutation(constraint, parent);
        self.publish_claim_qualified_parent_admission(snapshot);
    }

    fn begin_non_replay_claim_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
        target_record: Option<BoundRecordId>,
        lower_carrier: Option<ProjectionProofCarrier>,
    ) -> Option<ReplayAdmissionPublicationFence> {
        let factored_admission = self.replay_read_authority() == ReplayReadAuthority::Factored;
        let mut publication_fence =
            factored_admission.then(ReplayAdmissionPublicationFence::default);
        for parent in parents.iter().copied() {
            let snapshot = self.commit_claim_qualified_parent_mutation(result, parent);
            if let Some(fence) = publication_fence.as_mut() {
                self.defer_claim_qualified_parent_admission(fence, snapshot);
            } else {
                self.publish_claim_qualified_parent_admission(snapshot);
            }
        }
        if let Some(lower_record) = self.lower_record_for_constraint(result) {
            self.register_claim_parent_clause_links_after_factored_projection(
                result,
                lower_record,
                parents,
                publication_fence.as_mut(),
            );
        }
        if factored_admission && self.replay_factored_terminal_failure().is_none() {
            let independent_supports = self
                .lower_record_for_constraint(result)
                .zip(lower_carrier)
                .filter(|(lower_record, carrier)| {
                    self.projection_carrier_is_independent(*lower_record, *carrier)
                })
                .map(|(_, carrier)| vec![carrier])
                .unwrap_or_default();
            if let Err(failure) = self.try_authoritative_claim_parent_full_plan(
                result,
                target_record.filter(|_| !parents.is_empty()),
                parents,
                &independent_supports,
            ) {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Read,
                );
            }
        }
        publication_fence
    }

    fn finish_non_replay_claim_parent_admission(
        &mut self,
        _result: ConstraintRecordId,
        publication_fence: Option<ReplayAdmissionPublicationFence>,
    ) {
        let Some(publication_fence) = publication_fence else {
            return;
        };
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        #[cfg(any(test, debug_assertions))]
        self.observe_factored_replay_event_boundary(_result);
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        self.publish_replay_admission_publication_fence(publication_fence);
    }

    pub(in crate::constraints) fn register_structural_claim_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
        derivation: StructuralDerivation,
        derivation_inserted: bool,
    ) {
        let carrier = ProjectionProofCarrier::StructuralConstraint { result, derivation };
        let mut publication_fence = self.begin_non_replay_claim_parent_admission(
            result,
            parents,
            None,
            derivation_inserted.then_some(carrier),
        );
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        if derivation_inserted {
            self.register_constraint_projection_carrier_delta_with_precommitted_clause_links(
                result,
                parents,
                carrier,
                true,
                publication_fence.as_mut(),
            );
        } else {
            self.register_existing_constraint_lower_projection_delta(
                result,
                parents,
                LowerProjectionDelta::ClaimsOnly,
                true,
                publication_fence.as_mut(),
            );
        }
        self.finish_non_replay_claim_parent_admission(result, publication_fence);
    }

    fn commit_claim_qualified_parent_mutation(
        &mut self,
        constraint: ConstraintRecordId,
        parent: ClaimQualifiedParent,
    ) -> ClaimQualifiedParentAdmissionSnapshot {
        let inclusion_before =
            self.projection_inclusion_snapshot(ProofPremise::Constraint(constraint));
        self.bounds.push_claim_qualified_parent(constraint, parent);
        self.observe_non_replay_claim_parent_admission(constraint, parent);
        self.register_new_constraint_premise_route_edges(constraint, parent);
        self.observe_first_qualified_parent_source(constraint, parent);
        ClaimQualifiedParentAdmissionSnapshot { inclusion_before }
    }

    fn publish_claim_qualified_parent_admission(
        &mut self,
        snapshot: ClaimQualifiedParentAdmissionSnapshot,
    ) {
        let intent = match self.try_evaluate_claim_qualified_parent_admission(&snapshot) {
            Ok(intent) => intent,
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Read,
                );
                return;
            }
        };
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        self.publish_scheme_projection_intent(intent);
    }

    fn try_evaluate_claim_qualified_parent_admission(
        &self,
        snapshot: &ClaimQualifiedParentAdmissionSnapshot,
    ) -> ReplayFactoredResult<SchemeProjectionPublicationIntent> {
        self.try_evaluate_projection_inclusion_snapshot(&snapshot.inclusion_before)
    }

    fn defer_replay_admission_publication(
        &mut self,
        fence: &mut ReplayAdmissionPublicationFence,
        intent: SchemeProjectionPublicationIntent,
    ) {
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        if let Err(failure) = fence.try_push(intent) {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Write,
            );
        }
    }

    fn defer_claim_qualified_parent_admission(
        &mut self,
        fence: &mut ReplayAdmissionPublicationFence,
        snapshot: ClaimQualifiedParentAdmissionSnapshot,
    ) {
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        #[cfg(test)]
        if rcpf_d2c_should_fail_deferred_evaluation() {
            self.mark_replay_factored_failure(
                ReplayFactoredShadowFailure::AllocationFailed,
                ReplayFactoredFailureOperation::Read,
            );
            return;
        }
        let intent = match self.try_evaluate_claim_qualified_parent_admission(&snapshot) {
            Ok(intent) => intent,
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Read,
                );
                return;
            }
        };
        #[cfg(test)]
        if matches!(&intent, SchemeProjectionPublicationIntent::OwnersChanged(_)) {
            RCPF_D2C_PHASE_A_OWNER_INTENT_PROBES.with(|probes| {
                probes.set(probes.get().saturating_add(1));
            });
        }
        self.defer_replay_admission_publication(fence, intent);
    }

    fn defer_scheme_projection_mutation(
        &mut self,
        fence: &mut ReplayAdmissionPublicationFence,
        mutation: SchemeProjectionMutation,
    ) {
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        #[cfg(test)]
        if rcpf_d2c_should_fail_deferred_evaluation() {
            self.mark_replay_factored_failure(
                ReplayFactoredShadowFailure::AllocationFailed,
                ReplayFactoredFailureOperation::Read,
            );
            return;
        }
        let intent = match self.try_evaluate_scheme_projection_mutation(mutation) {
            Ok(intent) => intent,
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Read,
                );
                return;
            }
        };
        self.defer_replay_admission_publication(fence, intent);
    }

    fn publish_replay_admission_publication_fence(
        &mut self,
        fence: ReplayAdmissionPublicationFence,
    ) {
        for intent in fence.intents {
            self.publish_scheme_projection_intent(intent);
        }
    }

    /// Observe an already completed legacy admission. Failure quarantines the additive RCPF
    /// representation without changing legacy route publication or evaluation.
    fn observe_non_replay_claim_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        parent: ClaimQualifiedParent,
    ) {
        if !self.replay_factored_writes_enabled() {
            return;
        }
        if let Err(failure) = self
            .non_replay_claim_parents_by_constraint
            .try_admit(result, parent)
        {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Write,
            );
        }
    }

    fn observe_first_qualified_parent_source(
        &mut self,
        result: ConstraintRecordId,
        parent: ClaimQualifiedParent,
    ) {
        if !self.replay_factored_writes_enabled() {
            return;
        }
        if let Err(failure) = self
            .replay_result_summary
            .try_record_first_qualified_parent_source(result, parent, &self.bounds)
        {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Write,
            );
        }
    }

    pub(in crate::constraints) fn lower_record_for_constraint(
        &self,
        producer: ConstraintRecordId,
    ) -> Option<BoundRecordId> {
        if let Some(record) = self
            .bounds
            .scheme_projection_lower_record_by_constraint
            .get(&producer)
            .copied()
        {
            return Some(record);
        }
        let constraint = &self.constraint_records.get(producer.0 as usize)?.key;
        let Neg::Var(target) = self.types.neg(constraint.upper) else {
            return None;
        };
        self.bounds
            .canonical
            .get(&BoundSemanticKey::Lower {
                owner: *target,
                endpoint: constraint.lower,
                weights: constraint.weights.clone(),
            })
            .copied()
    }

    fn register_lower_projection_derivation(
        &mut self,
        lower_record: BoundRecordId,
        producer: Option<ConstraintRecordId>,
        derivation: BoundDerivation,
    ) {
        #[cfg(test)]
        match &derivation {
            BoundDerivation::Constraint(_) => {
                self.cdm_lower_delta_census.constraint_bound_events += 1;
            }
            _ => self.cdm_lower_delta_census.other_bound_events += 1,
        }
        let parents = producer
            .and_then(|producer| self.bounds.claim_parents_by_constraint.get(&producer))
            .cloned()
            .unwrap_or_default();
        let claims = if self
            .bounds
            .projection_proofs_by_lower_record
            .contains_key(&lower_record)
        {
            Vec::new()
        } else {
            parents.iter().map(|parent| parent.parent_claim()).collect()
        };
        self.register_lower_projection_delta(
            lower_record,
            &claims,
            LowerProjectionDelta::Bound(derivation),
            None,
        );
        #[cfg(any(test, debug_assertions))]
        if let Some(producer) = producer {
            self.observe_factored_lower_projection_full(lower_record, producer);
        }
        if let Some(producer) = producer {
            self.register_claim_parent_clause_links_after_factored_projection(
                producer,
                lower_record,
                &parents,
                None,
            );
            #[cfg(any(test, debug_assertions))]
            self.observe_factored_replay_event_boundary(producer);
        }
    }

    fn register_existing_constraint_lower_projection_delta(
        &mut self,
        producer: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
        delta: LowerProjectionDelta,
        replay_clause_work_precommitted: bool,
        mut publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        let Some(lower_record) = self.lower_record_for_constraint(producer) else {
            return;
        };
        let ledger_exists = self
            .bounds
            .projection_proofs_by_lower_record
            .contains_key(&lower_record);
        let parents = if ledger_exists {
            parents.to_vec()
        } else {
            self.bounds
                .claim_parents_by_constraint
                .get(&producer)
                .cloned()
                .unwrap_or_default()
        };
        let claims = parents
            .iter()
            .map(|parent| parent.parent_claim())
            .collect::<Vec<_>>();
        self.register_lower_projection_delta(
            lower_record,
            &claims,
            delta,
            publication_fence.as_deref_mut(),
        );
        if !replay_clause_work_precommitted {
            self.register_claim_parent_clause_links_after_factored_projection(
                producer,
                lower_record,
                &parents,
                publication_fence.as_deref_mut(),
            );
        }
    }

    pub(in crate::constraints) fn register_constraint_projection_carrier_delta(
        &mut self,
        producer: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
        carrier: ProjectionProofCarrier,
    ) {
        self.register_constraint_projection_carrier_delta_with_precommitted_clause_links(
            producer, parents, carrier, false, None,
        );
    }

    fn register_constraint_projection_carrier_delta_with_precommitted_clause_links(
        &mut self,
        producer: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
        carrier: ProjectionProofCarrier,
        replay_clause_work_precommitted: bool,
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        #[cfg(test)]
        self.record_cdm_lower_carrier_event(carrier);
        let delta = if !parents.is_empty()
            && self
                .bounds
                .claim_parents_by_constraint
                .get(&producer)
                .is_some_and(|all| all.len() == parents.len())
        {
            // A producer's bound derivation can predate its first qualified-parent admission.
            // Classify that one bound derivation once; later admissions are exact carrier deltas.
            LowerProjectionDelta::Bound(BoundDerivation::Constraint(producer))
        } else {
            LowerProjectionDelta::Carrier(carrier)
        };
        self.register_existing_constraint_lower_projection_delta(
            producer,
            parents,
            delta,
            replay_clause_work_precommitted,
            publication_fence,
        );
    }

    fn register_lower_record_projection_carrier_delta(
        &mut self,
        lower_record: BoundRecordId,
        carrier: ProjectionProofCarrier,
    ) {
        #[cfg(test)]
        self.record_cdm_lower_carrier_event(carrier);
        self.register_lower_projection_delta(
            lower_record,
            &[],
            LowerProjectionDelta::Carrier(carrier),
            None,
        );
    }

    fn register_lower_projection_delta(
        &mut self,
        lower_record: BoundRecordId,
        claims_to_link: &[UpperReplayClaimId],
        delta: LowerProjectionDelta,
        mut publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        let ledger_exists = self
            .bounds
            .projection_proofs_by_lower_record
            .contains_key(&lower_record);
        #[cfg(test)]
        {
            if !claims_to_link.is_empty() {
                self.cdm_lower_delta_census.parent_batches += 1;
            }
            if !ledger_exists && !claims_to_link.is_empty() {
                self.cdm_lower_delta_census.bootstrap_scans += 1;
            }
        }
        if claims_to_link.is_empty() && !ledger_exists {
            return;
        }
        // Preserve D2-5: classify against the pre-link claim ledger. Exact carrier parents have
        // already entered the append-only index, matching the old current-producer in-flight view.
        let independent_supports = if ledger_exists {
            match delta {
                LowerProjectionDelta::ClaimsOnly => Vec::new(),
                LowerProjectionDelta::Bound(derivation) => {
                    self.independent_projection_supports_for_derivation(lower_record, &derivation)
                }
                LowerProjectionDelta::Carrier(carrier) => self
                    .projection_carrier_is_independent(lower_record, carrier)
                    .then_some(carrier)
                    .into_iter()
                    .collect(),
            }
        } else {
            self.bootstrap_independent_projection_supports(lower_record)
        };
        let mutation = self.bounds.update_scheme_projection_proofs(
            lower_record,
            claims_to_link,
            &independent_supports,
        );
        #[cfg(any(test, debug_assertions))]
        let lower_projection_oracle =
            (matches!(mutation, SchemeProjectionMutation::ProofsChanged { .. })
                && self.replay_factored_writes_enabled()
                && self.replay_result_summary.event_oracle_enabled())
            .then(|| {
                self.try_factored_lower_projection_mutation_oracle(
                    lower_record,
                    &mutation,
                    &independent_supports,
                )
            });
        if let Some(fence) = publication_fence.as_deref_mut() {
            self.defer_scheme_projection_mutation(fence, mutation);
        } else {
            self.apply_scheme_projection_mutation(mutation);
        }
        let mut pending_links = Vec::new();
        let mut batch_link_keys = FxHashSet::default();
        for support in independent_supports {
            let support = SchemeProjectionProofSupport::Independent(support);
            let clause = RecordProofClause::Standalone { support };
            if self
                .bounds
                .record_proof_clause_link_is_registered(lower_record, support, clause)
            {
                continue;
            }
            let batch_link_key = (
                TypeBounds::record_proof_clause_key(lower_record, clause),
                support,
            );
            if !batch_link_keys.insert(batch_link_key) {
                continue;
            }
            pending_links.push(RecordProofClauseLinkAdmission::independent(
                support, clause,
            ));
        }
        if pending_links.is_empty() {
            #[cfg(any(test, debug_assertions))]
            if let Some(result) = lower_projection_oracle {
                self.observe_factored_lower_projection_result(result);
            }
            return;
        }
        self.commit_record_proof_clause_link_batch_with_fence(
            lower_record,
            pending_links,
            publication_fence,
        );
        #[cfg(any(test, debug_assertions))]
        if let Some(result) = lower_projection_oracle {
            self.observe_factored_lower_projection_result(result);
        }
    }

    fn bootstrap_independent_projection_supports(
        &self,
        lower_record: BoundRecordId,
    ) -> Vec<ProjectionProofCarrier> {
        let mut supports = Vec::new();
        let Some(record) = self.bounds.record(lower_record) else {
            return supports;
        };
        for derivation in record.derivations() {
            supports.extend(
                self.independent_projection_supports_for_derivation(lower_record, derivation),
            );
        }
        let mut seen = FxHashSet::default();
        supports.retain(|support| seen.insert(*support));
        supports
    }

    fn independent_projection_supports_for_derivation(
        &self,
        lower_record: BoundRecordId,
        derivation: &BoundDerivation,
    ) -> Vec<ProjectionProofCarrier> {
        let mut supports = Vec::new();
        match derivation {
            BoundDerivation::Constraint(producer) => {
                let constraint = &self.constraint_records[producer.0 as usize];
                supports.extend(constraint.root_origins.iter().filter_map(|origin| {
                    let carrier = ProjectionProofCarrier::ConstraintOrigin {
                        constraint: *producer,
                        origin: *origin,
                    };
                    self.projection_carrier_is_independent(lower_record, carrier)
                        .then_some(carrier)
                }));
                supports.extend(constraint.structural_derivations.iter().filter_map(
                    |derivation| {
                        let carrier = ProjectionProofCarrier::StructuralConstraint {
                            result: *producer,
                            derivation: *derivation,
                        };
                        self.projection_carrier_is_independent(lower_record, carrier)
                            .then_some(carrier)
                    },
                ));
                supports.extend(
                    constraint
                        .replay_derivations
                        .iter()
                        .filter_map(|derivation| {
                            let carrier = ProjectionProofCarrier::ReplayConstraint {
                                result: *producer,
                                derivation: *derivation,
                            };
                            self.projection_carrier_is_independent(lower_record, carrier)
                                .then_some(carrier)
                        }),
                );
                supports.extend(constraint.row_derivations.iter().filter_map(|derivation| {
                    let carrier = ProjectionProofCarrier::RowConstraint {
                        result: *producer,
                        derivation: *derivation,
                    };
                    self.projection_carrier_is_independent(lower_record, carrier)
                        .then_some(carrier)
                }));
                supports.extend(constraint.scheme_instantiation_derivations.iter().map(
                    |derivation| ProjectionProofCarrier::SchemeInstantiationConstraint {
                        result: *producer,
                        source_witness: derivation.source_witness,
                    },
                ));
            }
            BoundDerivation::Origin(origin) => {
                supports.push(ProjectionProofCarrier::Origin(*origin));
            }
            BoundDerivation::ReplayEvidence(replay) => {
                supports.push(ProjectionProofCarrier::ReplayEvidence(*replay));
            }
            BoundDerivation::Row(row) => supports.push(ProjectionProofCarrier::Row(*row)),
            BoundDerivation::SchemeInstantiation(derivation) => {
                supports.push(ProjectionProofCarrier::SchemeInstantiation(
                    derivation.source_witness,
                ));
            }
            BoundDerivation::IncompleteReplay => {
                supports.push(ProjectionProofCarrier::Incomplete);
            }
        }
        supports
    }

    fn projection_carrier_is_independent(
        &self,
        lower_record: BoundRecordId,
        carrier: ProjectionProofCarrier,
    ) -> bool {
        match carrier {
            ProjectionProofCarrier::ConstraintOrigin { constraint, .. } => !self
                .bounds
                .scheme_projection_claims_by_lower_record
                .get(&lower_record)
                .into_iter()
                .flatten()
                .any(|claim| {
                    self.bounds.upper_replay_claims[claim.0 as usize].producer_constraint
                        == constraint
                }),
            ProjectionProofCarrier::StructuralConstraint { result, derivation } => !self
                .bounds
                .qualified_carrier_index
                .get(&result)
                .is_some_and(|carriers| {
                    carriers.contains(&QualifiedCarrier::Structural(derivation))
                }),
            ProjectionProofCarrier::ReplayConstraint { result, derivation } => !self
                .bounds
                .qualified_carrier_index
                .get(&result)
                .is_some_and(|carriers| carriers.contains(&QualifiedCarrier::Replay(derivation))),
            ProjectionProofCarrier::RowConstraint { result, derivation } => !self
                .bounds
                .qualified_carrier_index
                .get(&result)
                .is_some_and(|carriers| {
                    carriers.contains(&QualifiedCarrier::ReductionRoute(derivation))
                }),
            ProjectionProofCarrier::SchemeInstantiationConstraint { .. }
            | ProjectionProofCarrier::Origin(_)
            | ProjectionProofCarrier::ReplayEvidence(_)
            | ProjectionProofCarrier::Row(_)
            | ProjectionProofCarrier::SchemeInstantiation(_)
            | ProjectionProofCarrier::Incomplete => true,
        }
    }

    #[cfg(test)]
    fn register_existing_constraint_lower_projection_proofs_bulk(
        &mut self,
        producer: ConstraintRecordId,
    ) {
        self.cdm_lower_delta_census.bulk_scans += 1;
        let Some(lower_record) = self.lower_record_for_constraint(producer) else {
            return;
        };
        let claim_parents = self
            .bounds
            .claim_parents_by_constraint
            .get(&producer)
            .cloned()
            .unwrap_or_default();
        let ledger_exists = self
            .bounds
            .projection_proofs_by_lower_record
            .contains_key(&lower_record);
        if claim_parents.is_empty() && !ledger_exists {
            return;
        }
        let claims = claim_parents
            .iter()
            .map(|parent| parent.parent_claim())
            .collect::<Vec<_>>();
        let independent_supports =
            self.independent_projection_supports_bulk(lower_record, Some(producer), &claim_parents);
        let mutation = self.bounds.update_scheme_projection_proofs(
            lower_record,
            &claims,
            &independent_supports,
        );
        self.apply_scheme_projection_mutation(mutation);
    }

    #[cfg(test)]
    fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
        self.cdm_lower_delta_census.bulk_scans += 1;
        let supports = self.independent_projection_supports_bulk(lower_record, None, &[]);
        let mutation = self
            .bounds
            .update_scheme_projection_proofs(lower_record, &[], &supports);
        self.apply_scheme_projection_mutation(mutation);
    }

    #[cfg(test)]
    fn independent_projection_supports_bulk(
        &self,
        lower_record: BoundRecordId,
        current_producer: Option<ConstraintRecordId>,
        current_claim_parents: &[ClaimQualifiedParent],
    ) -> Vec<ProjectionProofCarrier> {
        let mut supports = Vec::new();
        let Some(record) = self.bounds.record(lower_record) else {
            return supports;
        };
        for derivation in record.derivations() {
            match derivation {
                BoundDerivation::Constraint(producer) => {
                    let parents = if Some(*producer) == current_producer {
                        current_claim_parents
                    } else {
                        self.bounds
                            .claim_parents_by_constraint
                            .get(producer)
                            .map(Vec::as_slice)
                            .unwrap_or(&[])
                    };
                    let constraint = &self.constraint_records[producer.0 as usize];
                    let roots_have_claim_support = self
                        .bounds
                        .scheme_projection_claims_by_lower_record
                        .get(&lower_record)
                        .into_iter()
                        .flatten()
                        .any(|claim| {
                            self.bounds.upper_replay_claims[claim.0 as usize].producer_constraint
                                == *producer
                        });
                    if !roots_have_claim_support {
                        supports.extend(constraint.root_origins.iter().map(|origin| {
                            ProjectionProofCarrier::ConstraintOrigin {
                                constraint: *producer,
                                origin: *origin,
                            }
                        }));
                    }
                    for carrier in &constraint.structural_derivations {
                        if !parents.iter().any(|parent| {
                            matches!(
                                parent,
                                ClaimQualifiedParent::StructuralConstraint {
                                    derivation,
                                    ..
                                } if derivation == carrier
                            )
                        }) {
                            supports.push(ProjectionProofCarrier::StructuralConstraint {
                                result: *producer,
                                derivation: *carrier,
                            });
                        }
                    }
                    for carrier in &constraint.replay_derivations {
                        if !parents.iter().any(|parent| {
                            matches!(
                                parent,
                                ClaimQualifiedParent::ReplayConstraint { replay, .. }
                                    if replay == carrier
                            )
                        }) {
                            supports.push(ProjectionProofCarrier::ReplayConstraint {
                                result: *producer,
                                derivation: *carrier,
                            });
                        }
                    }
                    for carrier in &constraint.row_derivations {
                        if !parents.iter().any(|parent| {
                            matches!(
                                parent,
                                ClaimQualifiedParent::ReductionRouteConstraint {
                                    derivation,
                                    ..
                                } if derivation == carrier
                            )
                        }) {
                            supports.push(ProjectionProofCarrier::RowConstraint {
                                result: *producer,
                                derivation: *carrier,
                            });
                        }
                    }
                    supports.extend(constraint.scheme_instantiation_derivations.iter().map(
                        |derivation| ProjectionProofCarrier::SchemeInstantiationConstraint {
                            result: *producer,
                            source_witness: derivation.source_witness,
                        },
                    ));
                }
                BoundDerivation::Origin(origin) => {
                    supports.push(ProjectionProofCarrier::Origin(*origin));
                }
                BoundDerivation::ReplayEvidence(replay) => {
                    supports.push(ProjectionProofCarrier::ReplayEvidence(*replay));
                }
                BoundDerivation::Row(row) => supports.push(ProjectionProofCarrier::Row(*row)),
                BoundDerivation::SchemeInstantiation(derivation) => {
                    supports.push(ProjectionProofCarrier::SchemeInstantiation(
                        derivation.source_witness,
                    ));
                }
                BoundDerivation::IncompleteReplay => {
                    supports.push(ProjectionProofCarrier::Incomplete);
                }
            }
        }
        let mut seen = FxHashSet::default();
        supports.retain(|support| seen.insert(*support));
        supports
    }

    #[cfg(test)]
    fn record_cdm_lower_carrier_event(&mut self, carrier: ProjectionProofCarrier) {
        match carrier {
            ProjectionProofCarrier::ReplayConstraint { .. } => {
                self.cdm_lower_delta_census.replay_carrier_events += 1;
            }
            ProjectionProofCarrier::StructuralConstraint { .. } => {
                self.cdm_lower_delta_census.structural_carrier_events += 1;
            }
            ProjectionProofCarrier::RowConstraint { .. } => {
                self.cdm_lower_delta_census.row_carrier_events += 1;
            }
            ProjectionProofCarrier::ReplayEvidence(_) | ProjectionProofCarrier::Incomplete => {
                self.cdm_lower_delta_census.evidence_carrier_events += 1;
            }
            ProjectionProofCarrier::ConstraintOrigin { .. }
            | ProjectionProofCarrier::SchemeInstantiationConstraint { .. }
            | ProjectionProofCarrier::Origin(_)
            | ProjectionProofCarrier::Row(_)
            | ProjectionProofCarrier::SchemeInstantiation(_) => {
                self.cdm_lower_delta_census.other_carrier_events += 1;
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
        self.cdm_lower_delta_census = CdmLowerDeltaCensus::default();
    }

    #[cfg(test)]
    pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
        self.cdm_lower_delta_census
    }

    #[cfg(test)]
    fn register_replay_claim_parents(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
        materialize_existing_target: bool,
    ) {
        assert!(
            matches!(
                self.replay_read_authority(),
                ReplayReadAuthority::LegacyRollback(_)
            ),
            "the legacy-only replay-parent helper requires LegacyRollback authority"
        );
        self.register_replay_claim_parents_with_factored_drafts(
            result,
            replay,
            parents,
            materialize_existing_target,
            None,
        );
    }

    fn register_replay_claim_parents_with_factored_drafts(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
        materialize_existing_target: bool,
        factored_drafts: Option<FactoredReplayParentDrafts<'_>>,
    ) {
        if !self.constraint_records[result.0 as usize]
            .replay_derivations
            .contains(&replay)
        {
            return;
        }
        let target_record = self.var_var_upper_record_for_constraint(result);
        let factored_admission = factored_drafts.is_some();
        let phase_b_enabled = factored_admission && self.replay_factored_writes_enabled();
        let mut publication_fence =
            factored_admission.then(ReplayAdmissionPublicationFence::default);
        let mut inserted_parents = Vec::new();
        for parent in parents {
            let coverage_root =
                self.bounds.upper_replay_claims[parent.claim.0 as usize].coverage_root;
            let key = ReplayClaimParentKey {
                result,
                coverage_root,
                parent_side: parent.parent_side,
                replay,
            };
            #[cfg(test)]
            RCPF_C3B_REPLAY_PARENT_ADMISSION_PROBES.with(|probes| {
                probes.set(probes.get().saturating_add(1));
            });
            if !self.bounds.replay_claim_parent_keys.insert(key) {
                continue;
            }
            let parent = ClaimQualifiedParent::ReplayConstraint {
                parent_claim: parent.claim,
                parent_side: parent.parent_side,
                replay,
            };
            let snapshot = self.commit_claim_qualified_parent_mutation(result, parent);
            if let Some(fence) = publication_fence.as_mut() {
                self.defer_claim_qualified_parent_admission(fence, snapshot);
            } else {
                self.publish_claim_qualified_parent_admission(snapshot);
            }
            inserted_parents.push(parent);
        }
        #[cfg(test)]
        proof::record_replay_parent_snapshot_shadow(
            &self.bounds,
            result,
            replay,
            &inserted_parents,
        );
        let bootstrap_clause_projection_parents = if phase_b_enabled
            && materialize_existing_target
            && let Some(lower_record) = self.lower_record_for_constraint(result)
            && !self
                .bounds
                .projection_proofs_by_lower_record
                .contains_key(&lower_record)
        {
            Some(
                self.bounds
                    .claim_parents_by_constraint
                    .get(&result)
                    .cloned()
                    .unwrap_or_default(),
            )
        } else {
            None
        };
        let clause_projection_parents = bootstrap_clause_projection_parents
            .as_deref()
            .unwrap_or(&inserted_parents);
        let pending_clause_link_snapshot = if phase_b_enabled
            && materialize_existing_target
            && let Some(lower_record) = self.lower_record_for_constraint(result)
        {
            self.commit_claim_parent_clause_links_mutation(
                result,
                lower_record,
                clause_projection_parents,
            )
        } else {
            None
        };
        let summary_delta = factored_drafts.map(|factored_drafts| {
            self.observe_factored_replay_parent_admission(
                result,
                replay,
                parents,
                &inserted_parents,
                clause_projection_parents,
                factored_drafts,
            )
        });
        if phase_b_enabled
            && materialize_existing_target
            && self.replay_factored_terminal_failure().is_none()
        {
            self.seal_record_proof_clause_link_batch(
                pending_clause_link_snapshot,
                publication_fence.as_mut(),
            );
        }
        if phase_b_enabled
            && materialize_existing_target
            && self.replay_factored_terminal_failure().is_none()
            && let Some(delta) = summary_delta.as_ref()
            && let Err(failure) = self.try_authoritative_replay_delta_plan(
                result,
                target_record,
                &inserted_parents,
                delta,
                ProjectionProofCarrier::ReplayConstraint {
                    result,
                    derivation: replay,
                },
            )
        {
            self.mark_replay_factored_failure(
                failure,
                ReplayFactoredFailureOperation::Write,
            );
        }
        if factored_admission && self.replay_factored_terminal_failure().is_some() {
            return;
        }
        // Newly enqueued constraints consume this metadata during their bound admission.
        // Queue-suppressed duplicates need the eager path because no later admission will run.
        if materialize_existing_target {
            #[cfg(any(test, debug_assertions))]
            if let (Some(record), Some(delta)) = (target_record, summary_delta.as_ref()) {
                self.observe_factored_upper_materialization_delta(
                    record,
                    result,
                    &inserted_parents,
                    delta,
                );
            }
            self.materialize_existing_claim_parents_delta(
                result,
                target_record,
                &inserted_parents,
                ProjectionProofCarrier::ReplayConstraint {
                    result,
                    derivation: replay,
                },
                phase_b_enabled,
                publication_fence.as_mut(),
            );
            #[cfg(any(test, debug_assertions))]
            if let (Some(lower_record), Some(delta)) = (
                self.lower_record_for_constraint(result),
                summary_delta.as_ref(),
            ) {
                self.observe_factored_lower_projection_delta(lower_record, result, delta);
            }
        }
        let _summary_delta = summary_delta;
        if factored_admission && self.replay_factored_terminal_failure().is_some() {
            return;
        }
        if factored_admission {
            #[cfg(any(test, debug_assertions))]
            self.observe_factored_replay_event_boundary(result);
        }
        if factored_admission && self.replay_factored_terminal_failure().is_some() {
            return;
        }
        if let Some(fence) = publication_fence {
            self.publish_replay_admission_publication_fence(fence);
        }
    }

    /// Observe an already completed legacy admission. Failure permanently quarantines only the
    /// shadow ledger; no legacy state, epoch, event, or queue decision depends on this result.
    fn observe_factored_replay_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        legacy_parents: &[SideTaggedReplayClaim],
        inserted_parents: &[ClaimQualifiedParent],
        clause_projection_parents: &[ClaimQualifiedParent],
        drafts: FactoredReplayParentDrafts<'_>,
    ) -> ReplayResultSummaryDelta {
        if !self.replay_factored_writes_enabled() {
            return ReplayResultSummaryDelta::default();
        }
        match self.try_observe_factored_replay_parent_admission(
            result,
            replay,
            legacy_parents,
            inserted_parents,
            drafts,
        ) {
            Ok(delta) => {
                if let Some(lower_record) = self.lower_record_for_constraint(result)
                    && let Err(failure) = self.try_project_factored_replay_clause_parents(
                        result,
                        lower_record,
                        clause_projection_parents,
                    )
                {
                    self.mark_replay_factored_failure(
                        failure,
                        ReplayFactoredFailureOperation::Write,
                    );
                    return ReplayResultSummaryDelta::default();
                }
                delta
            }
            Err(failure) => {
                self.mark_replay_factored_failure(
                    failure,
                    ReplayFactoredFailureOperation::Write,
                );
                ReplayResultSummaryDelta::default()
            }
        }
    }

    fn try_observe_factored_replay_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        legacy_parents: &[SideTaggedReplayClaim],
        inserted_parents: &[ClaimQualifiedParent],
        drafts: FactoredReplayParentDrafts<'_>,
    ) -> ReplayFactoredResult<ReplayResultSummaryDelta> {
        let lower_draft = drafts.resolve(drafts.lower)?;
        let upper_draft = drafts.resolve(drafts.upper)?;
        for (side, draft) in [
            (ReplayClaimParentSide::Lower, lower_draft),
            (ReplayClaimParentSide::Upper, upper_draft),
        ] {
            let matches_legacy = draft
                .into_iter()
                .flat_map(|draft| draft.claims.iter().copied())
                .eq(legacy_parents
                    .iter()
                    .filter(|parent| parent.parent_side == side)
                    .map(|parent| parent.claim));
            if !matches_legacy {
                return Err(ReplayFactoredShadowFailure::ReplayParentDraftMismatch(side));
            }
        }
        if lower_draft.is_none() && upper_draft.is_none() {
            return Ok(ReplayResultSummaryDelta::default());
        }
        let admission_ordinal = self.replay_occurrences.claim_admission_ordinal()?;

        let key = ReplayOccurrenceKey {
            result,
            carrier: replay,
        };
        let occurrence_id = self.replay_occurrences.occurrence_id(key);
        let empty = self.replay_parent_sets.empty_version();
        let (lower_base, upper_base) = if let Some(occurrence_id) = occurrence_id {
            let occurrence = self.replay_occurrences.occurrence(occurrence_id)?;
            (occurrence.lower_parents, occurrence.upper_parents)
        } else {
            (empty, empty)
        };

        let (lower_parents, lower_changed) = if let Some(draft) = lower_draft {
            let plan = self
                .replay_parent_sets
                .preflight_extend(lower_base, draft, &self.bounds)?;
            let extension = self.replay_parent_sets.commit_extend(plan)?;
            (extension.version, extension.changed)
        } else {
            (lower_base, false)
        };
        let (upper_parents, upper_changed) = if let Some(draft) = upper_draft {
            let plan = self
                .replay_parent_sets
                .preflight_extend(upper_base, draft, &self.bounds)?;
            let extension = self.replay_parent_sets.commit_extend(plan)?;
            (extension.version, extension.changed)
        } else {
            (upper_base, false)
        };

        let occurrence_id = if let Some(occurrence_id) = occurrence_id {
            if lower_changed || upper_changed {
                self.replay_occurrences.update_parent_versions(
                    occurrence_id,
                    lower_parents,
                    upper_parents,
                )?;
            }
            occurrence_id
        } else if lower_changed || upper_changed {
            self.replay_occurrences.try_insert(
                key,
                lower_parents,
                upper_parents,
                admission_ordinal,
            )?
        } else if inserted_parents.is_empty() {
            return Ok(ReplayResultSummaryDelta::default());
        } else {
            return Err(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex);
        };
        let summary_delta = self.replay_result_summary.try_record_admission(
            result,
            occurrence_id,
            replay,
            admission_ordinal,
            inserted_parents,
            &[
                (ReplayClaimParentSide::Lower, lower_parents, lower_changed),
                (ReplayClaimParentSide::Upper, upper_parents, upper_changed),
            ],
            &self.bounds,
        )?;
        Ok(summary_delta)
    }

    fn materialize_existing_claim_parents_delta(
        &mut self,
        result: ConstraintRecordId,
        target_record: Option<BoundRecordId>,
        parents: &[ClaimQualifiedParent],
        lower_carrier: ProjectionProofCarrier,
        replay_clause_work_precommitted: bool,
        mut publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        if let Some(record) = target_record
            && !parents.is_empty()
        {
            self.register_constraint_upper_replay_claims_delta(
                record,
                result,
                parents,
                replay_clause_work_precommitted,
                publication_fence.as_deref_mut(),
            );
        }
        if publication_fence.is_some() && self.replay_factored_terminal_failure().is_some() {
            return;
        }
        self.register_constraint_projection_carrier_delta_with_precommitted_clause_links(
            result,
            parents,
            lower_carrier,
            replay_clause_work_precommitted,
            publication_fence,
        );
    }

    /// Recompute every claim-parent consequence already attached to `result`.
    ///
    /// CDM-A keeps the current correct-but-expensive implementation as one named bulk reference
    /// point. The upper eager writers now use their delta path, while tests call this oracle to
    /// compare maintained state against the original full recomputation ground truth.
    #[cfg(test)]
    fn materialize_existing_claim_parents_bulk(
        &mut self,
        result: ConstraintRecordId,
        target_record: Option<BoundRecordId>,
    ) {
        if let Some(record) = target_record {
            self.register_constraint_upper_replay_claims(record, Some(result));
        }
        self.register_existing_constraint_lower_projection_proofs_bulk(result);
    }

    #[cfg(test)]
    pub(in crate::constraints) fn recompute_claim_parent_bulk_oracle(
        &mut self,
        result: ConstraintRecordId,
    ) {
        let target_record = self.var_var_upper_record_for_constraint(result);
        self.materialize_existing_claim_parents_bulk(result, target_record);
    }

    pub(in crate::constraints) fn register_reduction_route_claim_parent(
        &mut self,
        result: ConstraintRecordId,
        derivation: RowDerivationId,
        claim: UpperReplayClaimId,
    ) {
        if !self.constraint_records[result.0 as usize]
            .row_derivations
            .contains(&derivation)
        {
            return;
        }
        let parent = ClaimQualifiedParent::ReductionRouteConstraint {
            parent_claim: claim,
            derivation,
        };
        if self
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .is_some_and(|entries| entries.contains(&parent))
        {
            return;
        }
        let target_record = self.var_var_upper_record_for_constraint(result);
        let carrier = ProjectionProofCarrier::RowConstraint { result, derivation };
        let mut publication_fence = self.begin_non_replay_claim_parent_admission(
            result,
            &[parent],
            target_record,
            Some(carrier),
        );
        #[cfg(test)]
        proof::record_reduction_route_shadow(result, derivation, claim);
        if self.replay_factored_terminal_failure().is_some() {
            return;
        }
        self.materialize_existing_claim_parents_delta(
            result,
            target_record,
            &[parent],
            carrier,
            true,
            publication_fence.as_mut(),
        );
        self.finish_non_replay_claim_parent_admission(result, publication_fence);
    }

    fn var_var_upper_record_for_constraint(
        &self,
        result: ConstraintRecordId,
    ) -> Option<BoundRecordId> {
        let constraint = &self.constraint_records[result.0 as usize].key;
        let (Pos::Var(source), Neg::Var(_)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return None;
        };
        self.bounds
            .canonical
            .get(&BoundSemanticKey::Upper {
                owner: *source,
                endpoint: constraint.upper,
                weights: constraint.weights.clone(),
            })
            .copied()
    }

    fn check_and_erase_lower_left_filter(
        &mut self,
        pos: PosId,
        weights: ConstraintWeights,
        derivation: &BoundDerivation,
    ) -> ConstraintWeights {
        let filter = weights.left_filter_set().clone();
        if !matches!(filter, Subtractability::All) {
            let mut parents = Self::row_derivation_parents_from_bound(derivation);
            parents.extend(self.row_derivation_parents(
                None,
                &weights,
                SubtractFactUseRule::Filter,
            ));
            self.constrain_weighted_pos_lower_by_filter(pos, &weights, &filter, &parents);
        }
        weights.without_left_filter()
    }

    fn check_and_erase_upper_left_filter(
        &mut self,
        source: TypeVar,
        weights: ConstraintWeights,
        derivation: &BoundDerivation,
    ) -> ConstraintWeights {
        let filter = weights.left_filter_set().clone();
        if !matches!(filter, Subtractability::All) {
            let mut parents = Self::row_derivation_parents_from_bound(derivation);
            parents.extend(self.row_derivation_parents(
                None,
                &weights,
                SubtractFactUseRule::Filter,
            ));
            self.constrain_stack_by_filter(&weights.left.to_stack_weight(), &filter, &parents);
            self.constrain_type_var_lowers_by_filter(source, filter, parents);
        }
        weights.without_left_filter()
    }

    pub(crate) fn constrain_type_var_lowers_by_filter(
        &mut self,
        var: TypeVar,
        filter: Subtractability,
        parents: Vec<RowDerivationParent>,
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        let is_new = self
            .lower_filters
            .entry(var)
            .or_default()
            .insert(filter.clone());
        let filter_record = self.record_lower_filter_provenance(var, &filter, parents);
        if !is_new {
            return;
        }
        let lowers = self
            .bounds
            .of(var)
            .map(|bounds| {
                bounds
                    .lower_record_ids()
                    .iter()
                    .copied()
                    .zip(bounds.lowers().iter().cloned())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        for (record, lower) in lowers {
            let lower_parents = [
                RowDerivationParent::LowerFilter(filter_record),
                RowDerivationParent::Bound(record),
            ];
            self.constrain_weighted_pos_lower_by_filter(
                lower.pos,
                &lower.weights,
                &filter,
                &lower_parents,
            );
        }
    }

    fn record_lower_filter_provenance(
        &mut self,
        var: TypeVar,
        filter: &Subtractability,
        parents: Vec<RowDerivationParent>,
    ) -> LowerFilterRecordId {
        let key = (var, filter.clone());
        let id = if let Some(id) = self.lower_filter_record_ids.get(&key).copied() {
            id
        } else {
            let id = LowerFilterRecordId(self.lower_filter_records.len() as u32);
            self.lower_filter_record_ids.insert(key, id);
            self.lower_filter_records.push(LowerFilterRecord {
                var,
                filter: filter.clone(),
                derivations: Vec::new(),
            });
            id
        };
        let derivations = &mut self.lower_filter_records[id.0 as usize].derivations;
        let derivation = LowerFilterDerivation { parents };
        if !derivations.contains(&derivation) {
            derivations.push(derivation);
            self.bump_provenance_epoch();
        }
        id
    }

    fn constrain_lower_bound_by_registered_filters(
        &mut self,
        target: TypeVar,
        record: BoundRecordId,
        pos: PosId,
        weights: &ConstraintWeights,
    ) {
        let filters = self.lower_filters.get(&target).cloned().unwrap_or_default();
        for filter in filters {
            let filter_record = self.lower_filter_record_ids[&(target, filter.clone())];
            let parents = [
                RowDerivationParent::LowerFilter(filter_record),
                RowDerivationParent::Bound(record),
            ];
            self.constrain_weighted_pos_lower_by_filter(pos, weights, &filter, &parents);
        }
    }

    fn constrain_weighted_pos_lower_by_filter(
        &mut self,
        pos: PosId,
        weights: &ConstraintWeights,
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        self.constrain_stack_by_filter(&weights.left.to_stack_weight(), filter, parents);
        let filter = weights.left.filter_set().clone().intersect(filter.clone());
        self.constrain_pos_lower_by_filter(pos, &filter, parents);
    }

    pub(in crate::constraints) fn constrain_pos_lower_by_filter(
        &mut self,
        pos: PosId,
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        match self.types.pos(pos).clone() {
            Pos::Con(path, args) => {
                if self.effect_family_paths.contains(&path) {
                    self.constrain_effect_family_by_filter(&path, &args, filter, parents);
                }
            }
            Pos::Row(items) => {
                for item in items {
                    self.constrain_pos_lower_by_filter(item, filter, parents);
                }
            }
            Pos::Stack { inner, weight } => {
                self.constrain_stack_by_filter(&weight, filter, parents);
                self.constrain_pos_lower_by_filter(inner, filter, parents);
            }
            Pos::NonSubtract(inner, weight) => {
                self.constrain_stack_by_filter(&weight, filter, parents);
                self.constrain_pos_lower_by_filter(inner, filter, parents);
            }
            Pos::Union(left, right) => {
                self.constrain_pos_lower_by_filter(left, filter, parents);
                self.constrain_pos_lower_by_filter(right, filter, parents);
            }
            Pos::Var(var) => {
                self.constrain_type_var_lowers_by_filter(var, filter.clone(), parents.to_vec())
            }
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_) => {}
        }
    }

    fn lower_bound_replay_actions(
        &self,
        target: TypeVar,
        lower_record: BoundRecordId,
        pos: PosId,
        weights: &ConstraintWeights,
        incremental_routes: &[UnweightedRowReductionReplayRoute],
    ) -> BoundReplayPlan {
        let Some(bounds) = self.bounds.of(target) else {
            return BoundReplayPlan::default();
        };
        let uppers = bounds
            .projection_upper_records()
            .map(|(record, upper)| (record, upper.clone()))
            .collect::<Vec<_>>();
        let lower_claim_parents = self.lower_record_replay_claim_parents(lower_record);
        let decisions = uppers
            .iter()
            .map(|(record, _)| {
                let requires_generic = self.upper_record_requires_generic_replay(*record);
                let upper_claim_parents =
                    self.upper_record_replay_claim_parents(pos, *record, incremental_routes);
                let should_replay = requires_generic || !upper_claim_parents.is_empty();
                let mut claim_parents = lower_claim_parents.clone();
                claim_parents.extend(upper_claim_parents);
                (*record, (should_replay, claim_parents))
            })
            .collect::<FxHashMap<_, _>>();
        let replay_input_count = decisions
            .values()
            .filter(|(should_replay, _)| *should_replay)
            .count();
        let mut replay = BoundReplayPlan {
            input_count: replay_input_count,
            ..BoundReplayPlan::default()
        };
        trace_bound_replay_start("lower", target, replay_input_count);
        for (index, (upper_record, upper)) in uppers.into_iter().enumerate() {
            let (should_replay, claim_parents) = &decisions[&upper_record];
            if !should_replay {
                continue;
            }
            trace_bound_replay_progress("lower", target, index);
            let replay_weights = weights.compose_for_replay(&upper.weights);
            if self.is_var_var_replay(pos, upper.neg) {
                replay.var_var += 1;
            }
            replay.generated += 1;
            self.push_replay_constraint_or_prefilter(
                pos,
                replay_weights,
                upper.neg,
                BinaryReplayDerivation {
                    pivot: target,
                    lower: lower_record,
                    upper: upper_record,
                    rule: ReplayRule::LowerBoundAdded,
                },
                claim_parents.clone(),
                &mut replay,
            );
        }
        replay
    }

    fn lower_record_replay_claim_parents(&self, lower_record: BoundRecordId) -> ReplayClaimParents {
        self.bounds
            .scheme_projection_claims_by_lower_record
            .get(&lower_record)
            .into_iter()
            .flatten()
            .copied()
            .map(|claim| SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Lower,
            })
            .collect()
    }

    fn upper_record_replay_claim_parents(
        &self,
        lower: PosId,
        upper_record: BoundRecordId,
        incremental_routes: &[UnweightedRowReductionReplayRoute],
    ) -> ReplayClaimParents {
        let mut parents = self.uncovered_upper_replay_claim_parents(upper_record);
        if matches!(self.types.pos(lower), Pos::Var(_)) {
            for claim in self.bounds.covered_claims(upper_record) {
                let handled_by_incremental_route = incremental_routes
                    .iter()
                    .any(|route| route.upper_record == upper_record && route.claim == Some(claim));
                let parent = SideTaggedReplayClaim {
                    claim,
                    parent_side: ReplayClaimParentSide::Upper,
                };
                if !handled_by_incremental_route && !parents.contains(&parent) {
                    parents.push(parent);
                }
            }
        }
        parents
    }

    fn uncovered_upper_replay_claim_parents(
        &self,
        upper_record: BoundRecordId,
    ) -> ReplayClaimParents {
        self.bounds
            .uncovered_claims(upper_record)
            .into_iter()
            .map(|claim| SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Upper,
            })
            .collect()
    }

    fn upper_record_requires_generic_replay(&self, upper: BoundRecordId) -> bool {
        if self.bounds.record(upper).is_none() {
            return false;
        };
        self.bounds.claim_requires_generic_replay(upper)
    }

    fn merge_unweighted_row_route_provenance(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        derivation: RowDerivationId,
        parent_claim: Option<UpperReplayClaimId>,
    ) {
        let Some(key) = self.canonical_subtype_constraint(lower, weights, upper) else {
            return;
        };
        let Some(record) = self.canonical_constraints.get(&key).copied() else {
            return;
        };
        let derivation_inserted = !self.constraint_records[record.0 as usize]
            .row_derivations
            .contains(&derivation);
        if derivation_inserted {
            self.constraint_records[record.0 as usize]
                .row_derivations
                .push(derivation);
            self.bump_provenance_epoch();
        }
        if let Some(parent_claim) = parent_claim {
            self.register_reduction_route_claim_parent(record, derivation, parent_claim);
        } else if derivation_inserted {
            self.register_constraint_projection_carrier_delta(
                record,
                &[],
                ProjectionProofCarrier::RowConstraint {
                    result: record,
                    derivation,
                },
            );
        }
    }

    fn upper_bound_replay_actions(
        &self,
        source: TypeVar,
        upper_record: BoundRecordId,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> BoundReplayPlan {
        let Some(bounds) = self.bounds.of(source) else {
            return BoundReplayPlan::default();
        };
        let requires_generic = self.upper_record_requires_generic_replay(upper_record);
        let replay_input_count = if requires_generic {
            bounds.projection_lowers().count()
        } else {
            0
        };
        let mut replay = BoundReplayPlan {
            input_count: replay_input_count,
            ..BoundReplayPlan::default()
        };
        trace_bound_replay_start("upper", source, replay_input_count);
        if !requires_generic {
            return replay;
        }
        let upper_claim_parents = self.uncovered_upper_replay_claim_parents(upper_record);
        for (index, (lower_record, lower)) in bounds.projection_lower_records().enumerate() {
            let mut claim_parents = self.lower_record_replay_claim_parents(lower_record);
            claim_parents.extend(upper_claim_parents.iter().copied());
            trace_bound_replay_progress("upper", source, index);
            let replay_weights = lower.weights.compose_for_replay(weights);
            if self.is_var_var_replay(lower.pos, neg) {
                replay.var_var += 1;
            }
            replay.generated += 1;
            self.push_replay_constraint_or_prefilter(
                lower.pos,
                replay_weights,
                neg,
                BinaryReplayDerivation {
                    pivot: source,
                    lower: lower_record,
                    upper: upper_record,
                    rule: ReplayRule::UpperBoundAdded,
                },
                claim_parents,
                &mut replay,
            );
        }
        replay
    }

    fn push_replay_constraint_or_prefilter(
        &self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        derivation: BinaryReplayDerivation,
        claim_parents: ReplayClaimParents,
        replay: &mut BoundReplayPlan,
    ) {
        let (lower_parents, upper_parents) = if self.replay_factored_writes_enabled() {
            (
                replay.intern_parent_draft(&claim_parents, ReplayClaimParentSide::Lower),
                replay.intern_parent_draft(&claim_parents, ReplayClaimParentSide::Upper),
            )
        } else {
            (ReplayParentDraftId::EMPTY, ReplayParentDraftId::EMPTY)
        };
        let attempted = SubtypeConstraintKey {
            lower,
            upper,
            weights: weights.clone(),
        };
        let duplicate_profile = self.replay_duplicate_profile(lower, &weights, upper);
        let canonicalization_disposition =
            self.terminal_weight_erasure_disposition(lower, &weights, upper);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            #[cfg(test)]
            super::global_alpha_census::record_prefiltered_trivial();
            replay.prefiltered += 1;
            replay.stats.trivial += 1;
            replay.trivial_actions.push(BoundReplayAction {
                constraint: attempted,
                derivation,
                claim_parents,
                lower_parents,
                upper_parents,
                canonicalization_disposition,
            });
            return;
        };
        let seen_before = self.has_canonical_constraint(&constraint);
        self.observe_weighted_routing_consequence_shadow(&constraint, seen_before);
        if seen_before {
            #[cfg(test)]
            super::global_alpha_census::record_prefiltered_exact_duplicate();
            replay.prefiltered += 1;
            replay.stats.duplicate += 1;
            replay.prefilter_duplicate.absorb(duplicate_profile);
            replay.duplicate_actions.push(BoundReplayAction {
                constraint,
                derivation,
                claim_parents,
                lower_parents,
                upper_parents,
                canonicalization_disposition,
            });
            return;
        }
        if self.should_store_replay_as_evidence_only(&constraint) {
            replay.prefiltered += 1;
            replay.evidence_actions.push(BoundReplayAction {
                constraint,
                derivation,
                claim_parents,
                lower_parents,
                upper_parents,
                canonicalization_disposition,
            });
            return;
        }
        replay.actions.push(BoundReplayAction {
            constraint,
            derivation,
            claim_parents,
            lower_parents,
            upper_parents,
            canonicalization_disposition,
        });
    }

    fn replay_duplicate_profile(
        &self,
        lower: PosId,
        weights: &ConstraintWeights,
        upper: NegId,
    ) -> ReplayDuplicateProfile {
        let var_var_key = self.is_var_var_replay(lower, upper);
        let terminal_weight_erased =
            !weights.is_empty() && self.has_terminal_subtype_endpoint(lower, upper);
        ReplayDuplicateProfile {
            exact_key: usize::from(!var_var_key && !terminal_weight_erased),
            var_var_key: usize::from(var_var_key),
            terminal_weight_erased: usize::from(terminal_weight_erased),
            row_tail: usize::from(self.is_row_tail_replay_candidate(upper)),
        }
    }

    fn is_row_tail_replay_candidate(&self, upper: NegId) -> bool {
        matches!(
            self.types.neg(upper),
            Neg::Row(_, tail) if matches!(self.types.neg(*tail), Neg::Var(_))
        )
    }

    fn observe_lower_replay_frontier_shadow(
        &mut self,
        pivot: TypeVar,
        pos: PosId,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        if self.replay_frontier_shadow.is_none() {
            return ReplayFrontierShadowObservation::NotCandidate;
        }
        let Pos::Var(endpoint) = self.types.pos(pos) else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        let Some(shadow) = self.replay_frontier_shadow.as_mut() else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        shadow.observe_lower_var_var(pivot, *endpoint, weights)
    }

    fn observe_upper_replay_frontier_shadow(
        &mut self,
        pivot: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        if self.replay_frontier_shadow.is_none() {
            return ReplayFrontierShadowObservation::NotCandidate;
        }
        let Neg::Var(endpoint) = self.types.neg(neg) else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        let Some(shadow) = self.replay_frontier_shadow.as_mut() else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        shadow.observe_upper_var_var(pivot, *endpoint, weights)
    }

    fn record_lower_replay_frontier_shadow(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        if let Some(shadow) = &mut self.replay_frontier_shadow {
            shadow.record_lower_result(observation, accepted);
        }
    }

    fn record_upper_replay_frontier_shadow(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        if let Some(shadow) = &mut self.replay_frontier_shadow {
            shadow.record_upper_result(observation, accepted);
        }
    }

    fn observe_weighted_routing_consequence_shadow(
        &self,
        constraint: &SubtypeConstraintKey,
        seen_before: bool,
    ) {
        let Some(shadow) = &self.replay_routing_shadow else {
            return;
        };
        let (Pos::Var(source), Neg::Var(target)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return;
        };
        shadow.borrow_mut().observe_var_var_consequence(
            *source,
            *target,
            &constraint.weights,
            seen_before,
        );
    }

    fn should_store_replay_as_evidence_only(&self, constraint: &SubtypeConstraintKey) -> bool {
        if !evidence_only_replay_skip_enabled() {
            return false;
        }
        let Some(shadow) = &self.replay_routing_shadow else {
            return false;
        };
        let (Pos::Var(source), Neg::Var(target)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return false;
        };
        shadow
            .borrow_mut()
            .has_weighted_frontier_path(*source, *target, &constraint.weights)
    }

    #[cfg(test)]
    fn apply_bound_replay_actions(&mut self, actions: BoundReplayActions) -> BoundReplayApplyStats {
        assert!(
            matches!(
                self.replay_read_authority(),
                ReplayReadAuthority::LegacyRollback(_)
            ),
            "the legacy-only replay-action helper requires LegacyRollback authority"
        );
        self.apply_bound_replay_actions_impl(actions, None)
    }

    fn apply_bound_replay_actions_with_parent_drafts(
        &mut self,
        actions: BoundReplayActions,
        parent_drafts: &[ReplayParentDraft],
    ) -> BoundReplayApplyStats {
        self.apply_bound_replay_actions_impl(actions, Some(parent_drafts))
    }

    fn apply_bound_replay_actions_impl(
        &mut self,
        actions: BoundReplayActions,
        parent_drafts: Option<&[ReplayParentDraft]>,
    ) -> BoundReplayApplyStats {
        let mut stats = BoundReplayApplyStats::default();
        for action in actions {
            let constraint = action.constraint.clone();
            let (enqueued, disposition) =
                self.enqueue_replay_subtype(action.constraint, action.derivation);
            if disposition != ReplayDerivationInsert::Incomplete {
                let result = self.canonical_constraints[&constraint];
                self.register_replay_claim_parents_with_factored_drafts(
                    result,
                    action.derivation,
                    &action.claim_parents,
                    !enqueued,
                    parent_drafts.map(|parent_drafts| FactoredReplayParentDrafts {
                        parent_drafts,
                        lower: action.lower_parents,
                        upper: action.upper_parents,
                    }),
                );
            }
            #[cfg(test)]
            proof::record_replay_admission_shadow(
                self.canonical_constraints.get(&constraint).copied(),
                action.derivation,
                match (enqueued, disposition) {
                    (_, ReplayDerivationInsert::Incomplete) => {
                        proof::ReplayAdmissionDisposition::Incomplete
                    }
                    (true, _) => proof::ReplayAdmissionDisposition::NewSemantic,
                    (false, ReplayDerivationInsert::Inserted) => {
                        proof::ReplayAdmissionDisposition::CanonicalDuplicate
                    }
                    (false, ReplayDerivationInsert::Duplicate) => {
                        proof::ReplayAdmissionDisposition::ExactDuplicate
                    }
                },
            );
            self.merge_constraint_canonicalization_disposition(
                &constraint,
                action.canonicalization_disposition,
            );
            self.timing.record_replay_derivation_edge(
                disposition == ReplayDerivationInsert::Inserted,
                disposition == ReplayDerivationInsert::Duplicate,
                disposition == ReplayDerivationInsert::Incomplete,
                !enqueued,
            );
            if enqueued {
                #[cfg(test)]
                super::global_alpha_census::record_accepted_consequence(
                    self,
                    &constraint,
                    action.derivation,
                );
                stats.accepted += 1;
            } else {
                #[cfg(test)]
                super::global_alpha_census::record_delayed_exact_duplicate();
                stats.duplicate += 1;
            }
        }
        stats
    }

    fn apply_bound_replay_evidence_actions(&mut self, actions: BoundReplayActions) {
        for action in actions {
            let constraint = action.constraint;
            let (source, target) = match (
                self.types.pos(constraint.lower),
                self.types.neg(constraint.upper),
            ) {
                (Pos::Var(source), Neg::Var(target)) => (*source, *target),
                _ => continue,
            };
            let replay_derivation = BoundDerivation::ReplayEvidence(action.derivation);
            let lower_key = BoundSemanticKey::Lower {
                owner: target,
                endpoint: constraint.lower,
                weights: constraint.weights.clone(),
            };
            let upper_key = BoundSemanticKey::Upper {
                owner: source,
                endpoint: constraint.upper,
                weights: constraint.weights.clone(),
            };
            let lower_derivation_new = !self
                .bounds
                .contains_derivation(&lower_key, &replay_derivation);
            let upper_derivation_new = !self
                .bounds
                .contains_derivation(&upper_key, &replay_derivation);
            let evidence_bytes = std::mem::size_of::<BinaryReplayDerivation>()
                * (usize::from(lower_derivation_new) + usize::from(upper_derivation_new));
            let evidence_complete = self.replay_derivation_session_budget_allows(evidence_bytes);
            if evidence_complete {
                self.charge_replay_derivation_bytes(evidence_bytes);
            } else {
                self.record_replay_budget_drop(None);
            }
            let lower_derivation = if evidence_complete || !lower_derivation_new {
                replay_derivation.clone()
            } else {
                BoundDerivation::IncompleteReplay
            };
            let lower_projection_carrier = match &lower_derivation {
                BoundDerivation::ReplayEvidence(replay) => {
                    ProjectionProofCarrier::ReplayEvidence(*replay)
                }
                BoundDerivation::IncompleteReplay => ProjectionProofCarrier::Incomplete,
                _ => unreachable!("evidence lower uses replay or incomplete provenance"),
            };
            let upper_derivation = if evidence_complete || !upper_derivation_new {
                replay_derivation
            } else {
                BoundDerivation::IncompleteReplay
            };
            let insertion = self.bounds.add_evidence_lower(
                target,
                constraint.lower,
                constraint.weights.clone(),
                lower_derivation,
            );
            let lower_record = insertion.id;
            let lower_edge_inserted = insertion.provenance_changed;
            self.record_bound_provenance(insertion, BoundDirection::Lower, true);
            if insertion.semantic_changed {
                self.timing.record_evidence_lower_bound_added();
                self.record_effective_bounds_mutation(target);
            }
            let insertion = self.bounds.add_evidence_upper(
                source,
                constraint.upper,
                constraint.weights,
                upper_derivation,
            );
            let upper_record = insertion.id;
            let upper_edge_inserted = insertion.provenance_changed;
            self.record_bound_provenance(insertion, BoundDirection::Upper, true);
            if insertion.semantic_changed {
                self.timing.record_evidence_upper_bound_added();
                self.record_effective_bounds_mutation(source);
            }
            #[cfg(test)]
            {
                proof::record_replay_admission_shadow(
                    None,
                    action.derivation,
                    if evidence_complete {
                        proof::ReplayAdmissionDisposition::EvidenceOnly
                    } else {
                        proof::ReplayAdmissionDisposition::Incomplete
                    },
                );
                if evidence_complete && lower_edge_inserted {
                    proof::record_replay_evidence_shadow(lower_record, action.derivation);
                }
                if evidence_complete && upper_edge_inserted {
                    proof::record_replay_evidence_shadow(upper_record, action.derivation);
                }
            }
            if evidence_complete {
                for parent in action.claim_parents {
                    let producer = self.bounds.upper_replay_claims[parent.claim.0 as usize]
                        .producer_constraint;
                    let registration = self.bounds.derived_upper_replay_claim(
                        upper_record,
                        parent.claim,
                        producer,
                        |depth| UpperReplayClaimLineage::ReplayEvidence {
                            parent_claim: parent.claim,
                            parent_side: parent.parent_side,
                            replay: action.derivation,
                            depth,
                        },
                    );
                    self.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
                    self.register_replay_evidence_clause_link(
                        lower_record,
                        parent.claim,
                        action.derivation,
                    );
                }
            }
            if lower_edge_inserted {
                self.register_lower_record_projection_carrier_delta(
                    lower_record,
                    lower_projection_carrier,
                );
            }
            self.timing.record_replay_derivation_edge(
                evidence_complete && (lower_edge_inserted || upper_edge_inserted),
                evidence_complete && !(lower_edge_inserted || upper_edge_inserted),
                !evidence_complete,
                false,
            );
        }
    }

    #[cfg(test)]
    fn apply_prefiltered_replay_provenance(
        &mut self,
        duplicates: BoundReplayActions,
        trivial: BoundReplayActions,
    ) {
        assert!(
            matches!(
                self.replay_read_authority(),
                ReplayReadAuthority::LegacyRollback(_)
            ),
            "the legacy-only prefiltered-replay helper requires LegacyRollback authority"
        );
        self.apply_prefiltered_replay_provenance_impl(duplicates, trivial, None);
    }

    fn apply_prefiltered_replay_provenance_with_parent_drafts(
        &mut self,
        duplicates: BoundReplayActions,
        trivial: BoundReplayActions,
        parent_drafts: &[ReplayParentDraft],
    ) {
        self.apply_prefiltered_replay_provenance_impl(duplicates, trivial, Some(parent_drafts));
    }

    fn apply_prefiltered_replay_provenance_impl(
        &mut self,
        duplicates: BoundReplayActions,
        trivial: BoundReplayActions,
        parent_drafts: Option<&[ReplayParentDraft]>,
    ) {
        for action in duplicates {
            let result = *self
                .canonical_constraints
                .get(&action.constraint)
                .expect("prefiltered replay duplicate remains canonical");
            let disposition = self.merge_replay_derivation(result, action.derivation);
            if disposition != ReplayDerivationInsert::Incomplete {
                self.register_replay_claim_parents_with_factored_drafts(
                    result,
                    action.derivation,
                    &action.claim_parents,
                    true,
                    parent_drafts.map(|parent_drafts| FactoredReplayParentDrafts {
                        parent_drafts,
                        lower: action.lower_parents,
                        upper: action.upper_parents,
                    }),
                );
            }
            #[cfg(test)]
            proof::record_replay_admission_shadow(
                Some(result),
                action.derivation,
                match disposition {
                    ReplayDerivationInsert::Inserted => {
                        proof::ReplayAdmissionDisposition::CanonicalDuplicate
                    }
                    ReplayDerivationInsert::Duplicate => {
                        proof::ReplayAdmissionDisposition::ExactDuplicate
                    }
                    ReplayDerivationInsert::Incomplete => {
                        proof::ReplayAdmissionDisposition::Incomplete
                    }
                },
            );
            self.merge_constraint_canonicalization_disposition(
                &action.constraint,
                action.canonicalization_disposition,
            );
            self.timing.record_replay_derivation_edge(
                disposition == ReplayDerivationInsert::Inserted,
                disposition == ReplayDerivationInsert::Duplicate,
                disposition == ReplayDerivationInsert::Incomplete,
                true,
            );
        }
        for action in trivial {
            let drop = ReplayDropRecord {
                attempted: action.constraint,
                derivation: action.derivation,
            };
            let disposition = self.intern_replay_drop(drop.clone());
            #[cfg(test)]
            {
                proof::record_replay_admission_shadow(
                    None,
                    action.derivation,
                    match disposition {
                        ReplayDerivationInsert::Inserted => {
                            proof::ReplayAdmissionDisposition::Trivial
                        }
                        ReplayDerivationInsert::Duplicate => {
                            proof::ReplayAdmissionDisposition::ExactDuplicate
                        }
                        ReplayDerivationInsert::Incomplete => {
                            proof::ReplayAdmissionDisposition::Incomplete
                        }
                    },
                );
                if disposition == ReplayDerivationInsert::Inserted {
                    let id = self.replay_drop_index[&drop];
                    proof::record_replay_drop_shadow(id, drop);
                }
            }
            self.timing.record_replay_derivation_edge(
                disposition == ReplayDerivationInsert::Inserted,
                disposition == ReplayDerivationInsert::Duplicate,
                disposition == ReplayDerivationInsert::Incomplete,
                false,
            );
        }
    }

    #[cfg(test)]
    pub(in crate::constraints) fn apply_cpk_trivial_replay_for_test(
        &mut self,
        attempted: SubtypeConstraintKey,
        derivation: BinaryReplayDerivation,
    ) {
        let mut replay = BoundReplayPlan::default();
        self.push_replay_constraint_or_prefilter(
            attempted.lower,
            attempted.weights.clone(),
            attempted.upper,
            derivation,
            ReplayClaimParents::new(),
            &mut replay,
        );
        assert_eq!(replay.trivial_actions.len(), 1);
        assert!(replay.duplicate_actions.is_empty());
        self.apply_prefiltered_replay_provenance_with_parent_drafts(
            replay.duplicate_actions,
            replay.trivial_actions,
            &replay.parent_drafts,
        );
    }

    #[cfg(test)]
    pub(in crate::constraints) fn apply_cpk_evidence_only_replay_for_test(
        &mut self,
        constraint: SubtypeConstraintKey,
        derivation: BinaryReplayDerivation,
    ) {
        let mut actions = BoundReplayActions::new();
        actions.push(BoundReplayAction {
            constraint,
            derivation,
            claim_parents: ReplayClaimParents::new(),
            lower_parents: ReplayParentDraftId::EMPTY,
            upper_parents: ReplayParentDraftId::EMPTY,
            canonicalization_disposition: None,
        });
        self.apply_bound_replay_evidence_actions(actions);
    }

    #[cfg(test)]
    pub(in crate::constraints) fn apply_cpk_replay_parent_arrival_for_test(
        &mut self,
        result: ConstraintRecordId,
        derivation: BinaryReplayDerivation,
        claim: UpperReplayClaimId,
    ) {
        let constraint = self.constraint_records[result.0 as usize].key.clone();
        let mut replay = BoundReplayPlan::default();
        self.push_replay_constraint_or_prefilter(
            constraint.lower,
            constraint.weights,
            constraint.upper,
            derivation,
            ReplayClaimParents::from_iter([SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Lower,
            }]),
            &mut replay,
        );
        assert_eq!(replay.duplicate_actions.len(), 1);
        assert!(replay.trivial_actions.is_empty());
        self.apply_prefiltered_replay_provenance_with_parent_drafts(
            replay.duplicate_actions,
            replay.trivial_actions,
            &replay.parent_drafts,
        );
    }

    pub(in crate::constraints) fn is_var_var_replay(&self, lower: PosId, upper: NegId) -> bool {
        matches!(self.types.pos(lower), Pos::Var(_)) && matches!(self.types.neg(upper), Neg::Var(_))
    }

    pub(in crate::constraints) fn upper_bound_subsumed_by_existing(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> Option<BoundRecordId> {
        if !weights.is_empty() {
            return None;
        }
        let Some(bounds) = self.bounds.of(source) else {
            return None;
        };
        if self.source_has_row_tail_boundary(source) {
            return bounds
                .uppers()
                .iter()
                .zip(bounds.upper_record_ids())
                .find_map(|(upper, id)| {
                    (upper.weights.is_empty() && upper.neg == neg).then_some(*id)
                });
        }
        let Neg::Row(_, tail) = self.types.neg(neg) else {
            return bounds
                .uppers()
                .iter()
                .zip(bounds.upper_record_ids())
                .find_map(|(upper, id)| {
                    (upper.weights.is_empty() && upper.neg == neg).then_some(*id)
                });
        };
        bounds
            .uppers()
            .iter()
            .zip(bounds.upper_record_ids())
            .find_map(|(upper, id)| {
                (upper.weights.is_empty() && self.neg_ids_match_for_row_tail(upper.neg, *tail))
                    .then_some(*id)
            })
    }

    fn lower_var_alias_replay_cycle_subsumed(
        &self,
        target: TypeVar,
        pos: PosId,
        weights: &ConstraintWeights,
    ) -> Option<BoundRecordId> {
        if !matches!(self.types.pos(pos), Pos::Var(_))
            || alias_replay_cycle_weight_key(weights).is_none()
        {
            return None;
        }
        self.bounds.of(target).and_then(|bounds| {
            bounds
                .lowers()
                .iter()
                .zip(bounds.lower_record_ids())
                .find_map(|(lower, id)| {
                    (lower.pos == pos && alias_replay_cycle_weights_match(&lower.weights, weights))
                        .then_some(*id)
                })
        })
    }

    fn upper_var_alias_replay_cycle_subsumed(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> Option<BoundRecordId> {
        if !matches!(self.types.neg(neg), Neg::Var(_))
            || alias_replay_cycle_weight_key(weights).is_none()
        {
            return None;
        }
        self.bounds.of(source).and_then(|bounds| {
            bounds
                .uppers()
                .iter()
                .zip(bounds.upper_record_ids())
                .find_map(|(upper, id)| {
                    (upper.neg == neg && alias_replay_cycle_weights_match(&upper.weights, weights))
                        .then_some(*id)
                })
        })
    }

    pub(in crate::constraints) fn prune_upper_rows_subsumed_by(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> Vec<BoundRecordId> {
        if !weights.is_empty() {
            return Vec::new();
        }
        if self.source_has_row_tail_boundary(source) {
            return Vec::new();
        }
        self.prune_upper_rows_subsumed_by_reduced_upper(source, neg)
    }

    pub(in crate::constraints) fn prune_upper_rows_subsumed_by_reduced_upper(
        &mut self,
        source: TypeVar,
        neg: NegId,
    ) -> Vec<BoundRecordId> {
        let TypeBounds { vars, records, .. } = &mut self.bounds;
        let Some(bounds) = vars
            .get_mut(source.0 as usize)
            .and_then(|bounds| bounds.as_mut())
        else {
            return Vec::new();
        };
        let mut removed = Vec::new();
        let old_uppers = std::mem::take(&mut bounds.uppers);
        let old_ids = std::mem::take(&mut bounds.upper_ids);
        for (id, upper) in old_ids.into_iter().zip(old_uppers) {
            let keep = !upper.weights.is_empty() || !row_tail_matches(&self.types, upper.neg, neg);
            if keep {
                bounds.upper_ids.push(id);
                bounds.uppers.push(upper);
            } else {
                removed.push((id, upper.neg));
                records[id.0 as usize].state = BoundRecordState::Tombstone;
            }
        }
        let bounds_changed = !removed.is_empty();
        for (_, upper) in &removed {
            self.unrecord_neg_bound_var_neighbors(source, *upper);
        }
        if bounds_changed {
            self.bump_role_solve_supplemental_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintBounds(source));
            }
        }
        removed.into_iter().map(|(id, _)| id).collect()
    }

    pub(in crate::constraints) fn record_pos_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        pos: PosId,
    ) {
        match self.types.pos(pos) {
            Pos::Bot => return,
            Pos::Var(var) => {
                self.record_var_neighbor(source, *var);
                return;
            }
            Pos::Con(_, args) if args.is_empty() => return,
            _ => {}
        }
        let mut vars = FxHashSet::default();
        collect_pos_id_vars(&self.types, pos, &mut vars);
        self.record_bound_var_neighbors(source, vars);
    }

    pub(in crate::constraints) fn record_neg_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        neg: NegId,
    ) {
        match self.types.neg(neg) {
            Neg::Top | Neg::Bot => return,
            Neg::Var(var) => {
                self.record_var_neighbor(source, *var);
                return;
            }
            Neg::Con(_, args) if args.is_empty() => return,
            _ => {}
        }
        let mut vars = FxHashSet::default();
        collect_neg_id_vars(&self.types, neg, &mut vars);
        self.record_bound_var_neighbors(source, vars);
    }

    pub(in crate::constraints) fn unrecord_neg_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        neg: NegId,
    ) {
        match self.types.neg(neg) {
            Neg::Top | Neg::Bot => return,
            Neg::Var(var) => {
                self.unrecord_var_neighbor(source, *var);
                return;
            }
            Neg::Con(_, args) if args.is_empty() => return,
            _ => {}
        }
        let mut vars = FxHashSet::default();
        collect_neg_id_vars(&self.types, neg, &mut vars);
        self.unrecord_bound_var_neighbors(source, vars);
    }

    fn record_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        vars: impl IntoIterator<Item = TypeVar>,
    ) {
        for var in vars {
            self.record_var_neighbor(source, var);
        }
    }

    fn unrecord_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        vars: impl IntoIterator<Item = TypeVar>,
    ) {
        for var in vars {
            self.unrecord_var_neighbor(source, var);
        }
    }

    fn record_var_neighbor(&mut self, left: TypeVar, right: TypeVar) {
        if left == right {
            return;
        }
        if !self.method_role_mutations.is_active() {
            increment_var_neighbor(&mut self.var_adjacency, left, right);
            increment_var_neighbor(&mut self.var_adjacency, right, left);
            return;
        }
        let left_transition =
            increment_var_neighbor_recording_transition(&mut self.var_adjacency, left, right);
        let right_transition =
            increment_var_neighbor_recording_transition(&mut self.var_adjacency, right, left);
        if left_transition != right_transition {
            self.method_role_mutations.invalidate_all(
                InvalidateAllReason::AuditFenceDisagreement {
                    site: "record_var_neighbor symmetry",
                },
            );
            return;
        }
        if left_transition {
            self.method_role_mutations.record_many([
                DependencyKey::ConstraintNeighbors(left),
                DependencyKey::ConstraintNeighbors(right),
            ]);
        }
    }

    fn unrecord_var_neighbor(&mut self, left: TypeVar, right: TypeVar) {
        if left == right {
            return;
        }
        let left_transition = decrement_var_neighbor(&mut self.var_adjacency, left, right);
        let right_transition = decrement_var_neighbor(&mut self.var_adjacency, right, left);
        if !self.method_role_mutations.is_active() {
            return;
        }
        if left_transition != right_transition {
            self.method_role_mutations.invalidate_all(
                InvalidateAllReason::AuditFenceDisagreement {
                    site: "unrecord_var_neighbor symmetry",
                },
            );
            return;
        }
        if left_transition {
            self.method_role_mutations.record_many([
                DependencyKey::ConstraintNeighbors(left),
                DependencyKey::ConstraintNeighbors(right),
            ]);
        }
    }

    fn neg_ids_match_for_row_tail(&self, lhs: NegId, rhs: NegId) -> bool {
        neg_ids_match_for_row_tail(&self.types, lhs, rhs)
    }

    fn source_has_row_tail_boundary(&self, source: TypeVar) -> bool {
        !self.pre_pop_effect_families(source).is_empty()
            || self.bounds.of(source).is_some_and(|bounds| {
                bounds
                    .lowers()
                    .iter()
                    .any(|lower| constraint_weights_have_row_tail_boundary(&lower.weights))
            })
    }

    pub(in crate::constraints) fn extrude_pos(&mut self, pos: PosId, target: TypeLevel) -> PosId {
        match self.types.pos(pos) {
            Pos::Bot => return pos,
            Pos::Var(var) if self.level_of(*var) <= target => return pos,
            Pos::Con(_, args) if args.is_empty() => return pos,
            _ => {}
        }
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_pos_id(pos, &mut ctx);
        pos
    }

    pub(in crate::constraints) fn extrude_neg(&mut self, neg: NegId, target: TypeLevel) -> NegId {
        match self.types.neg(neg) {
            Neg::Top | Neg::Bot => return neg,
            Neg::Var(var) if self.level_of(*var) <= target => return neg,
            Neg::Con(_, args) if args.is_empty() => return neg,
            _ => {}
        }
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_neg_id(neg, &mut ctx);
        neg
    }

    pub(in crate::constraints) fn extrude_pos_id(&mut self, id: PosId, ctx: &mut ExtrudeCtx) {
        if !ctx.visited_pos.insert(id) {
            return;
        }
        match self.types.pos(id).clone() {
            Pos::Bot => {}
            Pos::Var(var) => self.extrude_type_var(var, ctx),
            Pos::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neg_id(arg, ctx);
                self.extrude_neg_id(arg_eff, ctx);
                self.extrude_pos_id(ret_eff, ctx);
                self.extrude_pos_id(ret, ctx);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
                self.extrude_pos_id(tail, ctx);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.extrude_pos_id(tail, ctx);
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_pos_id(payload, ctx);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.extrude_pos_id(item, ctx);
                }
            }
            Pos::Stack { inner, .. } => self.extrude_pos_id(inner, ctx),
            Pos::NonSubtract(pos, _) => self.extrude_pos_id(pos, ctx),
            Pos::Union(left, right) => {
                self.extrude_pos_id(left, ctx);
                self.extrude_pos_id(right, ctx);
            }
        }
    }

    pub(in crate::constraints) fn extrude_neg_id(&mut self, id: NegId, ctx: &mut ExtrudeCtx) {
        if !ctx.visited_neg.insert(id) {
            return;
        }
        match self.types.neg(id).clone() {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => self.extrude_type_var(var, ctx),
            Neg::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_pos_id(arg, ctx);
                self.extrude_pos_id(arg_eff, ctx);
                self.extrude_neg_id(ret_eff, ctx);
                self.extrude_neg_id(ret, ctx);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.extrude_neg_id(field.value, ctx);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neg_id(payload, ctx);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
                self.extrude_neg_id(tail, ctx);
            }
            Neg::Stack { inner, .. } => self.extrude_neg_id(inner, ctx),
            Neg::Intersection(left, right) => {
                self.extrude_neg_id(left, ctx);
                self.extrude_neg_id(right, ctx);
            }
        }
    }

    pub(in crate::constraints) fn extrude_neu_ids(
        &mut self,
        ids: Vec<NeuId>,
        ctx: &mut ExtrudeCtx,
    ) {
        for id in ids {
            self.extrude_neu_id(id, ctx);
        }
    }

    pub(in crate::constraints) fn extrude_neu_id(&mut self, id: NeuId, ctx: &mut ExtrudeCtx) {
        if !ctx.visited_neu.insert(id) {
            return;
        }
        match self.types.neu(id).clone() {
            Neu::Bounds(lower, upper) => {
                self.extrude_pos_id(lower, ctx);
                self.extrude_neg_id(upper, ctx);
            }
            Neu::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neu_id(arg, ctx);
                self.extrude_neu_id(arg_eff, ctx);
                self.extrude_neu_id(ret_eff, ctx);
                self.extrude_neu_id(ret, ctx);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.extrude_neu_id(field.value, ctx);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neu_id(payload, ctx);
                    }
                }
            }
            Neu::Tuple(items) => self.extrude_neu_ids(items, ctx),
        }
    }

    pub(in crate::constraints) fn extrude_type_var(&mut self, var: TypeVar, ctx: &mut ExtrudeCtx) {
        if self.level_of(var) <= ctx.target {
            return;
        }
        if !ctx.visited.insert(var) {
            return;
        }
        let level_lowered = self.levels.lower_to(var, ctx.target);
        if level_lowered {
            self.bump_role_solve_supplemental_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintLevel(var));
            }
        }
        let bounds = self
            .bounds
            .of(var)
            .map(|bounds| (bounds.lowers.clone(), bounds.uppers.clone()));
        if let Some((lowers, uppers)) = bounds {
            for lower in lowers {
                self.extrude_pos_id(lower.pos, ctx);
            }
            for upper in uppers {
                self.extrude_neg_id(upper.neg, ctx);
            }
        }
    }
}

#[cfg(test)]
mod mutation_tests {
    use super::*;

    fn legacy_rollback_test_authority() -> ReplayReadAuthority {
        ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure::AllocationFailed)
    }

    fn replay_plan_actions(replay: &BoundReplayPlan) -> impl Iterator<Item = &BoundReplayAction> {
        replay
            .actions
            .iter()
            .chain(&replay.evidence_actions)
            .chain(&replay.duplicate_actions)
            .chain(&replay.trivial_actions)
    }

    fn assert_parent_drafts_match_legacy(replay: &BoundReplayPlan) {
        for action in replay_plan_actions(replay) {
            for (side, draft_id) in [
                (ReplayClaimParentSide::Lower, action.lower_parents),
                (ReplayClaimParentSide::Upper, action.upper_parents),
            ] {
                let expected = action
                    .claim_parents
                    .iter()
                    .filter(|parent| parent.parent_side == side)
                    .map(|parent| parent.claim)
                    .collect::<Vec<_>>();
                let actual = if draft_id == ReplayParentDraftId::EMPTY {
                    &[][..]
                } else {
                    replay
                        .parent_draft(draft_id)
                        .expect("action draft ID belongs to its replay plan")
                        .claims
                        .as_ref()
                };
                assert_eq!(actual, expected);
            }
        }
    }

    #[test]
    fn replay_plan_parent_drafts_match_legacy_parent_order() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let target = TypeVar(1);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        let derivation = BinaryReplayDerivation {
            pivot: target,
            lower: BoundRecordId(20),
            upper: BoundRecordId(21),
            rule: ReplayRule::LowerBoundAdded,
        };
        let claim_parents = ReplayClaimParents::from_iter([
            SideTaggedReplayClaim {
                claim: UpperReplayClaimId(30),
                parent_side: ReplayClaimParentSide::Lower,
            },
            SideTaggedReplayClaim {
                claim: UpperReplayClaimId(31),
                parent_side: ReplayClaimParentSide::Lower,
            },
            SideTaggedReplayClaim {
                claim: UpperReplayClaimId(40),
                parent_side: ReplayClaimParentSide::Upper,
            },
            SideTaggedReplayClaim {
                claim: UpperReplayClaimId(41),
                parent_side: ReplayClaimParentSide::Upper,
            },
        ]);
        let mut replay = BoundReplayPlan::default();

        machine.push_replay_constraint_or_prefilter(
            lower,
            ConstraintWeights::empty(),
            upper,
            derivation,
            claim_parents.clone(),
            &mut replay,
        );

        let mut actions = replay_plan_actions(&replay);
        let action = actions.next().expect("planning retains one replay action");
        assert!(actions.next().is_none());
        assert_eq!(action.claim_parents, claim_parents);
        assert_eq!(
            replay
                .parent_draft(action.lower_parents)
                .expect("non-empty lower draft")
                .claims
                .as_ref(),
            &[UpperReplayClaimId(30), UpperReplayClaimId(31)]
        );
        assert_eq!(
            replay
                .parent_draft(action.upper_parents)
                .expect("non-empty upper draft")
                .claims
                .as_ref(),
            &[UpperReplayClaimId(40), UpperReplayClaimId(41)]
        );
        let first_draft_ids = (action.lower_parents, action.upper_parents);
        drop(actions);

        machine.push_replay_constraint_or_prefilter(
            lower,
            ConstraintWeights::empty(),
            upper,
            BinaryReplayDerivation {
                rule: ReplayRule::UpperBoundAdded,
                ..derivation
            },
            claim_parents,
            &mut replay,
        );

        assert_eq!(replay.parent_drafts.len(), 2);
        assert_eq!(replay_plan_actions(&replay).count(), 2);
        for action in replay_plan_actions(&replay) {
            assert_eq!(
                (action.lower_parents, action.upper_parents),
                first_draft_ids
            );
        }
        assert_parent_drafts_match_legacy(&replay);
    }

    #[test]
    fn lower_and_upper_replay_planning_capture_legacy_parent_drafts() {
        let mut machine = ConstraintMachine::new();
        let pivot = TypeVar(0);
        let lower_parent_owner = TypeVar(1);
        let lower = machine.alloc_pos(Pos::Var(TypeVar(2)));
        let upper = machine.alloc_neg(Neg::Var(TypeVar(3)));
        let origin = OriginId::unknown_internal();
        let lower_record = machine
            .bounds
            .add_lower(
                pivot,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let upper_record = machine
            .bounds
            .add_upper(
                pivot,
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let lower_parent_record = machine
            .bounds
            .add_upper(
                lower_parent_owner,
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let lower_parent = machine
            .bounds
            .original_upper_replay_claim(
                lower_parent_record,
                ConstraintRecordId(10_000),
                UpperReplayClaimKind::Direct,
            )
            .claim;
        let upper_parent = machine
            .bounds
            .original_upper_replay_claim(
                upper_record,
                ConstraintRecordId(10_001),
                UpperReplayClaimKind::Direct,
            )
            .claim;
        machine
            .bounds
            .scheme_projection_claims_by_lower_record
            .insert(lower_record, vec![lower_parent]);

        let lower_plan = machine.lower_bound_replay_actions(
            pivot,
            lower_record,
            lower,
            &ConstraintWeights::empty(),
            &[],
        );
        let upper_plan = machine.upper_bound_replay_actions(
            pivot,
            upper_record,
            upper,
            &ConstraintWeights::empty(),
        );

        for replay in [&lower_plan, &upper_plan] {
            assert_eq!(replay_plan_actions(replay).count(), 1);
            let action = replay_plan_actions(replay)
                .next()
                .expect("the lower/upper pairing is planned");
            assert_eq!(
                action.claim_parents.as_slice(),
                &[
                    SideTaggedReplayClaim {
                        claim: lower_parent,
                        parent_side: ReplayClaimParentSide::Lower,
                    },
                    SideTaggedReplayClaim {
                        claim: upper_parent,
                        parent_side: ReplayClaimParentSide::Upper,
                    },
                ]
            );
            assert_parent_drafts_match_legacy(replay);
        }
    }

    type ReplayParentOracleKey = (
        ConstraintRecordId,
        UpperReplayClaimId,
        ReplayClaimParentSide,
        BinaryReplayDerivation,
    );

    fn register_factored_parent_snapshot(
        machine: &mut ConstraintMachine,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
    ) {
        register_factored_parent_snapshot_with_materialization(
            machine, result, replay, parents, true,
        );
    }

    fn register_factored_parent_snapshot_with_materialization(
        machine: &mut ConstraintMachine,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
        materialize_existing_target: bool,
    ) {
        let claim_parents = parents.iter().copied().collect::<ReplayClaimParents>();
        let mut plan = BoundReplayPlan::default();
        let lower = plan.intern_parent_draft(&claim_parents, ReplayClaimParentSide::Lower);
        let upper = plan.intern_parent_draft(&claim_parents, ReplayClaimParentSide::Upper);
        machine.register_replay_claim_parents_with_factored_drafts(
            result,
            replay,
            parents,
            materialize_existing_target,
            Some(FactoredReplayParentDrafts {
                parent_drafts: &plan.parent_drafts,
                lower,
                upper,
            }),
        );
    }

    fn apply_factored_canonical_duplicate_snapshot(
        machine: &mut ConstraintMachine,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
    ) {
        let constraint = machine.constraint_records[result.0 as usize].key.clone();
        let mut plan = BoundReplayPlan::default();
        machine.push_replay_constraint_or_prefilter(
            constraint.lower,
            constraint.weights,
            constraint.upper,
            replay,
            parents.iter().copied().collect(),
            &mut plan,
        );
        assert_eq!(plan.duplicate_actions.len(), 1);
        assert!(plan.trivial_actions.is_empty());
        machine.apply_prefiltered_replay_provenance_with_parent_drafts(
            plan.duplicate_actions,
            plan.trivial_actions,
            &plan.parent_drafts,
        );
    }

    fn legacy_replay_parent_oracle(
        machine: &ConstraintMachine,
    ) -> FxHashMap<ReplayParentOracleKey, UpperReplayClaimId> {
        let mut oracle = FxHashMap::default();
        for (&result, parents) in &machine.bounds.claim_parents_by_constraint {
            for parent in parents {
                let ClaimQualifiedParent::ReplayConstraint {
                    parent_claim,
                    parent_side,
                    replay,
                } = *parent
                else {
                    continue;
                };
                let root =
                    machine.bounds.upper_replay_claims[parent_claim.0 as usize].coverage_root;
                assert!(
                    oracle
                        .insert((result, root, parent_side, replay), parent_claim)
                        .is_none(),
                    "legacy replay parent keys are exact-deduplicated"
                );
            }
        }
        oracle
    }

    fn factored_replay_parent_oracle(
        machine: &ConstraintMachine,
    ) -> FxHashMap<ReplayParentOracleKey, UpperReplayClaimId> {
        let mut oracle = FxHashMap::default();
        for occurrence in &machine.replay_occurrences.occurrences {
            assert_eq!(
                machine
                    .replay_occurrences
                    .occurrence_id(ReplayOccurrenceKey {
                        result: occurrence.result,
                        carrier: occurrence.carrier,
                    }),
                Some(occurrence.id)
            );
            for (side, version) in [
                (ReplayClaimParentSide::Lower, occurrence.lower_parents),
                (ReplayClaimParentSide::Upper, occurrence.upper_parents),
            ] {
                for entry in machine
                    .replay_parent_sets
                    .iter(version)
                    .expect("shadow parent-set versions remain readable")
                {
                    assert!(
                        oracle
                            .insert(
                                (
                                    occurrence.result,
                                    entry.coverage_root,
                                    side,
                                    occurrence.carrier,
                                ),
                                entry.representative_claim,
                            )
                            .is_none(),
                        "one occurrence version has one representative per root and side"
                    );
                }
            }
        }
        oracle
    }

    type ReplayFirstWitnessOracleValue = (
        UpperReplayClaimId,
        ReplayClaimParentSide,
        BinaryReplayDerivation,
    );

    fn legacy_replay_first_witness_oracle(
        machine: &ConstraintMachine,
    ) -> FxHashMap<(ConstraintRecordId, UpperReplayClaimId), ReplayFirstWitnessOracleValue> {
        let mut oracle = FxHashMap::default();
        for (&result, parents) in &machine.bounds.claim_parents_by_constraint {
            for &parent in parents {
                let ClaimQualifiedParent::ReplayConstraint {
                    parent_claim,
                    parent_side,
                    replay,
                } = parent
                else {
                    continue;
                };
                let root =
                    machine.bounds.upper_replay_claims[parent_claim.0 as usize].coverage_root;
                oracle
                    .entry((result, root))
                    .or_insert((parent_claim, parent_side, replay));
            }
        }
        oracle
    }

    fn factored_replay_first_witness_oracle(
        machine: &ConstraintMachine,
    ) -> FxHashMap<(ConstraintRecordId, UpperReplayClaimId), ReplayFirstWitnessOracleValue> {
        let mut oracle = FxHashMap::default();
        for (&key, &witness) in &machine.replay_result_summary.first_parent_by_root {
            let occurrence = machine
                .replay_occurrences
                .occurrence(witness.occurrence)
                .expect("first witness references a live shadow occurrence");
            assert_eq!(occurrence.result, key.0);
            assert!(occurrence.first_admission_ordinal <= witness.admission_ordinal);
            assert!(
                oracle
                    .insert(
                        key,
                        (
                            witness.parent_claim,
                            witness.parent_side,
                            occurrence.carrier,
                        ),
                    )
                    .is_none(),
                "one shadow summary entry exists per result and root"
            );
        }
        oracle
    }

    type ReplayClauseLinkOracleKey = (BoundRecordId, UpperReplayClaimId, RecordProofClauseId);

    fn legacy_replay_clause_link_oracle(
        machine: &ConstraintMachine,
    ) -> FxHashSet<ReplayClauseLinkOracleKey> {
        let mut oracle = FxHashSet::default();
        for (&result, parents) in &machine.bounds.claim_parents_by_constraint {
            let Some(lower_record) = machine.lower_record_for_constraint(result) else {
                continue;
            };
            for &parent in parents {
                let ClaimQualifiedParent::ReplayConstraint {
                    parent_claim,
                    replay,
                    ..
                } = parent
                else {
                    continue;
                };
                let root =
                    machine.bounds.upper_replay_claims[parent_claim.0 as usize].coverage_root;
                let clause = RecordProofClause::ReplayConjunction {
                    carrier: replay,
                    lower_premise: replay.lower,
                    upper_premise: replay.upper,
                };
                let Some(clause_id) = machine
                    .bounds
                    .record_proof_clause_by_key
                    .get(&TypeBounds::record_proof_clause_key(lower_record, clause))
                    .copied()
                else {
                    continue;
                };
                let support = SchemeProjectionProofSupport::Claimed(root);
                if machine.bounds.record_proof_clause_link_keys.contains(
                    &TypeBounds::record_proof_clause_link_key(lower_record, support, clause_id),
                ) {
                    oracle.insert((lower_record, root, clause_id));
                }
            }
        }
        oracle
    }

    fn factored_replay_clause_link_oracle(
        machine: &ConstraintMachine,
    ) -> FxHashSet<ReplayClauseLinkOracleKey> {
        machine
            .replay_clause_projection
            .try_exact_links(&machine.replay_parent_sets, &machine.replay_occurrences)
            .expect("shadow replay clause links remain reconstructible")
            .collect()
    }

    fn assert_factored_replay_clause_projection_matches_legacy(machine: &ConstraintMachine) {
        let legacy = legacy_replay_clause_link_oracle(machine);
        let factored = factored_replay_clause_link_oracle(machine);
        assert_eq!(legacy, factored);
        let attributed = legacy
            .iter()
            .map(|&(record, root, _)| (record, root))
            .collect::<FxHashSet<_>>();
        assert_eq!(
            attributed,
            machine
                .replay_clause_projection
                .replay_attributed_claim_supports
        );
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct ReplayFactoredStorageCensus {
        arena: (usize, usize, usize, usize, usize, usize, usize, usize),
        occurrences: (usize, usize),
        by_key: (usize, usize),
        by_result: (usize, usize, usize, usize),
        attachment_batches: (usize, usize),
        first_parent_by_root: (usize, usize),
        projected_parent_versions: (usize, usize),
        clause_by_record_and_occurrence: (usize, usize),
        replay_attributed_claim_supports: (usize, usize),
    }

    fn replay_factored_storage_census(machine: &ConstraintMachine) -> ReplayFactoredStorageCensus {
        ReplayFactoredStorageCensus {
            arena: machine.replay_parent_sets.storage_census(),
            occurrences: (
                machine.replay_occurrences.occurrences.len(),
                machine.replay_occurrences.occurrences.capacity(),
            ),
            by_key: (
                machine.replay_occurrences.by_key.len(),
                machine.replay_occurrences.by_key.capacity(),
            ),
            by_result: (
                machine.replay_occurrences.by_result.len(),
                machine.replay_occurrences.by_result.capacity(),
                machine
                    .replay_occurrences
                    .by_result
                    .values()
                    .map(Vec::len)
                    .sum(),
                machine
                    .replay_occurrences
                    .by_result
                    .values()
                    .map(Vec::capacity)
                    .sum(),
            ),
            attachment_batches: (
                machine.replay_occurrences.attachment_batches.len(),
                machine.replay_occurrences.attachment_batches.capacity(),
            ),
            first_parent_by_root: (
                machine.replay_result_summary.first_parent_by_root.len(),
                machine
                    .replay_result_summary
                    .first_parent_by_root
                    .capacity(),
            ),
            projected_parent_versions: (
                machine
                    .replay_result_summary
                    .projected_parent_versions
                    .len(),
                machine
                    .replay_result_summary
                    .projected_parent_versions
                    .capacity(),
            ),
            clause_by_record_and_occurrence: (
                machine
                    .replay_clause_projection
                    .clause_by_record_and_occurrence
                    .len(),
                machine
                    .replay_clause_projection
                    .clause_by_record_and_occurrence
                    .capacity(),
            ),
            replay_attributed_claim_supports: (
                machine
                    .replay_clause_projection
                    .replay_attributed_claim_supports
                    .len(),
                machine
                    .replay_clause_projection
                    .replay_attributed_claim_supports
                    .capacity(),
            ),
        }
    }

    fn add_original_replay_parent_claim(
        machine: &mut ConstraintMachine,
        owner: TypeVar,
        endpoint: NegId,
        producer: ConstraintRecordId,
    ) -> UpperReplayClaimId {
        let record = machine
            .bounds
            .add_upper(
                owner,
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        machine
            .bounds
            .original_upper_replay_claim(record, producer, UpperReplayClaimKind::Direct)
            .claim
    }

    fn add_derived_replay_parent_claim(
        machine: &mut ConstraintMachine,
        owner: TypeVar,
        endpoint: NegId,
        root: UpperReplayClaimId,
        producer: ConstraintRecordId,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
    ) -> UpperReplayClaimId {
        let record = machine
            .bounds
            .add_upper(
                owner,
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        machine
            .bounds
            .derived_upper_replay_claim(record, root, producer, |depth| {
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim: root,
                    parent_side: ReplayClaimParentSide::Lower,
                    result,
                    replay,
                    depth,
                }
            })
            .claim
    }

    fn legacy_non_replay_claim_parents(
        machine: &ConstraintMachine,
        result: ConstraintRecordId,
    ) -> Vec<ClaimQualifiedParent> {
        machine
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .into_iter()
            .flat_map(|parents| parents.iter().copied())
            .filter(|parent| !matches!(parent, ClaimQualifiedParent::ReplayConstraint { .. }))
            .collect()
    }

    fn assert_non_replay_store_matches_legacy(
        machine: &ConstraintMachine,
        result: ConstraintRecordId,
    ) {
        assert_eq!(
            machine
                .non_replay_claim_parents_for_result(result)
                .collect::<Vec<_>>(),
            legacy_non_replay_claim_parents(machine, result),
            "the RCPF-C1 flat store is the legacy ledger with replay parents filtered out"
        );
    }

    #[test]
    fn rcpf_c1_query_facade_reuses_the_occurrence_store_indexes() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);

        let occurrence_ids = fixture
            .machine
            .replay_occurrences_for_result(fixture.result)
            .collect::<Vec<_>>();
        assert_eq!(occurrence_ids.len(), 1);
        let occurrence = fixture
            .machine
            .replay_occurrence(occurrence_ids[0])
            .expect("the facade resolves an ID from the existing by-result index");
        assert_eq!(occurrence.result, fixture.result);
        assert_eq!(occurrence.carrier, replay);
        assert!(
            fixture
                .machine
                .replay_occurrences_for_result(ConstraintRecordId(u32::MAX))
                .next()
                .is_none()
        );
    }

    #[test]
    fn rcpf_c1_no_claim_and_replay_only_records_allocate_no_non_replay_storage() {
        let mut fixture = cdm_replay_claim_fixture();
        assert_eq!(
            fixture
                .machine
                .try_factored_lower_projection_full(fixture.result, []),
            Ok(LowerProjectionAdapterSnapshot::default())
        );
        assert!(
            fixture
                .machine
                .try_factored_upper_materialization_full(fixture.upper_record, fixture.result)
                .expect("the no-root summary is readable")
                .is_empty()
        );
        assert_non_replay_store_matches_legacy(&fixture.machine, fixture.result);
        assert_eq!(
            fixture
                .machine
                .non_replay_claim_parents_by_constraint
                .storage_census(),
            (0, 0, 0, 0),
            "a no-claim record does not allocate the flat non-replay store"
        );

        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);
        assert_non_replay_store_matches_legacy(&fixture.machine, fixture.result);
        assert_eq!(
            fixture
                .machine
                .non_replay_claim_parents_by_constraint
                .storage_census(),
            (0, 0, 0, 0),
            "a replay-only record does not create a non-replay map entry"
        );
    }

    #[test]
    fn rcpf_c1_non_replay_store_matches_legacy_for_structural_reduction_and_mixed_records() {
        let mut fixture = cdm_replay_claim_fixture();
        let reduction = RowDerivationId(70_000);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(reduction);
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction,
            fixture.coverage_root,
        );
        assert!(
            fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
                .iter()
                .all(|parent| matches!(
                    parent,
                    ClaimQualifiedParent::ReductionRouteConstraint { .. }
                )),
            "the parent fixture is reduction-only"
        );
        assert_non_replay_store_matches_legacy(&fixture.machine, fixture.result);

        let child_lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["rcpf-c1-child".into()], Vec::new()));
        let child_upper = fixture.machine.alloc_neg(Neg::Var(TypeVar(70)));
        let structural_rule = StructuralDerivationRule::FunctionReturn;
        assert!(fixture.machine.enqueue_derived_subtype(
            child_lower,
            ConstraintWeights::empty(),
            child_upper,
            fixture.result,
            structural_rule,
        ));
        let child = fixture
            .machine
            .constraint_record_id(child_lower, ConstraintWeights::empty(), child_upper)
            .expect("the structural-only child is canonical");
        assert!(
            fixture.machine.bounds.claim_parents_by_constraint[&child]
                .iter()
                .all(|parent| matches!(parent, ClaimQualifiedParent::StructuralConstraint { .. })),
            "the child starts structural-only"
        );
        assert_non_replay_store_matches_legacy(&fixture.machine, child);

        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture.machine.merge_replay_derivation(child, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot(&mut fixture.machine, child, replay, &[parent]);
        let child_reduction = RowDerivationId(70_001);
        fixture.machine.constraint_records[child.0 as usize]
            .row_derivations
            .push(child_reduction);
        fixture.machine.register_reduction_route_claim_parent(
            child,
            child_reduction,
            fixture.coverage_root,
        );
        let mixed = &fixture.machine.bounds.claim_parents_by_constraint[&child];
        assert!(
            mixed
                .iter()
                .any(|parent| matches!(parent, ClaimQualifiedParent::StructuralConstraint { .. }))
        );
        assert!(mixed.iter().any(|parent| matches!(
            parent,
            ClaimQualifiedParent::ReductionRouteConstraint { .. }
        )));
        assert!(
            mixed
                .iter()
                .any(|parent| matches!(parent, ClaimQualifiedParent::ReplayConstraint { .. }))
        );
        assert_non_replay_store_matches_legacy(&fixture.machine, child);
    }

    #[test]
    fn rcpf_c1_non_replay_store_preserves_structural_and_reduction_exact_dedup() {
        let mut fixture = cdm_replay_claim_fixture();
        let reduction = RowDerivationId(70_002);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(reduction);
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction,
            fixture.coverage_root,
        );
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction,
            fixture.coverage_root,
        );
        assert_eq!(
            legacy_non_replay_claim_parents(&fixture.machine, fixture.result).len(),
            1
        );
        assert_non_replay_store_matches_legacy(&fixture.machine, fixture.result);

        let child_lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["rcpf-c1-dedup-child".into()], Vec::new()));
        let child_upper = fixture.machine.alloc_neg(Neg::Var(TypeVar(71)));
        let rule = StructuralDerivationRule::FunctionReturn;
        assert!(fixture.machine.enqueue_derived_subtype(
            child_lower,
            ConstraintWeights::empty(),
            child_upper,
            fixture.result,
            rule,
        ));
        assert!(!fixture.machine.enqueue_derived_subtype(
            child_lower,
            ConstraintWeights::empty(),
            child_upper,
            fixture.result,
            rule,
        ));
        let child = fixture
            .machine
            .constraint_record_id(child_lower, ConstraintWeights::empty(), child_upper)
            .expect("the dedup child is canonical");
        assert_eq!(
            legacy_non_replay_claim_parents(&fixture.machine, child).len(),
            1
        );
        assert_non_replay_store_matches_legacy(&fixture.machine, child);
    }

    #[test]
    fn rcpf_c1_non_replay_store_failure_quarantines_after_legacy_admission() {
        let mut fixture = cdm_replay_claim_fixture();
        let reduction = RowDerivationId(70_003);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(reduction);
        fixture
            .machine
            .non_replay_claim_parents_by_constraint
            .fail_next_reservation();

        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction,
            fixture.coverage_root,
        );

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            legacy_non_replay_claim_parents(&fixture.machine, fixture.result).len(),
            1
        );
        assert!(
            fixture
                .machine
                .non_replay_claim_parents_for_result(fixture.result)
                .next()
                .is_none(),
            "the failed shadow store does not partially commit"
        );
    }

    #[test]
    fn rcpf_d3a_0b_cross_kind_winner_matches_legacy_for_both_orders_and_kinds() {
        for (replay_first, structural) in
            [(true, true), (false, true), (true, false), (false, false)]
        {
            let mut fixture = cdm_replay_claim_fixture();
            let (result, root) = (fixture.result, fixture.coverage_root);
            let replay = fixture.replay(ReplayRule::LowerBoundAdded);
            let non_replay = if structural {
                ClaimQualifiedParent::StructuralConstraint {
                    parent_claim: root,
                    derivation: StructuralDerivation {
                        parent: result,
                        rule: StructuralDerivationRule::FunctionReturn,
                    },
                }
            } else {
                ClaimQualifiedParent::ReductionRouteConstraint {
                    parent_claim: root,
                    derivation: RowDerivationId(72_000),
                }
            };
            if !replay_first {
                fixture
                    .machine
                    .admit_claim_qualified_parent(result, non_replay);
            }
            assert_eq!(
                fixture.machine.merge_replay_derivation(result, replay),
                ReplayDerivationInsert::Inserted
            );
            let replay_parent = fixture.parent;
            register_factored_parent_snapshot_with_materialization(
                &mut fixture.machine,
                result,
                replay,
                &[replay_parent],
                false,
            );
            if replay_first {
                fixture
                    .machine
                    .admit_claim_qualified_parent(result, non_replay);
            }
            let comparison = fixture
                .machine
                .try_compare_first_qualified_parent_sources(result);
            assert_eq!(comparison, Ok(()));
            let legacy = fixture
                .machine
                .try_upper_materialization_lineages_from_parents(
                    fixture.upper_record,
                    result,
                    fixture.machine.bounds.claim_parents_by_constraint[&result]
                        .iter()
                        .copied(),
                    false,
                );
            let factored = fixture
                .machine
                .try_factored_upper_materialization_full(fixture.upper_record, result);
            assert_eq!(legacy, factored);
            assert_eq!(
                fixture
                    .machine
                    .try_factored_lower_projection_full(
                        result,
                        [ProjectionProofCarrier::Incomplete]
                    )
                    .expect("cross-kind lower adapter"),
                LowerProjectionAdapterSnapshot {
                    claimed_roots: vec![root],
                    proof_keys: vec![
                        CanonicalProjectionKey::Claimed(root),
                        CanonicalProjectionKey::Independent(ProjectionProofCarrier::Incomplete)
                    ],
                }
            );
        }
    }

    #[test]
    fn rcpf_d3a_0b_winner_failure_follows_legacy_parent_and_route_commit() {
        let mut fixture = cdm_replay_claim_fixture();
        let (result, root) = (fixture.result, fixture.coverage_root);
        let dependent = fixture.upper_record;
        fixture
            .machine
            .bounds
            .insert_dependent_record_edge(ProofPremise::Constraint(result), dependent);
        let parent = ClaimQualifiedParent::ReductionRouteConstraint {
            parent_claim: root,
            derivation: RowDerivationId(72_001),
        };
        fixture
            .machine
            .replay_result_summary
            .fail_next_source_reservation();

        fixture.machine.admit_claim_qualified_parent(result, parent);

        assert_eq!(
            fixture.machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            fixture.machine.bounds.claim_parents_by_constraint[&result],
            vec![parent]
        );
        let root_dependents =
            &fixture.machine.bounds.dependent_records_by_premise[&ProofPremise::RootCoverage(root)];
        assert!(root_dependents.contains(&dependent));
        let winner = fixture
            .machine
            .replay_result_summary
            .first_qualified_parent_source(result, root);
        assert_eq!(winner, Ok(None));
    }

    #[test]
    fn rcpf_c3a_legacy_rollback_disables_factored_writers_and_oracles() {
        let mut fixture = cdm_replay_claim_fixture_with_authority(
            ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure::AllocationFailed),
        );
        let factored_before = replay_factored_storage_census(&fixture.machine);
        let non_replay_before = fixture
            .machine
            .non_replay_claim_parents_by_constraint
            .storage_census();
        fixture.machine.enable_replay_factored_event_oracle();
        fixture.machine.enable_replay_factored_evaluator_oracle();

        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        register_factored_parent_snapshot(
            &mut fixture.machine,
            fixture.result,
            replay,
            &[fixture.parent],
        );
        let reduction = RowDerivationId(70_004);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(reduction);
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction,
            fixture.coverage_root,
        );

        assert_eq!(
            replay_factored_storage_census(&fixture.machine),
            factored_before
        );
        assert_eq!(
            fixture
                .machine
                .non_replay_claim_parents_by_constraint
                .storage_census(),
            non_replay_before
        );
        assert!(!fixture.machine.replay_result_summary.event_oracle_enabled());
        assert!(
            !fixture
                .machine
                .replay_result_summary
                .evaluator_oracle_enabled()
        );
        assert_eq!(fixture.machine.replay_factored_terminal_failure(), None);
        let winner = fixture
            .machine
            .replay_result_summary
            .first_qualified_parent_source(fixture.result, fixture.coverage_root);
        assert_eq!(winner, Ok(None));
        assert_eq!(
            fixture.machine.replay_read_authority(),
            ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            SchemeProjectionEvaluator::new(&fixture.machine).replay_source,
            ReplayEvaluatorSource::Legacy,
        );
        assert_eq!(
            SchemeProjectionEvaluationRound::new(&fixture.machine).replay_source,
            ReplayEvaluatorSource::Legacy,
        );
        assert!(
            fixture
                .machine
                .bounds
                .claim_parents_by_constraint
                .get(&fixture.result)
                .is_some_and(|parents| !parents.is_empty()),
            "legacy admission remains active during rollback"
        );
    }

    #[test]
    fn rcpf_d2a_legacy_rollback_split_preserves_immediate_publication_sequence() {
        let authority =
            ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure::AllocationFailed);
        let mut split = cdm_replay_claim_fixture_with_authority(authority);
        let mut combined = cdm_replay_claim_fixture_with_authority(authority);

        let add_result = |fixture: &mut CdmReplayClaimFixture| {
            let lower = fixture
                .machine
                .alloc_pos(Pos::Con(vec!["rcpf-d2a-lower".into()], Vec::new()));
            let upper = fixture
                .machine
                .alloc_neg(Neg::Con(vec!["rcpf-d2a-upper".into()], Vec::new()));
            fixture
                .machine
                .subtype(lower, upper, OriginId::unknown_internal());
            fixture
                .machine
                .constraint_record_id(lower, ConstraintWeights::empty(), upper)
                .expect("the publication fixture constraint is canonical")
        };
        let split_result = add_result(&mut split);
        let combined_result = add_result(&mut combined);
        assert_eq!(split_result, combined_result);

        let attach_dependent = |fixture: &mut CdmReplayClaimFixture, result| {
            let (dependent, support) = dpn_b_synthetic_projection_record(&mut fixture.machine, 70);
            fixture.machine.register_record_proof_clause_link(
                dependent,
                RecordProofClauseLinkAdmission::independent(
                    support,
                    RecordProofClause::DerivedUnary {
                        carrier: dpn_b_synthetic_unary_carrier(70),
                        premise: ProofPremise::Constraint(result),
                    },
                ),
            );
            dependent
        };
        let split_dependent = attach_dependent(&mut split, split_result);
        let combined_dependent = attach_dependent(&mut combined, combined_result);
        assert_eq!(split_dependent, combined_dependent);
        let replay = BinaryReplayDerivation {
            pivot: split.pivot,
            lower: split_dependent,
            upper: split_dependent,
            rule: ReplayRule::LowerBoundAdded,
        };
        for (fixture, result) in [(&mut split, split_result), (&mut combined, combined_result)] {
            assert_eq!(
                fixture.machine.merge_replay_derivation(result, replay),
                ReplayDerivationInsert::Inserted
            );
        }

        let epoch_snapshot = |fixture: &CdmReplayClaimFixture, dependent: BoundRecordId| {
            let owner = fixture.machine.bounds.record(dependent).unwrap().owner();
            (
                fixture.machine.epoch,
                fixture.machine.provenance_epoch,
                fixture.machine.bounds.of(owner).unwrap().epoch(),
                fixture
                    .machine
                    .scheme_projection_record_is_included(dependent),
            )
        };
        let mut split_epochs = vec![epoch_snapshot(&split, split_dependent)];
        let mut combined_epochs = vec![epoch_snapshot(&combined, combined_dependent)];
        let split_factored_before = replay_factored_storage_census(&split.machine);
        let combined_factored_before = replay_factored_storage_census(&combined.machine);
        let split_journal = split.machine.activate_method_role_mutations();
        let combined_journal = combined.machine.activate_method_role_mutations();

        let split_parent = ClaimQualifiedParent::ReplayConstraint {
            parent_claim: split.parent.claim,
            parent_side: split.parent.parent_side,
            replay,
        };
        let split_snapshot = split
            .machine
            .commit_claim_qualified_parent_mutation(split_result, split_parent);
        split
            .machine
            .publish_claim_qualified_parent_admission(split_snapshot);
        combined.machine.admit_claim_qualified_parent(
            combined_result,
            ClaimQualifiedParent::ReplayConstraint {
                parent_claim: combined.parent.claim,
                parent_side: combined.parent.parent_side,
                replay,
            },
        );

        split_epochs.push(epoch_snapshot(&split, split_dependent));
        combined_epochs.push(epoch_snapshot(&combined, combined_dependent));
        let split_affected = changed_keys(split.machine.take_method_role_mutations());
        let combined_affected = changed_keys(combined.machine.take_method_role_mutations());
        split_journal.finish();
        combined_journal.finish();

        assert_eq!(split_epochs, combined_epochs);
        assert!(
            split_epochs[1].0 > split_epochs[0].0
                && split_epochs[1].1 > split_epochs[0].1
                && split_epochs[1].2 > split_epochs[0].2,
            "the fixture must advance global, provenance, and owner epochs"
        );
        assert_eq!((split_epochs[0].3, split_epochs[1].3), (true, false));
        assert_eq!(split_epochs[1].2, split_epochs[1].0);
        assert_eq!(split_affected, combined_affected);
        assert_eq!(
            split.machine.bounds.claim_parents_by_constraint,
            combined.machine.bounds.claim_parents_by_constraint
        );
        assert_eq!(
            split.machine.bounds.dependent_records_by_premise,
            combined.machine.bounds.dependent_records_by_premise
        );
        assert_eq!(
            replay_factored_storage_census(&split.machine),
            split_factored_before
        );
        assert_eq!(
            replay_factored_storage_census(&combined.machine),
            combined_factored_before
        );
        assert_eq!(split.machine.replay_read_authority(), authority);
        assert_eq!(combined.machine.replay_read_authority(), authority);
    }

    #[test]
    fn rcpf_d2c_2c_2a_deferred_clause_intent_preserves_immediate_value() {
        let authority =
            ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure::AllocationFailed);
        let mut split = ConstraintMachine::new_with_replay_read_authority(authority);
        let mut combined = ConstraintMachine::new_with_replay_read_authority(authority);
        let (split_record, split_support) = dpn_b_synthetic_projection_record(&mut split, 71);
        let (combined_record, combined_support) =
            dpn_b_synthetic_projection_record(&mut combined, 71);
        assert_eq!(split_record, combined_record);
        assert_eq!(split_support, combined_support);
        let split_clause = RecordProofClause::DerivedUnary {
            carrier: dpn_b_synthetic_unary_carrier(71),
            premise: ProofPremise::Record(split_record),
        };
        let combined_clause = RecordProofClause::DerivedUnary {
            carrier: dpn_b_synthetic_unary_carrier(71),
            premise: ProofPremise::Record(combined_record),
        };
        let epoch_snapshot = |machine: &ConstraintMachine, record| {
            let owner = machine.bounds.record(record).unwrap().owner();
            (
                machine.epoch,
                machine.provenance_epoch,
                machine.bounds.of(owner).unwrap().epoch(),
                machine.scheme_projection_record_is_included(record),
            )
        };
        let mut split_epochs = vec![epoch_snapshot(&split, split_record)];
        let mut combined_epochs = vec![epoch_snapshot(&combined, combined_record)];
        let split_journal = split.activate_method_role_mutations();
        let combined_journal = combined.activate_method_role_mutations();

        let mut publication_fence = ReplayAdmissionPublicationFence::default();
        split.commit_record_proof_clause_link_batch_with_fence(
            split_record,
            [RecordProofClauseLinkAdmission::independent(
                split_support,
                split_clause,
            )],
            Some(&mut publication_fence),
        );
        combined.commit_record_proof_clause_link_batch(
            combined_record,
            [RecordProofClauseLinkAdmission::independent(
                combined_support,
                combined_clause,
            )],
        );
        assert!(!split.scheme_projection_record_is_included(split_record));
        assert!(!combined.scheme_projection_record_is_included(combined_record));
        assert_eq!(split.epoch, split_epochs[0].0);
        assert!(combined.epoch > combined_epochs[0].0);
        let late_support = ProjectionProofCarrier::Origin(OriginId::unknown_internal());
        split
            .bounds
            .update_scheme_projection_proofs(split_record, &[], &[late_support]);
        combined
            .bounds
            .update_scheme_projection_proofs(combined_record, &[], &[late_support]);
        assert!(split.scheme_projection_record_is_included(split_record));
        assert!(combined.scheme_projection_record_is_included(combined_record));
        split.publish_replay_admission_publication_fence(publication_fence);

        split_epochs.push(epoch_snapshot(&split, split_record));
        combined_epochs.push(epoch_snapshot(&combined, combined_record));
        let split_affected = changed_keys(split.take_method_role_mutations());
        let combined_affected = changed_keys(combined.take_method_role_mutations());
        split_journal.finish();
        combined_journal.finish();

        assert_eq!(split_epochs, combined_epochs);
        assert!(
            split_epochs[1].0 > split_epochs[0].0
                && split_epochs[1].1 > split_epochs[0].1
                && split_epochs[1].2 > split_epochs[0].2,
            "the fixture must advance global, provenance, and owner epochs"
        );
        assert_eq!((split_epochs[0].3, split_epochs[1].3), (true, true));
        assert_eq!(split_epochs[1].2, split_epochs[1].0);
        assert_eq!(split_affected, combined_affected);
        assert_eq!(
            split.bounds.record_proof_clause_link_keys,
            combined.bounds.record_proof_clause_link_keys
        );
        assert_eq!(
            split.bounds.dependent_records_by_premise,
            combined.bounds.dependent_records_by_premise
        );
        assert_eq!(split.replay_read_authority(), authority);
        assert_eq!(combined.replay_read_authority(), authority);
    }

    #[test]
    fn rcpf_d2c_2c_2b_later_phase_c_failure_discards_whole_event_publication() {
        let mut fixture = cdm_replay_claim_fixture_with_authority(
            ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure::AllocationFailed),
        );
        let lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["rcpf-d2c-2c-event-lower".into()], Vec::new()));
        let upper = fixture
            .machine
            .alloc_neg(Neg::Con(vec!["rcpf-d2c-2c-event-upper".into()], Vec::new()));
        fixture
            .machine
            .subtype(lower, upper, OriginId::unknown_internal());
        let result = fixture
            .machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the event fixture constraint is canonical");
        let (dependent, support) = dpn_b_synthetic_projection_record(&mut fixture.machine, 73);
        fixture.machine.register_record_proof_clause_link(
            dependent,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: dpn_b_synthetic_unary_carrier(73),
                    premise: ProofPremise::Constraint(result),
                },
            ),
        );
        fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint
            .insert(result, dependent);
        assert!(
            !fixture
                .machine
                .scheme_projection_record_is_included(dependent)
        );
        let replay = BinaryReplayDerivation {
            pivot: fixture.pivot,
            lower: fixture.lower_record,
            upper: fixture.upper_record,
            rule: ReplayRule::LowerBoundAdded,
        };
        assert_eq!(
            fixture.machine.merge_replay_derivation(result, replay),
            ReplayDerivationInsert::Inserted
        );
        let dependent_owner = fixture.machine.bounds.record(dependent).unwrap().owner();
        let epoch_snapshot = |machine: &ConstraintMachine| {
            (
                machine.epoch,
                machine.provenance_epoch,
                machine.bounds.of(dependent_owner).unwrap().epoch(),
            )
        };
        let before = epoch_snapshot(&fixture.machine);
        let journal = fixture.machine.activate_method_role_mutations();
        RCPF_D2C_FAIL_DEFERRED_EVALUATION_AT.with(|fail_at| fail_at.set(Some(2)));
        RCPF_D2C_PHASE_A_OWNER_INTENT_PROBES.with(|probes| probes.set(0));
        let parent = fixture.parent;

        register_factored_parent_snapshot(&mut fixture.machine, result, replay, &[parent]);

        let published = fixture.machine.take_method_role_mutations();
        journal.finish();
        assert_eq!(
            fixture.machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            RCPF_D2C_FAIL_DEFERRED_EVALUATION_AT.with(std::cell::Cell::get),
            None,
            "the second deferred evaluation, in Phase C, must consume the injected failure"
        );
        assert_eq!(
            epoch_snapshot(&fixture.machine),
            before,
            "a later Phase C failure discards Phase A's owner-changing publication intent"
        );
        assert!(
            published.is_empty(),
            "the whole event publishes no cache keys"
        );
        assert_eq!(
            RCPF_D2C_PHASE_A_OWNER_INTENT_PROBES.with(std::cell::Cell::get),
            1,
            "the qualified-parent mutation must create one real deferred Phase A intent"
        );
        let qualified_parent = ClaimQualifiedParent::ReplayConstraint {
            parent_claim: parent.claim,
            parent_side: parent.parent_side,
            replay,
        };
        let bounds = &fixture.machine.bounds;
        assert!(bounds.claim_parents_by_constraint[&result].contains(&qualified_parent));
        assert!(
            bounds
                .replay_claim_parent_keys
                .contains(&ReplayClaimParentKey {
                    result,
                    coverage_root: fixture.coverage_root,
                    parent_side: parent.parent_side,
                    replay,
                })
        );
        let clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };
        assert!(bounds.record_proof_clause_link_is_registered(
            dependent,
            SchemeProjectionProofSupport::Claimed(fixture.coverage_root),
            clause,
        ));
        for premise in [replay.lower, replay.upper] {
            assert!(
                bounds
                    .dependent_records_by_premise
                    .get(&ProofPremise::Record(premise))
                    .is_some_and(|records| records.contains(&dependent))
            );
        }
        assert!(
            bounds
                .scheme_projection_claims_by_lower_record
                .get(&dependent)
                .is_some_and(|claims| claims.contains(&fixture.coverage_root))
        );
    }

    #[test]
    fn rcpf_d2b_factored_clause_projection_failure_keeps_legacy_links_and_edges() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        let parent = ClaimQualifiedParent::ReplayConstraint {
            parent_claim: fixture.parent.claim,
            parent_side: fixture.parent.parent_side,
            replay,
        };
        let support = SchemeProjectionProofSupport::Claimed(fixture.coverage_root);
        let clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };

        fixture
            .machine
            .register_claim_parent_clause_links(
                fixture.result,
                fixture.lower_record,
                &[parent],
            );
        RCPF_D2B_FAIL_NEXT_CLAUSE_PROJECTION.with(|fail| fail.set(true));
        fixture.machine.observe_factored_replay_clause_projection(
            fixture.result,
            fixture.lower_record,
            &[parent],
        );

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert!(
            fixture
                .machine
                .bounds
                .record_proof_clause_link_is_registered(fixture.lower_record, support, clause)
        );
        for premise in [replay.lower, replay.upper] {
            assert!(
                fixture
                    .machine
                    .bounds
                    .dependent_records_by_premise
                    .get(&ProofPremise::Record(premise))
                    .is_some_and(|dependents| dependents.contains(&fixture.lower_record)),
                "legacy replay dependency edges commit before the factored projection can fail"
            );
        }
        assert!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .is_empty(),
            "the injected factored projection failure must not partially publish"
        );
    }

    fn rcpf_d2c_2c_1_missing_occurrence_publication_fixture()
    -> (ConstraintMachine, BoundRecordId, TypeVar) {
        let mut machine = ConstraintMachine::new();
        let owner = TypeVar(72_000);
        let lower = machine.alloc_pos(Pos::Con(vec!["d2c-2c-lower".into()], Vec::new()));
        let upper = machine.alloc_neg(Neg::Var(owner));
        machine.subtype(lower, upper, OriginId::unknown_internal());
        let constraint = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the synthetic constraint is canonical");
        let lower_record = machine.bounds.of(owner).unwrap().lower_record_ids()[0];
        machine.replay_occurrences.by_result.insert(
            constraint,
            vec![crate::constraints::replay_factored::ReplayOccurrenceId(
                u32::MAX,
            )],
        );

        let carrier = ProjectionProofCarrier::ConstraintOrigin {
            constraint: ConstraintRecordId(72_001),
            origin: OriginId::unknown_internal(),
        };
        let support = SchemeProjectionProofSupport::Independent(carrier);
        machine.bounds.projection_proofs_by_lower_record.insert(
            lower_record,
            vec![SchemeProjectionProof {
                lower_record,
                support,
            }],
        );
        machine.bounds.register_record_proof_clause_link(
            lower_record,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: dpn_b_synthetic_unary_carrier(72_001),
                    premise: ProofPremise::Constraint(constraint),
                },
            ),
        );
        (machine, lower_record, owner)
    }

    #[test]
    fn rcpf_d2c_2c_1_snapshot_evaluation_failure_does_not_publish() {
        for publication in ["qualified-parent", "clause-link"] {
            let (mut machine, lower_record, owner) =
                rcpf_d2c_2c_1_missing_occurrence_publication_fixture();
            let before = (
                machine.epoch,
                machine.provenance_epoch,
                machine.bounds.of(owner).unwrap().epoch(),
            );
            let journal = machine.activate_method_role_mutations();
            mark_next_replay_soak_failure_as_intentional();
            match publication {
                "qualified-parent" => {
                    let snapshot = ClaimQualifiedParentAdmissionSnapshot {
                        inclusion_before: FxHashMap::from_iter([(lower_record, true)]),
                    };
                    machine.publish_claim_qualified_parent_admission(snapshot);
                }
                "clause-link" => {
                    let snapshot = ClauseLinkBatchAdmissionSnapshot {
                        lower_record,
                        was_included: true,
                    };
                    machine.publish_record_proof_clause_link_batch(snapshot);
                }
                _ => unreachable!("the fixture enumerates both publication snapshots"),
            }
            let published = machine.take_method_role_mutations();
            journal.finish();

            assert_eq!(
                machine.replay_factored_terminal_failure(),
                Some(ReplayFactoredShadowFailure::UnknownReplayOccurrence(
                    crate::constraints::replay_factored::ReplayOccurrenceId(u32::MAX)
                )),
                "{publication} snapshot records the fallible read"
            );
            assert_eq!(
                (
                    machine.epoch,
                    machine.provenance_epoch,
                    machine.bounds.of(owner).unwrap().epoch(),
                ),
                before,
                "{publication} snapshot must not publish epochs from a placeholder"
            );
            assert!(
                published.is_empty(),
                "{publication} snapshot must not publish cache invalidations"
            );
        }
    }

    #[test]
    fn rcpf_d2c_1_phase_b_failure_blocks_materialization_and_event_oracle() {
        let mut fixture = cdm_replay_claim_fixture();
        fixture.machine.enable_replay_factored_event_oracle();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.replay_parent_sets.fail_next_reservation();
        RCPF_D2C_EVENT_ORACLE_PROBES.with(|probes| probes.set(0));
        let parent = fixture.parent;

        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            fixture.machine.bounds.claim_parents_by_constraint[&fixture.result].len(),
            1,
            "Phase A legacy parent mutation is unconditional"
        );
        let support = SchemeProjectionProofSupport::Claimed(fixture.coverage_root);
        let clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };
        assert!(
            fixture
                .machine
                .bounds
                .record_proof_clause_link_is_registered(fixture.lower_record, support, clause)
        );
        for premise in [replay.lower, replay.upper] {
            assert!(
                fixture
                    .machine
                    .bounds
                    .dependent_records_by_premise
                    .get(&ProofPremise::Record(premise))
                    .is_some_and(|records| records.contains(&fixture.lower_record))
            );
        }
        assert!(
            !fixture
                .machine
                .bounds
                .derived_claim_by_record_and_root
                .contains_key(&(fixture.upper_record, fixture.coverage_root))
        );
        assert_eq!(RCPF_D2C_EVENT_ORACLE_PROBES.with(std::cell::Cell::get), 0);
    }

    #[test]
    fn rcpf_e2c_a1_read_failure_keeps_legacy_phase_a_before_terminal_stop() {
        let mut fixture = cdm_replay_claim_fixture();
        fixture.machine.enable_replay_factored_event_oracle();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        let support = SchemeProjectionProofSupport::Claimed(fixture.coverage_root);
        let clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };
        assert!(!fixture.machine.bounds.record_proof_clause_link_is_registered(
            fixture.lower_record,
            support,
            clause,
        ));
        let publication_before = (fixture.machine.epoch, fixture.machine.provenance_epoch);

        RCPF_E2C_FAIL_NEXT_A1_READ.with(|fail| fail.set(true));
        RCPF_D2C_EVENT_ORACLE_PROBES.with(|probes| probes.set(0));
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);

        assert!(!RCPF_E2C_FAIL_NEXT_A1_READ.with(std::cell::Cell::get));
        assert_eq!(
            fixture.machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert!(fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
            .iter()
            .any(|candidate| candidate.parent_claim() == parent.claim));
        assert!(
            fixture.machine.bounds.record_proof_clause_link_is_registered(
                fixture.lower_record,
                support,
                clause,
            ),
            "Factored A1 failure must not skip the unconditional legacy Phase A link"
        );
        assert!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .is_empty(),
            "terminal A1 failure stops before factored Phase B"
        );
        assert_eq!(
            (fixture.machine.epoch, fixture.machine.provenance_epoch),
            publication_before,
            "terminal A1 failure must not publish the failed attempt"
        );
        assert_eq!(RCPF_D2C_EVENT_ORACLE_PROBES.with(std::cell::Cell::get), 0);
    }

    type D4PhaseCState = (
        Option<Vec<UpperReplayClaimId>>,
        Option<Vec<UpperReplayClaimId>>,
        Option<Vec<SchemeProjectionProof>>,
        ConstraintEpoch,
        ProvenanceEpoch,
    );

    fn d4_phase_c_state(fixture: &CdmReplayClaimFixture) -> D4PhaseCState {
        (
            fixture
                .machine
                .bounds
                .claims_by_upper_record
                .get(&fixture.upper_record)
                .cloned(),
            fixture
                .machine
                .bounds
                .scheme_projection_claims_by_lower_record
                .get(&fixture.lower_record)
                .cloned(),
            fixture
                .machine
                .bounds
                .projection_proofs_by_lower_record
                .get(&fixture.lower_record)
                .cloned(),
            fixture.machine.epoch,
            fixture.machine.provenance_epoch,
        )
    }

    #[test]
    fn rcpf_d4_replay_pre_consumer_failure_blocks_phase_c_and_publication() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let phase_c_before = d4_phase_c_state(&fixture);
        let journal = fixture.machine.activate_method_role_mutations();
        RCPF_D4_FAIL_NEXT_PRE_CONSUMER_QUERY.with(|fail| fail.set(true));
        let parent = fixture.parent;

        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);

        assert_eq!(
            fixture.machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert!(
            fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
                .iter()
                .any(|candidate| candidate.parent_claim() == parent.claim)
        );
        assert_eq!(
            phase_c_before,
            d4_phase_c_state(&fixture),
            "Phase B failure must leave upper/lower Phase C and epochs untouched"
        );
        assert!(fixture.machine.take_method_role_mutations().is_empty());
        journal.finish();
    }

    #[test]
    fn rcpf_d4_non_replay_pre_consumer_failure_blocks_phase_c_and_publication() {
        let mut fixture = cdm_replay_claim_fixture();
        let derivation = RowDerivationId(72_100);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(derivation);
        let phase_c_before = d4_phase_c_state(&fixture);
        let journal = fixture.machine.activate_method_role_mutations();
        RCPF_D4_FAIL_NEXT_PRE_CONSUMER_QUERY.with(|fail| fail.set(true));

        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            derivation,
            fixture.coverage_root,
        );

        assert_eq!(
            fixture.machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert!(fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
            .iter()
            .any(|candidate| matches!(candidate,
                ClaimQualifiedParent::ReductionRouteConstraint {
                    parent_claim, derivation: candidate_derivation,
                } if *parent_claim == fixture.coverage_root && *candidate_derivation == derivation
            )));
        assert_eq!(
            phase_c_before,
            d4_phase_c_state(&fixture),
            "Phase B failure must leave upper/lower Phase C and epochs untouched"
        );
        assert!(fixture.machine.take_method_role_mutations().is_empty());
        journal.finish();
    }

    #[test]
    fn rcpf_d2c_2a_clause_projection_failure_stops_before_materialization() {
        let mut fixture = cdm_replay_claim_fixture();
        fixture.machine.enable_replay_factored_event_oracle();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        RCPF_D2B_FAIL_NEXT_CLAUSE_PROJECTION.with(|fail| fail.set(true));
        RCPF_D2C_EVENT_ORACLE_PROBES.with(|probes| probes.set(0));
        let parent = fixture.parent;

        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::AllocationFailed)
        );
        let support = SchemeProjectionProofSupport::Claimed(fixture.coverage_root);
        let clause = RecordProofClause::ReplayConjunction {
            carrier: replay,
            lower_premise: replay.lower,
            upper_premise: replay.upper,
        };
        assert!(
            fixture
                .machine
                .bounds
                .record_proof_clause_link_is_registered(fixture.lower_record, support, clause),
            "Phase A legacy clause-link mutation remains unconditional"
        );
        assert!(
            !fixture
                .machine
                .bounds
                .derived_claim_by_record_and_root
                .contains_key(&(fixture.upper_record, fixture.coverage_root)),
            "Phase B clause-projection failure must stop before upper materialization"
        );
        assert_eq!(RCPF_D2C_EVENT_ORACLE_PROBES.with(std::cell::Cell::get), 0);
    }

    fn rcpf_c2_replay_inspection_census(root_count: usize) -> (usize, usize, usize) {
        assert!(root_count > 0);
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let endpoint = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let mut parents = vec![fixture.parent];
        for index in 1..root_count {
            let offset = u32::try_from(index).expect("test root count fits in u32");
            let claim = add_original_replay_parent_claim(
                &mut fixture.machine,
                TypeVar(80_000 + offset),
                endpoint,
                ConstraintRecordId(80_000 + offset),
            );
            parents.push(SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Lower,
            });
        }
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &parents);

        let mut legacy = SchemeProjectionEvaluator::with_replay_source(
            &fixture.machine,
            ReplayEvaluatorSource::Legacy,
        )
        .with_record_result_override(fixture.lower_record, false);
        let legacy_result = legacy.eval_constraint(fixture.result);
        let mut factored = SchemeProjectionEvaluator::new(&fixture.machine)
            .with_record_result_override(fixture.lower_record, false);
        assert_eq!(factored.replay_source, ReplayEvaluatorSource::Factored);
        assert_eq!(
            SchemeProjectionEvaluationRound::new(&fixture.machine).replay_source,
            ReplayEvaluatorSource::Factored,
        );
        let factored_result = factored.eval_constraint(fixture.result);
        assert_eq!(factored_result, legacy_result);
        (
            legacy.replay_inspections,
            factored.replay_inspections,
            fixture.machine.replay_occurrences.occurrences.len(),
        )
    }

    #[test]
    fn rcpf_c2_factored_replay_inspections_scale_with_occurrences_not_roots() {
        assert_eq!(rcpf_c2_replay_inspection_census(1), (1, 1, 1));
        assert_eq!(rcpf_c2_replay_inspection_census(8), (8, 1, 1));
    }

    #[test]
    fn rcpf_c2_factored_evaluator_uses_structural_and_reduction_flat_sources() {
        let mut fixture = cdm_replay_claim_fixture();
        let reduction = RowDerivationId(70_100);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(reduction);
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction,
            fixture.coverage_root,
        );
        let child_lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["rcpf-c2-structural".into()], Vec::new()));
        let child_upper = fixture.machine.alloc_neg(Neg::Var(TypeVar(72)));
        assert!(fixture.machine.enqueue_derived_subtype(
            child_lower,
            ConstraintWeights::empty(),
            child_upper,
            fixture.result,
            StructuralDerivationRule::FunctionReturn,
        ));
        let child = fixture
            .machine
            .constraint_record_id(child_lower, ConstraintWeights::empty(), child_upper)
            .expect("the structural child is canonical");

        for constraint in [fixture.result, child] {
            let legacy = SchemeProjectionEvaluator::with_replay_source(
                &fixture.machine,
                ReplayEvaluatorSource::Legacy,
            )
            .with_record_result_override(fixture.lower_record, false)
            .eval_constraint(constraint);
            let mut factored = SchemeProjectionEvaluator::with_replay_source(
                &fixture.machine,
                ReplayEvaluatorSource::Factored,
            )
            .with_record_result_override(fixture.lower_record, false);
            let factored_result = factored.eval_constraint(constraint);
            assert_eq!(factored_result, legacy);
        }
    }

    #[test]
    fn rcpf_c2_factored_oracle_matches_fresh_shared_and_insertion_order_queries() {
        for standalone_first in [false, true] {
            let mut machine = ConstraintMachine::new();
            machine.enable_replay_factored_evaluator_oracle();
            let (source, cycle_support) =
                dpn_b_synthetic_projection_record(&mut machine, 100 + standalone_first as u32);
            let (dependent, dependent_support) =
                dpn_b_synthetic_projection_record(&mut machine, 110 + standalone_first as u32);
            let standalone_support =
                SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::Incomplete);
            machine
                .bounds
                .projection_proofs_by_lower_record
                .get_mut(&source)
                .expect("the synthetic record has a proof ledger")
                .push(SchemeProjectionProof {
                    lower_record: source,
                    support: standalone_support,
                });
            let cycle_clause = RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(100),
                premise: ProofPremise::Record(dependent),
            };
            let standalone_clause = RecordProofClause::Standalone {
                support: standalone_support,
            };
            let clauses = if standalone_first {
                [
                    (standalone_support, standalone_clause),
                    (cycle_support, cycle_clause),
                ]
            } else {
                [
                    (cycle_support, cycle_clause),
                    (standalone_support, standalone_clause),
                ]
            };
            for (support, clause) in clauses {
                dpn_b_register_synthetic_clause(&mut machine, source, support, clause);
            }
            dpn_b_register_synthetic_clause(
                &mut machine,
                dependent,
                dependent_support,
                RecordProofClause::DerivedUnary {
                    carrier: dpn_b_synthetic_unary_carrier(101),
                    premise: ProofPremise::Record(source),
                },
            );

            for roots in [[source, dependent], [dependent, source]] {
                for replay_source in [
                    ReplayEvaluatorSource::Legacy,
                    ReplayEvaluatorSource::Factored,
                ] {
                    let fresh = roots.map(|record| {
                        let mut evaluator =
                            SchemeProjectionEvaluator::with_replay_source(&machine, replay_source);
                        evaluator.eval_record(record)
                    });
                    let mut round = SchemeProjectionEvaluationRound::with_replay_source(
                        &machine,
                        replay_source,
                    );
                    let shared = roots.map(|record| round.eval_record(record));
                    assert_eq!(fresh, shared);
                    assert_eq!(fresh, [Ok(true), Ok(true)]);
                }
            }
        }
    }

    #[test]
    fn rcpf_c3d_factored_read_error_quarantines_the_production_attempt() {
        let mut machine = ConstraintMachine::new();
        let lower = machine.alloc_pos(Pos::Con(vec!["rcpf-c3c-lower".into()], Vec::new()));
        let upper = machine.alloc_neg(Neg::Con(vec!["rcpf-c3c-upper".into()], Vec::new()));
        machine.subtype(lower, upper, OriginId::unknown_internal());
        let constraint = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the synthetic constraint is canonical");
        let missing_occurrence = crate::constraints::replay_factored::ReplayOccurrenceId(u32::MAX);
        machine
            .replay_occurrences
            .by_result
            .insert(constraint, vec![missing_occurrence]);
        let (record, support) = dpn_b_synthetic_projection_record(&mut machine, 119);
        dpn_b_register_synthetic_clause(
            &mut machine,
            record,
            support,
            RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(119),
                premise: ProofPremise::Constraint(constraint),
            },
        );
        let expected = Err(ReplayFactoredShadowFailure::UnknownReplayOccurrence(
            missing_occurrence,
        ));

        let mut evaluator = SchemeProjectionEvaluator::with_replay_source(
            &machine,
            ReplayEvaluatorSource::Factored,
        );
        assert_eq!(evaluator.eval_record(record), expected);
        assert_eq!(evaluator.visiting_nodes, 0);
        assert!(evaluator.states.is_empty());
        assert_eq!(evaluator.eval_record(record), expected);
        assert_eq!(evaluator.visiting_nodes, 0);
        assert!(evaluator.states.is_empty());

        let mut round = SchemeProjectionEvaluationRound::with_replay_source(
            &machine,
            ReplayEvaluatorSource::Factored,
        );
        assert_eq!(round.eval_record(record), expected);
        let shared = round
            .shared
            .as_ref()
            .expect("an error without a cycle cut keeps the shared evaluator");
        assert_eq!(shared.visiting_nodes, 0);
        assert!(shared.states.is_empty());

        assert_eq!(machine.replay_factored_terminal_failure(), None);
        mark_next_replay_soak_failure_as_intentional();
        assert!(
            !machine.scheme_projection_record_is_included(record),
            "the terminal attempt returns an inert value that C3a will discard"
        );
        assert_eq!(
            machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::UnknownReplayOccurrence(
                missing_occurrence,
            ))
        );
        assert!(!machine.replay_factored_writes_enabled());
    }

    #[test]
    fn rcpf_c2_factored_oracle_skips_a_quarantined_shadow() {
        let mut machine = ConstraintMachine::new();
        machine.enable_replay_factored_evaluator_oracle();
        let lower = machine.alloc_pos(Pos::Con(vec!["rcpf-c2-skip-lower".into()], Vec::new()));
        let upper = machine.alloc_neg(Neg::Con(vec!["rcpf-c2-skip-upper".into()], Vec::new()));
        machine.subtype(lower, upper, OriginId::unknown_internal());
        let constraint = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the synthetic constraint is canonical");
        machine.replay_occurrences.by_result.insert(
            constraint,
            vec![crate::constraints::replay_factored::ReplayOccurrenceId(
                u32::MAX,
            )],
        );
        machine
            .replay_factored_shadow_status
            .set(ReplayFactoredShadowStatus::Failed(
                ReplayFactoredShadowFailure::AllocationFailed,
            ));
        let (record, support) = dpn_b_synthetic_projection_record(&mut machine, 120);
        dpn_b_register_synthetic_clause(
            &mut machine,
            record,
            support,
            RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(120),
                premise: ProofPremise::Constraint(constraint),
            },
        );

        let mut legacy =
            SchemeProjectionEvaluator::with_replay_source(&machine, ReplayEvaluatorSource::Legacy);
        assert!(legacy.eval_record_or_quarantine(record));
    }

    #[test]
    fn rcpf_shadow_exact_relation_matches_legacy_across_extensions_and_carriers() {
        let mut fixture = cdm_replay_claim_fixture();
        let first = fixture.replay(ReplayRule::LowerBoundAdded);
        let root = fixture.coverage_root;
        apply_factored_canonical_duplicate_snapshot(
            &mut fixture.machine,
            fixture.result,
            first,
            &[
                SideTaggedReplayClaim {
                    claim: root,
                    parent_side: ReplayClaimParentSide::Lower,
                },
                SideTaggedReplayClaim {
                    claim: root,
                    parent_side: ReplayClaimParentSide::Upper,
                },
            ],
        );
        assert_factored_replay_clause_projection_matches_legacy(&fixture.machine);
        assert_eq!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .len(),
            1
        );
        assert_eq!(
            factored_replay_clause_link_oracle(&fixture.machine).len(),
            1
        );
        let replay_clause = RecordProofClause::ReplayConjunction {
            carrier: first,
            lower_premise: first.lower,
            upper_premise: first.upper,
        };
        let replay_parent = ClaimQualifiedParent::ReplayConstraint {
            parent_claim: root,
            parent_side: ReplayClaimParentSide::Lower,
            replay: first,
        };
        assert_eq!(
            fixture
                .machine
                .try_authoritative_claim_parent_clause_link_is_registered(
                    fixture.result,
                    fixture.lower_record,
                    replay_parent,
                    SchemeProjectionProofSupport::Claimed(root),
                    replay_clause,
                ),
            Ok(true),
            "the Factored A1 predicate reads the occurrence parent sets"
        );
        let single_root = fixture
            .machine
            .try_factored_upper_materialization_full(fixture.upper_record, fixture.result)
            .expect("the single-root summary is readable");
        assert_eq!(single_root.len(), 1);
        assert!(single_root.contains_key(&(fixture.upper_record, root)));

        let endpoint = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let late_root = add_original_replay_parent_claim(
            &mut fixture.machine,
            TypeVar(90),
            endpoint,
            ConstraintRecordId(30_000),
        );
        assert_eq!(
            fixture
                .machine
                .try_factored_replay_clause_link_is_registered(
                    fixture.result,
                    fixture.lower_record,
                    late_root,
                    first,
                    replay_clause,
                ),
            Ok(false),
            "an occurrence does not acquire a link before the root delta commits"
        );
        apply_factored_canonical_duplicate_snapshot(
            &mut fixture.machine,
            fixture.result,
            first,
            &[SideTaggedReplayClaim {
                claim: late_root,
                parent_side: ReplayClaimParentSide::Lower,
            }],
        );
        assert_factored_replay_clause_projection_matches_legacy(&fixture.machine);
        assert_eq!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .len(),
            1,
            "a late root reuses the occurrence clause"
        );
        assert_eq!(
            factored_replay_clause_link_oracle(&fixture.machine).len(),
            2
        );
        assert_eq!(
            fixture
                .machine
                .try_factored_replay_clause_link_is_registered(
                    fixture.result,
                    fixture.lower_record,
                    late_root,
                    first,
                    replay_clause,
                ),
            Ok(true),
            "the exact predicate observes a late root without another clause"
        );
        assert!(
            fixture
                .machine
                .try_factored_upper_materialization_full(fixture.upper_record, fixture.result)
                .expect("the late-root summary is readable")
                .contains_key(&(fixture.upper_record, late_root))
        );
        assert_eq!(
            fixture
                .machine
                .try_factored_lower_projection_full(fixture.result, [])
                .expect("late-root lower adapter")
                .claimed_roots,
            vec![root, late_root]
        );

        let alternate_claim = add_derived_replay_parent_claim(
            &mut fixture.machine,
            TypeVar(91),
            endpoint,
            root,
            ConstraintRecordId(30_001),
            fixture.result,
            first,
        );
        assert_ne!(alternate_claim, root);
        apply_factored_canonical_duplicate_snapshot(
            &mut fixture.machine,
            fixture.result,
            first,
            &[SideTaggedReplayClaim {
                claim: alternate_claim,
                parent_side: ReplayClaimParentSide::Lower,
            }],
        );

        let second = fixture.replay(ReplayRule::UpperBoundAdded);
        let second_parents = [SideTaggedReplayClaim {
            claim: late_root,
            parent_side: ReplayClaimParentSide::Upper,
        }];
        apply_factored_canonical_duplicate_snapshot(
            &mut fixture.machine,
            fixture.result,
            second,
            &second_parents,
        );

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        );
        assert_eq!(fixture.machine.replay_occurrences.occurrences.len(), 2);
        assert_eq!(
            legacy_replay_parent_oracle(&fixture.machine),
            factored_replay_parent_oracle(&fixture.machine)
        );
        assert_eq!(
            legacy_replay_first_witness_oracle(&fixture.machine),
            factored_replay_first_witness_oracle(&fixture.machine)
        );
        assert_factored_replay_clause_projection_matches_legacy(&fixture.machine);
        assert_eq!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .len(),
            2,
            "each exact carrier has one occurrence clause"
        );
        assert_eq!(
            factored_replay_clause_link_oracle(&fixture.machine).len(),
            3,
            "the shared lower/upper root is deduplicated while the second carrier stays exact"
        );
        let empty_version = fixture.machine.replay_parent_sets.empty_version();
        assert!(
            fixture
                .machine
                .replay_result_summary
                .projected_parent_versions
                .iter()
                .all(|(_, _, version)| *version != empty_version)
        );
        for occurrence in &fixture.machine.replay_occurrences.occurrences {
            for (side, version) in [
                (ReplayClaimParentSide::Lower, occurrence.lower_parents),
                (ReplayClaimParentSide::Upper, occurrence.upper_parents),
            ] {
                if version != empty_version {
                    assert!(
                        fixture
                            .machine
                            .replay_result_summary
                            .projected_parent_versions
                            .contains(&(occurrence.result, side, version)),
                        "every changed nonempty current version is recorded as projected"
                    );
                }
            }
        }
        let first_occurrence = fixture.machine.replay_occurrences.occurrences[0].clone();
        assert_eq!(
            fixture
                .machine
                .replay_parent_sets
                .representative_claim(first_occurrence.lower_parents, root)
                .expect("first occurrence lower version is valid"),
            Some(root),
            "the first claim for a canonical root remains representative"
        );

        let before_noop = replay_factored_storage_census(&fixture.machine);
        apply_factored_canonical_duplicate_snapshot(
            &mut fixture.machine,
            fixture.result,
            second,
            &second_parents,
        );
        assert_eq!(
            replay_factored_storage_census(&fixture.machine),
            before_noop
        );
        assert_eq!(
            legacy_replay_parent_oracle(&fixture.machine),
            factored_replay_parent_oracle(&fixture.machine)
        );
        assert_eq!(
            legacy_replay_first_witness_oracle(&fixture.machine),
            factored_replay_first_witness_oracle(&fixture.machine)
        );
    }

    #[test]
    fn rcpf_summary_first_witness_tracks_legacy_insertion_order() {
        for alternate_first in [false, true] {
            let mut fixture = cdm_replay_claim_fixture();
            let replay = fixture.replay(ReplayRule::LowerBoundAdded);
            let root = fixture.coverage_root;
            let endpoint = fixture.machine.constraint_records[fixture.result.0 as usize]
                .key
                .upper;
            let alternate = add_derived_replay_parent_claim(
                &mut fixture.machine,
                TypeVar(92),
                endpoint,
                root,
                ConstraintRecordId(30_002),
                fixture.result,
                replay,
            );
            let ordered_claims = if alternate_first {
                [alternate, root]
            } else {
                [root, alternate]
            };
            let parents = ordered_claims.map(|claim| SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Lower,
            });

            apply_factored_canonical_duplicate_snapshot(
                &mut fixture.machine,
                fixture.result,
                replay,
                &parents,
            );

            let legacy = legacy_replay_first_witness_oracle(&fixture.machine);
            let factored = factored_replay_first_witness_oracle(&fixture.machine);
            assert_eq!(legacy, factored);
            assert_eq!(
                legacy[&(fixture.result, root)].0,
                ordered_claims[0],
                "the first legacy claim wins for its insertion order"
            );
            assert!(matches!(
                fixture
                    .machine
                    .try_factored_upper_materialization_full(
                        fixture.upper_record,
                        fixture.result,
                    )
                    .expect("the multi-candidate summary is readable")
                    [&(fixture.upper_record, root)],
                UpperReplayClaimLineage::ReplayConstraint { parent_claim, .. }
                    if parent_claim == ordered_claims[0]
            ));
            let lower = fixture
                .machine
                .try_factored_lower_projection_full(fixture.result, [])
                .expect("same-root lower adapter");
            assert_eq!(lower.claimed_roots, vec![root]);
        }
    }

    #[test]
    fn rcpf_clause_projection_bootstraps_after_the_target_record_consumes_metadata() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot_with_materialization(
            &mut fixture.machine,
            fixture.result,
            replay,
            &[parent],
            false,
        );

        assert!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .is_empty(),
            "the occurrence exists before legacy clause materialization"
        );
        fixture.machine.enable_replay_factored_event_oracle();
        fixture
            .machine
            .register_constraint_upper_replay_claims(fixture.upper_record, Some(fixture.result));

        assert_factored_replay_clause_projection_matches_legacy(&fixture.machine);
        assert!(
            fixture
                .machine
                .try_factored_upper_materialization_full(fixture.upper_record, fixture.result)
                .expect("the target-late summary is readable")
                .contains_key(&(fixture.upper_record, fixture.coverage_root))
        );
        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        );
        assert_eq!(
            factored_replay_clause_link_oracle(&fixture.machine).len(),
            1
        );
    }

    #[test]
    fn rcpf_clause_projection_excludes_evidence_and_trivial_replays() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        fixture.machine.register_replay_evidence_clause_link(
            fixture.lower_record,
            fixture.coverage_root,
            replay,
        );
        assert!(
            fixture
                .machine
                .bounds
                .record_proof_clause_links_by_lower_record
                .contains_key(&fixture.lower_record),
            "the evidence path has a legacy ReplayConjunction link"
        );

        let lower = fixture.machine.alloc_pos(Pos::Bot);
        let upper = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let mut plan = BoundReplayPlan::default();
        fixture.machine.push_replay_constraint_or_prefilter(
            lower,
            ConstraintWeights::empty(),
            upper,
            replay,
            [fixture.parent].into_iter().collect(),
            &mut plan,
        );
        assert_eq!(plan.trivial_actions.len(), 1);
        fixture
            .machine
            .apply_prefiltered_replay_provenance_with_parent_drafts(
                plan.duplicate_actions,
                plan.trivial_actions,
                &plan.parent_drafts,
            );

        assert!(fixture.machine.replay_occurrences.occurrences.is_empty());
        assert!(
            fixture
                .machine
                .replay_clause_projection
                .clause_by_record_and_occurrence
                .is_empty()
        );
        assert!(
            fixture
                .machine
                .replay_clause_projection
                .replay_attributed_claim_supports
                .is_empty()
        );
        assert!(factored_replay_clause_link_oracle(&fixture.machine).is_empty());
    }

    #[test]
    fn rcpf_e2a_claimed_attribution_matrix_partitions_all_five_sources_at_the_writer() {
        fn matrix_lower(
            machine: &mut ConstraintMachine,
            result: ConstraintRecordId,
            owner: u32,
        ) -> BoundRecordId {
            let lower = machine.constraint_records[result.0 as usize].key.lower;
            machine
                .bounds
                .add_lower(
                    TypeVar(owner),
                    lower,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                )
                .id
        }

        fn matrix_upper(
            machine: &mut ConstraintMachine,
            result: ConstraintRecordId,
            owner: u32,
        ) -> BoundRecordId {
            let upper = machine.constraint_records[result.0 as usize].key.upper;
            machine
                .bounds
                .add_upper(
                    TypeVar(owner),
                    upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                )
                .id
        }

        fn matrix_root(
            machine: &mut ConstraintMachine,
            result: ConstraintRecordId,
            owner: u32,
            producer: u32,
        ) -> UpperReplayClaimId {
            let record = matrix_upper(machine, result, owner);
            machine
                .bounds
                .original_upper_replay_claim(
                    record,
                    ConstraintRecordId(producer),
                    UpperReplayClaimKind::Direct,
                )
                .claim
        }

        let mut fixture = cdm_replay_claim_fixture();
        assert_eq!(
            fixture
                .machine
                .bounds
                .flat_retained_attributed_claim_supports
                .len(),
            1,
            "the direct constraint fixture starts with one Original/Standalone attribution"
        );
        assert_eq!(
            fixture.machine.bounds.attributed_claim_supports,
            fixture
                .machine
                .bounds
                .flat_retained_attributed_claim_supports
        );
        assert!(
            fixture
                .machine
                .replay_clause_projection
                .replay_attributed_claim_supports
                .is_empty()
        );
        let original_key = *fixture
            .machine
            .bounds
            .flat_retained_attributed_claim_supports
            .iter()
            .next()
            .expect("the Original/Standalone attribution");
        assert_eq!(
            fixture.machine.bounds.upper_replay_claims[original_key.1.0 as usize].lineage,
            UpperReplayClaimLineage::Original
        );

        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let replay_parent = fixture.parent;
        register_factored_parent_snapshot(
            &mut fixture.machine,
            fixture.result,
            replay,
            &[replay_parent],
        );
        let replay_key = (fixture.lower_record, fixture.coverage_root);
        assert!(fixture.machine.bounds.upper_replay_claims.iter().any(|claim| {
            claim.coverage_root == fixture.coverage_root
                && matches!(
                    claim.lineage,
                    UpperReplayClaimLineage::ReplayConstraint { .. }
                )
        }));

        let structural_root = matrix_root(&mut fixture.machine, fixture.result, 80_000, 80_000);
        let structural_derivation = StructuralDerivation {
            parent: fixture.result,
            rule: StructuralDerivationRule::FunctionReturn,
        };
        let structural_record = matrix_upper(&mut fixture.machine, fixture.result, 80_001);
        let structural_claim = fixture.machine.bounds.derived_upper_replay_claim(
            structural_record,
            structural_root,
            ConstraintRecordId(80_001),
            |depth| UpperReplayClaimLineage::StructuralConstraint {
                parent_claim: structural_root,
                result: fixture.result,
                derivation: structural_derivation,
                depth,
            },
        );
        assert!(matches!(
            fixture.machine.bounds.upper_replay_claims[structural_claim.claim.0 as usize].lineage,
            UpperReplayClaimLineage::StructuralConstraint { .. }
        ));
        let structural_lower = matrix_lower(&mut fixture.machine, fixture.result, 80_002);
        fixture.machine.register_claim_parent_clause_links(
            fixture.result,
            structural_lower,
            &[ClaimQualifiedParent::StructuralConstraint {
                parent_claim: structural_claim.claim,
                derivation: structural_derivation,
            }],
        );
        let structural_key = (structural_lower, structural_root);

        let reduction_root = matrix_root(&mut fixture.machine, fixture.result, 80_003, 80_002);
        let reduction_derivation = RowDerivationId(80_003);
        let reduction_record = matrix_upper(&mut fixture.machine, fixture.result, 80_004);
        let reduction_claim = fixture.machine.bounds.derived_upper_replay_claim(
            reduction_record,
            reduction_root,
            ConstraintRecordId(80_004),
            |depth| UpperReplayClaimLineage::ReductionRouteConstraint {
                parent_claim: reduction_root,
                result: fixture.result,
                derivation: reduction_derivation,
                depth,
            },
        );
        assert!(matches!(
            fixture.machine.bounds.upper_replay_claims[reduction_claim.claim.0 as usize].lineage,
            UpperReplayClaimLineage::ReductionRouteConstraint { .. }
        ));
        let reduction_lower = matrix_lower(&mut fixture.machine, fixture.result, 80_005);
        fixture.machine.register_claim_parent_clause_links(
            fixture.result,
            reduction_lower,
            &[ClaimQualifiedParent::ReductionRouteConstraint {
                parent_claim: reduction_claim.claim,
                derivation: reduction_derivation,
            }],
        );
        let reduction_key = (reduction_lower, reduction_root);

        let evidence_root = matrix_root(&mut fixture.machine, fixture.result, 80_006, 80_005);
        let evidence_lower = matrix_lower(&mut fixture.machine, fixture.result, 80_007);
        let evidence_replay = BinaryReplayDerivation {
            pivot: TypeVar(80_007),
            lower: evidence_lower,
            upper: fixture.machine.bounds.upper_replay_claims[evidence_root.0 as usize]
                .current_record,
            rule: ReplayRule::UpperBoundAdded,
        };
        let evidence_record = matrix_upper(&mut fixture.machine, fixture.result, 80_008);
        let evidence_claim = fixture.machine.bounds.derived_upper_replay_claim(
            evidence_record,
            evidence_root,
            ConstraintRecordId(80_006),
            |depth| UpperReplayClaimLineage::ReplayEvidence {
                parent_claim: evidence_root,
                parent_side: ReplayClaimParentSide::Upper,
                replay: evidence_replay,
                depth,
            },
        );
        assert!(matches!(
            fixture.machine.bounds.upper_replay_claims[evidence_claim.claim.0 as usize].lineage,
            UpperReplayClaimLineage::ReplayEvidence { .. }
        ));
        fixture.machine.register_replay_evidence_clause_link(
            evidence_lower,
            evidence_claim.claim,
            evidence_replay,
        );
        let evidence_key = (evidence_lower, evidence_root);

        let flat_retained = FxHashSet::from_iter([
            original_key,
            structural_key,
            reduction_key,
            evidence_key,
        ]);
        let replay_attributed = FxHashSet::from_iter([replay_key]);
        let all_source = flat_retained
            .union(&replay_attributed)
            .copied()
            .collect::<FxHashSet<_>>();
        assert_eq!(
            fixture
                .machine
                .bounds
                .flat_retained_attributed_claim_supports,
            flat_retained
        );
        assert_eq!(
            fixture
                .machine
                .replay_clause_projection
                .replay_attributed_claim_supports,
            replay_attributed
        );
        assert_eq!(fixture.machine.bounds.attributed_claim_supports, all_source);

        let attribution_keys = [
            original_key,
            replay_key,
            structural_key,
            reduction_key,
            evidence_key,
        ];
        let production_results = |machine: &ConstraintMachine| {
            [ReplayEvaluatorSource::Legacy, ReplayEvaluatorSource::Factored]
                .map(|source| {
                    let evaluator = SchemeProjectionEvaluator::with_replay_source(machine, source);
                    attribution_keys.map(|(record, root)| {
                        evaluator.support_has_clause_link(
                            record,
                            SchemeProjectionProofSupport::Claimed(root),
                        )
                    })
                })
        };
        assert_eq!(production_results(&fixture.machine), [[true; 5]; 2]);
        fixture
            .machine
            .try_compare_factored_claimed_attribution_union()
            .expect("the five-source writer partition must reconstruct the all-source relation");

        let shadow = std::mem::take(
            &mut fixture
                .machine
                .bounds
                .flat_retained_attributed_claim_supports,
        );
        assert_eq!(
            production_results(&fixture.machine),
            [[true; 5], [false, true, false, false, false]],
            "Legacy remains all-source while Factored reads replay OR flat-retained attribution"
        );
        assert!(matches!(
            fixture
                .machine
                .try_compare_factored_claimed_attribution_union(),
            Err(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ClaimedAttributionUnion
            ))
        ));
        fixture
            .machine
            .bounds
            .flat_retained_attributed_claim_supports = shadow;
        assert_eq!(production_results(&fixture.machine), [[true; 5]; 2]);
    }

    #[test]
    fn rcpf_e2b_claimed_attribution_union_mismatch_quarantines_event_oracle() {
        let mut fixture = cdm_replay_claim_fixture();
        fixture.machine.enable_replay_factored_event_oracle();
        let original_key = *fixture
            .machine
            .bounds
            .flat_retained_attributed_claim_supports
            .iter()
            .next()
            .expect("the fixture starts with one Original attribution");
        assert!(
            fixture
                .machine
                .bounds
                .flat_retained_attributed_claim_supports
                .remove(&original_key)
        );

        mark_next_replay_soak_failure_as_intentional();
        fixture
            .machine
            .observe_factored_replay_event_boundary(fixture.result);

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::ClaimedAttributionUnion
            ))
        );
    }

    #[test]
    fn rcpf_f_consumer_2_factored_dependency_chain_matches_legacy_oracle() {
        let mut fixture = cdm_replay_claim_fixture();
        fixture.machine.enable_replay_factored_event_oracle();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot(
            &mut fixture.machine,
            fixture.result,
            replay,
            &[parent],
        );

        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let dependent = fixture
            .machine
            .bounds
            .add_lower(
                TypeVar(89_000),
                key.lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let mut visited = FxHashSet::default();
        fixture.machine.register_premise_dependency_chain(
            ProofPremise::Constraint(fixture.result),
            dependent,
            &mut visited,
        );

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        );
        for premise in [
            ProofPremise::Constraint(fixture.result),
            ProofPremise::Record(fixture.lower_record),
            ProofPremise::Record(replay.lower),
            ProofPremise::Record(replay.upper),
        ] {
            assert!(
                fixture
                    .machine
                    .bounds
                    .dependent_records_by_premise
                    .get(&premise)
                    .is_some_and(|dependents| dependents.contains(&dependent)),
                "Factored dependency-chain plan omitted {premise:?}"
            );
        }
    }

    #[test]
    fn rcpf_f_consumer_2_factored_lookup_failure_commits_no_dependency_edges() {
        let mut fixture = cdm_replay_claim_fixture();
        let missing = crate::constraints::replay_factored::ReplayOccurrenceId(u32::MAX);
        fixture
            .machine
            .replay_occurrences
            .by_result
            .insert(fixture.result, vec![missing]);
        let before = fixture
            .machine
            .bounds
            .dependent_records_by_premise
            .clone();
        let mut visited = FxHashSet::default();

        mark_next_replay_soak_failure_as_intentional();
        fixture.machine.register_premise_dependency_chain(
            ProofPremise::Constraint(fixture.result),
            fixture.lower_record,
            &mut visited,
        );

        assert_eq!(
            fixture.machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::UnknownReplayOccurrence(
                missing
            ))
        );
        assert_eq!(
            fixture.machine.bounds.dependent_records_by_premise,
            before,
            "Factored dependency-chain lookup must finish before any edge mutation"
        );
        assert!(visited.is_empty());
    }

    #[test]
    fn rcpf_f_consumer_2_legacy_rollback_ignores_factored_occurrence_corruption() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.register_replay_claim_parents(
            fixture.result,
            replay,
            &[fixture.parent],
            true,
        );
        fixture.machine.replay_occurrences.by_result.insert(
            fixture.result,
            vec![crate::constraints::replay_factored::ReplayOccurrenceId(
                u32::MAX,
            )],
        );
        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let dependent = fixture
            .machine
            .bounds
            .add_lower(
                TypeVar(89_001),
                key.lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let mut visited = FxHashSet::default();

        fixture.machine.register_premise_dependency_chain(
            ProofPremise::Constraint(fixture.result),
            dependent,
            &mut visited,
        );

        assert_eq!(fixture.machine.replay_factored_terminal_failure(), None);
        for premise in [replay.lower, replay.upper] {
            assert!(
                fixture
                    .machine
                    .bounds
                    .dependent_records_by_premise
                    .get(&ProofPremise::Record(premise))
                    .is_some_and(|dependents| dependents.contains(&dependent))
            );
        }
    }

    fn assert_replay_shadow_does_not_interfere(
        shadow: &CdmReplayClaimFixture,
        legacy: &CdmReplayClaimFixture,
        shadow_affected: Vec<DependencyKey>,
        legacy_affected: Vec<DependencyKey>,
    ) {
        assert_eq!(
            cdm_oracle_ledger_snapshot(shadow),
            cdm_oracle_ledger_snapshot(legacy),
            "projectability and projection ledgers remain legacy-authoritative"
        );
        assert_eq!(
            shadow.machine.bounds.replay_claim_parent_keys,
            legacy.machine.bounds.replay_claim_parent_keys
        );
        assert_eq!(
            shadow.machine.bounds.qualified_carrier_index,
            legacy.machine.bounds.qualified_carrier_index
        );
        assert_eq!(shadow.machine.epoch, legacy.machine.epoch);
        assert_eq!(
            shadow.machine.provenance_epoch,
            legacy.machine.provenance_epoch
        );
        assert_eq!(shadow.machine.queue.len(), legacy.machine.queue.len());
        assert_eq!(shadow.machine.events.len(), legacy.machine.events.len());
        assert_eq!(shadow_affected, legacy_affected);
        assert_eq!(
            shadow.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        );
    }

    #[test]
    fn rcpf_event_oracle_is_opt_in_and_shadow_writes_do_not_interfere() {
        let mut shadow = cdm_replay_claim_fixture();
        let mut legacy =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        shadow.machine.enable_replay_factored_event_oracle();
        let mut epoch_sequence = Vec::new();

        let first = shadow.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(first, legacy.replay(ReplayRule::LowerBoundAdded));
        for fixture in [&mut shadow, &mut legacy] {
            assert_eq!(
                fixture
                    .machine
                    .merge_replay_derivation(fixture.result, first),
                ReplayDerivationInsert::Inserted
            );
        }
        let shadow_journal = shadow.machine.activate_method_role_mutations();
        let legacy_journal = legacy.machine.activate_method_role_mutations();
        let shadow_parent = shadow.parent;
        RCPF_D2C_CLAUSE_LINK_REGISTRATION_PROBES.with(|probes| probes.set(0));
        RCPF_D2C_EVENT_ORACLE_PROBES.with(|probes| probes.set(0));
        register_factored_parent_snapshot(
            &mut shadow.machine,
            shadow.result,
            first,
            &[shadow_parent],
        );
        assert_eq!(
            RCPF_D2C_CLAUSE_LINK_REGISTRATION_PROBES.with(std::cell::Cell::get),
            1,
            "the factored eager path commits legacy clause links exactly once in Phase A"
        );
        legacy
            .machine
            .register_replay_claim_parents(legacy.result, first, &[legacy.parent], true);
        let shadow_affected = changed_keys(shadow.machine.take_method_role_mutations());
        let legacy_affected = changed_keys(legacy.machine.take_method_role_mutations());
        shadow_journal.finish();
        legacy_journal.finish();
        assert_replay_shadow_does_not_interfere(&shadow, &legacy, shadow_affected, legacy_affected);
        assert_eq!(RCPF_D2C_EVENT_ORACLE_PROBES.with(std::cell::Cell::get), 1);
        assert!(
            shadow
                .machine
                .bounds
                .derived_claim_by_record_and_root
                .contains_key(&(shadow.upper_record, shadow.coverage_root)),
            "the complete-event oracle runs after eager derived materialization"
        );
        epoch_sequence.push((shadow.machine.epoch, shadow.machine.provenance_epoch));

        let endpoint = shadow.machine.constraint_records[shadow.result.0 as usize]
            .key
            .upper;
        let shadow_late = add_original_replay_parent_claim(
            &mut shadow.machine,
            TypeVar(96),
            endpoint,
            ConstraintRecordId(31_000),
        );
        let legacy_late = add_original_replay_parent_claim(
            &mut legacy.machine,
            TypeVar(96),
            endpoint,
            ConstraintRecordId(31_000),
        );
        assert_eq!(shadow_late, legacy_late);
        let shadow_journal = shadow.machine.activate_method_role_mutations();
        let legacy_journal = legacy.machine.activate_method_role_mutations();
        register_factored_parent_snapshot(
            &mut shadow.machine,
            shadow.result,
            first,
            &[SideTaggedReplayClaim {
                claim: shadow_late,
                parent_side: ReplayClaimParentSide::Upper,
            }],
        );
        legacy.machine.register_replay_claim_parents(
            legacy.result,
            first,
            &[SideTaggedReplayClaim {
                claim: legacy_late,
                parent_side: ReplayClaimParentSide::Upper,
            }],
            true,
        );
        let shadow_affected = changed_keys(shadow.machine.take_method_role_mutations());
        let legacy_affected = changed_keys(legacy.machine.take_method_role_mutations());
        shadow_journal.finish();
        legacy_journal.finish();
        assert_replay_shadow_does_not_interfere(&shadow, &legacy, shadow_affected, legacy_affected);
        epoch_sequence.push((shadow.machine.epoch, shadow.machine.provenance_epoch));

        let second = shadow.replay(ReplayRule::UpperBoundAdded);
        assert_eq!(second, legacy.replay(ReplayRule::UpperBoundAdded));
        for fixture in [&mut shadow, &mut legacy] {
            assert_eq!(
                fixture
                    .machine
                    .merge_replay_derivation(fixture.result, second),
                ReplayDerivationInsert::Inserted
            );
        }
        let shadow_journal = shadow.machine.activate_method_role_mutations();
        let legacy_journal = legacy.machine.activate_method_role_mutations();
        register_factored_parent_snapshot(
            &mut shadow.machine,
            shadow.result,
            second,
            &[SideTaggedReplayClaim {
                claim: shadow_late,
                parent_side: ReplayClaimParentSide::Lower,
            }],
        );
        legacy.machine.register_replay_claim_parents(
            legacy.result,
            second,
            &[SideTaggedReplayClaim {
                claim: legacy_late,
                parent_side: ReplayClaimParentSide::Lower,
            }],
            true,
        );
        let shadow_affected = changed_keys(shadow.machine.take_method_role_mutations());
        let legacy_affected = changed_keys(legacy.machine.take_method_role_mutations());
        shadow_journal.finish();
        legacy_journal.finish();
        assert_replay_shadow_does_not_interfere(&shadow, &legacy, shadow_affected, legacy_affected);
        epoch_sequence.push((shadow.machine.epoch, shadow.machine.provenance_epoch));
        assert!(
            epoch_sequence
                .windows(2)
                .all(|epochs| epochs[0] <= epochs[1])
        );

        // Exercise the two target-late boundaries after the A3 observer has completed.
        let shadow_journal = shadow.machine.activate_method_role_mutations();
        let legacy_journal = legacy.machine.activate_method_role_mutations();
        let shadow_claims = shadow
            .machine
            .register_constraint_upper_replay_claims(shadow.upper_record, Some(shadow.result));
        let legacy_claims = legacy
            .machine
            .register_constraint_upper_replay_claims(legacy.upper_record, Some(legacy.result));
        assert_eq!(shadow_claims, legacy_claims);
        shadow.machine.register_lower_projection_derivation(
            shadow.lower_record,
            Some(shadow.result),
            BoundDerivation::Constraint(shadow.result),
        );
        legacy.machine.register_lower_projection_derivation(
            legacy.lower_record,
            Some(legacy.result),
            BoundDerivation::Constraint(legacy.result),
        );
        let shadow_affected = changed_keys(shadow.machine.take_method_role_mutations());
        let legacy_affected = changed_keys(legacy.machine.take_method_role_mutations());
        shadow_journal.finish();
        legacy_journal.finish();
        assert_replay_shadow_does_not_interfere(&shadow, &legacy, shadow_affected, legacy_affected);
    }

    #[test]
    fn rcpf_event_oracle_mismatch_is_quarantined_after_legacy_noop() {
        let mut fixture = cdm_replay_claim_fixture();
        fixture.machine.enable_replay_factored_event_oracle();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);
        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        );
        let legacy_before = cdm_oracle_ledger_snapshot(&fixture);
        fixture
            .machine
            .replay_result_summary
            .first_parent_by_root
            .clear();

        mark_next_replay_soak_failure_as_intentional();
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);

        assert_eq!(
            fixture.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::OracleMismatch(
                ReplayFactoredOracleMismatch::FirstReplayWitness
            ))
        );
        assert_eq!(cdm_oracle_ledger_snapshot(&fixture), legacy_before);
    }

    #[test]
    fn rcpf_phase_b_failure_preserves_legacy_parent_admission_before_terminal_stop() {
        let mut shadow = cdm_replay_claim_fixture();
        let mut legacy =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let projection_claims_before = shadow
            .machine
            .bounds
            .scheme_projection_claims_by_lower_record[&shadow.lower_record]
            .clone();
        let projection_proofs_before =
            shadow.machine.bounds.projection_proofs_by_lower_record[&shadow.lower_record].clone();
        let first = shadow.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(first, legacy.replay(ReplayRule::LowerBoundAdded));
        for fixture in [&mut shadow, &mut legacy] {
            assert_eq!(
                fixture
                    .machine
                    .merge_replay_derivation(fixture.result, first),
                ReplayDerivationInsert::Inserted
            );
        }

        shadow.machine.replay_parent_sets.fail_next_reservation();
        let shadow_parent = shadow.parent;
        register_factored_parent_snapshot(
            &mut shadow.machine,
            shadow.result,
            first,
            &[shadow_parent],
        );
        legacy
            .machine
            .register_replay_claim_parents(legacy.result, first, &[legacy.parent], true);

        assert_eq!(
            shadow.machine.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            shadow.machine.bounds.claim_parents_by_constraint[&shadow.result].len(),
            1,
            "the real legacy parent is committed before the factored writer can fail"
        );
        assert!(shadow.machine.replay_occurrences.occurrences.is_empty());
        assert_eq!(
            shadow.machine.bounds.claim_parents_by_constraint[&shadow.result],
            legacy.machine.bounds.claim_parents_by_constraint[&legacy.result]
        );
        assert_eq!(
            shadow.machine.bounds.replay_claim_parent_keys,
            legacy.machine.bounds.replay_claim_parent_keys
        );
        assert_eq!(
            shadow.machine.bounds.qualified_carrier_index,
            legacy.machine.bounds.qualified_carrier_index
        );
        assert_eq!(
            shadow
                .machine
                .bounds
                .scheme_projection_claims_by_lower_record[&shadow.lower_record],
            projection_claims_before,
            "terminal Phase B failure skips eager claim materialization"
        );
        assert_eq!(
            shadow.machine.bounds.projection_proofs_by_lower_record[&shadow.lower_record],
            projection_proofs_before,
            "terminal Phase B failure skips eager projection materialization"
        );
    }

    fn rcpf_c3b_replay_parent_admission_census(parent_count: usize) -> (usize, usize) {
        assert!(parent_count > 0);
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let endpoint = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let mut parents = vec![fixture.parent];
        for index in 1..parent_count {
            let offset = u32::try_from(index).expect("test parent count fits in u32");
            let claim = add_original_replay_parent_claim(
                &mut fixture.machine,
                TypeVar(90_000 + offset),
                endpoint,
                ConstraintRecordId(90_000 + offset),
            );
            parents.push(SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Lower,
            });
        }
        let legacy_before = fixture
            .machine
            .bounds
            .claim_parents_by_constraint
            .get(&fixture.result)
            .map_or(0, Vec::len);
        let keys_before = fixture.machine.bounds.replay_claim_parent_keys.len();
        RCPF_C3B_REPLAY_PARENT_ADMISSION_PROBES.with(|probes| probes.set(0));

        fixture
            .machine
            .register_replay_claim_parents(fixture.result, replay, &parents, false);

        let probes = RCPF_C3B_REPLAY_PARENT_ADMISSION_PROBES.with(std::cell::Cell::get);
        let legacy_after =
            fixture.machine.bounds.claim_parents_by_constraint[&fixture.result].len();
        assert_eq!(legacy_after - legacy_before, parent_count);
        (
            probes,
            fixture.machine.bounds.replay_claim_parent_keys.len() - keys_before,
        )
    }

    #[test]
    fn rcpf_c3b_replay_parent_admission_uses_one_hash_probe_per_parent() {
        assert_eq!(rcpf_c3b_replay_parent_admission_census(1), (1, 1));
        assert_eq!(rcpf_c3b_replay_parent_admission_census(96), (96, 96));
    }

    #[test]
    fn rcpf_c3b_terminal_failure_stops_drain_before_the_next_queued_work() {
        let mut machine = ConstraintMachine::new();
        let pivot = TypeVar(91_000);
        let replay_target = TypeVar(91_001);
        let first_source = TypeVar(91_002);
        let sentinel_source = TypeVar(91_003);
        let sentinel_target = TypeVar(91_004);
        let origin = OriginId::unknown_internal();

        let replay_upper = machine.alloc_neg(Neg::Var(replay_target));
        let replay_parent_record = machine
            .bounds
            .add_upper(
                pivot,
                replay_upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let replay_parent = machine.bounds.original_upper_replay_claim(
            replay_parent_record,
            ConstraintRecordId(91_000),
            UpperReplayClaimKind::Direct,
        );
        machine.apply_scheme_projection_mutation(replay_parent.scheme_projection_mutation);

        let first_lower = machine.alloc_pos(Pos::Var(first_source));
        let first_upper = machine.alloc_neg(Neg::Var(pivot));
        assert!(machine.enqueue_root_subtype(
            first_lower,
            ConstraintWeights::empty(),
            first_upper,
            origin,
        ));
        let sentinel_lower = machine.alloc_pos(Pos::Var(sentinel_source));
        let sentinel_upper = machine.alloc_neg(Neg::Var(sentinel_target));
        assert!(machine.enqueue_root_subtype(
            sentinel_lower,
            ConstraintWeights::empty(),
            sentinel_upper,
            origin,
        ));
        let sentinel = machine
            .constraint_record_id(sentinel_lower, ConstraintWeights::empty(), sentinel_upper)
            .expect("the sentinel work item is queued");

        machine.replay_parent_sets.fail_next_reservation();
        machine.drain();

        assert_eq!(
            machine.replay_factored_terminal_failure(),
            Some(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_eq!(
            machine.queue.front(),
            Some(&ConstraintWork::Subtype(sentinel))
        );
        assert!(
            machine.bounds.of(sentinel_target).is_none(),
            "the queued sentinel must not mutate bounds after terminal failure"
        );
    }

    #[test]
    fn replay_claim_parent_dedup_keeps_each_exact_replay_carrier() {
        let mut machine =
            ConstraintMachine::new_with_replay_read_authority(legacy_rollback_test_authority());
        let source = TypeVar(0);
        let target = TypeVar(1);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        machine.subtype(lower, upper, OriginId::unknown_internal());

        let result = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the direct relation is canonical");
        let lower_record = machine.bounds.of(target).unwrap().lower_record_ids()[0];
        let upper_record = machine.bounds.of(source).unwrap().upper_record_ids()[0];
        let claim = machine.bounds.claims_by_upper_record[&upper_record][0];
        let first = BinaryReplayDerivation {
            pivot: source,
            lower: lower_record,
            upper: upper_record,
            rule: ReplayRule::LowerBoundAdded,
        };
        let second = BinaryReplayDerivation {
            rule: ReplayRule::UpperBoundAdded,
            ..first
        };
        let parent = SideTaggedReplayClaim {
            claim,
            parent_side: ReplayClaimParentSide::Lower,
        };

        assert_eq!(
            machine.merge_replay_derivation(result, first),
            ReplayDerivationInsert::Inserted
        );
        machine.register_replay_claim_parents(result, first, &[parent], false);
        assert_eq!(
            machine.merge_replay_derivation(result, second),
            ReplayDerivationInsert::Inserted
        );
        machine.register_replay_claim_parents(result, second, &[parent], false);

        let exact_claim_parents = |replay| {
            machine
                .bounds
                .claim_parents_by_constraint
                .get(&result)
                .into_iter()
                .flatten()
                .filter(|parent| {
                    matches!(
                        parent,
                        ClaimQualifiedParent::ReplayConstraint {
                            replay: candidate,
                            ..
                        } if *candidate == replay
                    )
                })
                .count()
        };
        assert_eq!(exact_claim_parents(first), 1);
        assert_eq!(
            exact_claim_parents(second),
            1,
            "dedup by result/root/side must not leave a second exact replay carrier unqualified"
        );
    }

    #[test]
    fn cdm_a_9_2_exact_carrier_arrival_order_preserves_bulk_snapshot() {
        let lower_first =
            cdm_carrier_order_snapshot([ReplayRule::LowerBoundAdded, ReplayRule::UpperBoundAdded]);
        let upper_first =
            cdm_carrier_order_snapshot([ReplayRule::UpperBoundAdded, ReplayRule::LowerBoundAdded]);

        assert_eq!(
            lower_first, upper_first,
            "exact carrier arrival order preserves parent keys, canonical roots, ledger, and inclusion"
        );
    }

    #[test]
    fn cdm_a_9_1_current_eager_path_matches_bulk_oracle() {
        let mut current =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = current.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            current
                .machine
                .merge_replay_derivation(current.result, replay),
            ReplayDerivationInsert::Inserted
        );
        current.machine.register_replay_claim_parents(
            current.result,
            replay,
            &[current.parent],
            true,
        );

        let mut oracle =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = oracle.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            oracle
                .machine
                .merge_replay_derivation(oracle.result, replay),
            ReplayDerivationInsert::Inserted
        );
        oracle.machine.register_replay_claim_parents(
            oracle.result,
            replay,
            &[oracle.parent],
            false,
        );
        oracle
            .machine
            .recompute_claim_parent_bulk_oracle(oracle.result);

        assert_eq!(
            cdm_oracle_ledger_snapshot(&current),
            cdm_oracle_ledger_snapshot(&oracle),
            "the production eager call and separately invoked bulk oracle agree on all four ledger surfaces"
        );
    }

    #[test]
    fn cdm_a_9_4_independent_then_claimed_keeps_both_occurrences() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let independent = fixture.replay(ReplayRule::LowerBoundAdded);
        let bootstrap_claimed = fixture.replay(ReplayRule::UpperBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, independent),
            ReplayDerivationInsert::Inserted
        );
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, bootstrap_claimed),
            ReplayDerivationInsert::Inserted
        );

        fixture.machine.register_replay_claim_parents(
            fixture.result,
            bootstrap_claimed,
            &[fixture.parent],
            true,
        );
        let independent_support = ProjectionProofCarrier::ReplayConstraint {
            result: fixture.result,
            derivation: independent,
        };
        assert!(
            fixture.machine.bounds.projection_proofs_by_lower_record[&fixture.lower_record]
                .iter()
                .any(|proof| {
                    proof.support == SchemeProjectionProofSupport::Independent(independent_support)
                }),
            "bootstrap records the exact unqualified replay occurrence as independent"
        );

        fixture.machine.register_replay_claim_parents(
            fixture.result,
            independent,
            &[fixture.parent],
            true,
        );
        let proofs =
            &fixture.machine.bounds.projection_proofs_by_lower_record[&fixture.lower_record];
        assert!(
            proofs.iter().any(|proof| {
                proof.support == SchemeProjectionProofSupport::Independent(independent_support)
            }),
            "the earlier independent occurrence remains in the add-only ledger"
        );
        assert!(
            proofs.iter().any(|proof| {
                matches!(proof.support, SchemeProjectionProofSupport::Claimed(claim)
                    if fixture.machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root
                        == fixture.coverage_root)
            }),
            "the later claim-qualified occurrence links the same root separately"
        );
        assert!(
            fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
                .iter()
                .any(|parent| {
                    matches!(parent, ClaimQualifiedParent::ReplayConstraint { replay, .. }
                        if *replay == independent)
                }),
            "the claimed occurrence retains its exact replay carrier"
        );
    }

    #[test]
    fn cdm_a_9_5_second_exact_carrier_keeps_bookkeeping_without_rematerializing_root() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let first = fixture.replay(ReplayRule::LowerBoundAdded);
        let second = fixture.replay(ReplayRule::UpperBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, first),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.register_replay_claim_parents(
            fixture.result,
            first,
            &[fixture.parent],
            true,
        );
        let claims_after_first = fixture.machine.bounds.upper_replay_claims.len();
        let proofs_after_first =
            fixture.machine.bounds.projection_proofs_by_lower_record[&fixture.lower_record].len();

        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, second),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.register_replay_claim_parents(
            fixture.result,
            second,
            &[fixture.parent],
            true,
        );

        let exact_keys = fixture
            .machine
            .bounds
            .replay_claim_parent_keys
            .iter()
            .filter(|key| {
                key.result == fixture.result && key.coverage_root == fixture.coverage_root
            })
            .count();
        let exact_parents = fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
            .iter()
            .filter(|parent| {
                matches!(parent, ClaimQualifiedParent::ReplayConstraint { parent_claim, .. }
                    if fixture.machine.bounds.upper_replay_claims[parent_claim.0 as usize]
                        .coverage_root == fixture.coverage_root)
            })
            .count();
        let materialized_roots = fixture
            .machine
            .bounds
            .derived_claim_by_record_and_root
            .keys()
            .filter(|(record, root)| {
                *record == fixture.upper_record && *root == fixture.coverage_root
            })
            .count();
        let linked_roots = fixture
            .machine
            .bounds
            .scheme_projection_claims_by_lower_record[&fixture.lower_record]
            .iter()
            .filter(|claim| {
                fixture.machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root
                    == fixture.coverage_root
            })
            .count();

        assert_eq!((exact_keys, exact_parents), (2, 2));
        assert_eq!(
            (materialized_roots, linked_roots),
            (1, 1),
            "the upper claim and lower ledger remain canonical per (record, root)"
        );
        assert_eq!(
            fixture.machine.bounds.upper_replay_claims.len(),
            claims_after_first,
            "the second exact carrier does not allocate another derived claim"
        );
        assert_eq!(
            fixture.machine.bounds.projection_proofs_by_lower_record[&fixture.lower_record].len(),
            proofs_after_first,
            "the second exact carrier does not add another root-ledger entry"
        );
    }

    #[test]
    fn cdm_a_9_6_materialized_state_census_is_linear_in_link_events() {
        // This baseline counts successful add-only entries, not the current bulk path's repeated
        // scan attempts. CDM-C/D retain these semantic counts while making the processing census
        // event-linear.
        for link_events in [1usize, 4, 16] {
            let census = cdm_linear_materialization_census(link_events);
            assert_eq!(
                census,
                CdmMaterializationCensus {
                    parent_entries: link_events,
                    materialized_roots: link_events,
                    claim_ledger_entries: link_events,
                    claimed_proof_entries: link_events,
                },
                "{link_events} distinct root-link events create one entry on each add-only semantic surface"
            );
        }
    }

    #[test]
    fn cdm_b_qualified_carrier_index_census_is_linear_in_distinct_carriers() {
        for link_events in [1usize, 4, 16] {
            let (materialized, indexed_carriers) =
                cdm_linear_qualified_carrier_index_census(link_events);
            assert_eq!(
                materialized,
                CdmMaterializationCensus {
                    parent_entries: link_events,
                    materialized_roots: link_events,
                    claim_ledger_entries: link_events,
                    claimed_proof_entries: link_events,
                },
                "{link_events} distinct carrier/root links retain the CDM-A semantic census"
            );
            assert_eq!(
                indexed_carriers, link_events,
                "each distinct exact carrier creates one append-only index entry"
            );
        }
    }

    #[test]
    fn cdm_b_no_claim_workload_does_not_allocate_qualified_carrier_index() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let lower = machine.alloc_pos(Pos::Con(vec!["plain".into()], Vec::new()));
        machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );

        assert!(machine.bounds.upper_replay_claims.is_empty());
        assert!(machine.bounds.claim_parents_by_constraint.is_empty());
        assert!(machine.bounds.qualified_carrier_index.is_empty());
        assert_eq!(
            machine.bounds.qualified_carrier_index.capacity(),
            0,
            "an ordinary no-claim bound must not allocate the carrier index"
        );
    }

    #[test]
    fn cdm_b_all_claim_parent_writer_kinds_update_qualified_carrier_index() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.register_replay_claim_parents(
            fixture.result,
            replay,
            &[fixture.parent],
            true,
        );

        let reduction_route = RowDerivationId(10_000);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(reduction_route);
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            reduction_route,
            fixture.coverage_root,
        );

        let child_lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["child".into()], Vec::new()));
        let child_upper = fixture.machine.alloc_neg(Neg::Var(TypeVar(50)));
        let structural_rule = StructuralDerivationRule::FunctionReturn;
        assert!(fixture.machine.enqueue_derived_subtype(
            child_lower,
            ConstraintWeights::empty(),
            child_upper,
            fixture.result,
            structural_rule,
        ));
        let child = fixture
            .machine
            .constraint_record_id(child_lower, ConstraintWeights::empty(), child_upper)
            .expect("the structural child is canonical");

        let parent_carriers = &fixture.machine.bounds.qualified_carrier_index[&fixture.result];
        assert!(parent_carriers.contains(&QualifiedCarrier::Replay(replay)));
        assert!(
            parent_carriers.contains(&QualifiedCarrier::ReductionRoute(reduction_route)),
            "reduction-route admission maintains the same index as replay admission"
        );
        assert!(
            fixture.machine.bounds.qualified_carrier_index[&child].contains(
                &QualifiedCarrier::Structural(StructuralDerivation {
                    parent: fixture.result,
                    rule: structural_rule,
                })
            ),
            "new structural admission maintains the exact child carrier"
        );
    }

    #[test]
    fn dpn_a_original_claim_mirror_is_injective_for_direct_and_reduced_roots() {
        let mut machine = ConstraintMachine::new();
        let upper = machine.alloc_neg(Neg::Var(TypeVar(90)));
        let origin = OriginId::unknown_internal();
        let direct_producer = ConstraintRecordId(50_000);
        let reduced_producer = ConstraintRecordId(50_001);
        let direct_record = machine
            .bounds
            .add_upper(
                TypeVar(91),
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let reduced_record = machine
            .bounds
            .add_upper(
                TypeVar(92),
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let moved_record = machine
            .bounds
            .add_upper(
                TypeVar(93),
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;

        let direct = machine.bounds.original_upper_replay_claim(
            direct_record,
            direct_producer,
            UpperReplayClaimKind::Direct,
        );
        let direct_again = machine.bounds.original_upper_replay_claim(
            direct_record,
            direct_producer,
            UpperReplayClaimKind::Direct,
        );
        let reduced = machine.bounds.original_upper_replay_claim(
            reduced_record,
            reduced_producer,
            UpperReplayClaimKind::Reduced(UnweightedRowReductionRecordId(50_000)),
        );
        assert_eq!(direct.claim, direct_again.claim);
        machine
            .bounds
            .move_upper_replay_claim(direct.claim, moved_record);
        assert!(
            machine.bounds.claims_by_upper_record[&direct_record].is_empty(),
            "the non-collision move removes the root from its old record"
        );
        assert_eq!(
            machine.bounds.claims_by_upper_record[&moved_record],
            vec![direct.claim],
            "the non-collision move keeps the existing single-entry behavior"
        );
        assert_eq!(
            machine.bounds.original_claim_by_record_and_producer[&(moved_record, direct_producer)],
            direct.claim
        );
        assert!(
            !machine
                .bounds
                .derived_claim_by_record_and_root
                .contains_key(&(moved_record, direct.claim))
        );

        let originals = machine
            .bounds
            .upper_replay_claims
            .iter()
            .filter(|claim| claim.lineage == UpperReplayClaimLineage::Original)
            .collect::<Vec<_>>();
        assert_eq!(originals.len(), 2);
        assert_eq!(
            machine.bounds.root_claim_by_producer_constraint.len(),
            originals.len(),
            "the lazy mirror contains exactly one entry per Original claim"
        );
        for claim in originals {
            assert_eq!(claim.coverage_root, claim.id);
            assert_eq!(
                machine.bounds.root_claim_by_producer_constraint[&claim.producer_constraint],
                claim.id,
                "each producer maps injectively to its own Original claim"
            );
        }
        assert_eq!(
            machine.bounds.root_claim_by_producer_constraint[&direct_producer], direct.claim,
            "moving an Original claim's current record does not change producer identity"
        );
        assert_eq!(
            machine.bounds.root_claim_by_producer_constraint[&reduced_producer], reduced.claim,
            "Reduced roots pass through the same shared constructor mirror"
        );
    }

    #[test]
    fn canonical_upper_claim_insertion_census_and_read_subsequences_are_root_ordered() {
        use crate::constraints::{
            canonical_upper_claim_insertion_census,
            reset_canonical_upper_claim_insertion_census,
        };

        reset_canonical_upper_claim_insertion_census();
        let mut machine = ConstraintMachine::new();
        let upper = machine.alloc_neg(Neg::Var(TypeVar(70)));
        let origin = OriginId::unknown_internal();
        let target = machine
            .bounds
            .add_upper(
                TypeVar(71),
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let roots = (0..8)
            .map(|index| {
                let parent_record = machine
                    .bounds
                    .add_upper(
                        TypeVar(80 + index),
                        upper,
                        ConstraintWeights::empty(),
                        BoundDerivation::Origin(origin),
                    )
                    .id;
                machine
                    .bounds
                    .original_upper_replay_claim(
                        parent_record,
                        ConstraintRecordId(70_000 + index),
                        UpperReplayClaimKind::Direct,
                    )
                    .claim
            })
            .collect::<Vec<_>>();
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(72),
            lower: target,
            upper: target,
            rule: ReplayRule::LowerBoundAdded,
        };
        for index in [7, 0, 6, 1, 5, 2, 4, 3] {
            let root = roots[index];
            machine.bounds.derived_upper_replay_claim(
                target,
                root,
                ConstraintRecordId(71_000 + index as u32),
                |depth| UpperReplayClaimLineage::ReplayEvidence {
                    parent_claim: root,
                    parent_side: ReplayClaimParentSide::Upper,
                    replay,
                    depth,
                },
            );
        }

        let claim_roots = |machine: &ConstraintMachine, claims: Vec<UpperReplayClaimId>| {
            claims
                .into_iter()
                .map(|claim| machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            claim_roots(
                &machine,
                machine.bounds.claims_by_upper_record[&target].clone(),
            ),
            roots
        );
        let mut record_lengths = machine
            .bounds
            .claims_by_upper_record
            .values()
            .map(Vec::len)
            .collect::<Vec<_>>();
        record_lengths.sort_unstable();
        assert_eq!(record_lengths, vec![1, 1, 1, 1, 1, 1, 1, 1, 8]);
        let percentile = |percentile: usize| {
            record_lengths[(record_lengths.len() * percentile).div_ceil(100) - 1]
        };
        assert_eq!(
            (*record_lengths.last().unwrap(), percentile(95), percentile(99)),
            (8, 8, 8)
        );
        assert_eq!(canonical_upper_claim_insertion_census(), (16, 4));

        for (index, root) in roots.iter().copied().enumerate().skip(5) {
            machine.bounds.live_coverage_by_root.insert(
                root,
                vec![UnweightedRowReductionRecordId(72_000 + index as u32)],
            );
        }
        assert_eq!(
            claim_roots(&machine, machine.bounds.uncovered_claims(target)),
            roots[..5]
        );
        assert_eq!(
            claim_roots(&machine, machine.bounds.covered_claims(target)),
            roots[5..]
        );
        let lower = machine.alloc_pos(Pos::Var(TypeVar(73)));
        let replay_parent_roots = machine
            .upper_record_replay_claim_parents(lower, target, &[])
            .iter()
            .map(|parent| {
                machine.bounds.upper_replay_claims[parent.claim.0 as usize].coverage_root
            })
            .collect::<Vec<_>>();
        assert_eq!(replay_parent_roots, roots);
    }

    #[test]
    fn moved_root_collision_reconstructs_original_full_and_delta_lineage() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let parent = fixture.parent;
        register_factored_parent_snapshot(&mut fixture.machine, fixture.result, replay, &[parent]);
        let root = fixture.coverage_root;
        let displaced =
            fixture.machine.bounds.derived_claim_by_record_and_root[&(fixture.upper_record, root)];
        assert_ne!(displaced, root);

        fixture
            .machine
            .bounds
            .move_upper_replay_claim(root, fixture.upper_record);

        let full = fixture
            .machine
            .try_factored_upper_materialization_full(fixture.upper_record, fixture.result)
            .expect("the full adapter reconstructs the moved root");
        assert_eq!(
            full.get(&(fixture.upper_record, root)),
            Some(&UpperReplayClaimLineage::Original)
        );
        assert_eq!(full.len(), 1);

        let witness = *fixture
            .machine
            .replay_result_summary
            .first_parent_witness(fixture.result, root)
            .expect("the replay summary index is valid")
            .expect("the delta has a first parent witness");
        let delta = ReplayResultSummaryDelta {
            entries: vec![(root, witness)],
        };
        let delta_lineage = fixture
            .machine
            .try_factored_upper_materialization(
                fixture.upper_record,
                fixture.result,
                delta.entries.iter().copied().map(Ok),
                false,
                false,
            )
            .expect("the delta witness reconstructs the moved root");
        assert_eq!(
            delta_lineage.get(&(fixture.upper_record, root)),
            Some(&UpperReplayClaimLineage::Original)
        );
        assert!(
            fixture
                .machine
                .try_factored_upper_materialization_delta(
                    fixture.upper_record,
                    fixture.result,
                    &delta,
                )
                .expect("the operational delta adapter observes existing materialization")
                .is_empty(),
            "an already-active Original root leaves no delta materialization work"
        );
    }

    #[test]
    fn dpn_a_no_claim_workload_allocates_no_registration_ledgers() {
        let mut machine = ConstraintMachine::new();
        let lower = machine.alloc_pos(Pos::Con(vec!["plain".into()], Vec::new()));
        machine.add_lower_bound(
            TypeVar(0),
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );

        assert!(machine.bounds.root_claim_by_producer_constraint.is_empty());
        assert_eq!(
            machine.bounds.root_claim_by_producer_constraint.capacity(),
            0
        );
        assert!(machine.bounds.record_proof_clauses.is_empty());
        assert!(machine.bounds.record_proof_clause_by_key.is_empty());
        assert!(
            machine
                .bounds
                .record_proof_clause_ids_by_lower_record
                .is_empty()
        );
        assert!(
            machine
                .bounds
                .record_proof_clause_links_by_lower_record
                .is_empty()
        );
        assert!(machine.bounds.record_proof_clause_link_keys.is_empty());
        assert!(machine.bounds.dependent_records_by_premise.is_empty());
    }

    #[test]
    fn dpn_b_cycle_guard_self_cycle_is_not_a_proof() {
        let mut machine = ConstraintMachine::new();
        machine.enable_replay_factored_evaluator_oracle();
        let (record, support) = dpn_b_synthetic_projection_record(&mut machine, 0);
        dpn_b_register_synthetic_clause(
            &mut machine,
            record,
            support,
            RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(0),
                premise: ProofPremise::Record(record),
            },
        );

        assert_eq!(
            machine.scheme_projection_cycle_guard_snapshot(record),
            (false, 1),
            "a self-referential clause is circular evidence, not a projectable proof"
        );
    }

    #[test]
    fn dpn_b_cycle_guard_two_node_cycle_is_not_a_proof() {
        let mut machine = ConstraintMachine::new();
        machine.enable_replay_factored_evaluator_oracle();
        let (first, first_support) = dpn_b_synthetic_projection_record(&mut machine, 1);
        let (second, second_support) = dpn_b_synthetic_projection_record(&mut machine, 2);
        dpn_b_register_synthetic_clause(
            &mut machine,
            first,
            first_support,
            RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(1),
                premise: ProofPremise::Record(second),
            },
        );
        dpn_b_register_synthetic_clause(
            &mut machine,
            second,
            second_support,
            RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(2),
                premise: ProofPremise::Record(first),
            },
        );

        assert_eq!(
            machine.scheme_projection_cycle_guard_snapshot(first),
            (false, 1)
        );
        assert_eq!(
            machine.scheme_projection_cycle_guard_snapshot(second),
            (false, 1),
            "the result is independent of which node begins the reachable-graph walk"
        );
    }

    #[test]
    fn dpn_b_cycle_guard_cyclic_route_plus_independent_source_stays_projectable() {
        for standalone_first in [false, true] {
            let mut machine = ConstraintMachine::new();
            machine.enable_replay_factored_evaluator_oracle();
            let (source, cycle_support) =
                dpn_b_synthetic_projection_record(&mut machine, standalone_first as u32 + 3);
            let (dependent, dependent_support) =
                dpn_b_synthetic_projection_record(&mut machine, standalone_first as u32 + 7);
            let standalone_carrier = ProjectionProofCarrier::Incomplete;
            let standalone_support = SchemeProjectionProofSupport::Independent(standalone_carrier);
            machine
                .bounds
                .projection_proofs_by_lower_record
                .get_mut(&source)
                .expect("the synthetic record has a proof ledger")
                .push(SchemeProjectionProof {
                    lower_record: source,
                    support: standalone_support,
                });
            let cycle_clause = RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(3),
                premise: ProofPremise::Record(dependent),
            };
            let standalone_clause = RecordProofClause::Standalone {
                support: standalone_support,
            };
            let clauses = if standalone_first {
                [
                    (standalone_support, standalone_clause),
                    (cycle_support, cycle_clause),
                ]
            } else {
                [
                    (cycle_support, cycle_clause),
                    (standalone_support, standalone_clause),
                ]
            };
            for (support, clause) in clauses {
                dpn_b_register_synthetic_clause(&mut machine, source, support, clause);
            }
            dpn_b_register_synthetic_clause(
                &mut machine,
                dependent,
                dependent_support,
                RecordProofClause::DerivedUnary {
                    carrier: dpn_b_synthetic_unary_carrier(4),
                    premise: ProofPremise::Record(source),
                },
            );

            let (projectable, cycle_cuts) = machine.scheme_projection_cycle_guard_snapshot(source);
            assert!(
                projectable,
                "the independent OR arm remains a complete proof"
            );
            if standalone_first {
                assert_eq!(cycle_cuts, 0, "OR short-circuit need not enter the cycle");
            } else {
                assert_eq!(
                    cycle_cuts, 1,
                    "cutting one circular arm must continue to the independent source"
                );
            }
            assert!(
                machine.scheme_projection_cycle_guard_snapshot(dependent).0,
                "a dependent route reaches the independent source through the cycle"
            );
        }
    }

    #[test]
    fn dpn_b_cycle_guard_mixed_record_constraint_cycle_is_not_a_proof() {
        let mut machine = ConstraintMachine::new();
        machine.enable_replay_factored_evaluator_oracle();
        let constraint_lower =
            machine.alloc_pos(Pos::Con(vec!["dpn-b-cycle-lower".into()], Vec::new()));
        let constraint_upper =
            machine.alloc_neg(Neg::Con(vec!["dpn-b-cycle-upper".into()], Vec::new()));
        machine.subtype(
            constraint_lower,
            constraint_upper,
            OriginId::unknown_internal(),
        );
        let constraint = machine
            .constraint_record_id(
                constraint_lower,
                ConstraintWeights::empty(),
                constraint_upper,
            )
            .expect("the synthetic constraint is canonical");
        let (record, support) = dpn_b_synthetic_projection_record(&mut machine, 5);
        machine
            .bounds
            .scheme_projection_lower_record_by_constraint
            .insert(constraint, record);
        dpn_b_register_synthetic_clause(
            &mut machine,
            record,
            support,
            RecordProofClause::DerivedUnary {
                carrier: dpn_b_synthetic_unary_carrier(5),
                premise: ProofPremise::Constraint(constraint),
            },
        );

        assert_eq!(
            machine.scheme_projection_cycle_guard_snapshot(record),
            (false, 1),
            "Record -> Constraint -> linked Record re-entry is cut like a record-only cycle"
        );
    }

    #[test]
    fn dpn_b_9_5_late_lower_map_retriggers_constraint_dependents() {
        let mut machine = ConstraintMachine::new();
        let state = UnweightedRowReductionRecordId(60_000);
        let root_upper = machine.alloc_neg(Neg::Con(vec!["dpn-b-covered-root".into()], Vec::new()));
        let root_record = machine
            .bounds
            .add_upper(
                TypeVar(80),
                root_upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let root = machine
            .bounds
            .original_upper_replay_claim(
                root_record,
                ConstraintRecordId(60_000),
                UpperReplayClaimKind::Reduced(state),
            )
            .claim;
        assert!(machine.insert_scheme_projection_live_coverage_state(root, state));

        let premise_lower =
            machine.alloc_pos(Pos::Con(vec!["dpn-b-premise-lower".into()], Vec::new()));
        let premise_upper =
            machine.alloc_neg(Neg::Con(vec!["dpn-b-premise-upper".into()], Vec::new()));
        machine.subtype(premise_lower, premise_upper, OriginId::unknown_internal());
        let premise = machine
            .constraint_record_id(premise_lower, ConstraintWeights::empty(), premise_upper)
            .expect("the premise constraint is canonical");
        let route = RowDerivationId(60_000);
        machine.constraint_records[premise.0 as usize]
            .row_derivations
            .push(route);
        machine.admit_claim_qualified_parent(
            premise,
            ClaimQualifiedParent::ReductionRouteConstraint {
                parent_claim: root,
                derivation: route,
            },
        );

        let (dependent, support) = dpn_b_synthetic_projection_record(&mut machine, 6);
        machine.register_record_proof_clause_link(
            dependent,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: dpn_b_synthetic_unary_carrier(6),
                    premise: ProofPremise::Constraint(premise),
                },
            ),
        );
        assert_eq!(
            machine.scheme_projection_record_is_included(dependent),
            false,
            "the live reduction route is the premise constraint's only source"
        );

        let linked_owner = TypeVar(81);
        let linked_endpoint =
            machine.alloc_pos(Pos::Con(vec!["dpn-b-late-linked-lower".into()], Vec::new()));
        let linked_record = machine
            .bounds
            .add_lower(
                linked_owner,
                linked_endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let dependent_owner = machine.bounds.record(dependent).unwrap().owner();
        let epoch_before = machine.bounds.of(dependent_owner).unwrap().epoch();
        let journal = machine.activate_method_role_mutations();

        machine.add_lower_bound(
            linked_owner,
            linked_endpoint,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(premise),
        );

        assert_eq!(
            machine.lower_record_for_constraint(premise),
            Some(linked_record)
        );
        assert!(machine.scheme_projection_record_is_included(linked_record));
        assert!(
            machine.scheme_projection_record_is_included(dependent),
            "source (a) delegates to the newly linked projectable record"
        );
        assert!(
            machine.bounds.of(dependent_owner).unwrap().epoch() > epoch_before,
            "hook 3 publishes the dependent owner's false-to-true transition"
        );
        assert!(
            machine
                .take_method_role_mutations()
                .iter()
                .any(|mutation| matches!(
                    mutation,
                    MethodRoleMutation::Changed {
                        key: DependencyKey::ConstraintBounds(owner),
                        ..
                    } if *owner == dependent_owner
                ))
        );
        journal.finish();
    }

    #[test]
    fn mpc_b_clause_and_dpn_a_edge_census_are_linear_in_link_events() {
        for link_events in [1usize, 4, 16] {
            assert_eq!(
                dpn_linear_registration_census(link_events),
                DpnRegistrationCensus {
                    clauses: link_events,
                    clause_links: link_events,
                    reverse_edges: link_events * 2,
                },
                "each exact replay occurrence creates one clause/link and two record-premise edges"
            );
        }
    }

    #[test]
    fn exact_clause_link_duplicate_preflight_keeps_new_support_distinct() {
        let mut machine = ConstraintMachine::new();
        let (record, support) = dpn_b_synthetic_projection_record(&mut machine, 30);
        let clause = RecordProofClause::DerivedUnary {
            carrier: dpn_b_synthetic_unary_carrier(30),
            premise: ProofPremise::Record(record),
        };

        assert!(
            !machine
                .bounds
                .record_proof_clause_link_is_registered(record, support, clause)
        );
        let (_, clause_inserted, link_inserted) = machine
            .bounds
            .register_record_proof_clause_link(
                record,
                RecordProofClauseLinkAdmission::independent(support, clause),
            );
        assert!(clause_inserted && link_inserted);
        assert!(
            machine
                .bounds
                .record_proof_clause_link_is_registered(record, support, clause)
        );

        let other_support =
            SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::ConstraintOrigin {
                constraint: ConstraintRecordId(10_031),
                origin: OriginId::unknown_internal(),
            });
        assert!(
            !machine
                .bounds
                .record_proof_clause_link_is_registered(record, other_support, clause),
            "an existing clause with a new support is a new attribution, not a duplicate"
        );
        let (_, clause_inserted, link_inserted) =
            machine
                .bounds
                .register_record_proof_clause_link(
                    record,
                    RecordProofClauseLinkAdmission::independent(other_support, clause),
                );
        assert!(!clause_inserted && link_inserted);
        assert!(machine.bounds.record_proof_clause_link_is_registered(
            record,
            other_support,
            clause
        ));
    }

    fn dpn_b_synthetic_projection_record(
        machine: &mut ConstraintMachine,
        ordinal: u32,
    ) -> (BoundRecordId, SchemeProjectionProofSupport) {
        let endpoint =
            machine.alloc_pos(Pos::Con(vec![format!("dpn-b-cycle-{ordinal}")], Vec::new()));
        let record = machine
            .bounds
            .add_lower(
                TypeVar(10_000 + ordinal),
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(OriginId::unknown_internal()),
            )
            .id;
        let carrier = ProjectionProofCarrier::ConstraintOrigin {
            constraint: ConstraintRecordId(10_000 + ordinal),
            origin: OriginId::unknown_internal(),
        };
        machine.bounds.projection_proofs_by_lower_record.insert(
            record,
            vec![SchemeProjectionProof {
                lower_record: record,
                support: SchemeProjectionProofSupport::Independent(carrier),
            }],
        );
        machine
            .bounds
            .scheme_projection_claimed_lower_owners
            .insert(TypeVar(10_000 + ordinal));
        (record, SchemeProjectionProofSupport::Independent(carrier))
    }

    fn dpn_b_register_synthetic_clause(
        machine: &mut ConstraintMachine,
        record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) {
        let (_, clause_inserted, link_inserted) = machine
            .bounds
            .register_record_proof_clause_link(
                record,
                RecordProofClauseLinkAdmission::independent(support, clause),
            );
        assert!(clause_inserted && link_inserted);
    }

    fn dpn_b_synthetic_unary_carrier(ordinal: u32) -> DerivedUnaryCarrier {
        DerivedUnaryCarrier::Structural(StructuralDerivation {
            parent: ConstraintRecordId(20_000 + ordinal),
            rule: StructuralDerivationRule::FunctionReturn,
        })
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "qualified carrier index diverged from claim-parent linear scan")]
    fn cdm_b_debug_cross_check_rejects_a_deliberately_corrupted_index() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.register_replay_claim_parents(
            fixture.result,
            replay,
            &[fixture.parent],
            false,
        );
        fixture
            .machine
            .bounds
            .qualified_carrier_index
            .get_mut(&fixture.result)
            .expect("the production insertion creates the index entry")
            .clear();

        fixture
            .machine
            .bounds
            .debug_assert_qualified_carrier_index_matches_linear_scan(fixture.result);
    }

    #[test]
    fn cdm_d_9_3_replay_new_emits_lower_delta_without_bulk_fallback() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let source = TypeVar(60);
        let target = TypeVar(61);
        let lower = fixture.machine.alloc_pos(Pos::Var(source));
        let upper = fixture.machine.alloc_neg(Neg::Var(target));
        let key = SubtypeConstraintKey {
            lower,
            upper,
            weights: ConstraintWeights::empty(),
        };
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        let mut actions = BoundReplayActions::new();
        actions.push(cdm_replay_action(&fixture, key.clone(), replay));

        fixture.machine.reset_cdm_lower_delta_census();
        let stats = fixture.machine.apply_bound_replay_actions(actions);
        assert_eq!(
            stats.accepted, 1,
            "the fixture takes replay-new queue admission"
        );
        fixture.machine.drain();
        let result = fixture.machine.canonical_constraints[&key];
        let lower_record = fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint[&result];
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert!(census.constraint_bound_events >= 1);
        assert!(census.bootstrap_scans >= 1);
        assert_cdm_result_bulk_fixed_point(
            &mut fixture.machine,
            result,
            lower_record,
            target,
            "replay new",
        );
    }

    #[test]
    fn cdm_d_9_3_replay_canonical_duplicate_emits_exact_carrier_delta() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let mut actions = BoundReplayActions::new();
        actions.push(cdm_replay_action(&fixture, key, replay));

        fixture.machine.reset_cdm_lower_delta_census();
        let stats = fixture.machine.apply_bound_replay_actions(actions);
        assert_eq!(
            stats.duplicate, 1,
            "the fixture takes canonical duplicate admission"
        );
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert_eq!(census.replay_carrier_events, 1);
        assert_eq!(census.parent_batches, 1);
        assert_cdm_result_bulk_fixed_point(
            &mut fixture.machine,
            fixture.result,
            fixture.lower_record,
            TypeVar(1),
            "replay canonical duplicate",
        );
    }

    #[test]
    fn cdm_d_9_3_replay_prefiltered_duplicate_emits_exact_carrier_delta() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::UpperBoundAdded);
        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let mut duplicates = BoundReplayActions::new();
        duplicates.push(cdm_replay_action(&fixture, key, replay));

        fixture.machine.reset_cdm_lower_delta_census();
        fixture
            .machine
            .apply_prefiltered_replay_provenance(duplicates, BoundReplayActions::new());
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert_eq!(census.replay_carrier_events, 1);
        assert_eq!(census.parent_batches, 1);
        assert_cdm_result_bulk_fixed_point(
            &mut fixture.machine,
            fixture.result,
            fixture.lower_record,
            TypeVar(1),
            "replay prefiltered duplicate",
        );
    }

    #[test]
    fn cdm_d_9_3_reduction_route_emits_row_carrier_delta() {
        let mut fixture = cdm_replay_claim_fixture();
        let derivation = RowDerivationId(40_000);
        fixture.machine.constraint_records[fixture.result.0 as usize]
            .row_derivations
            .push(derivation);

        fixture.machine.reset_cdm_lower_delta_census();
        fixture.machine.register_reduction_route_claim_parent(
            fixture.result,
            derivation,
            fixture.coverage_root,
        );
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert_eq!(census.row_carrier_events, 1);
        assert_eq!(census.parent_batches, 1);
        assert_cdm_result_bulk_fixed_point(
            &mut fixture.machine,
            fixture.result,
            fixture.lower_record,
            TypeVar(1),
            "reduction route",
        );
    }

    #[test]
    fn cdm_d_9_3_structural_admission_emits_structural_carrier_delta() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        fixture.machine.register_replay_claim_parents(
            fixture.result,
            replay,
            &[fixture.parent],
            true,
        );
        let lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["cdm-d-structural".into()], Vec::new()));
        let target = TypeVar(62);
        let upper = fixture.machine.alloc_neg(Neg::Var(target));
        let rule = StructuralDerivationRule::FunctionReturn;

        fixture.machine.reset_cdm_lower_delta_census();
        assert!(fixture.machine.enqueue_derived_subtype(
            lower,
            ConstraintWeights::empty(),
            upper,
            fixture.result,
            rule,
        ));
        fixture.machine.drain();
        let result = fixture
            .machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the structural child is canonical");
        let lower_record = fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint[&result];
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert_eq!(census.structural_carrier_events, 1);
        assert!(census.constraint_bound_events >= 1);
        assert_cdm_result_bulk_fixed_point(
            &mut fixture.machine,
            result,
            lower_record,
            target,
            "structural admission",
        );
    }

    #[test]
    fn cpk_0b_captures_canonical_logical_proof_surfaces_end_to_end() {
        let mut fixture = cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let mut replay_plan = BoundReplayPlan::default();
        let mut action = cdm_replay_action(&fixture, key, replay);
        action.lower_parents = replay_plan.intern_parent_draft(
            &action.claim_parents,
            ReplayClaimParentSide::Lower,
        );
        action.upper_parents = replay_plan.intern_parent_draft(
            &action.claim_parents,
            ReplayClaimParentSide::Upper,
        );
        let mut actions = BoundReplayActions::new();
        actions.push(action);
        assert_eq!(
            fixture
                .machine
                .apply_bound_replay_actions_with_parent_drafts(
                    actions,
                    &replay_plan.parent_drafts,
                )
                .duplicate,
            1,
            "the fixture must exercise canonical-duplicate replay admission",
        );
        let mutation = fixture.machine.bounds.update_scheme_projection_proofs(
            fixture.lower_record,
            &[],
            &[ProjectionProofCarrier::Origin(OriginId::unknown_internal())],
        );
        fixture.machine.apply_scheme_projection_mutation(mutation);

        let child_lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["cpk-0b-structural".into()], Vec::new()));
        let child_upper = fixture.machine.alloc_neg(Neg::Var(TypeVar(62)));
        assert!(fixture.machine.enqueue_derived_subtype(
            child_lower,
            ConstraintWeights::empty(),
            child_upper,
            fixture.result,
            StructuralDerivationRule::FunctionReturn,
        ));
        fixture.machine.drain();

        let snapshot = fixture.machine.logical_proof_snapshot();
        assert!(snapshot.occurrences.len() >= 2);
        assert!(!snapshot.claim_relation.is_empty());
        assert!(snapshot
            .claim_relation
            .windows(2)
            .all(|pair| pair[0] <= pair[1]));
        assert!(!snapshot.projection.is_empty());
        assert!(snapshot
            .projection
            .iter()
            .any(|entry| !entry.supports.is_empty() && !entry.clauses.is_empty()));
        assert!(!snapshot.dependencies.is_empty());
        assert!(!snapshot.portable.snapshot.nodes().is_empty());
        assert_eq!(
            snapshot.portable.roots.len(),
            snapshot.portable.root_anchors.len()
        );
        let rendered = format!("{snapshot:?}");
        assert!(rendered.contains("Claimed"));
        assert!(rendered.contains("Independent"));
        assert!(rendered.contains("Structural"));
    }

    #[test]
    fn cpk_0c_fixture_matrix_captures_semantic_and_logical_baselines() {
        let mut fixture = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            cdm_replay_claim_fixture()
        });
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let apply_replay = |fixture: &mut CdmReplayClaimFixture| {
            let mut replay_plan = BoundReplayPlan::default();
            let mut action = cdm_replay_action(fixture, key.clone(), replay);
            action.lower_parents = replay_plan.intern_parent_draft(
                &action.claim_parents,
                ReplayClaimParentSide::Lower,
            );
            action.upper_parents = replay_plan.intern_parent_draft(
                &action.claim_parents,
                ReplayClaimParentSide::Upper,
            );
            let mut actions = BoundReplayActions::new();
            actions.push(action);
            fixture
                .machine
                .apply_bound_replay_actions_with_parent_drafts(
                    actions,
                    &replay_plan.parent_drafts,
                )
        };
        assert_eq!(apply_replay(&mut fixture).duplicate, 1);

        let logical_before_noop = fixture.machine.logical_proof_snapshot();
        assert_eq!(apply_replay(&mut fixture).duplicate, 1);
        let logical_after_noop = fixture.machine.logical_proof_snapshot();
        assert_eq!(
            logical_after_noop, logical_before_noop,
            "duplicate/no-op replay must not change the logical proof baseline"
        );

        let scc = crate::scc::SccMachine::new();
        let semantic = fixture.machine.semantic_execution_snapshot(
            SccExecutionSnapshot::new(scc.stats(), Vec::new()),
            SemanticOutputSnapshot::default(),
        );
        assert!(!semantic.queue_events.is_empty());
        assert!(!semantic.constraints.is_empty());
        assert!(!semantic.bounds.is_empty());
        assert!(!logical_after_noop.occurrences.is_empty());
        assert!(!logical_after_noop.claim_relation.is_empty());
        assert!(!logical_after_noop.projection.is_empty());
    }

    #[test]
    fn cdm_d_9_3_one_sided_lower_emits_bound_delta() {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let target = TypeVar(63);
        let lower = fixture
            .machine
            .alloc_pos(Pos::Con(vec!["cdm-d-one-sided".into()], Vec::new()));
        let upper = fixture.machine.alloc_neg(Neg::Var(target));
        let key = SubtypeConstraintKey {
            lower,
            upper,
            weights: ConstraintWeights::empty(),
        };
        let mut actions = BoundReplayActions::new();
        actions.push(cdm_replay_action(
            &fixture,
            key.clone(),
            fixture.replay(ReplayRule::LowerBoundAdded),
        ));

        fixture.machine.reset_cdm_lower_delta_census();
        assert_eq!(
            fixture.machine.apply_bound_replay_actions(actions).accepted,
            1
        );
        fixture.machine.drain();
        let result = fixture.machine.canonical_constraints[&key];
        let lower_record = fixture
            .machine
            .bounds
            .scheme_projection_lower_record_by_constraint[&result];
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert!(census.constraint_bound_events >= 1);
        assert!(
            fixture
                .machine
                .var_var_upper_record_for_constraint(result)
                .is_none(),
            "the fixture stays on the one-sided lower surface"
        );
        assert_cdm_result_bulk_fixed_point(
            &mut fixture.machine,
            result,
            lower_record,
            target,
            "one-sided lower",
        );
    }

    #[test]
    fn cdm_d_9_3_evidence_only_emits_replay_evidence_delta() {
        let mut fixture = cdm_replay_claim_fixture();
        let source = TypeVar(64);
        let target = TypeVar(65);
        let lower = fixture.machine.alloc_pos(Pos::Var(source));
        let upper = fixture.machine.alloc_neg(Neg::Var(target));
        let action = cdm_replay_action(
            &fixture,
            SubtypeConstraintKey {
                lower,
                upper,
                weights: ConstraintWeights::empty(),
            },
            fixture.replay(ReplayRule::LowerBoundAdded),
        );
        let mut actions = BoundReplayActions::new();
        actions.push(action);

        fixture.machine.reset_cdm_lower_delta_census();
        fixture.machine.apply_bound_replay_evidence_actions(actions);
        let lower_record = fixture
            .machine
            .bounds
            .of(target)
            .unwrap()
            .evidence_lower_record_ids()[0];
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert_eq!(census.evidence_carrier_events, 1);
        assert_cdm_lower_record_bulk_fixed_point(
            &mut fixture.machine,
            lower_record,
            target,
            "evidence-only",
        );
    }

    #[test]
    fn cdm_d_9_3_promotion_emits_single_bound_derivation_delta() {
        let mut fixture = cdm_replay_claim_fixture();
        let source = TypeVar(66);
        let target = TypeVar(67);
        let lower = fixture.machine.alloc_pos(Pos::Var(source));
        let upper = fixture.machine.alloc_neg(Neg::Var(target));
        let mut evidence = BoundReplayActions::new();
        evidence.push(cdm_replay_action(
            &fixture,
            SubtypeConstraintKey {
                lower,
                upper,
                weights: ConstraintWeights::empty(),
            },
            fixture.replay(ReplayRule::LowerBoundAdded),
        ));
        fixture
            .machine
            .apply_bound_replay_evidence_actions(evidence);
        let lower_record = fixture
            .machine
            .bounds
            .of(target)
            .unwrap()
            .evidence_lower_record_ids()[0];

        fixture.machine.reset_cdm_lower_delta_census();
        fixture.machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        let census = fixture.machine.cdm_lower_delta_census();
        assert_eq!(census.bulk_scans, 0);
        assert!(census.other_bound_events >= 1);
        assert_cdm_lower_record_bulk_fixed_point(
            &mut fixture.machine,
            lower_record,
            target,
            "promotion",
        );
    }

    struct CdmReplayClaimFixture {
        machine: ConstraintMachine,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        upper_record: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        parent: SideTaggedReplayClaim,
        pivot: TypeVar,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct DpnRegistrationCensus {
        clauses: usize,
        clause_links: usize,
        reverse_edges: usize,
    }

    impl DpnRegistrationCensus {
        fn delta_from(self, baseline: Self) -> Self {
            Self {
                clauses: self.clauses - baseline.clauses,
                clause_links: self.clause_links - baseline.clause_links,
                reverse_edges: self.reverse_edges - baseline.reverse_edges,
            }
        }
    }

    fn dpn_registration_census(machine: &ConstraintMachine) -> DpnRegistrationCensus {
        DpnRegistrationCensus {
            clauses: machine.bounds.record_proof_clauses.len(),
            clause_links: machine.bounds.record_proof_clause_link_keys.len(),
            reverse_edges: machine
                .bounds
                .dependent_records_by_premise
                .values()
                .map(FxHashSet::len)
                .sum(),
        }
    }

    fn dpn_linear_registration_census(link_events: usize) -> DpnRegistrationCensus {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let baseline = dpn_registration_census(&fixture.machine);
        let key = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .clone();
        let origin = OriginId::unknown_internal();

        for index in 0..link_events {
            let offset = u32::try_from(index).expect("test link-event index fits in u32");
            let lower_record = fixture
                .machine
                .bounds
                .add_lower(
                    TypeVar(600u32.checked_add(offset).expect("test lower owner")),
                    key.lower,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(origin),
                )
                .id;
            let upper_record = fixture
                .machine
                .bounds
                .add_upper(
                    TypeVar(700u32.checked_add(offset).expect("test upper owner")),
                    key.upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(origin),
                )
                .id;
            let replay = BinaryReplayDerivation {
                pivot: TypeVar(800u32.checked_add(offset).expect("test replay pivot")),
                lower: lower_record,
                upper: upper_record,
                rule: ReplayRule::LowerBoundAdded,
            };
            assert_eq!(
                fixture
                    .machine
                    .merge_replay_derivation(fixture.result, replay),
                ReplayDerivationInsert::Inserted
            );
            let parent_record = fixture
                .machine
                .bounds
                .add_upper(
                    TypeVar(900u32.checked_add(offset).expect("test parent source")),
                    key.upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(origin),
                )
                .id;
            let registration = fixture.machine.bounds.original_upper_replay_claim(
                parent_record,
                ConstraintRecordId(60_000u32.checked_add(offset).expect("test producer")),
                UpperReplayClaimKind::Direct,
            );
            fixture.machine.register_replay_claim_parents(
                fixture.result,
                replay,
                &[SideTaggedReplayClaim {
                    claim: registration.claim,
                    parent_side: ReplayClaimParentSide::Lower,
                }],
                true,
            );
        }

        dpn_registration_census(&fixture.machine).delta_from(baseline)
    }

    impl CdmReplayClaimFixture {
        fn replay(&self, rule: ReplayRule) -> BinaryReplayDerivation {
            BinaryReplayDerivation {
                pivot: self.pivot,
                lower: self.lower_record,
                upper: self.upper_record,
                rule,
            }
        }
    }

    fn cdm_replay_action(
        fixture: &CdmReplayClaimFixture,
        constraint: SubtypeConstraintKey,
        derivation: BinaryReplayDerivation,
    ) -> BoundReplayAction {
        let mut claim_parents = ReplayClaimParents::new();
        claim_parents.push(fixture.parent);
        BoundReplayAction {
            constraint,
            derivation,
            claim_parents,
            lower_parents: ReplayParentDraftId::EMPTY,
            upper_parents: ReplayParentDraftId::EMPTY,
            canonicalization_disposition: None,
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct CdmLowerOracleSnapshot {
        projection_claims: Vec<UpperReplayClaimId>,
        projection_proofs: Vec<SchemeProjectionProof>,
        included: bool,
    }

    fn cdm_lower_oracle_snapshot(
        machine: &ConstraintMachine,
        lower_record: BoundRecordId,
        owner: TypeVar,
    ) -> CdmLowerOracleSnapshot {
        CdmLowerOracleSnapshot {
            projection_claims: machine
                .bounds
                .scheme_projection_claims_by_lower_record
                .get(&lower_record)
                .cloned()
                .unwrap_or_default(),
            projection_proofs: machine
                .bounds
                .projection_proofs_by_lower_record
                .get(&lower_record)
                .cloned()
                .unwrap_or_default(),
            included: machine
                .scheme_projectable_lowers(owner)
                .any(|candidate| candidate.record == lower_record),
        }
    }

    fn assert_cdm_lower_record_bulk_fixed_point(
        machine: &mut ConstraintMachine,
        lower_record: BoundRecordId,
        owner: TypeVar,
        path: &str,
    ) {
        let delta = cdm_lower_oracle_snapshot(machine, lower_record, owner);
        machine.recompute_lower_projection_bulk_oracle_record(lower_record);
        let bulk = cdm_lower_oracle_snapshot(machine, lower_record, owner);
        assert_eq!(
            delta, bulk,
            "{path}: lower claim ledger, proof ledger, and inclusion match the bulk oracle"
        );
    }

    fn assert_cdm_result_bulk_fixed_point(
        machine: &mut ConstraintMachine,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        owner: TypeVar,
        path: &str,
    ) {
        let parents = machine
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .cloned()
            .unwrap_or_default();
        let delta = cdm_lower_oracle_snapshot(machine, lower_record, owner);
        machine.recompute_claim_parent_bulk_oracle(result);
        let bulk_parents = machine
            .bounds
            .claim_parents_by_constraint
            .get(&result)
            .cloned()
            .unwrap_or_default();
        let bulk = cdm_lower_oracle_snapshot(machine, lower_record, owner);
        assert_eq!(parents, bulk_parents, "{path}: claim parents match bulk");
        assert_eq!(
            delta, bulk,
            "{path}: lower claim ledger, proof ledger, and inclusion match the bulk oracle"
        );
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct CdmOracleLedgerSnapshot {
        claim_parents: Vec<ClaimQualifiedParent>,
        projection_claims: Vec<UpperReplayClaimId>,
        projection_proofs: Vec<SchemeProjectionProof>,
        included: bool,
    }

    fn cdm_oracle_ledger_snapshot(fixture: &CdmReplayClaimFixture) -> CdmOracleLedgerSnapshot {
        CdmOracleLedgerSnapshot {
            claim_parents: fixture.machine.bounds.claim_parents_by_constraint[&fixture.result]
                .clone(),
            projection_claims: fixture
                .machine
                .bounds
                .scheme_projection_claims_by_lower_record[&fixture.lower_record]
                .clone(),
            projection_proofs: fixture.machine.bounds.projection_proofs_by_lower_record
                [&fixture.lower_record]
                .clone(),
            included: fixture
                .machine
                .scheme_projectable_lowers(TypeVar(1))
                .any(|candidate| candidate.record == fixture.lower_record),
        }
    }

    fn cdm_replay_claim_fixture() -> CdmReplayClaimFixture {
        cdm_replay_claim_fixture_with_authority(ReplayReadAuthority::Factored)
    }

    fn cdm_replay_claim_fixture_with_authority(
        replay_read_authority: ReplayReadAuthority,
    ) -> CdmReplayClaimFixture {
        let mut machine = ConstraintMachine::new_with_replay_read_authority(replay_read_authority);
        let source = TypeVar(0);
        let target = TypeVar(1);
        let parent_source = TypeVar(2);
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        let origin = OriginId::unknown_internal();
        machine.subtype(lower, upper, origin);

        let result = machine
            .constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("the direct relation is canonical");
        let lower_record = machine.bounds.of(target).unwrap().lower_record_ids()[0];
        let upper_record = machine.bounds.of(source).unwrap().upper_record_ids()[0];
        let parent_record = machine
            .bounds
            .add_upper(
                parent_source,
                upper,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            )
            .id;
        let registration = machine.bounds.original_upper_replay_claim(
            parent_record,
            ConstraintRecordId(10_000),
            UpperReplayClaimKind::Direct,
        );
        machine.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
        let coverage_root = registration.claim;

        CdmReplayClaimFixture {
            machine,
            result,
            lower_record,
            upper_record,
            coverage_root,
            parent: SideTaggedReplayClaim {
                claim: coverage_root,
                parent_side: ReplayClaimParentSide::Lower,
            },
            pivot: source,
        }
    }

    #[derive(Debug, PartialEq, Eq)]
    struct CdmCarrierOrderSnapshot {
        lower_rule_parents: usize,
        upper_rule_parents: usize,
        exact_keys: usize,
        materialized_roots: usize,
        linked_roots: usize,
        claimed_proofs: usize,
        independent_proofs: usize,
        included: bool,
    }

    fn cdm_carrier_order_snapshot(order: [ReplayRule; 2]) -> CdmCarrierOrderSnapshot {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        for rule in order {
            let replay = fixture.replay(rule);
            assert_eq!(
                fixture
                    .machine
                    .merge_replay_derivation(fixture.result, replay),
                ReplayDerivationInsert::Inserted
            );
            fixture.machine.register_replay_claim_parents(
                fixture.result,
                replay,
                &[fixture.parent],
                true,
            );
        }
        fixture
            .machine
            .recompute_claim_parent_bulk_oracle(fixture.result);

        let parents = &fixture.machine.bounds.claim_parents_by_constraint[&fixture.result];
        let proofs =
            &fixture.machine.bounds.projection_proofs_by_lower_record[&fixture.lower_record];
        CdmCarrierOrderSnapshot {
            lower_rule_parents: parents
                .iter()
                .filter(|parent| {
                    matches!(parent, ClaimQualifiedParent::ReplayConstraint { replay, .. }
                        if replay.rule == ReplayRule::LowerBoundAdded)
                })
                .count(),
            upper_rule_parents: parents
                .iter()
                .filter(|parent| {
                    matches!(parent, ClaimQualifiedParent::ReplayConstraint { replay, .. }
                        if replay.rule == ReplayRule::UpperBoundAdded)
                })
                .count(),
            exact_keys: fixture
                .machine
                .bounds
                .replay_claim_parent_keys
                .iter()
                .filter(|key| {
                    key.result == fixture.result && key.coverage_root == fixture.coverage_root
                })
                .count(),
            materialized_roots: fixture
                .machine
                .bounds
                .derived_claim_by_record_and_root
                .contains_key(&(fixture.upper_record, fixture.coverage_root))
                .into(),
            linked_roots: fixture
                .machine
                .bounds
                .scheme_projection_claims_by_lower_record[&fixture.lower_record]
                .iter()
                .filter(|claim| {
                    fixture.machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root
                        == fixture.coverage_root
                })
                .count(),
            claimed_proofs: proofs
                .iter()
                .filter(|proof| matches!(proof.support, SchemeProjectionProofSupport::Claimed(_)))
                .count(),
            independent_proofs: proofs
                .iter()
                .filter(|proof| {
                    matches!(proof.support, SchemeProjectionProofSupport::Independent(_))
                })
                .count(),
            included: fixture
                .machine
                .scheme_projectable_lowers(TypeVar(1))
                .any(|candidate| candidate.record == fixture.lower_record),
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct CdmMaterializationCensus {
        parent_entries: usize,
        materialized_roots: usize,
        claim_ledger_entries: usize,
        claimed_proof_entries: usize,
    }

    impl CdmMaterializationCensus {
        fn delta_from(self, baseline: Self) -> Self {
            Self {
                parent_entries: self.parent_entries - baseline.parent_entries,
                materialized_roots: self.materialized_roots - baseline.materialized_roots,
                claim_ledger_entries: self.claim_ledger_entries - baseline.claim_ledger_entries,
                claimed_proof_entries: self.claimed_proof_entries - baseline.claimed_proof_entries,
            }
        }
    }

    fn cdm_materialization_census(fixture: &CdmReplayClaimFixture) -> CdmMaterializationCensus {
        CdmMaterializationCensus {
            parent_entries: fixture
                .machine
                .bounds
                .claim_parents_by_constraint
                .get(&fixture.result)
                .map_or(0, Vec::len),
            materialized_roots: fixture
                .machine
                .bounds
                .derived_claim_by_record_and_root
                .keys()
                .filter(|(record, _)| *record == fixture.upper_record)
                .count(),
            claim_ledger_entries: fixture
                .machine
                .bounds
                .scheme_projection_claims_by_lower_record
                .get(&fixture.lower_record)
                .map_or(0, Vec::len),
            claimed_proof_entries: fixture
                .machine
                .bounds
                .projection_proofs_by_lower_record
                .get(&fixture.lower_record)
                .into_iter()
                .flatten()
                .filter(|proof| matches!(proof.support, SchemeProjectionProofSupport::Claimed(_)))
                .count(),
        }
    }

    fn cdm_linear_materialization_census(link_events: usize) -> CdmMaterializationCensus {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture
                .machine
                .merge_replay_derivation(fixture.result, replay),
            ReplayDerivationInsert::Inserted
        );
        let baseline = cdm_materialization_census(&fixture);
        let upper = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let origin = OriginId::unknown_internal();

        for index in 0..link_events {
            let parent_source = TypeVar(
                20u32
                    .checked_add(index as u32)
                    .expect("test parent source ID"),
            );
            let parent_record = fixture
                .machine
                .bounds
                .add_upper(
                    parent_source,
                    upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(origin),
                )
                .id;
            let registration = fixture.machine.bounds.original_upper_replay_claim(
                parent_record,
                ConstraintRecordId(
                    20_000u32
                        .checked_add(index as u32)
                        .expect("test producer ID"),
                ),
                UpperReplayClaimKind::Direct,
            );
            fixture
                .machine
                .apply_scheme_projection_mutation(registration.scheme_projection_mutation);
            let parent = SideTaggedReplayClaim {
                claim: registration.claim,
                parent_side: ReplayClaimParentSide::Lower,
            };
            fixture
                .machine
                .register_replay_claim_parents(fixture.result, replay, &[parent], true);
        }

        cdm_materialization_census(&fixture).delta_from(baseline)
    }

    fn cdm_linear_qualified_carrier_index_census(
        link_events: usize,
    ) -> (CdmMaterializationCensus, usize) {
        let mut fixture =
            cdm_replay_claim_fixture_with_authority(legacy_rollback_test_authority());
        let baseline = cdm_materialization_census(&fixture);
        let indexed_baseline = fixture
            .machine
            .bounds
            .qualified_carrier_index
            .get(&fixture.result)
            .map_or(0, FxHashSet::len);
        let upper = fixture.machine.constraint_records[fixture.result.0 as usize]
            .key
            .upper;
        let origin = OriginId::unknown_internal();

        for index in 0..link_events {
            let offset = u32::try_from(index).expect("test link-event index fits in u32");
            let replay = BinaryReplayDerivation {
                pivot: TypeVar(100u32.checked_add(offset).expect("test replay pivot ID")),
                lower: fixture.lower_record,
                upper: fixture.upper_record,
                rule: ReplayRule::LowerBoundAdded,
            };
            assert_eq!(
                fixture
                    .machine
                    .merge_replay_derivation(fixture.result, replay),
                ReplayDerivationInsert::Inserted
            );
            let parent_record = fixture
                .machine
                .bounds
                .add_upper(
                    TypeVar(200u32.checked_add(offset).expect("test parent source ID")),
                    upper,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(origin),
                )
                .id;
            let registration = fixture.machine.bounds.original_upper_replay_claim(
                parent_record,
                ConstraintRecordId(
                    30_000u32
                        .checked_add(offset)
                        .expect("test parent producer ID"),
                ),
                UpperReplayClaimKind::Direct,
            );
            fixture
                .machine
                .apply_scheme_projection_mutation(registration.scheme_projection_mutation);
            fixture.machine.register_replay_claim_parents(
                fixture.result,
                replay,
                &[SideTaggedReplayClaim {
                    claim: registration.claim,
                    parent_side: ReplayClaimParentSide::Lower,
                }],
                true,
            );
        }

        let indexed = fixture.machine.bounds.qualified_carrier_index[&fixture.result].len();
        (
            cdm_materialization_census(&fixture).delta_from(baseline),
            indexed - indexed_baseline,
        )
    }

    #[test]
    fn evidence_add_and_promotion_emit_bounds_only_while_active() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let target = TypeVar(1);
        machine.register_type_var(source, TypeLevel::root());
        machine.register_type_var(target, TypeLevel::root());
        assert!(machine.take_method_role_mutations().is_empty());

        let journal = machine.activate_method_role_mutations();
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        let mut actions = BoundReplayActions::new();
        actions.push(BoundReplayAction {
            constraint: SubtypeConstraintKey {
                lower,
                upper,
                weights: ConstraintWeights::empty(),
            },
            derivation: BinaryReplayDerivation {
                pivot: target,
                lower: BoundRecordId(0),
                upper: BoundRecordId(1),
                rule: ReplayRule::LowerBoundAdded,
            },
            claim_parents: ReplayClaimParents::new(),
            lower_parents: ReplayParentDraftId::EMPTY,
            upper_parents: ReplayParentDraftId::EMPTY,
            canonicalization_disposition: None,
        });
        machine.apply_bound_replay_evidence_actions(actions);
        assert_eq!(
            changed_keys(machine.take_method_role_mutations()),
            [
                DependencyKey::ConstraintBounds(target),
                DependencyKey::ConstraintBounds(source),
            ]
        );
        assert_eq!(
            machine.bounds().of(target).unwrap().evidence_lower_count(),
            1
        );
        assert_eq!(
            machine.bounds().of(source).unwrap().evidence_upper_count(),
            1
        );

        machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        assert!(
            changed_keys(machine.take_method_role_mutations())
                .contains(&DependencyKey::ConstraintBounds(target))
        );
        assert_eq!(
            machine.bounds().of(target).unwrap().evidence_lower_count(),
            0
        );

        machine.add_upper_bound(
            source,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );
        assert!(
            changed_keys(machine.take_method_role_mutations())
                .contains(&DependencyKey::ConstraintBounds(source))
        );
        assert_eq!(
            machine.bounds().of(source).unwrap().evidence_upper_count(),
            0
        );
        journal.finish();

        machine.register_type_var(TypeVar(2), TypeLevel::root());
        assert!(machine.take_method_role_mutations().is_empty());
    }

    #[test]
    fn neighbor_symmetry_audit_fences_fail_closed_when_active() {
        let left = TypeVar(3);
        let right = TypeVar(4);

        let mut add = ConstraintMachine::new();
        add.var_adjacency.entry(left).or_default().insert(right, 1);
        let add_journal = add.activate_method_role_mutations();
        add.record_var_neighbor(left, right);
        assert!(matches!(
            add.method_role_mutations(),
            [MethodRoleMutation::InvalidateAll {
                reason: InvalidateAllReason::AuditFenceDisagreement {
                    site: "record_var_neighbor symmetry",
                },
                ..
            }]
        ));
        add_journal.finish();

        let mut remove = ConstraintMachine::new();
        remove
            .var_adjacency
            .entry(left)
            .or_default()
            .insert(right, 1);
        let remove_journal = remove.activate_method_role_mutations();
        remove.unrecord_var_neighbor(left, right);
        assert!(matches!(
            remove.method_role_mutations(),
            [MethodRoleMutation::InvalidateAll {
                reason: InvalidateAllReason::AuditFenceDisagreement {
                    site: "unrecord_var_neighbor symmetry",
                },
                ..
            }]
        ));
        remove_journal.finish();
    }

    #[rustfmt::skip]
    mod rcpf_d3b_projection_oracle_tests {
        use super::*;
        use crate::compact::CompactRoot;
        use crate::constraints::canonical_projection_key::{self, Key};
        use crate::constraints::{
            canonical_projection_insertion_census, reset_canonical_projection_insertion_census,
        };
        use crate::SourceSpan;
        use crate::constraints::explain::{
            PortableProvenanceExport, PortableProvenanceExportBudget, PortableProvenanceExportRoot,
        };
        use crate::generalize::{GeneralizedCompactRoot, capture_generalized_witnesses};
        use poly::provenance::{
            PortableByteRange, PortableProvenanceTruncation, PortableSourceLocation,
            ProvenanceCompleteness as PortableCompleteness,
        };

        #[derive(Clone, Copy)]
        enum Event { Replay, NonReplay, Independent(usize) }

        struct Fixture {
            machine: ConstraintMachine,
            result: ConstraintRecordId,
            lower_record: BoundRecordId,
            source: TypeVar,
            target: TypeVar,
            upper: NegId,
            replay: BinaryReplayDerivation,
            row: RowDerivationId,
            roots: [UpperReplayClaimId; 2],
            origins: Vec<OriginId>,
            boundaries: Vec<SourceBoundaryId>,
        }

        impl Fixture {
            fn new() -> Self {
                Self::new_with_independent_count(2)
            }

            fn new_with_independent_count(independent_count: usize) -> Self {
                let mut machine = ConstraintMachine::new();
                let source = TypeVar(0);
                let target = TypeVar(1);
                let lower = machine.alloc_pos(Pos::Var(source));
                let upper = machine.alloc_neg(Neg::Var(target));
                let result = ConstraintRecordId(0);
                machine.constraint_records.push(ConstraintRecord {
                    key: SubtypeConstraintKey { lower, upper, weights: ConstraintWeights::empty() },
                    root_origins: Vec::new(), structural_derivations: Vec::new(),
                    row_derivations: Vec::new(), replay_derivations: Vec::new(),
                    scheme_instantiation_derivations: Vec::new(), scheme_instantiation_routes: Vec::new(),
                    canonicalization_dispositions: Vec::new(), replay_provenance: ProvenanceCompleteness::Complete,
                });
                let root_producer = machine.constraint_records[0].clone();
                machine.constraint_records.extend([root_producer.clone(), root_producer]);
                let parent_record = machine.bounds.add_upper(
                    TypeVar(2), upper, ConstraintWeights::empty(), BoundDerivation::Origin(OriginId::unknown_internal()),
                ).id;
                let roots = [1, 2].map(|producer| {
                    let registration = machine.bounds.original_upper_replay_claim(
                        parent_record, ConstraintRecordId(producer), UpperReplayClaimKind::Direct,
                    );
                    assert_eq!(registration.scheme_projection_mutation, SchemeProjectionMutation::None);
                    registration.claim
                });
                let lower_record = machine.bounds.add_lower(
                    target, lower, ConstraintWeights::empty(), BoundDerivation::Constraint(result),
                ).id;
                assert!(!machine.bounds.scheme_projection_claims_by_lower_record.contains_key(&lower_record));
                assert!(!machine.bounds.projection_proofs_by_lower_record.contains_key(&lower_record));
                let source_origins = (0..independent_count).map(|index| machine.alloc_source_boundary(
                    if index % 2 == 0 { ConstraintOriginKind::Field } else { ConstraintOriginKind::Return },
                )).collect::<Vec<_>>();
                let origins = source_origins.iter().map(|source| source.origin()).collect();
                let boundaries = source_origins.iter().map(|source| source.boundary()).collect();
                Self {
                    machine, result, lower_record, source, target, upper,
                    replay: BinaryReplayDerivation {
                        pivot: target, lower: lower_record, upper: parent_record,
                        rule: ReplayRule::LowerBoundAdded,
                    },
                    row: RowDerivationId(0), roots, origins, boundaries,
                }
            }

            fn add_claimed_source_origins(
                &mut self,
                kinds: [ConstraintOriginKind; 2],
            ) -> [SourceBoundaryId; 2] {
                let sources = kinds.map(|kind| self.machine.alloc_source_boundary(kind));
                for (producer, source) in [1_usize, 2].into_iter().zip(sources) {
                    self.machine.constraint_records[producer].root_origins.push(source.origin());
                }
                sources.map(|source| source.boundary())
            }

            fn admit(&mut self, event: Event) {
                match event {
                    Event::Replay => {
                        assert_eq!(self.machine.merge_replay_derivation(self.result, self.replay), ReplayDerivationInsert::Inserted);
                        let parent = SideTaggedReplayClaim {
                            claim: self.roots[0], parent_side: ReplayClaimParentSide::Lower,
                        };
                        register_factored_parent_snapshot(
                            &mut self.machine, self.result, self.replay, &[parent],
                        );
                    }
                    Event::NonReplay => {
                        self.machine.constraint_records[self.result.0 as usize].row_derivations.push(self.row);
                        self.machine.register_reduction_route_claim_parent(self.result, self.row, self.roots[1]);
                    }
                    Event::Independent(index) => self.machine.add_lower_bound(
                        self.target, self.machine.constraint_records[self.result.0 as usize].key.lower,
                        ConstraintWeights::empty(), BoundDerivation::Origin(self.origins[index]),
                    ),
                }
            }

            fn admit_factored_replay(&mut self, materialize: bool) {
                assert_eq!(self.machine.merge_replay_derivation(self.result, self.replay), ReplayDerivationInsert::Inserted);
                let parent = SideTaggedReplayClaim { claim: self.roots[0], parent_side: ReplayClaimParentSide::Lower };
                register_factored_parent_snapshot_with_materialization(
                    &mut self.machine, self.result, self.replay, &[parent], materialize,
                );
            }

            fn root(&self, claim: UpperReplayClaimId) -> UpperReplayClaimId {
                self.machine.bounds.upper_replay_claims[claim.0 as usize].coverage_root
            }

            fn snapshot(&self) -> (Vec<UpperReplayClaimId>, Vec<SchemeProjectionProofSupport>, Vec<Key>) {
                let claims = self.machine.bounds.scheme_projection_claims_by_lower_record[&self.lower_record].clone();
                let supports = self.machine.bounds.projection_proofs_by_lower_record[&self.lower_record]
                    .iter().map(|proof| proof.support).collect::<Vec<_>>();
                let keys = supports.iter().map(|support| match support {
                    SchemeProjectionProofSupport::Claimed(claim) => Key::Claimed(self.root(*claim)),
                    SchemeProjectionProofSupport::Independent(carrier) => Key::Independent(*carrier),
                }).collect();
                (claims, supports, keys)
            }

            fn key(&self, support: SchemeProjectionProofSupport) -> Key {
                match support {
                    SchemeProjectionProofSupport::Claimed(claim) => Key::Claimed(self.root(claim)),
                    SchemeProjectionProofSupport::Independent(carrier) => Key::Independent(carrier),
                }
            }

            fn canonicalize_shadow_ledgers(&mut self) {
                let mut claims = self.machine.bounds.scheme_projection_claims_by_lower_record[&self.lower_record].clone();
                claims.sort_by(|left, right| canonical_projection_key::cmp(
                    &Key::Claimed(self.root(*left)), &Key::Claimed(self.root(*right)),
                ));
                self.machine.bounds.scheme_projection_claims_by_lower_record.insert(self.lower_record, claims);
                let mut proofs = self.machine.bounds.projection_proofs_by_lower_record[&self.lower_record].clone();
                proofs.sort_by(|left, right| canonical_projection_key::cmp(
                    &self.key(left.support), &self.key(right.support),
                ));
                self.machine.bounds.projection_proofs_by_lower_record.insert(self.lower_record, proofs);
            }

            fn consumer_snapshot(&self) -> ConsumerSnapshot {
                let qualified = self.machine.scheme_projectable_lowers(self.target)
                    .find(|entry| entry.record == self.lower_record).expect("isolated lower remains projectable").reason;
                let (drafts, completeness) = self.capture_witnesses();
                let parents = drafts.iter().flat_map(|draft| &draft.incoming)
                    .flat_map(|edge| &edge.parents).copied().collect();
                ConsumerSnapshot { qualified, drafts, parents, completeness }
            }

            fn capture_witnesses(&self) -> (Vec<GeneralizedWitnessDraft>, ProvenanceCompleteness) {
                let generalized = GeneralizedCompactRoot {
                    compact: CompactRoot::default(), role_predicates: Vec::new(), quantifiers: Vec::new(),
                    stack_quantifiers: Vec::new(), substitutions: Vec::new(), sandwiches: Vec::new(),
                };
                capture_generalized_witnesses(&self.machine, self.target, &generalized)
            }

            fn record_witness_roots(&mut self) -> Vec<PortableProvenanceExportRoot> {
                let (drafts, completeness) = self.capture_witnesses();
                let scheme = self.machine.alloc_generalized_scheme_record(poly::expr::DefId(0), 0, drafts, completeness);
                let witnesses = self.machine.generalized_scheme_record(scheme).expect("oracle scheme").witnesses.clone();
                witnesses.into_iter().map(PortableProvenanceExportRoot::GeneralizedWitness).collect()
            }

            fn portable_consumer_snapshot(
                &self,
                roots: &[PortableProvenanceExportRoot],
                budget: PortableProvenanceExportBudget,
            ) -> PortableConsumerSnapshot {
                self.portable_consumer_snapshot_with_location(roots, budget, |boundary, _| {
                    Some(PortableSourceLocation {
                        module: vec!["rcpf".to_string()],
                        range: PortableByteRange { start: boundary.0 * 2, end: boundary.0 * 2 + 1 },
                    })
                })
            }

            fn portable_consumer_snapshot_with_location(
                &self,
                roots: &[PortableProvenanceExportRoot],
                budget: PortableProvenanceExportBudget,
                source_location: impl FnMut(SourceBoundaryId, ConstraintOriginKind) -> Option<PortableSourceLocation>,
            ) -> PortableConsumerSnapshot {
                let export = self.machine.export_portable_provenance(
                    roots, budget, source_location,
                ).expect("full-budget portable export");
                let anchors = export.root_anchors.iter().flatten().copied().collect::<Vec<_>>();
                assert!(!anchors.is_empty(), "portable oracle must retain at least one root anchor");
                let explanation = explain_portable_subtype(
                    &export.snapshot, &anchors, &anchors, PortableExplanationBudget::default(),
                );
                PortableConsumerSnapshot { export, explanation }
            }
        }

        struct TargetLateFixture {
            machine: ConstraintMachine,
            result: ConstraintRecordId,
            source: TypeVar,
            target: TypeVar,
            lower: PosId,
            upper: NegId,
            replay: BinaryReplayDerivation,
            roots: [UpperReplayClaimId; 2],
            rows: [RowDerivationId; 2],
            boundaries: [SourceBoundaryId; 2],
        }

        impl TargetLateFixture {
            fn new_with_authority(authority: ReplayReadAuthority) -> Self {
                let mut machine = ConstraintMachine::new_with_replay_read_authority(authority);
                machine.enable_replay_factored_event_oracle();
                let source = TypeVar(0);
                let target = TypeVar(1);
                let pivot = TypeVar(2);
                let lower = machine.alloc_pos(Pos::Var(source));
                let upper = machine.alloc_neg(Neg::Var(target));
                let result = ConstraintRecordId(0);
                let record = ConstraintRecord {
                    key: SubtypeConstraintKey { lower, upper, weights: ConstraintWeights::empty() },
                    root_origins: Vec::new(), structural_derivations: Vec::new(),
                    row_derivations: Vec::new(), replay_derivations: Vec::new(),
                    scheme_instantiation_derivations: Vec::new(), scheme_instantiation_routes: Vec::new(),
                    canonicalization_dispositions: Vec::new(), replay_provenance: ProvenanceCompleteness::Complete,
                };
                machine.constraint_records.extend([record.clone(), record.clone(), record]);
                let sources = [ConstraintOriginKind::Annotation, ConstraintOriginKind::Pattern]
                    .map(|kind| machine.alloc_source_boundary(kind));
                for (producer, source) in [1_usize, 2].into_iter().zip(sources) {
                    machine.constraint_records[producer].root_origins.push(source.origin());
                }
                let parent_upper = machine.bounds.add_upper(
                    pivot, upper, ConstraintWeights::empty(), BoundDerivation::Origin(OriginId::unknown_internal()),
                ).id;
                let roots = [1, 2].map(|producer| machine.bounds.original_upper_replay_claim(
                    parent_upper, ConstraintRecordId(producer), UpperReplayClaimKind::Direct,
                ).claim);
                let replay_lower = machine.bounds.add_lower(
                    pivot, lower, ConstraintWeights::empty(), BoundDerivation::Origin(OriginId::unknown_internal()),
                ).id;
                Self {
                    machine, result, source, target, lower, upper,
                    replay: BinaryReplayDerivation {
                        pivot, lower: replay_lower, upper: parent_upper, rule: ReplayRule::LowerBoundAdded,
                    },
                    roots, rows: [RowDerivationId(90_000), RowDerivationId(90_001)],
                    boundaries: sources.map(|source| source.boundary()),
                }
            }

            fn epoch_checkpoint(&self) -> TargetLateEpochCheckpoint {
                let owner_epoch = |var| self.machine.bounds.of(var).map(VarBounds::epoch);
                (
                    self.machine.epoch,
                    self.machine.provenance_epoch,
                    [owner_epoch(self.source), owner_epoch(self.target), owner_epoch(self.replay.pivot)],
                )
            }

            fn admit_replay(&mut self) {
                assert_eq!(self.machine.merge_replay_derivation(self.result, self.replay), ReplayDerivationInsert::Inserted);
                let parent = SideTaggedReplayClaim {
                    claim: self.roots[0], parent_side: ReplayClaimParentSide::Lower,
                };
                register_factored_parent_snapshot_with_materialization(
                    &mut self.machine, self.result, self.replay, &[parent], false,
                );
            }

            fn admit_non_replay(&mut self, index: usize) {
                let row = self.rows[index];
                self.machine.constraint_records[self.result.0 as usize].row_derivations.push(row);
                self.machine.register_reduction_route_claim_parent(self.result, row, self.roots[index]);
            }

            fn materialize(mut self) -> TargetLateMaterialized {
                let upper_record = self.machine.bounds.add_upper(
                    self.source, self.upper, ConstraintWeights::empty(), BoundDerivation::Constraint(self.result),
                ).id;
                let published_claims = self.machine
                    .register_constraint_upper_replay_claims(upper_record, Some(self.result));
                let lower_record = self.machine.bounds.add_lower(
                    self.target, self.lower, ConstraintWeights::empty(), BoundDerivation::Constraint(self.result),
                ).id;
                self.machine.register_lower_projection_derivation(
                    lower_record, Some(self.result), BoundDerivation::Constraint(self.result),
                );
                let legacy_parents = self.machine.bounds.claim_parents_by_constraint[&self.result].clone();
                let legacy_upper = self.machine.try_upper_materialization_lineages_from_parents(
                    upper_record, self.result, legacy_parents.iter().copied(), false,
                );
                assert_eq!(
                    self.machine.try_authoritative_upper_materialization_full(
                        upper_record, self.result,
                    ),
                    legacy_upper,
                );
                let legacy_lower = self.machine.try_legacy_record_lower_projection(lower_record).unwrap();
                assert_eq!(
                    self.machine.try_authoritative_lower_projection_full(
                        self.result, &legacy_parents, &[],
                    ).unwrap(),
                    legacy_lower.canonical,
                );
                if self.machine.replay_read_authority() == ReplayReadAuthority::Factored {
                    assert_eq!(self.machine.try_upper_materialization_lineages_from_parents(
                        upper_record, self.result,
                        legacy_parents.iter().copied(), false,
                    ), self.machine.try_factored_upper_materialization_full(upper_record, self.result));
                    assert_eq!(legacy_lower,
                        self.machine.try_compare_factored_record_lower_projection(lower_record, &[]).unwrap());
                    assert_eq!(self.machine.replay_factored_shadow_status.get(), ReplayFactoredShadowStatus::Active);
                }
                let upper_replay_parents = self.machine.upper_record_replay_claim_parents(
                    self.lower, upper_record, &[],
                );
                let replay_parent_roots = upper_replay_parents.iter().map(|parent| {
                    self.machine.bounds.upper_replay_claims[parent.claim.0 as usize].coverage_root
                }).collect::<Vec<_>>();
                let lower_replay_parents =
                    self.machine.lower_record_replay_claim_parents(lower_record);
                let qualified = self.machine.scheme_projectable_lowers(self.target)
                    .find(|entry| entry.record == lower_record).expect("target-late lower remains projectable").reason;
                let generalized = GeneralizedCompactRoot {
                    compact: CompactRoot::default(), role_predicates: Vec::new(), quantifiers: Vec::new(),
                    stack_quantifiers: Vec::new(), substitutions: Vec::new(), sandwiches: Vec::new(),
                };
                let (drafts, completeness) = capture_generalized_witnesses(
                    &self.machine, self.target, &generalized,
                );
                let parents = drafts.iter().flat_map(|draft| &draft.incoming)
                    .flat_map(|edge| &edge.parents).copied().collect::<Vec<_>>();
                let scheme = self.machine.alloc_generalized_scheme_record(
                    poly::expr::DefId(0), 0, drafts.clone(), completeness,
                );
                let witnesses = self.machine.generalized_scheme_record(scheme)
                    .expect("target-late oracle scheme").witnesses.clone();
                // Mirror `append_generalized_occurrences`: store each witness's exact parent carriers.
                let occurrence_roots = witnesses.iter().map(|witness| {
                    let witness = self.machine.generalized_scheme_witness(*witness)
                        .expect("target-late occurrence witness");
                    let mut roots = Vec::new();
                    for parent in witness.incoming.iter().flat_map(|edge| &edge.parents) {
                        let Some(carriers) = self.machine.generalization_parent_carriers(*parent) else {
                            continue;
                        };
                        let candidates = match carriers {
                            GeneralizationParentCarriers::Constraint(id) =>
                                vec![PortableProvenanceExportRoot::Constraint(id)],
                            GeneralizationParentCarriers::Bound(id) =>
                                vec![PortableProvenanceExportRoot::Bound(id)],
                            GeneralizationParentCarriers::ReplayEvidence { lower, upper } => vec![
                                PortableProvenanceExportRoot::Bound(lower),
                                PortableProvenanceExportRoot::Bound(upper),
                            ],
                            GeneralizationParentCarriers::Origin(id) =>
                                vec![PortableProvenanceExportRoot::Origin(id)],
                            GeneralizationParentCarriers::RowDerivation(id) =>
                                vec![PortableProvenanceExportRoot::RowDerivation(id)],
                            GeneralizationParentCarriers::GeneralizedWitness(id) =>
                                vec![PortableProvenanceExportRoot::GeneralizedWitness(id)],
                        };
                        for root in candidates {
                            if !roots.contains(&root) { roots.push(root); }
                        }
                    }
                    roots
                }).collect::<Vec<_>>();
                let portable_roots = occurrence_roots.iter().flatten().copied().collect::<Vec<_>>();
                let portable = self.portable_snapshot(&portable_roots, false);
                let mut root_offset = 0;
                let occurrence_anchors = occurrence_roots.iter().map(|roots| {
                    let anchors = portable.export.root_anchors[root_offset..root_offset + roots.len()].to_vec();
                    root_offset += roots.len();
                    anchors
                }).collect::<Vec<_>>();
                let anchors = portable.export.root_anchors.iter().flatten().copied().collect::<Vec<_>>();
                let tight_explanation = explain_portable_subtype(
                    &portable.export.snapshot, &anchors, &anchors,
                    PortableExplanationBudget { max_edges: 0, ..PortableExplanationBudget::default() },
                );
                let duplicate = self.portable_snapshot(&portable_roots, true).explanation;
                let mut duplicate_survivors = Vec::new();
                for cause in &duplicate.lower_sites {
                    if !duplicate_survivors.iter().any(|survivor: &DiagnosticTypeCause| {
                        survivor.source_span == cause.source_span
                    }) {
                        duplicate_survivors.push(cause.clone());
                    }
                }
                let duplicate_primary = duplicate_survivors.first()
                    .map(|cause| cause.source_span.clone());
                let publication = TargetLatePublicationSnapshot {
                    published_claims,
                    target_claims: self.machine.bounds.claims_by_upper_record[&upper_record].clone(),
                    upper_replay_parents,
                    lower_replay_parents,
                    lower_claims: self.machine.bounds.scheme_projection_claims_by_lower_record
                        [&lower_record].clone(),
                    lower_proofs: self.machine.bounds.projection_proofs_by_lower_record
                        [&lower_record].clone(),
                    claim_arena: self.machine.bounds.upper_replay_claims.clone(),
                    final_epoch: self.epoch_checkpoint(),
                };
                TargetLateMaterialized {
                    roots: self.roots,
                    consumer: TargetLateConsumerSnapshot {
                        lower_record,
                        replay_parent_roots,
                        lower_claimed_roots: legacy_lower.canonical.claimed_roots,
                        lower_proof_keys: legacy_lower.canonical.proof_keys,
                        generalized: ConsumerSnapshot { qualified, drafts, parents, completeness },
                        occurrence_roots,
                        occurrence_anchors,
                        portable,
                        tight_explanation,
                        duplicate_causes: duplicate.lower_sites,
                        duplicate_survivors,
                        duplicate_primary,
                    },
                    publication,
                }
            }

            fn portable_snapshot(&self, roots: &[PortableProvenanceExportRoot],
                duplicate_span: bool) -> PortableConsumerSnapshot {
                let boundaries = self.boundaries;
                let export = self.machine.export_portable_provenance(
                    roots, PortableProvenanceExportBudget::default(), move |boundary, _| {
                        let start = if duplicate_span && boundaries.contains(&boundary) {
                            10
                        } else {
                            boundary.0 * 2
                        };
                        Some(PortableSourceLocation {
                            module: vec!["rcpf-target-late".to_string()],
                            range: PortableByteRange { start, end: start + 1 },
                        })
                    },
                ).expect("target-late portable export");
                let anchors = export.root_anchors.iter().flatten().copied().collect::<Vec<_>>();
                let explanation = explain_portable_subtype(
                    &export.snapshot, &anchors, &anchors, PortableExplanationBudget::default(),
                );
                PortableConsumerSnapshot { export, explanation }
            }
        }

        type TargetLateEpochCheckpoint =
            (ConstraintEpoch, ProvenanceEpoch, [Option<ConstraintEpoch>; 3]);

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct TargetLateConsumerSnapshot {
            lower_record: BoundRecordId,
            replay_parent_roots: Vec<UpperReplayClaimId>,
            lower_claimed_roots: Vec<UpperReplayClaimId>,
            lower_proof_keys: Vec<Key>,
            generalized: ConsumerSnapshot,
            occurrence_roots: Vec<Vec<PortableProvenanceExportRoot>>,
            occurrence_anchors: Vec<Vec<Option<poly::provenance::ProvenanceAnchor>>>,
            portable: PortableConsumerSnapshot,
            tight_explanation: DiagnosticSubtypeExplanation,
            duplicate_causes: Vec<DiagnosticTypeCause>,
            duplicate_survivors: Vec<DiagnosticTypeCause>,
            duplicate_primary: Option<SourceSpan>,
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct TargetLatePublicationSnapshot {
            published_claims: Vec<UpperReplayClaimId>,
            target_claims: Vec<UpperReplayClaimId>,
            upper_replay_parents: ReplayClaimParents,
            lower_replay_parents: ReplayClaimParents,
            lower_claims: Vec<UpperReplayClaimId>,
            lower_proofs: Vec<SchemeProjectionProof>,
            claim_arena: Vec<UpperReplayClaim>,
            final_epoch: TargetLateEpochCheckpoint,
        }

        struct TargetLateMaterialized {
            roots: [UpperReplayClaimId; 2],
            consumer: TargetLateConsumerSnapshot,
            publication: TargetLatePublicationSnapshot,
        }

        fn run_target_late(
            replay_wins_same_root: bool,
            root_a_before_root_b: bool,
            authority: ReplayReadAuthority,
        ) -> (Vec<TargetLateEpochCheckpoint>, TargetLateMaterialized) {
            let mut fixture = TargetLateFixture::new_with_authority(authority);
            let mut epochs = vec![fixture.epoch_checkpoint()];
            let order: [u8; 3] = match (replay_wins_same_root, root_a_before_root_b) {
                (true, true) => [0, 1, 2],
                (true, false) => [2, 0, 1],
                (false, true) => [1, 0, 2],
                (false, false) => [2, 1, 0],
            };
            for event in order {
                match event {
                    0 => fixture.admit_replay(),
                    1 => fixture.admit_non_replay(0),
                    2 => fixture.admit_non_replay(1),
                    _ => unreachable!(),
                }
                epochs.push(fixture.epoch_checkpoint());
            }
            if authority == ReplayReadAuthority::Factored {
                let winner = fixture.machine.replay_result_summary
                    .first_qualified_parent_source(fixture.result, fixture.roots[0]).unwrap();
                assert_eq!(matches!(winner, Some(FirstQualifiedParentSource::Replay)), replay_wins_same_root);
            }
            let materialized = fixture.materialize();
            epochs.push(materialized.publication.final_epoch);
            (epochs, materialized)
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct ConsumerSnapshot {
            qualified: SchemeProjectableLowerReason,
            drafts: Vec<GeneralizedWitnessDraft>,
            parents: Vec<GeneralizationParent>,
            completeness: ProvenanceCompleteness,
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct PortableConsumerSnapshot {
            export: PortableProvenanceExport,
            explanation: DiagnosticSubtypeExplanation,
        }

        fn qualified_parents(reason: &SchemeProjectableLowerReason, bound: BoundRecordId) -> Vec<GeneralizationParent> {
            let SchemeProjectableLowerReason::Qualified { uncovered_claims, independent_supports } = reason else {
                panic!("canonical projection fixture must remain qualified")
            };
            uncovered_claims.iter().map(|claim| GeneralizationParent::BoundClaim { bound, claim: *claim })
                .chain(independent_supports.iter().map(|carrier| GeneralizationParent::BoundProjectionProof {
                    bound, carrier: *carrier,
                })).collect()
        }

        fn lower_draft(snapshot: &ConsumerSnapshot) -> &GeneralizedWitnessDraft {
            snapshot.drafts.iter().find(|draft| draft.path == GeneralizedTypePath::default()
                && draft.role == GeneralizedWitnessRole::LowerBound).expect("root lower draft")
        }

        fn export_budget_ladder() -> Vec<(
            &'static str, PortableProvenanceExportBudget, PortableProvenanceTruncation, [bool; 2],
        )> {
            let full = PortableProvenanceExportBudget::default();
            vec![
                ("per-anchor nodes", PortableProvenanceExportBudget {
                    max_anchors: 1, max_nodes_per_anchor: 4, ..full
                }, PortableProvenanceTruncation::NodeBudget { limit: 4 }, [true, false]),
                ("per-anchor edges", PortableProvenanceExportBudget {
                    max_anchors: 1, max_edges_per_anchor: 3, ..full
                }, PortableProvenanceTruncation::EdgeBudget { limit: 3 }, [true, false]),
                ("global nodes", PortableProvenanceExportBudget { max_nodes: 4, ..full },
                    PortableProvenanceTruncation::NodeBudget { limit: 4 }, [true, false]),
                ("global edges", PortableProvenanceExportBudget { max_edges: 3, ..full },
                    PortableProvenanceTruncation::EdgeBudget { limit: 3 }, [true, true]),
                ("parent fan-in", PortableProvenanceExportBudget { max_parents_per_edge: 0, ..full },
                    PortableProvenanceTruncation::ParentFanInBudget { limit: 0 }, [true, true]),
            ]
        }

        fn explanation_budget_ladder() -> Vec<(
            &'static str, PortableExplanationBudget, DiagnosticExplanationTruncationReason,
        )> {
            let full = PortableExplanationBudget::default();
            vec![
                ("query nodes", PortableExplanationBudget { max_nodes: 4, ..full },
                    DiagnosticExplanationTruncationReason::NodeBudget { limit: 4 }),
                ("query edges", PortableExplanationBudget { max_edges: 3, ..full },
                    DiagnosticExplanationTruncationReason::EdgeBudget { limit: 3 }),
                ("query depth", PortableExplanationBudget { max_depth: 0, ..full },
                    DiagnosticExplanationTruncationReason::DepthBudget { limit: 0 }),
            ]
        }

        fn permutations() -> Vec<[usize; 4]> {
            let mut result = Vec::new();
            for a in 0..4 { for b in 0..4 { for c in 0..4 { for d in 0..4 {
                if a != b && a != c && a != d && b != c && b != d && c != d { result.push([a, b, c, d]); }
            }}}}
            result
        }

        #[test]
        fn target_late_mixed_roots_do_not_expose_historical_order_to_later_replay() {
            for replay_wins_same_root in [true, false] {
                let mut expected = None;
                for root_a_before_root_b in [true, false] {
                    let (_, materialized) = run_target_late(
                        replay_wins_same_root, root_a_before_root_b, ReplayReadAuthority::Factored,
                    );
                    let roots = materialized.roots;
                    let snapshot = materialized.consumer;
                    assert_eq!(snapshot.replay_parent_roots, roots);
                    assert_eq!(snapshot.lower_claimed_roots, roots);
                    assert_eq!(snapshot.lower_proof_keys,
                        roots.map(Key::Claimed));
                    let SchemeProjectableLowerReason::Qualified {
                        uncovered_claims, independent_supports,
                    } = &snapshot.generalized.qualified else {
                        panic!("target-late lower must remain claim-qualified")
                    };
                    assert_eq!(uncovered_claims, &roots);
                    assert!(independent_supports.is_empty());
                    let qualified = qualified_parents(
                        &snapshot.generalized.qualified, snapshot.lower_record,
                    );
                    assert_eq!(lower_draft(&snapshot.generalized).incoming.iter()
                        .flat_map(|edge| &edge.parents).copied().collect::<Vec<_>>(), qualified);
                    assert_eq!(snapshot.generalized.parents.len(), qualified.len() * 2,
                        "the root lower and recursive-lower drafts retain the same exact parents");
                    assert!(snapshot.generalized.parents.chunks(qualified.len())
                        .all(|parents| parents == qualified));
                    assert_eq!(snapshot.generalized.completeness, ProvenanceCompleteness::Incomplete);
                    assert!(snapshot.generalized.drafts.iter()
                        .all(|draft| draft.completeness == ProvenanceCompleteness::Complete));
                    assert_eq!(snapshot.occurrence_roots.len(), snapshot.occurrence_anchors.len());
                    assert_eq!(snapshot.portable.export.root_anchors.len(),
                        snapshot.occurrence_roots.iter().map(Vec::len).sum::<usize>());
                    let occurrence_pair = [1, 2].map(|id| PortableProvenanceExportRoot::Constraint(ConstraintRecordId(id)));
                    assert!(snapshot.occurrence_roots.iter()
                        .all(|occurrence| occurrence.as_slice() == occurrence_pair));
                    assert!(snapshot.occurrence_anchors.iter().all(|anchors| {
                        anchors.len() == roots.len() && anchors.iter().all(Option::is_some)
                    }));
                    assert_eq!(snapshot.portable.export.snapshot.completeness(), PortableCompleteness::Complete);
                    assert_eq!(snapshot.portable.export.snapshot.truncation(), None);
                    assert_eq!(snapshot.portable.export.snapshot.source_sites().len(), roots.len());
                    assert_eq!(snapshot.portable.explanation.lower_sites.iter()
                        .map(|cause| cause.role).collect::<Vec<_>>(), vec![
                            DiagnosticTypeCauseRole::RequiredByAnnotation,
                            DiagnosticTypeCauseRole::RequiredByPattern,
                        ]);
                    assert_eq!(snapshot.portable.explanation.upper_sites,
                        snapshot.portable.explanation.lower_sites);
                    assert_eq!(snapshot.portable.explanation.completeness,
                        DiagnosticExplanationCompleteness::Complete);
                    assert_eq!(snapshot.tight_explanation.completeness,
                        DiagnosticExplanationCompleteness::TruncatedByBudget);
                    assert_eq!(snapshot.tight_explanation.truncation,
                        Some(DiagnosticExplanationTruncationReason::EdgeBudget { limit: 0 }));
                    assert_eq!(snapshot.tight_explanation.lower_sites,
                        snapshot.portable.explanation.lower_sites[..snapshot.tight_explanation.lower_sites.len()]);
                    assert_eq!(snapshot.duplicate_causes.len(), roots.len());
                    assert_eq!(snapshot.duplicate_causes[0].source_span,
                        snapshot.duplicate_causes[1].source_span);
                    assert_eq!([snapshot.duplicate_causes[0].role, snapshot.duplicate_causes[1].role], [DiagnosticTypeCauseRole::RequiredByAnnotation, DiagnosticTypeCauseRole::RequiredByPattern]);
                    assert_eq!(snapshot.duplicate_survivors, snapshot.duplicate_causes[..1]);
                    assert_eq!(snapshot.duplicate_primary,
                        Some(snapshot.duplicate_causes[0].source_span.clone()));
                    assert_eq!(snapshot,
                        *expected.get_or_insert_with(|| snapshot.clone()),
                        "target-late consumer chain exposed cross-root admission order; replay same-root winner: {replay_wins_same_root}",
                    );
                }
            }
        }

        #[test]
        fn target_late_legacy_rollback_reproduces_epoch_publication_and_consumer_sequences() {
            let rollback = ReplayReadAuthority::LegacyRollback(
                ReplayFactoredShadowFailure::AllocationFailed,
            );
            for replay_wins_same_root in [true, false] {
                for root_a_before_root_b in [true, false] {
                    let (factored_epochs, factored) = run_target_late(
                        replay_wins_same_root, root_a_before_root_b, ReplayReadAuthority::Factored,
                    );
                    let (rollback_epochs, rollback_run) = run_target_late(
                        replay_wins_same_root, root_a_before_root_b, rollback,
                    );
                    assert_eq!(rollback_epochs, factored_epochs,
                        "LegacyRollback changed global/provenance/owner epochs");
                    assert_eq!(rollback_run.publication, factored.publication,
                        "LegacyRollback changed exact replay-parent reads, canonical upper/lower storage, claim publication, or derived allocation");
                    assert_eq!(rollback_run.consumer, factored.consumer,
                        "LegacyRollback changed the downstream target-late consumer chain");
                }
            }
        }

        #[test]
        fn canonical_projection_storage_is_invariant_across_all_four_event_permutations() {
            let events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let orders = permutations();
            assert_eq!(orders.len(), 24);
            for order in orders {
                let mut fixture = Fixture::new();
                for index in order { fixture.admit(events[index]); }
                let (claims, supports, keys) = fixture.snapshot();
                assert_eq!((claims.len(), supports.len()), (2, 4), "event order: {order:?}, supports: {supports:?}");
                assert_eq!(claims.iter().map(|claim| fixture.root(*claim)).collect::<Vec<_>>(), fixture.roots);
                let expected = vec![Key::Claimed(fixture.roots[0]), Key::Claimed(fixture.roots[1]),
                    Key::Independent(ProjectionProofCarrier::Origin(fixture.origins[0])),
                    Key::Independent(ProjectionProofCarrier::Origin(fixture.origins[1]))];
                assert_eq!(keys, expected, "the production writer must store canonical keys for order {order:?}");
                assert_eq!(canonical_projection_key::normalize_clone(&keys), keys);
            }
        }

        #[test]
        fn same_root_replacement_preserves_raw_and_canonical_positions() {
            let mut fixture = Fixture::new();
            for event in [Event::NonReplay, Event::Independent(0), Event::Replay, Event::Independent(1)] { fixture.admit(event); }
            let (before_claims, before_supports, before_keys) = fixture.snapshot();
            let root = fixture.roots[0];
            let claim_position = before_claims.iter().position(|claim| fixture.root(*claim) == root).unwrap();
            let proof_position = before_keys.iter().position(|key| *key == Key::Claimed(root)).unwrap();
            let replacement_record = fixture.machine.bounds.add_upper(
                fixture.source, fixture.upper, ConstraintWeights::empty(), BoundDerivation::Origin(OriginId::unknown_internal()),
            ).id;
            fixture.machine.register_constraint_upper_replay_claims(replacement_record, Some(fixture.result));
            let (after_claims, after_supports, after_keys) = fixture.snapshot();
            assert_ne!(before_claims[claim_position], after_claims[claim_position]);
            assert_eq!(fixture.root(after_claims[claim_position]), root);
            assert!(matches!((before_supports[proof_position], after_supports[proof_position]),
                (SchemeProjectionProofSupport::Claimed(before), SchemeProjectionProofSupport::Claimed(after)) if before != after));
            assert_eq!(after_keys.iter().position(|key| *key == Key::Claimed(root)), Some(proof_position));
            let before_normalized = canonical_projection_key::normalize_clone(&before_keys);
            let after_normalized = canonical_projection_key::normalize_clone(&after_keys);
            assert_eq!(before_normalized, after_normalized);
            assert_eq!(before_normalized.iter().position(|key| *key == Key::Claimed(root)),
                after_normalized.iter().position(|key| *key == Key::Claimed(root)));
        }

        #[test]
        fn canonical_qualified_and_generalized_parent_sequences_are_invariant_across_all_permutations() {
            let events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let mut expected = None;
            for order in permutations() {
                let mut fixture = Fixture::new();
                for index in order { fixture.admit(events[index]); }
                fixture.canonicalize_shadow_ledgers();
                let snapshot = fixture.consumer_snapshot();
                let parents = qualified_parents(&snapshot.qualified, fixture.lower_record);
                assert_eq!(parents, vec![
                    GeneralizationParent::BoundClaim { bound: fixture.lower_record, claim: fixture.roots[0] },
                    GeneralizationParent::BoundClaim { bound: fixture.lower_record, claim: fixture.roots[1] },
                    GeneralizationParent::BoundProjectionProof { bound: fixture.lower_record,
                        carrier: ProjectionProofCarrier::Origin(fixture.origins[0]) },
                    GeneralizationParent::BoundProjectionProof { bound: fixture.lower_record,
                        carrier: ProjectionProofCarrier::Origin(fixture.origins[1]) },
                ]);
                assert_eq!(lower_draft(&snapshot).incoming.iter().flat_map(|edge| &edge.parents)
                    .copied().collect::<Vec<_>>(), parents);
                assert_eq!(snapshot, *expected.get_or_insert_with(|| snapshot.clone()));
            }
        }

        fn sampled_orders(len: usize) -> Vec<Vec<usize>> {
            let ascending = (0..len).collect::<Vec<_>>();
            let descending = (0..len).rev().collect();
            let mut rotated = ascending.clone();
            rotated.rotate_left(73);
            let parity = (0..len).step_by(2).chain((1..len).step_by(2)).collect();
            let stride = (0..len).map(|index| index * 101 % len).collect();
            vec![ascending, descending, rotated, parity, stride]
        }

        fn insertion_census(
            events: &[Event],
            orders: Vec<Vec<usize>>,
        ) -> (Vec<usize>, Vec<usize>) {
            let mut claim_lengths = Vec::new();
            let mut proof_lengths = Vec::new();
            for order in orders {
                let independent_count = events.len() - 2;
                let mut fixture = Fixture::new_with_independent_count(independent_count);
                for index in order {
                    fixture.admit(events[index]);
                    let keys = fixture.machine.bounds.projection_proofs_by_lower_record
                        .get(&fixture.lower_record).into_iter().flatten()
                        .map(|proof| fixture.key(proof.support)).collect::<Vec<_>>();
                    assert_eq!(keys, canonical_projection_key::normalize_clone(&keys));
                }
                claim_lengths.push(fixture.machine.bounds.scheme_projection_claims_by_lower_record
                    [&fixture.lower_record].len());
                proof_lengths.push(fixture.machine.bounds.projection_proofs_by_lower_record
                    [&fixture.lower_record].len());
            }
            (claim_lengths, proof_lengths)
        }

        fn percentile(values: &mut [usize], percentile: usize) -> usize {
            values.sort_unstable();
            values[(values.len() * percentile).div_ceil(100) - 1]
        }

        #[test]
        fn canonical_insertion_census_pins_lengths_and_entry_moves() {
            reset_canonical_projection_insertion_census();
            let small_events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let small_orders = permutations().into_iter().map(Vec::from).collect();
            let (mut claim_lengths, mut proof_lengths) = insertion_census(&small_events, small_orders);

            const INDEPENDENT_SUPPORTS: usize = 258;
            let mut large_events = vec![Event::Replay, Event::NonReplay];
            large_events.extend((0..INDEPENDENT_SUPPORTS).map(Event::Independent));
            let (large_claim_lengths, large_proof_lengths) =
                insertion_census(&large_events, sampled_orders(large_events.len()));
            claim_lengths.extend(large_claim_lengths);
            proof_lengths.extend(large_proof_lengths);

            assert_eq!((claim_lengths.len(), proof_lengths.len()), (29, 29));
            assert_eq!((*claim_lengths.iter().max().unwrap(), percentile(&mut claim_lengths, 95),
                percentile(&mut claim_lengths, 99)), (2, 2, 2));
            assert_eq!((*proof_lengths.iter().max().unwrap(), percentile(&mut proof_lengths, 95),
                percentile(&mut proof_lengths, 99)), (260, 260, 260));
            assert_eq!(canonical_projection_insertion_census(), (72_370, 259));
        }

        #[test]
        fn canonical_generalized_witness_prefix_and_completeness_survive_sampled_large_orders() {
            const INDEPENDENT_SUPPORTS: usize = 258;
            let mut events = vec![Event::Replay, Event::NonReplay];
            events.extend((0..INDEPENDENT_SUPPORTS).map(Event::Independent));
            let orders = sampled_orders(events.len());
            assert_eq!(orders.iter().collect::<FxHashSet<_>>().len(), 5);
            let mut expected = None;
            for order in orders {
                let mut fixture = Fixture::new_with_independent_count(INDEPENDENT_SUPPORTS);
                for index in order { fixture.admit(events[index]); }
                assert_eq!(fixture.snapshot().1.len(), 260);
                fixture.canonicalize_shadow_ledgers();
                let snapshot = fixture.consumer_snapshot();
                let parents = qualified_parents(&snapshot.qualified, fixture.lower_record);
                let draft = lower_draft(&snapshot);
                assert_eq!(parents.len(), 260);
                assert_eq!(draft.incoming.len(), 256);
                assert_eq!(draft.completeness, ProvenanceCompleteness::Incomplete);
                assert_eq!(snapshot.completeness, ProvenanceCompleteness::Incomplete);
                let prefix = draft.incoming.iter().flat_map(|edge| &edge.parents).copied().collect::<Vec<_>>();
                assert_eq!(prefix, parents[..256]);
                let capped = (draft.incoming.clone(), prefix, draft.completeness, snapshot.completeness);
                assert_eq!(capped, *expected.get_or_insert_with(|| capped.clone()));
            }
        }

        #[test]
        fn canonical_portable_export_and_explanation_sequences_are_invariant_across_all_permutations() {
            let events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let mut expected = None;
            for order in permutations() {
                let mut fixture = Fixture::new();
                for index in order { fixture.admit(events[index]); }
                fixture.canonicalize_shadow_ledgers();
                let roots = fixture.record_witness_roots();
                let snapshot = fixture.portable_consumer_snapshot(&roots, PortableProvenanceExportBudget::default());
                assert_eq!(snapshot.export.root_anchors.len(), 2);
                assert_eq!(snapshot.export.snapshot.completeness(), PortableCompleteness::Complete);
                assert_eq!(snapshot.export.snapshot.truncation(), None);
                assert!(!snapshot.export.snapshot.nodes().is_empty());
                assert!(!snapshot.export.snapshot.edges().is_empty());
                assert_eq!(snapshot.export.snapshot.source_sites().len(), 2);
                assert_eq!(snapshot.explanation.lower_sites.len(), 2);
                assert_eq!(snapshot.explanation.upper_sites, snapshot.explanation.lower_sites);
                assert_eq!(snapshot.explanation.completeness, DiagnosticExplanationCompleteness::Complete);
                assert_eq!(snapshot.explanation.truncation, None);
                assert_eq!(snapshot, *expected.get_or_insert_with(|| snapshot.clone()));
            }
        }

        #[test]
        fn canonical_diagnostic_roles_remain_ordered_when_distinct_causes_share_a_location() {
            let events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let mut expected = None;
            for order in permutations() {
                let mut fixture = Fixture::new();
                let claimed_boundaries = fixture.add_claimed_source_origins([
                    ConstraintOriginKind::Annotation, ConstraintOriginKind::Pattern,
                ]);
                let independent_boundaries = [fixture.boundaries[0], fixture.boundaries[1]];
                for index in order { fixture.admit(events[index]); }
                fixture.canonicalize_shadow_ledgers();
                let roots = fixture.record_witness_roots();
                let snapshot = fixture.portable_consumer_snapshot_with_location(
                    &roots, PortableProvenanceExportBudget::default(), move |boundary, _| {
                        let start = if boundary == claimed_boundaries[0]
                            || boundary == independent_boundaries[0] { 10 }
                        else if boundary == claimed_boundaries[1] { 20 }
                        else if boundary == independent_boundaries[1] { 30 }
                        else { 100 + boundary.0 * 2 };
                        Some(PortableSourceLocation {
                            module: vec!["rcpf-duplicate".to_string()],
                            range: PortableByteRange { start, end: start + 1 },
                        })
                    },
                );
                let source_sites = snapshot.export.snapshot.source_sites();
                assert_eq!(source_sites.len(), 4);
                assert_eq!(source_sites[0].location.as_ref(), source_sites[2].location.as_ref());
                assert_ne!(source_sites[0].role, source_sites[2].role);
                assert_ne!(source_sites[1].location.as_ref(), source_sites[0].location.as_ref());
                assert_ne!(source_sites[3].location.as_ref(), source_sites[0].location.as_ref());
                let explanation = snapshot.explanation;
                assert_eq!(explanation.completeness, DiagnosticExplanationCompleteness::Complete);
                assert_eq!(explanation.truncation, None);
                assert_eq!(explanation.lower_sites.iter().map(|cause| cause.role).collect::<Vec<_>>(), vec![
                    DiagnosticTypeCauseRole::RequiredByAnnotation,
                    DiagnosticTypeCauseRole::RequiredByPattern,
                    DiagnosticTypeCauseRole::InferredFromExpression,
                    DiagnosticTypeCauseRole::InferredFromExpression,
                ]);
                assert_eq!(explanation.upper_sites, explanation.lower_sites);
                let causes = &explanation.lower_sites;
                assert_eq!(causes[0].source_span, causes[2].source_span, "cross-category causes share one location");
                assert_ne!(causes[0].role, causes[2].role, "shared-location causes retain distinct roles");
                assert_ne!(causes[1].source_span, causes[0].source_span, "second claim remains distinct");
                assert_ne!(causes[3].source_span, causes[0].source_span, "second independent remains distinct");
                assert_ne!(causes[1].source_span, causes[3].source_span, "unpaired causes remain distinct");
                assert_eq!(explanation, *expected.get_or_insert_with(|| explanation.clone()));
            }
        }

        #[test]
        fn canonical_export_budget_truncation_is_invariant_and_a_full_snapshot_prefix() {
            let events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let mut expected_full = None;
            let mut expected_tight = None;
            for order in permutations() {
                let mut fixture = Fixture::new();
                for index in order { fixture.admit(events[index]); }
                fixture.canonicalize_shadow_ledgers();
                let roots = fixture.record_witness_roots();
                let full = fixture.portable_consumer_snapshot(&roots, PortableProvenanceExportBudget::default());
                assert!(full.export.snapshot.nodes().len() > 4);
                assert!(full.export.snapshot.edges().len() > 3);
                let mut tight_snapshots = Vec::new();
                for (name, budget, truncation, anchor_survival) in export_budget_ladder() {
                    let tight = fixture.portable_consumer_snapshot(&roots, budget);
                    let snapshot = &tight.export.snapshot;
                    assert_eq!(snapshot.completeness(), PortableCompleteness::Incomplete, "{name}");
                    assert_eq!(snapshot.truncation(), Some(truncation), "{name}");
                    assert_eq!(tight.export.root_anchors.iter().map(Option::is_some).collect::<Vec<_>>(),
                        anchor_survival, "{name}: root-anchor survival");
                    let anchor = tight.export.root_anchors[0].expect("tight export retains its first root anchor");
                    assert_eq!(snapshot.anchor(anchor).expect("retained anchor").completeness,
                        PortableCompleteness::Incomplete, "{name}");
                    assert!(snapshot.nodes().len() < full.export.snapshot.nodes().len()
                        || snapshot.edges().len() < full.export.snapshot.edges().len(), "{name}: budget must truncate content");
                    assert_eq!(snapshot.nodes(), &full.export.snapshot.nodes()[..snapshot.nodes().len()], "{name}: node prefix");
                    assert_eq!(snapshot.edges(), &full.export.snapshot.edges()[..snapshot.edges().len()], "{name}: edge prefix");
                    assert_eq!(snapshot.source_sites(),
                        &full.export.snapshot.source_sites()[..snapshot.source_sites().len()], "{name}: source-site prefix");
                    assert_eq!(tight.explanation.lower_sites,
                        full.explanation.lower_sites[..tight.explanation.lower_sites.len()], "{name}: lower cause prefix");
                    assert_eq!(tight.explanation.upper_sites,
                        full.explanation.upper_sites[..tight.explanation.upper_sites.len()], "{name}: upper cause prefix");
                    assert_eq!(tight.explanation.completeness,
                        DiagnosticExplanationCompleteness::IncompleteProvenance, "{name}");
                    assert_eq!(tight.explanation.truncation, None, "{name}");
                    tight_snapshots.push(tight);
                }
                assert_eq!(full, *expected_full.get_or_insert_with(|| full.clone()));
                assert_eq!(tight_snapshots, *expected_tight.get_or_insert_with(|| tight_snapshots.clone()));
            }
        }

        #[test]
        fn canonical_portable_query_budget_causes_are_invariant_full_result_prefixes() {
            let events = [Event::Replay, Event::NonReplay, Event::Independent(0), Event::Independent(1)];
            let mut expected_full = None;
            let mut expected_tight = None;
            for order in permutations() {
                let mut fixture = Fixture::new();
                for index in order { fixture.admit(events[index]); }
                fixture.canonicalize_shadow_ledgers();
                let roots = fixture.record_witness_roots();
                let full = fixture.portable_consumer_snapshot(&roots, PortableProvenanceExportBudget::default());
                assert_eq!(full.export.snapshot.completeness(), PortableCompleteness::Complete);
                assert_eq!(full.explanation.lower_sites.len(), 2);
                assert_eq!(full.explanation.upper_sites.len(), 2);
                let anchors = full.export.root_anchors.iter().flatten().copied().collect::<Vec<_>>();
                let mut tight_results = Vec::new();
                let mut retained_nonempty_prefix = false;
                for (name, budget, truncation) in explanation_budget_ladder() {
                    let tight = explain_portable_subtype(&full.export.snapshot, &anchors, &anchors, budget);
                    assert_eq!(tight.completeness, DiagnosticExplanationCompleteness::TruncatedByBudget, "{name}");
                    assert_eq!(tight.truncation, Some(truncation), "{name}");
                    assert!(tight.lower_sites.len() < full.explanation.lower_sites.len(), "{name}: lower causes truncate");
                    assert!(tight.upper_sites.len() < full.explanation.upper_sites.len(), "{name}: upper causes truncate");
                    assert_eq!(tight.lower_sites,
                        full.explanation.lower_sites[..tight.lower_sites.len()], "{name}: lower cause prefix");
                    assert_eq!(tight.upper_sites,
                        full.explanation.upper_sites[..tight.upper_sites.len()], "{name}: upper cause prefix");
                    assert_eq!(tight.upper_sites, tight.lower_sites, "{name}: endpoint symmetry");
                    retained_nonempty_prefix |= !tight.lower_sites.is_empty();
                    tight_results.push(tight);
                }
                assert!(retained_nonempty_prefix, "node or edge budget retains a genuine non-empty cause prefix");
                assert_eq!(full, *expected_full.get_or_insert_with(|| full.clone()));
                assert_eq!(tight_results, *expected_tight.get_or_insert_with(|| tight_results.clone()));
            }
        }

        #[test]
        fn factored_lower_full_oracle_matches_target_late_bootstrap() {
            let mut fixture = Fixture::new(); fixture.machine.enable_replay_factored_event_oracle();
            fixture.admit_factored_replay(false);
            fixture.machine.register_lower_projection_derivation(
                fixture.lower_record, Some(fixture.result), BoundDerivation::Constraint(fixture.result),
            );
            assert_eq!(fixture.machine.try_legacy_lower_projection(fixture.lower_record).unwrap(),
                LowerProjectionAdapterSnapshot { claimed_roots: vec![fixture.roots[0]],
                    proof_keys: vec![Key::Claimed(fixture.roots[0])] });
            assert_eq!(fixture.machine.replay_factored_shadow_status.get(), ReplayFactoredShadowStatus::Active);
        }
        #[test]
        fn factored_lower_delta_oracle_matches_populated_replay_delta() {
            let mut fixture = Fixture::new(); fixture.machine.enable_replay_factored_event_oracle();
            fixture.admit_factored_replay(true);
            assert_eq!(fixture.snapshot().2, vec![Key::Claimed(fixture.roots[0])]);
            assert_eq!(fixture.machine.replay_factored_shadow_status.get(), ReplayFactoredShadowStatus::Active);
        }
        #[test]
        fn factored_lower_oracle_mismatch_quarantines_after_legacy_commit() {
            let mut fixture = Fixture::new(); fixture.machine.enable_replay_factored_event_oracle();
            fixture.admit_factored_replay(false);
            fixture.machine.register_lower_projection_derivation(
                fixture.lower_record, Some(fixture.result), BoundDerivation::Constraint(fixture.result),
            );
            fixture.machine.bounds.scheme_projection_claims_by_lower_record
                .get_mut(&fixture.lower_record).unwrap().clear();
            fixture.machine.bounds.projection_proofs_by_lower_record
                .get_mut(&fixture.lower_record).unwrap().clear();
            mark_next_replay_soak_failure_as_intentional();
            fixture.machine.register_lower_projection_derivation(
                fixture.lower_record, Some(fixture.result), BoundDerivation::Constraint(fixture.result),
            );
            assert_eq!(fixture.machine.replay_factored_shadow_status.get(),
                ReplayFactoredShadowStatus::Failed(ReplayFactoredShadowFailure::OracleMismatch(
                    ReplayFactoredOracleMismatch::DerivedReplayLineage)));
        }

        #[test]
        fn factored_record_lower_projection_includes_direct_and_qualified_roots() {
            let mut fixture = cdm_replay_claim_fixture();
            let replay = fixture.replay(ReplayRule::LowerBoundAdded);
            assert_eq!(fixture.machine.merge_replay_derivation(fixture.result, replay),
                ReplayDerivationInsert::Inserted);
            register_factored_parent_snapshot(
                &mut fixture.machine, fixture.result, replay, &[fixture.parent],
            );
            let direct_root = fixture.machine.bounds.root_claim_by_producer_constraint[&fixture.result];
            let legacy = fixture.machine.try_legacy_record_lower_projection(fixture.lower_record).unwrap();
            let factored = fixture.machine.try_factored_record_lower_projection(fixture.lower_record).unwrap();
            assert_eq!(factored, legacy);
            assert_eq!(factored.support_map, [
                SchemeProjectionProofSupport::Claimed(direct_root),
                SchemeProjectionProofSupport::Claimed(fixture.coverage_root),
            ].into_iter().collect());
            let mut expected_keys = vec![Key::Claimed(direct_root), Key::Claimed(fixture.coverage_root)];
            expected_keys.sort_by(canonical_projection_key::cmp);
            assert_eq!(factored.canonical.proof_keys, expected_keys);
        }

        #[test]
        fn factored_record_lower_projection_preserves_independent_supports() {
            let mut fixture = Fixture::new();
            fixture.admit(Event::Independent(0));
            fixture.admit_factored_replay(true);
            let claimed = SchemeProjectionProofSupport::Claimed(fixture.roots[0]);
            let independent = SchemeProjectionProofSupport::Independent(
                ProjectionProofCarrier::Origin(fixture.origins[0]),
            );
            let legacy = fixture.machine.try_legacy_record_lower_projection(fixture.lower_record).unwrap();
            let factored = fixture.machine.try_factored_record_lower_projection(fixture.lower_record).unwrap();
            assert_eq!(factored, legacy);
            assert_eq!(factored.support_map, [claimed, independent].into_iter().collect());
            assert_eq!(factored.canonical.proof_keys,
                vec![fixture.key(claimed), fixture.key(independent)]);
        }

        #[test]
        fn factored_record_lower_projection_keeps_first_winner_for_new_occurrence_old_root() {
            let mut fixture = Fixture::new();
            fixture.machine.enable_replay_factored_event_oracle();
            fixture.machine.constraint_records[fixture.result.0 as usize]
                .row_derivations.push(fixture.row);
            fixture.machine.register_reduction_route_claim_parent(
                fixture.result, fixture.row, fixture.roots[0],
            );
            let first = ClaimQualifiedParent::ReductionRouteConstraint {
                parent_claim: fixture.roots[0], derivation: fixture.row,
            };
            let before = fixture.machine
                .try_compare_factored_record_lower_projection(fixture.lower_record, &[]).unwrap();

            fixture.admit_factored_replay(true);

            let after = fixture.machine
                .try_compare_factored_record_lower_projection(fixture.lower_record, &[]).unwrap();
            assert_eq!(after, before, "the new occurrence reuses the existing logical root");
            assert!(fixture.machine.replay_result_summary
                .first_parent_witness(fixture.result, fixture.roots[0]).unwrap().is_some(),
                "D1 still records the new replay occurrence for the old root");
            assert_eq!(fixture.machine.replay_result_summary
                .first_qualified_parent_source(fixture.result, fixture.roots[0]),
                Ok(Some(FirstQualifiedParentSource::NonReplay(first))));
            assert_eq!(fixture.machine.bounds.scheme_projection_lower_records_by_root
                [&fixture.roots[0]].iter().filter(|record| **record == fixture.lower_record).count(), 1);
            assert_eq!(fixture.machine.replay_factored_shadow_status.get(),
                ReplayFactoredShadowStatus::Active);
        }

        #[test]
        fn factored_record_lower_projection_transitions_independent_then_claimed_canonically() {
            let mut fixture = Fixture::new();
            fixture.machine.enable_replay_factored_event_oracle();
            fixture.admit(Event::Independent(0));
            fixture.machine.bounds.projection_proofs_by_lower_record
                .insert(fixture.lower_record, Vec::new());
            let carrier = ProjectionProofCarrier::Origin(fixture.origins[0]);
            fixture.machine.register_lower_record_projection_carrier_delta(
                fixture.lower_record, carrier,
            );
            let independent = SchemeProjectionProofSupport::Independent(carrier);
            let before = fixture.machine
                .try_compare_factored_record_lower_projection(fixture.lower_record, &[]).unwrap();
            assert_eq!(before.canonical.proof_keys, vec![Key::Independent(carrier)]);
            let previous_proofs = vec![SchemeProjectionProof {
                lower_record: fixture.lower_record, support: independent,
            }];
            let provenance_before = fixture.machine.provenance_epoch;

            fixture.admit_factored_replay(true);

            let claimed = SchemeProjectionProofSupport::Claimed(fixture.roots[0]);
            let after = fixture.machine
                .try_compare_factored_record_lower_projection(fixture.lower_record, &[]).unwrap();
            assert_eq!(after.canonical.proof_keys,
                vec![fixture.key(claimed), fixture.key(independent)]);
            let current_proofs = ConstraintMachine::try_lower_projection_proofs_from_snapshot(
                fixture.lower_record, &after,
            ).unwrap();
            assert_eq!(fixture.machine.try_factored_lower_projection_publication_class(
                fixture.lower_record, Some(&previous_proofs), &current_proofs,
            ), Ok(LowerProjectionPublicationClass::MetadataOnly));
            assert!(fixture.machine.provenance_epoch > provenance_before);
            assert!(fixture.machine.bounds.scheme_projection_lower_record_memberships
                .contains(&(fixture.roots[0], fixture.lower_record)));
            assert_eq!(fixture.machine.replay_factored_shadow_status.get(),
                ReplayFactoredShadowStatus::Active);
        }
    }

    fn changed_keys(mutations: Vec<MethodRoleMutation>) -> Vec<DependencyKey> {
        mutations
            .into_iter()
            .filter_map(|mutation| match mutation {
                MethodRoleMutation::Changed { key, .. } => Some(key),
                MethodRoleMutation::InvalidateAll { reason, .. } => {
                    panic!("unexpected InvalidateAll: {reason:?}")
                }
            })
            .collect()
    }
}

fn increment_var_neighbor(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) {
    *adjacency.entry(left).or_default().entry(right).or_default() += 1;
}

fn increment_var_neighbor_recording_transition(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) -> bool {
    let count = adjacency.entry(left).or_default().entry(right).or_default();
    let absent = *count == 0;
    *count += 1;
    absent
}

fn decrement_var_neighbor(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) -> bool {
    let Some(neighbors) = adjacency.get_mut(&left) else {
        return false;
    };
    let Some(count) = neighbors.get_mut(&right) else {
        return false;
    };
    *count = count.saturating_sub(1);
    let removed = *count == 0;
    if *count == 0 {
        neighbors.remove(&right);
    }
    if neighbors.is_empty() {
        adjacency.remove(&left);
    }
    removed
}

fn collect_pos_id_vars(types: &TypeArena, id: PosId, out: &mut FxHashSet<TypeVar>) {
    match types.pos(id) {
        Pos::Bot => {}
        Pos::Var(var) => {
            out.insert(*var);
        }
        Pos::Con(_, args) => collect_neu_id_vars(types, args.iter().copied(), out),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_id_vars(types, *arg, out);
            collect_neg_id_vars(types, *arg_eff, out);
            collect_pos_id_vars(types, *ret_eff, out);
            collect_pos_id_vars(types, *ret, out);
        }
        Pos::Record(fields) => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
        }
        Pos::RecordTailSpread { fields, tail } => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
            collect_pos_id_vars(types, *tail, out);
        }
        Pos::RecordHeadSpread { tail, fields } => {
            collect_pos_id_vars(types, *tail, out);
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
        }
        Pos::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_pos_id_vars(types, *payload, out);
                }
            }
        }
        Pos::Tuple(items) | Pos::Row(items) => {
            for item in items {
                collect_pos_id_vars(types, *item, out);
            }
        }
        Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
            collect_pos_id_vars(types, *inner, out);
        }
        Pos::Union(left, right) => {
            collect_pos_id_vars(types, *left, out);
            collect_pos_id_vars(types, *right, out);
        }
    }
}

fn collect_neg_id_vars(types: &TypeArena, id: NegId, out: &mut FxHashSet<TypeVar>) {
    match types.neg(id) {
        Neg::Top | Neg::Bot => {}
        Neg::Var(var) => {
            out.insert(*var);
        }
        Neg::Con(_, args) => collect_neu_id_vars(types, args.iter().copied(), out),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_id_vars(types, *arg, out);
            collect_pos_id_vars(types, *arg_eff, out);
            collect_neg_id_vars(types, *ret_eff, out);
            collect_neg_id_vars(types, *ret, out);
        }
        Neg::Record(fields) => {
            for field in fields {
                collect_neg_id_vars(types, field.value, out);
            }
        }
        Neg::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neg_id_vars(types, *payload, out);
                }
            }
        }
        Neg::Tuple(items) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
        }
        Neg::Row(items, tail) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
            collect_neg_id_vars(types, *tail, out);
        }
        Neg::Stack { inner, .. } => collect_neg_id_vars(types, *inner, out),
        Neg::Intersection(left, right) => {
            collect_neg_id_vars(types, *left, out);
            collect_neg_id_vars(types, *right, out);
        }
    }
}

fn collect_neu_id_vars(
    types: &TypeArena,
    ids: impl IntoIterator<Item = NeuId>,
    out: &mut FxHashSet<TypeVar>,
) {
    for id in ids {
        match types.neu(id) {
            Neu::Bounds(lower, upper) => {
                collect_pos_id_vars(types, *lower, out);
                collect_neg_id_vars(types, *upper, out);
            }
            Neu::Con(_, args) => collect_neu_id_vars(types, args.iter().copied(), out),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                collect_neu_id_vars(types, [*arg, *arg_eff, *ret_eff, *ret], out);
            }
            Neu::Record(fields) => {
                for field in fields {
                    collect_neu_id_vars(types, [field.value], out);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    collect_neu_id_vars(types, payloads.iter().copied(), out);
                }
            }
            Neu::Tuple(items) => collect_neu_id_vars(types, items.iter().copied(), out),
        }
    }
}

fn row_tail_matches(types: &TypeArena, row_upper: NegId, tail_upper: NegId) -> bool {
    let Neg::Row(_, tail) = types.neg(row_upper) else {
        return false;
    };
    neg_ids_match_for_row_tail(types, *tail, tail_upper)
}

fn neg_ids_match_for_row_tail(types: &TypeArena, lhs: NegId, rhs: NegId) -> bool {
    if lhs == rhs {
        return true;
    }
    match (types.neg(lhs), types.neg(rhs)) {
        (Neg::Var(left), Neg::Var(right)) => left == right,
        (Neg::Top, Neg::Top) | (Neg::Bot, Neg::Bot) => true,
        _ => false,
    }
}

fn constraint_weights_have_row_tail_boundary(weights: &ConstraintWeights) -> bool {
    left_constraint_weight_has_row_tail_boundary(&weights.left)
}

fn left_constraint_weight_has_row_tail_boundary(weight: &LeftConstraintWeight) -> bool {
    weight.has_filter() || weight.entries().iter().any(|entry| entry.pushes > 0)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AliasReplayCycleLeftEntry {
    id: SubtractId,
    leading_pop: bool,
    family: Option<Subtractability>,
    push: bool,
}

fn alias_replay_cycle_weights_match(lhs: &ConstraintWeights, rhs: &ConstraintWeights) -> bool {
    let Some(lhs) = alias_replay_cycle_weight_key(lhs) else {
        return false;
    };
    let Some(rhs) = alias_replay_cycle_weight_key(rhs) else {
        return false;
    };
    lhs == rhs
}

fn alias_replay_cycle_weight_key(
    weights: &ConstraintWeights,
) -> Option<(Vec<AliasReplayCycleLeftEntry>, Vec<SubtractId>)> {
    if weights.left.has_filter() {
        return None;
    }
    let left = weights
        .left
        .entries()
        .iter()
        .filter(|entry| entry.leading_pops > 0 || entry.pushes > 0)
        .map(|entry| AliasReplayCycleLeftEntry {
            id: entry.id,
            leading_pop: entry.leading_pops > 0,
            family: entry.family.clone(),
            push: entry.pushes > 0,
        })
        .collect::<Vec<_>>();
    let right = weights
        .right
        .entries()
        .iter()
        .filter(|entry| entry.pops > 0)
        .map(|entry| entry.id)
        .collect::<Vec<_>>();
    if left.is_empty() && right.is_empty() {
        None
    } else {
        Some((left, right))
    }
}
