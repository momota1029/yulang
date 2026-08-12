use super::*;

use crate::constraints::proof::ProofKernelResult;
use smallvec::SmallVec;

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
    // CPK prepares the event-local exact-parent candidates; admission filters them atomically.
    claim_parents: ReplayClaimParents,
    canonicalization_disposition: Option<ConstraintCanonicalizationDisposition>,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct BoundReplayPlan {
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

fn incremental_route_key(route: &UnweightedRowReductionReplayRoute) -> proof::IncrementalRouteKey {
    proof::IncrementalRouteKey {
        upper: route.upper,
        upper_record: route.upper_record,
        provenance: route.provenance,
        claim: route.claim,
    }
}

fn replay_claim_parents(parents: &proof::PreparedReplayParentSet) -> ReplayClaimParents {
    parents
        .iter()
        .map(|parent| SideTaggedReplayClaim {
            claim: parent.representative_claim,
            parent_side: parent.side,
        })
        .collect()
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
    links: Vec<RecordProofClauseLinkAdmission>,
}

#[derive(Default)]
struct ReplayAdmissionPublicationFence {
    intents: Vec<SchemeProjectionPublicationIntent>,
}

impl ReplayAdmissionPublicationFence {
    fn try_push(&mut self, intent: SchemeProjectionPublicationIntent) -> ProofKernelResult<()> {
        self.intents
            .try_reserve(1)
            .map_err(|_| proof::ProofFailure::ResourceExhausted {
                operation: proof::ProofOperation::UpdateClaimLifecycle,
            })?;
        self.intents.push(intent);
        Ok(())
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
        self.proof_store.record_bound_disposition(
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
        if let Some(producer) = producer
            && !self.admit_projection_index(
                Some((proof::ProjectionTarget::Constraint(producer), insertion.id)),
                &[],
            )
        {
            return;
        }
        if insertion.provenance_changed {
            self.proof_store
                .record_bound(insertion.id, derivation.clone());
        }
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
        if self.proof_terminal_failure().is_some() {
            return;
        }
        self.apply_cpk_prefiltered_replay_provenance(
            replay.duplicate_actions,
            replay.trivial_actions,
        );
        let apply = self.apply_cpk_bound_replay_actions(replay.actions);
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
                    self.proof_store.record_bound(id, derivation.clone());
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
        if insertion.provenance_changed {
            self.proof_store
                .record_bound(insertion.id, derivation.clone());
        }
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
        if self.proof_terminal_failure().is_some() {
            return;
        }
        self.apply_cpk_prefiltered_replay_provenance(
            replay.duplicate_actions,
            replay.trivial_actions,
        );
        let apply = self.apply_cpk_bound_replay_actions(replay.actions);
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
        let parents = self
            .proof_store
            .canonical_qualified_parents_by_root(producer)
            .map(|entry| entry.parent)
            .collect::<Vec<_>>();
        if let Some(lower_record) = self.lower_record_for_constraint(producer) {
            self.register_all_claim_parent_clause_links_after_factored_projection(
                producer,
                lower_record,
                None,
            );
            if self.proof_terminal_failure().is_some() {
                return Vec::new();
            }
        }
        let mut claims: Vec<UpperReplayClaimId> = Vec::new();
        for parent in parents {
            let parent_claim = parent.parent_claim();
            let coverage_root = self
                .proof_store
                .claim_coverage_root(parent_claim)
                .expect("qualified replay parent must exist in the CPK claim arena");
            // The exact route carrier remains in the CPK result-local parent view, while the
            // materialized upper claim is canonical per record and coverage root. Replaying the
            // second carrier would only count the same proof as a claim cycle.
            if matches!(
                parent,
                ClaimQualifiedParent::ReductionRouteConstraint { .. }
            ) && claims
                .iter()
                .any(|claim| self.proof_store.claim_coverage_root(*claim) == Some(coverage_root))
            {
                continue;
            }
            let Some(claim) =
                self.materialize_constraint_upper_replay_claim(record, producer, parent, None)
            else {
                return claims;
            };
            if !claims.contains(&claim) {
                claims.push(claim);
            }
        }
        if claims.is_empty() {
            let Some(registration) = self.admit_original_upper_replay_claim(
                record,
                producer,
                UpperReplayClaimKind::Direct,
            ) else {
                return claims;
            };
            self.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
            claims.push(registration.claim);
        }
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
            let coverage_root = self
                .proof_store
                .claim_coverage_root(parent.parent_claim())
                .expect("qualified replay parent must exist in the CPK claim arena");
            // Materialization is canonical per (record, root), not per exact carrier. The caller
            // has already recorded every newly admitted key and qualified parent unconditionally.
            if self
                .proof_store
                .derived_claim(record, coverage_root)
                .is_some()
            {
                continue;
            }
            let Some(claim) = self.materialize_constraint_upper_replay_claim(
                record,
                producer,
                parent,
                publication_fence.as_deref_mut(),
            ) else {
                return claims;
            };
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
    ) -> Option<UpperReplayClaimId> {
        let parent_claim = parent.parent_claim();
        let registration = match parent {
            ClaimQualifiedParent::ReplayConstraint {
                parent_side,
                replay,
                ..
            } => self.admit_derived_upper_replay_claim(record, parent_claim, producer, |depth| {
                UpperReplayClaimLineage::ReplayConstraint {
                    parent_claim,
                    parent_side,
                    result: producer,
                    replay,
                    depth,
                }
            }),
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => self
                .admit_derived_upper_replay_claim(record, parent_claim, producer, |depth| {
                    UpperReplayClaimLineage::StructuralConstraint {
                        parent_claim,
                        result: producer,
                        derivation,
                        depth,
                    }
                }),
            ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => self
                .admit_derived_upper_replay_claim(record, parent_claim, producer, |depth| {
                    UpperReplayClaimLineage::ReductionRouteConstraint {
                        parent_claim,
                        result: producer,
                        derivation,
                        depth,
                    }
                }),
        }?;
        if let Some(fence) = publication_fence {
            self.defer_scheme_projection_mutation(fence, registration.scheme_projection_mutation);
        } else {
            self.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
        }
        Some(registration.claim)
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
        let preflight =
            self.preflight_claim_parent_clause_links(result, lower_record, parents.iter().copied());
        self.commit_record_proof_clause_link_batch_mutation(lower_record, preflight.links)
    }

    fn try_commit_all_claim_parent_clause_links_mutation(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
    ) -> ProofKernelResult<Option<ClauseLinkBatchAdmissionSnapshot>> {
        let associations = self
            .proof_store
            .try_replay_clause_link_associations(result)?;
        let preflight = self.preflight_claim_parent_clause_links(
            result,
            lower_record,
            associations.map(|entry| entry.parent),
        );
        Ok(self.commit_record_proof_clause_link_batch_mutation(lower_record, preflight.links))
    }

    fn preflight_claim_parent_clause_links(
        &self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: impl IntoIterator<Item = ClaimQualifiedParent>,
    ) -> ClaimParentClauseLinkPreflight {
        let mut pending_links = Vec::new();
        let mut batch_link_keys = FxHashSet::default();
        for parent in parents {
            let Some(root) = self.proof_store.claim_coverage_root(parent.parent_claim()) else {
                continue;
            };
            let (clause, attribution_source, proof_source) = match parent {
                ClaimQualifiedParent::ReplayConstraint { replay, .. } => (
                    RecordProofClause::ReplayConjunction {
                        carrier: replay,
                        lower_premise: replay.lower,
                        upper_premise: replay.upper,
                    },
                    ClaimedAttributionSource::CanonicalReplay,
                    ClaimedProjectionProofSource::ReplayConstraint {
                        coverage_root: root,
                        result,
                    },
                ),
                ClaimQualifiedParent::StructuralConstraint { derivation, .. } => (
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::Structural(derivation),
                        premise: ProofPremise::Constraint(derivation.parent),
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::DerivedUnary {
                        coverage_root: root,
                        result,
                    },
                ),
                ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => (
                    RecordProofClause::DerivedUnary {
                        carrier: DerivedUnaryCarrier::ReductionRoute(derivation),
                        premise: ProofPremise::RootCoverage(root),
                    },
                    ClaimedAttributionSource::FlatRetained,
                    ClaimedProjectionProofSource::DerivedUnary {
                        coverage_root: root,
                        result,
                    },
                ),
            };
            let support = SchemeProjectionProofSupport::Claimed(root);
            if self
                .proof_store
                .projection_clause_link_is_registered(lower_record, support, clause)
            {
                continue;
            }
            let batch_link_key = ((lower_record, clause), support);
            if !batch_link_keys.insert(batch_link_key) {
                continue;
            }
            pending_links.push(RecordProofClauseLinkAdmission::claimed(
                root,
                clause,
                attribution_source,
                proof_source,
            ));
        }
        ClaimParentClauseLinkPreflight {
            links: pending_links,
        }
    }

    fn register_claim_parent_clause_links_after_factored_projection(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        parents: &[ClaimQualifiedParent],
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        // Phase A is unconditional. Only after Phase B has made the factored occurrence/parent
        // view current may the pending after-view be evaluated and published.
        let snapshot =
            self.commit_claim_parent_clause_links_mutation(result, lower_record, parents);
        if self.proof_terminal_failure().is_none() {
            self.seal_record_proof_clause_link_batch(snapshot, publication_fence);
        }
    }

    fn register_all_claim_parent_clause_links_after_factored_projection(
        &mut self,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        publication_fence: Option<&mut ReplayAdmissionPublicationFence>,
    ) {
        let snapshot =
            match self.try_commit_all_claim_parent_clause_links_mutation(result, lower_record) {
                Ok(snapshot) => snapshot,
                Err(failure) => {
                    self.mark_proof_terminal_failure(
                        proof::ProofOperation::ProjectLowerSupportCollection,
                        failure,
                    );
                    return;
                }
            };
        if self.proof_terminal_failure().is_none() {
            self.seal_record_proof_clause_link_batch(snapshot, publication_fence);
        }
    }

    fn register_replay_evidence_clause_link(
        &mut self,
        lower_record: BoundRecordId,
        parent_claim: UpperReplayClaimId,
        replay: BinaryReplayDerivation,
    ) {
        let Some(root) = self.proof_store.claim_coverage_root(parent_claim) else {
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
                ClaimedProjectionProofSource::ReplayEvidence {
                    coverage_root: root,
                },
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
            .proof_store
            .projection_clause_link_is_registered(lower_record, support, clause)
        {
            return;
        }
        self.commit_record_proof_clause_link_batch(lower_record, [admission]);
    }

    #[cfg(test)]
    pub(in crate::constraints) fn register_cpk_projection_clause_for_test(
        &mut self,
        lower_record: BoundRecordId,
        admission: RecordProofClauseLinkAdmission,
    ) {
        self.register_record_proof_clause_link(lower_record, admission);
    }

    #[cfg(test)]
    pub(in crate::constraints) fn materialize_replay_evidence_claim_for_test(
        &mut self,
        lower: PosId,
        upper: NegId,
        replay: BinaryReplayDerivation,
        parent_claim: UpperReplayClaimId,
    ) -> UpperReplayClaimId {
        let claim_count_before = self.proof_store.upper_claims_for_test().len();
        let mut actions = BoundReplayActions::new();
        actions.push(BoundReplayAction {
            constraint: SubtypeConstraintKey {
                lower,
                upper,
                weights: ConstraintWeights::empty(),
            },
            derivation: replay,
            claim_parents: [SideTaggedReplayClaim {
                claim: parent_claim,
                parent_side: ReplayClaimParentSide::Upper,
            }]
            .into_iter()
            .collect(),
            canonicalization_disposition: None,
        });
        self.apply_bound_replay_evidence_actions(actions);
        self.proof_store.upper_claims_for_test()[claim_count_before..]
            .iter()
            .find_map(|claim| {
                matches!(
                    claim.full_lineage,
                    proof::UpperClaimLineage::ReplayEvidence {
                        parent_claim: found_parent,
                        replay: found_replay,
                        ..
                    } if found_parent == parent_claim && found_replay == replay
                )
                .then_some(claim.claim)
            })
            .expect("production replay-evidence admission materializes the derived claim")
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
                    self.mark_proof_terminal_failure(
                        proof::ProofOperation::ProjectLowerEvaluation,
                        failure,
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
        let links = links.into_iter().collect::<Vec<_>>();
        if links.is_empty() {
            return None;
        }
        let was_included = self.scheme_projection_record_is_included(lower_record);
        let mut prepared = match self
            .proof_store
            .try_prepare_projection_clause_admission(lower_record, &links)
        {
            Ok(Some(prepared)) => prepared,
            Ok(None) => return None,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::UpdateClaimLifecycle,
                    failure,
                );
                return None;
            }
        };
        self.proof_store
            .commit_projection_clause_admission(&mut prepared);
        let mut inserted_clauses = Vec::new();
        for event in prepared.accepted().iter().copied() {
            if event.clause_inserted {
                inserted_clauses.push(event.admission.clause);
            }
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
                    self.admit_projection_index(
                        None,
                        &[
                            (ProofPremise::Record(lower_premise), lower_record),
                            (ProofPremise::Record(upper_premise), lower_record),
                        ],
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
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::ProjectLowerEvaluation,
                    failure,
                );
                return;
            }
        };
        if self.proof_terminal_failure().is_some() {
            return;
        }
        self.publish_scheme_projection_intent(intent);
    }

    fn try_admit_projection_index(
        &mut self,
        target: Option<(proof::ProjectionTarget, BoundRecordId)>,
        edges: &[(ProofPremise, BoundRecordId)],
    ) -> Result<(), proof::ProofFailure> {
        let mut admission = self
            .proof_store
            .try_prepare_projection_index_admission(target, edges)?;
        self.proof_store
            .commit_projection_index_admission(&mut admission);
        Ok(())
    }

    fn admit_projection_index(
        &mut self,
        target: Option<(proof::ProjectionTarget, BoundRecordId)>,
        edges: &[(ProofPremise, BoundRecordId)],
    ) -> bool {
        match self.try_admit_projection_index(target, edges) {
            Ok(()) => true,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::UpdateClaimLifecycle,
                    failure,
                );
                false
            }
        }
    }

    #[cfg(test)]
    pub(in crate::constraints) fn admit_projection_target_for_test(
        &mut self,
        target: proof::ProjectionTarget,
        record: BoundRecordId,
    ) {
        assert!(
            self.admit_projection_index(Some((target, record)), &[]),
            "CPK-aware fixture projection-target admission must succeed",
        );
    }

    fn try_evaluate_record_proof_clause_link_batch(
        &self,
        snapshot: &ClauseLinkBatchAdmissionSnapshot,
    ) -> ProofKernelResult<SchemeProjectionPublicationIntent> {
        let is_included = self.scheme_projection_record_is_included(snapshot.lower_record);
        Ok(self.evaluate_record_inclusion_publication(
            snapshot.lower_record,
            snapshot.was_included,
            is_included,
            false,
        ))
    }

    fn register_premise_dependency_chain(
        &mut self,
        premise: ProofPremise,
        dependent: BoundRecordId,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
    ) {
        // Factored occurrence lookup is fallible, so finish the whole graph-local read before
        // publishing any dependency edge from this chain.
        let mut authoritative_visited = visited_constraints.clone();
        let mut pending_premises = FxHashSet::default();
        let collection = self.try_collect_premise_dependency_chain(
            premise,
            &mut authoritative_visited,
            &mut pending_premises,
        );
        if let Err(failure) = collection {
            self.mark_proof_terminal_failure(
                proof::ProofOperation::ProjectLowerSupportCollection,
                failure,
            );
            return;
        }

        let edges = pending_premises
            .into_iter()
            .map(|pending| (pending, dependent))
            .collect::<Vec<_>>();
        if self.admit_projection_index(None, &edges) {
            *visited_constraints = authoritative_visited;
        }
    }

    fn try_collect_premise_dependency_chain(
        &self,
        premise: ProofPremise,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        pending_premises: &mut FxHashSet<ProofPremise>,
    ) -> ProofKernelResult<()> {
        pending_premises.insert(premise);
        let ProofPremise::Constraint(constraint) = premise else {
            return Ok(());
        };
        if !visited_constraints.insert(constraint) {
            return Ok(());
        }
        if let Some(lower_record) = self.lower_record_for_constraint(constraint) {
            pending_premises.insert(ProofPremise::Record(lower_record));
        }
        for item in self
            .proof_store
            .qualified_parent_evaluation_items(constraint)
        {
            match item {
                proof::QualifiedParentEvaluationItem::Replay(replay) => {
                    pending_premises.insert(ProofPremise::Record(replay.lower));
                    pending_premises.insert(ProofPremise::Record(replay.upper));
                }
                proof::QualifiedParentEvaluationItem::NonReplay(parent) => {
                    self.try_collect_claim_parent_dependency_chain(
                        parent,
                        visited_constraints,
                        pending_premises,
                    )?;
                }
            }
        }
        if let Some(root_claim) = self.proof_store.root_claim_for_producer(constraint)
            && let Some(root) = self.proof_store.claim_coverage_root(root_claim)
        {
            pending_premises.insert(ProofPremise::RootCoverage(root));
        }
        Ok(())
    }

    fn try_collect_claim_parent_dependency_chain(
        &self,
        parent: ClaimQualifiedParent,
        visited_constraints: &mut FxHashSet<ConstraintRecordId>,
        pending_premises: &mut FxHashSet<ProofPremise>,
    ) -> ProofKernelResult<()> {
        match parent {
            ClaimQualifiedParent::ReplayConstraint { replay, .. } => {
                pending_premises.insert(ProofPremise::Record(replay.lower));
                pending_premises.insert(ProofPremise::Record(replay.upper));
            }
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                self.try_collect_premise_dependency_chain(
                    ProofPremise::Constraint(derivation.parent),
                    visited_constraints,
                    pending_premises,
                )?;
            }
            ClaimQualifiedParent::ReductionRouteConstraint { parent_claim, .. } => {
                if let Some(root) = self.proof_store.claim_coverage_root(parent_claim) {
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
                self.admit_projection_index(
                    None,
                    &[
                        (ProofPremise::Record(replay.lower), dependent),
                        (ProofPremise::Record(replay.upper), dependent),
                    ],
                );
            }
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                self.register_premise_dependency_chain(
                    ProofPremise::Constraint(derivation.parent),
                    dependent,
                    visited_constraints,
                );
            }
            ClaimQualifiedParent::ReductionRouteConstraint { parent_claim, .. } => {
                if let Some(root) = self.proof_store.claim_coverage_root(parent_claim) {
                    self.admit_projection_index(
                        None,
                        &[(ProofPremise::RootCoverage(root), dependent)],
                    );
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
            .proof_store
            .dependent_records(ProofPremise::Constraint(constraint))
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
        self.admit_claim_qualified_parents(constraint, &[parent]);
    }

    #[cfg(test)]
    pub(in crate::constraints) fn admit_claim_qualified_parents(
        &mut self,
        constraint: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
    ) {
        let Ok(mut admission) = self.try_prepare_qualified_parent_admission(constraint, parents)
        else {
            return;
        };
        let (accepted, snapshot) = self.begin_qualified_parent_admission(&mut admission);
        for entry in accepted.iter().copied() {
            self.commit_claim_qualified_parent_mutation(constraint, entry);
        }
        if !accepted.is_empty() {
            self.publish_claim_qualified_parent_admission(snapshot);
        }
    }

    fn try_prepare_qualified_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
    ) -> Result<proof::PreparedQualifiedParentAdmission, proof::ProofFailure> {
        self.proof_store
            .try_prepare_qualified_parent_admission(result, parents)
    }

    fn begin_qualified_parent_admission(
        &mut self,
        admission: &mut proof::PreparedQualifiedParentAdmission,
    ) -> (
        Vec<proof::ExactQualifiedParent>,
        ClaimQualifiedParentAdmissionSnapshot,
    ) {
        let inclusion_before =
            self.projection_inclusion_snapshot(ProofPremise::Constraint(admission.result()));
        let accepted = admission.accepted().to_vec();
        self.proof_store
            .commit_qualified_parent_admission(admission);
        (
            accepted,
            ClaimQualifiedParentAdmissionSnapshot { inclusion_before },
        )
    }

    fn try_prepare_replay_qualified_parent_transaction(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[ClaimQualifiedParent],
    ) -> Result<proof::PreparedReplayQualifiedParentTransaction, proof::ProofFailure> {
        self.proof_store
            .try_prepare_replay_qualified_parent_transaction(result, replay, parents)
    }

    fn begin_replay_qualified_parent_transaction(
        &mut self,
        transaction: &mut proof::PreparedReplayQualifiedParentTransaction,
    ) -> (
        Vec<proof::ExactQualifiedParent>,
        ClaimQualifiedParentAdmissionSnapshot,
    ) {
        let inclusion_before =
            self.projection_inclusion_snapshot(ProofPremise::Constraint(transaction.result()));
        let accepted = transaction.accepted().to_vec();
        self.proof_store
            .commit_replay_qualified_parent_transaction(transaction);
        (
            accepted,
            ClaimQualifiedParentAdmissionSnapshot { inclusion_before },
        )
    }

    fn begin_non_replay_claim_parent_admission(
        &mut self,
        result: ConstraintRecordId,
        parents: &[ClaimQualifiedParent],
    ) -> (
        Option<ReplayAdmissionPublicationFence>,
        Vec<ClaimQualifiedParent>,
    ) {
        let mut publication_fence = Some(ReplayAdmissionPublicationFence::default());
        let mut admission = match self.try_prepare_qualified_parent_admission(result, parents) {
            Ok(prepared) => prepared,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::UpdateClaimLifecycle,
                    failure,
                );
                return (publication_fence, Vec::new());
            }
        };
        let (accepted, snapshot) = self.begin_qualified_parent_admission(&mut admission);
        let accepted_parents = accepted
            .iter()
            .map(|entry| entry.parent)
            .collect::<Vec<_>>();
        for entry in accepted.iter().copied() {
            self.commit_claim_qualified_parent_mutation(result, entry);
        }
        if !accepted.is_empty() {
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
                &accepted_parents,
                publication_fence.as_mut(),
            );
        }
        (publication_fence, accepted_parents)
    }

    fn finish_non_replay_claim_parent_admission(
        &mut self,
        _result: ConstraintRecordId,
        publication_fence: Option<ReplayAdmissionPublicationFence>,
    ) {
        let Some(publication_fence) = publication_fence else {
            return;
        };
        if self.proof_terminal_failure().is_some() {
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
    ) -> bool {
        let carrier = ProjectionProofCarrier::StructuralConstraint { result, derivation };
        let (mut publication_fence, admitted_parents) =
            self.begin_non_replay_claim_parent_admission(result, parents);
        if self.proof_terminal_failure().is_some() {
            return !admitted_parents.is_empty();
        }
        if derivation_inserted {
            self.register_constraint_projection_carrier_delta_with_precommitted_clause_links(
                result,
                &admitted_parents,
                carrier,
                true,
                publication_fence.as_mut(),
            );
        } else {
            self.register_existing_constraint_lower_projection_delta(
                result,
                &admitted_parents,
                LowerProjectionDelta::ClaimsOnly,
                true,
                publication_fence.as_mut(),
            );
        }
        self.finish_non_replay_claim_parent_admission(result, publication_fence);
        !admitted_parents.is_empty()
    }

    fn commit_claim_qualified_parent_mutation(
        &mut self,
        constraint: ConstraintRecordId,
        entry: proof::ExactQualifiedParent,
    ) {
        let parent = entry.parent;
        self.register_new_constraint_premise_route_edges(constraint, parent);
    }

    fn publish_claim_qualified_parent_admission(
        &mut self,
        snapshot: ClaimQualifiedParentAdmissionSnapshot,
    ) {
        let intent = match self.try_evaluate_claim_qualified_parent_admission(&snapshot) {
            Ok(intent) => intent,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::ProjectLowerEvaluation,
                    failure,
                );
                return;
            }
        };
        if self.proof_terminal_failure().is_some() {
            return;
        }
        self.publish_scheme_projection_intent(intent);
    }

    fn try_evaluate_claim_qualified_parent_admission(
        &self,
        snapshot: &ClaimQualifiedParentAdmissionSnapshot,
    ) -> ProofKernelResult<SchemeProjectionPublicationIntent> {
        self.try_evaluate_projection_inclusion_snapshot(&snapshot.inclusion_before)
    }

    fn defer_replay_admission_publication(
        &mut self,
        fence: &mut ReplayAdmissionPublicationFence,
        intent: SchemeProjectionPublicationIntent,
    ) {
        if self.proof_terminal_failure().is_some() {
            return;
        }
        if let Err(failure) = fence.try_push(intent) {
            self.mark_proof_terminal_failure(proof::ProofOperation::UpdateClaimLifecycle, failure);
        }
    }

    fn defer_claim_qualified_parent_admission(
        &mut self,
        fence: &mut ReplayAdmissionPublicationFence,
        snapshot: ClaimQualifiedParentAdmissionSnapshot,
    ) {
        if self.proof_terminal_failure().is_some() {
            return;
        }
        let intent = match self.try_evaluate_claim_qualified_parent_admission(&snapshot) {
            Ok(intent) => intent,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::ProjectLowerEvaluation,
                    failure,
                );
                return;
            }
        };
        self.defer_replay_admission_publication(fence, intent);
    }

    fn defer_scheme_projection_mutation(
        &mut self,
        fence: &mut ReplayAdmissionPublicationFence,
        mut mutation: SchemeProjectionMutation,
    ) {
        if self.proof_terminal_failure().is_some() {
            return;
        }
        let inclusion_before = self.cpk_projection_mutation_inclusion_before(&mutation);
        self.commit_scheme_projection_mutation(&mut mutation);
        let intent = self.evaluate_cpk_scheme_projection_mutation(mutation, inclusion_before);
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

    pub(in crate::constraints) fn lower_record_for_constraint(
        &self,
        producer: ConstraintRecordId,
    ) -> Option<BoundRecordId> {
        if let Some(record) = self
            .proof_store
            .projection_lower_record_for_constraint(producer)
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
            .map(|producer| {
                self.proof_store
                    .canonical_qualified_parents_by_root(producer)
                    .map(|entry| entry.parent)
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let claims = if self.proof_store.has_projection_support_ledger(lower_record) {
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
        if let Some(producer) = producer {
            self.register_all_claim_parent_clause_links_after_factored_projection(
                producer,
                lower_record,
                None,
            );
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
        let ledger_exists = self.proof_store.has_projection_support_ledger(lower_record);
        let bootstrap = !ledger_exists;
        let parents = if ledger_exists {
            parents.to_vec()
        } else {
            self.proof_store
                .canonical_qualified_parents_by_root(producer)
                .map(|entry| entry.parent)
                .collect()
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
            if bootstrap {
                self.register_all_claim_parent_clause_links_after_factored_projection(
                    producer,
                    lower_record,
                    publication_fence.as_deref_mut(),
                );
            } else {
                self.register_claim_parent_clause_links_after_factored_projection(
                    producer,
                    lower_record,
                    &parents,
                    publication_fence.as_deref_mut(),
                );
            }
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
            && self.proof_store.qualified_parent_count(producer) == parents.len()
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
        let ledger_exists = self.proof_store.has_projection_support_ledger(lower_record);
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
        let mutation = match self.try_prepare_scheme_projection_mutation(
            lower_record,
            claims_to_link,
            &independent_supports,
        ) {
            Ok(mutation) => mutation,
            Err(failure) => {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::UpdateClaimLifecycle,
                    failure,
                );
                return;
            }
        };
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
                .proof_store
                .projection_clause_link_is_registered(lower_record, support, clause)
            {
                continue;
            }
            let batch_link_key = ((lower_record, clause), support);
            if !batch_link_keys.insert(batch_link_key) {
                continue;
            }
            pending_links.push(RecordProofClauseLinkAdmission::independent(support, clause));
        }
        if pending_links.is_empty() {
            return;
        }
        self.commit_record_proof_clause_link_batch_with_fence(
            lower_record,
            pending_links,
            publication_fence,
        );
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
                .proof_store
                .projection_claims_for_record(lower_record)
                .iter()
                .any(|claim| {
                    self.proof_store
                        .upper_claim(*claim)
                        .is_some_and(|claim| claim.producer == constraint)
                }),
            ProjectionProofCarrier::StructuralConstraint { result, .. }
            | ProjectionProofCarrier::ReplayConstraint { result, .. }
            | ProjectionProofCarrier::RowConstraint { result, .. } => !self
                .proof_store
                .contains_qualified_parent_carrier(result, carrier),
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
            .proof_store
            .qualified_parent_values_for_result(producer)
            .collect::<Vec<_>>();
        let ledger_exists = self.proof_store.has_projection_support_ledger(lower_record);
        if claim_parents.is_empty() && !ledger_exists {
            return;
        }
        let claims = claim_parents
            .iter()
            .map(|parent| parent.parent_claim())
            .collect::<Vec<_>>();
        let independent_supports =
            self.independent_projection_supports_bulk(lower_record, Some(producer), &claim_parents);
        let mutation = self
            .try_prepare_scheme_projection_mutation(lower_record, &claims, &independent_supports)
            .expect("bulk projection oracle must have capacity");
        self.apply_scheme_projection_mutation(mutation);
    }

    #[cfg(test)]
    fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
        self.cdm_lower_delta_census.bulk_scans += 1;
        let supports = self.independent_projection_supports_bulk(lower_record, None, &[]);
        let mutation = self
            .try_prepare_scheme_projection_mutation(lower_record, &[], &supports)
            .expect("bulk projection oracle must have capacity");
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
                    let owned_parents;
                    let parents = if Some(*producer) == current_producer {
                        current_claim_parents
                    } else {
                        owned_parents = self
                            .proof_store
                            .qualified_parents_for_result(*producer)
                            .iter()
                            .map(|entry| entry.parent)
                            .collect::<Vec<_>>();
                        &owned_parents
                    };
                    let constraint = &self.constraint_records[producer.0 as usize];
                    let roots_have_claim_support = self
                        .proof_store
                        .projection_claims_for_record(lower_record)
                        .iter()
                        .any(|claim| {
                            self.proof_store
                                .upper_claim(*claim)
                                .is_some_and(|claim| claim.producer == *producer)
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

    fn register_cpk_replay_claim_parents(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
        materialize_existing_target: bool,
    ) {
        if !self.constraint_records[result.0 as usize]
            .replay_derivations
            .contains(&replay)
        {
            return;
        }
        let target_record = self.var_var_upper_record_for_constraint(result);
        let phase_b_enabled = self.proof_terminal_failure().is_none();
        let mut publication_fence = Some(ReplayAdmissionPublicationFence::default());
        let candidates = parents
            .iter()
            .map(|parent| ClaimQualifiedParent::ReplayConstraint {
                parent_claim: parent.claim,
                parent_side: parent.parent_side,
                replay,
            })
            .collect::<Vec<_>>();
        let mut admission =
            match self.try_prepare_replay_qualified_parent_transaction(result, replay, &candidates)
            {
                Ok(prepared) => prepared,
                Err(failure) => {
                    self.mark_proof_terminal_failure(
                        proof::ProofOperation::UpdateClaimLifecycle,
                        failure,
                    );
                    return;
                }
            };
        let (accepted, snapshot) = self.begin_replay_qualified_parent_transaction(&mut admission);
        let mut inserted_parents = Vec::new();
        inserted_parents.reserve(accepted.len());
        for entry in accepted.iter().copied() {
            let parent = entry.parent;
            self.commit_claim_qualified_parent_mutation(result, entry);
            inserted_parents.push(parent);
        }
        if !accepted.is_empty() {
            if let Some(fence) = publication_fence.as_mut() {
                self.defer_claim_qualified_parent_admission(fence, snapshot);
            } else {
                self.publish_claim_qualified_parent_admission(snapshot);
            }
        }
        let clause_projection_lower = self.lower_record_for_constraint(result);
        let bootstrap_clause_projection = phase_b_enabled
            && materialize_existing_target
            && clause_projection_lower.is_some_and(|lower_record| {
                !self.proof_store.has_projection_support_ledger(lower_record)
            });
        let pending_clause_link_snapshot = if phase_b_enabled
            && materialize_existing_target
            && let Some(lower_record) = clause_projection_lower
        {
            if bootstrap_clause_projection {
                match self.try_commit_all_claim_parent_clause_links_mutation(result, lower_record) {
                    Ok(snapshot) => snapshot,
                    Err(failure) => {
                        self.mark_proof_terminal_failure(
                            proof::ProofOperation::ProjectLowerSupportCollection,
                            failure,
                        );
                        None
                    }
                }
            } else {
                self.commit_claim_parent_clause_links_mutation(
                    result,
                    lower_record,
                    &inserted_parents,
                )
            }
        } else {
            None
        };
        if phase_b_enabled && materialize_existing_target && self.proof_terminal_failure().is_none()
        {
            self.seal_record_proof_clause_link_batch(
                pending_clause_link_snapshot,
                publication_fence.as_mut(),
            );
        }
        if self.proof_terminal_failure().is_some() {
            return;
        }
        // Newly enqueued constraints consume this metadata during their bound admission.
        // Queue-suppressed duplicates need the eager path because no later admission will run.
        if materialize_existing_target {
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
        }
        if self.proof_terminal_failure().is_some() {
            return;
        }
        if let Some(fence) = publication_fence {
            self.publish_replay_admission_publication_fence(fence);
        }
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
        if publication_fence.is_some() && self.proof_terminal_failure().is_some() {
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
        let target_record = self.var_var_upper_record_for_constraint(result);
        let carrier = ProjectionProofCarrier::RowConstraint { result, derivation };
        let (mut publication_fence, admitted_parents) =
            self.begin_non_replay_claim_parent_admission(result, &[parent]);
        if admitted_parents.is_empty() {
            return;
        }
        self.proof_store
            .record_reduction_route(result, derivation, claim);
        if self.proof_terminal_failure().is_some() {
            return;
        }
        self.materialize_existing_claim_parents_delta(
            result,
            target_record,
            &admitted_parents,
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
        self.cpk_lower_bound_replay_actions(target, lower_record, pos, weights, incremental_routes)
            .unwrap_or_else(|failure| {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::PrepareReplayRouteBatch,
                    failure,
                );
                BoundReplayPlan::default()
            })
    }

    fn cpk_lower_bound_replay_actions(
        &self,
        target: TypeVar,
        lower_record: BoundRecordId,
        pos: PosId,
        weights: &ConstraintWeights,
        incremental_routes: &[UnweightedRowReductionReplayRoute],
    ) -> Result<BoundReplayPlan, proof::ProofFailure> {
        let Some(bounds) = self.bounds.of(target) else {
            return Ok(BoundReplayPlan::default());
        };
        let upper_count = bounds.projection_upper_records().count();
        let mut uppers = Vec::new();
        uppers
            .try_reserve(upper_count)
            .map_err(|_| proof::ProofFailure::ResourceExhausted {
                operation: proof::ProofOperation::PrepareReplayRouteBatch,
            })?;
        uppers.extend(
            bounds
                .projection_upper_records()
                .map(|(record, upper)| (record, upper.clone())),
        );

        let mut routes_by_upper =
            FxHashMap::<BoundRecordId, Vec<proof::IncrementalRouteKey>>::default();
        routes_by_upper
            .try_reserve(incremental_routes.len())
            .map_err(|_| proof::ProofFailure::ResourceExhausted {
                operation: proof::ProofOperation::PrepareReplayRouteBatch,
            })?;
        for route in incremental_routes {
            let routes = routes_by_upper.entry(route.upper_record).or_default();
            routes
                .try_reserve(1)
                .map_err(|_| proof::ProofFailure::ResourceExhausted {
                    operation: proof::ProofOperation::PrepareReplayRouteBatch,
                })?;
            routes.push(incremental_route_key(route));
        }

        let prepared_routes = self.proof_store.prepare_replay_routes_for_lower(
            self,
            lower_record,
            uppers.iter().map(|(upper_record, _)| {
                let incremental = routes_by_upper
                    .get(upper_record)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                (*upper_record, incremental)
            }),
        )?;
        debug_assert_eq!(prepared_routes.len(), uppers.len());

        let pair_count = prepared_routes
            .iter()
            .filter(|route| route.proof_event.pair_replay.is_some())
            .count();
        let incremental_count = prepared_routes
            .iter()
            .map(|route| route.proof_event.incremental_replays.len())
            .sum::<usize>();
        let replay_input_count = pair_count + incremental_count;
        let mut replay = BoundReplayPlan {
            input_count: replay_input_count,
            ..BoundReplayPlan::default()
        };
        trace_bound_replay_start("lower", target, replay_input_count);
        for (index, ((upper_record, upper), prepared)) in
            uppers.iter().zip(&prepared_routes).enumerate()
        {
            let Some(parents) = &prepared.proof_event.pair_replay else {
                continue;
            };
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
                    upper: *upper_record,
                    rule: ReplayRule::LowerBoundAdded,
                },
                replay_claim_parents(parents),
                &mut replay,
            );
        }

        let mut residual_by_key = FxHashMap::default();
        residual_by_key
            .try_reserve(incremental_count)
            .map_err(|_| proof::ProofFailure::ResourceExhausted {
                operation: proof::ProofOperation::PrepareReplayRouteBatch,
            })?;
        for prepared in &prepared_routes {
            for incremental in &prepared.proof_event.incremental_replays {
                residual_by_key.insert(
                    (incremental.route.upper, incremental.route.upper_record),
                    incremental,
                );
            }
        }
        for route in incremental_routes {
            let Some(prepared) = residual_by_key.remove(&(route.upper, route.upper_record)) else {
                continue;
            };
            replay.generated += 1;
            if self.is_var_var_replay(pos, prepared.route.upper) {
                replay.var_var += 1;
            }
            self.push_replay_constraint_or_prefilter(
                pos,
                weights.clone(),
                prepared.route.upper,
                BinaryReplayDerivation {
                    pivot: target,
                    lower: lower_record,
                    upper: prepared.route.upper_record,
                    rule: ReplayRule::LowerBoundAdded,
                },
                replay_claim_parents(&prepared.parents),
                &mut replay,
            );
        }
        Ok(replay)
    }

    #[cfg(test)]
    fn lower_record_replay_claim_parents(&self, lower_record: BoundRecordId) -> ReplayClaimParents {
        self.proof_store
            .projection_claims_for_record(lower_record)
            .iter()
            .copied()
            .map(|claim| SideTaggedReplayClaim {
                claim,
                parent_side: ReplayClaimParentSide::Lower,
            })
            .collect()
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
        self.cpk_upper_bound_replay_actions(source, upper_record, neg, weights)
            .unwrap_or_else(|failure| {
                self.mark_proof_terminal_failure(
                    proof::ProofOperation::PrepareReplayRouteBatch,
                    failure,
                );
                BoundReplayPlan::default()
            })
    }

    fn cpk_upper_bound_replay_actions(
        &self,
        source: TypeVar,
        upper_record: BoundRecordId,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> Result<BoundReplayPlan, proof::ProofFailure> {
        let Some(bounds) = self.bounds.of(source) else {
            return Ok(BoundReplayPlan::default());
        };
        let lower_count = bounds.projection_lower_records().count();
        let mut lowers = Vec::new();
        lowers
            .try_reserve(lower_count)
            .map_err(|_| proof::ProofFailure::ResourceExhausted {
                operation: proof::ProofOperation::PrepareReplayRouteBatch,
            })?;
        lowers.extend(
            bounds
                .projection_lower_records()
                .map(|(record, lower)| (record, lower.clone())),
        );
        let prepared_routes = self.proof_store.prepare_replay_routes_for_upper(
            self,
            lowers.iter().map(|(lower_record, _)| *lower_record),
            upper_record,
        )?;
        debug_assert_eq!(prepared_routes.len(), lowers.len());
        let replay_input_count = prepared_routes
            .iter()
            .filter(|route| route.proof_event.pair_replay.is_some())
            .count();
        let mut replay = BoundReplayPlan {
            input_count: replay_input_count,
            ..BoundReplayPlan::default()
        };
        trace_bound_replay_start("upper", source, replay_input_count);
        for (index, ((lower_record, lower), prepared)) in
            lowers.iter().zip(&prepared_routes).enumerate()
        {
            let Some(parents) = &prepared.proof_event.pair_replay else {
                continue;
            };
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
                    lower: *lower_record,
                    upper: upper_record,
                    rule: ReplayRule::UpperBoundAdded,
                },
                replay_claim_parents(parents),
                &mut replay,
            );
        }
        Ok(replay)
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
                canonicalization_disposition,
            });
            return;
        }
        replay.actions.push(BoundReplayAction {
            constraint,
            derivation,
            claim_parents,
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

    fn apply_cpk_bound_replay_actions(
        &mut self,
        actions: BoundReplayActions,
    ) -> BoundReplayApplyStats {
        let mut stats = BoundReplayApplyStats::default();
        for action in actions {
            let constraint = action.constraint.clone();
            let (enqueued, disposition) =
                self.enqueue_replay_subtype(action.constraint, action.derivation);
            if disposition != ReplayDerivationInsert::Incomplete {
                let result = self.canonical_constraints[&constraint];
                self.register_cpk_replay_claim_parents(
                    result,
                    action.derivation,
                    &action.claim_parents,
                    !enqueued,
                );
            }
            let admission_disposition = match (enqueued, disposition) {
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
            };
            let replay_result = self.canonical_constraints.get(&constraint).copied();
            self.proof_store.record_replay_admission(
                replay_result,
                action.derivation,
                admission_disposition,
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
            let projection_replay = match &lower_derivation {
                BoundDerivation::ReplayEvidence(replay) => Some(*replay),
                BoundDerivation::IncompleteReplay => None,
                _ => unreachable!("evidence lower uses replay or incomplete provenance"),
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
            if let Some(replay) = projection_replay
                && !self.admit_projection_index(
                    Some((proof::ProjectionTarget::Replay(replay), lower_record)),
                    &[],
                )
            {
                return;
            }
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
            let admission_disposition = if evidence_complete {
                proof::ReplayAdmissionDisposition::EvidenceOnly
            } else {
                proof::ReplayAdmissionDisposition::Incomplete
            };
            self.proof_store.record_replay_admission(
                None,
                action.derivation,
                admission_disposition,
            );
            if evidence_complete && lower_edge_inserted {
                self.proof_store
                    .record_replay_evidence(lower_record, action.derivation);
            }
            if evidence_complete && upper_edge_inserted {
                self.proof_store
                    .record_replay_evidence(upper_record, action.derivation);
            }
            if evidence_complete {
                for parent in action.claim_parents {
                    let producer = self
                        .proof_store
                        .upper_claim(parent.claim)
                        .expect("replay-evidence parents must reference admitted CPK claims")
                        .producer;
                    let Some(registration) = self.admit_derived_upper_replay_claim(
                        upper_record,
                        parent.claim,
                        producer,
                        |depth| UpperReplayClaimLineage::ReplayEvidence {
                            parent_claim: parent.claim,
                            parent_side: parent.parent_side,
                            replay: action.derivation,
                            depth,
                        },
                    ) else {
                        return;
                    };
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

    fn apply_cpk_prefiltered_replay_provenance(
        &mut self,
        duplicates: BoundReplayActions,
        trivial: BoundReplayActions,
    ) {
        for action in duplicates {
            let result = *self
                .canonical_constraints
                .get(&action.constraint)
                .expect("prefiltered replay duplicate remains canonical");
            let disposition = self.merge_replay_derivation(result, action.derivation);
            if disposition != ReplayDerivationInsert::Incomplete {
                self.register_cpk_replay_claim_parents(
                    result,
                    action.derivation,
                    &action.claim_parents,
                    true,
                );
            }
            let admission_disposition = match disposition {
                ReplayDerivationInsert::Inserted => {
                    proof::ReplayAdmissionDisposition::CanonicalDuplicate
                }
                ReplayDerivationInsert::Duplicate => {
                    proof::ReplayAdmissionDisposition::ExactDuplicate
                }
                ReplayDerivationInsert::Incomplete => proof::ReplayAdmissionDisposition::Incomplete,
            };
            self.proof_store.record_replay_admission(
                Some(result),
                action.derivation,
                admission_disposition,
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
            let admission_disposition = match disposition {
                ReplayDerivationInsert::Inserted => proof::ReplayAdmissionDisposition::Trivial,
                ReplayDerivationInsert::Duplicate => {
                    proof::ReplayAdmissionDisposition::ExactDuplicate
                }
                ReplayDerivationInsert::Incomplete => proof::ReplayAdmissionDisposition::Incomplete,
            };
            self.proof_store.record_replay_admission(
                None,
                action.derivation,
                admission_disposition,
            );
            if disposition == ReplayDerivationInsert::Inserted {
                let id = self.replay_drop_index[&drop];
                self.proof_store.record_replay_drop(id, drop.clone());
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
        self.apply_cpk_prefiltered_replay_provenance(
            replay.duplicate_actions,
            replay.trivial_actions,
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
    ) -> usize {
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
        let duplicate_count = replay.duplicate_actions.len();
        self.apply_cpk_prefiltered_replay_provenance(
            replay.duplicate_actions,
            replay.trivial_actions,
        );
        duplicate_count
    }

    #[cfg(test)]
    pub(in crate::constraints) fn apply_cpk_replay_parent_arrival_without_materialization_for_test(
        &mut self,
        result: ConstraintRecordId,
        derivation: BinaryReplayDerivation,
        claim: UpperReplayClaimId,
    ) {
        let parent = ClaimQualifiedParent::ReplayConstraint {
            parent_claim: claim,
            parent_side: ReplayClaimParentSide::Lower,
            replay: derivation,
        };
        let mut transaction = self
            .try_prepare_replay_qualified_parent_transaction(result, derivation, &[parent])
            .expect("QORF test replay parent transaction must prepare");
        let (accepted, snapshot) = self.begin_replay_qualified_parent_transaction(&mut transaction);
        for entry in accepted.iter().copied() {
            self.commit_claim_qualified_parent_mutation(result, entry);
        }
        if !accepted.is_empty() {
            self.publish_claim_qualified_parent_admission(snapshot);
        }
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

    #[test]
    fn cpk_no_claim_workload_does_not_allocate_qualified_parent_index() {
        let mut machine = ConstraintMachine::new();
        let target = TypeVar(0);
        let lower = machine.alloc_pos(Pos::Con(vec!["plain".into()], Vec::new()));
        machine.add_lower_bound(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        );

        assert!(machine.proof_store.upper_claims_for_test().is_empty());
        assert_eq!(
            machine.proof_store.qualified_parent_storage_census(),
            (0, 0, 0, 0, 0, 0),
            "an ordinary no-claim bound must not allocate the CPK exact-parent indexes"
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

        let direct = machine.original_upper_replay_claim(
            direct_record,
            direct_producer,
            UpperReplayClaimKind::Direct,
        );
        let direct_again = machine.original_upper_replay_claim(
            direct_record,
            direct_producer,
            UpperReplayClaimKind::Direct,
        );
        let reduced = machine.original_upper_replay_claim(
            reduced_record,
            reduced_producer,
            UpperReplayClaimKind::Reduced(UnweightedRowReductionRecordId(50_000)),
        );
        assert_eq!(direct.claim, direct_again.claim);
        machine.move_upper_replay_claim(direct.claim, moved_record);
        assert!(
            machine
                .proof_store
                .claims_for_upper_record_for_test(direct_record)
                .is_empty(),
            "the non-collision move removes the root from its old record"
        );
        assert_eq!(
            machine
                .proof_store
                .claims_for_upper_record_for_test(moved_record),
            &[direct.claim],
            "the non-collision move keeps the existing single-entry behavior"
        );
        assert_eq!(
            machine
                .proof_store
                .original_claim(moved_record, direct_producer),
            Some(direct.claim)
        );
        assert!(
            machine
                .proof_store
                .derived_claim(moved_record, direct.claim)
                .is_none()
        );

        let originals = machine
            .proof_store
            .upper_claims_for_test()
            .iter()
            .filter(|claim| claim.full_lineage == proof::UpperClaimLineage::Original)
            .collect::<Vec<_>>();
        assert_eq!(originals.len(), 2);
        assert_eq!(
            machine
                .proof_store
                .upper_claims_for_test()
                .iter()
                .filter(|claim| claim.full_lineage == proof::UpperClaimLineage::Original)
                .count(),
            originals.len(),
            "the lazy mirror contains exactly one entry per Original claim"
        );
        for claim in originals {
            assert_eq!(claim.coverage_root, claim.claim);
            assert_eq!(
                machine.proof_store.root_claim_for_producer(claim.producer),
                Some(claim.claim),
                "each producer maps injectively to its own Original claim"
            );
        }
        assert_eq!(
            machine.proof_store.root_claim_for_producer(direct_producer),
            Some(direct.claim),
            "moving an Original claim's current record does not change producer identity"
        );
        assert_eq!(
            machine
                .proof_store
                .root_claim_for_producer(reduced_producer),
            Some(reduced.claim),
            "Reduced roots pass through the same shared constructor mirror"
        );
    }

    #[test]
    fn canonical_upper_claim_insertion_census_and_read_subsequences_are_root_ordered() {
        use crate::constraints::{
            canonical_upper_claim_insertion_census, reset_canonical_upper_claim_insertion_census,
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
            machine.derived_upper_replay_claim(
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
                .map(|claim| {
                    machine
                        .proof_store
                        .claim_coverage_root(claim)
                        .expect("CPK claim root")
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            claim_roots(
                &machine,
                machine
                    .proof_store
                    .claims_for_upper_record_for_test(target)
                    .to_vec(),
            ),
            roots
        );
        let mut record_lengths = machine
            .proof_store
            .upper_claim_record_entries_for_test()
            .map(|(_, claims)| claims.len())
            .collect::<Vec<_>>();
        record_lengths.sort_unstable();
        assert_eq!(record_lengths, vec![1, 1, 1, 1, 1, 1, 1, 1, 8]);
        let percentile = |percentile: usize| {
            record_lengths[(record_lengths.len() * percentile).div_ceil(100) - 1]
        };
        assert_eq!(
            (
                *record_lengths.last().unwrap(),
                percentile(95),
                percentile(99)
            ),
            (8, 8, 8)
        );
        assert_eq!(canonical_upper_claim_insertion_census(), (16, 4));

        for (index, root) in roots.iter().copied().enumerate().skip(5) {
            machine.insert_scheme_projection_live_coverage_state(
                root,
                UnweightedRowReductionRecordId(72_000 + index as u32),
            );
        }
        let target_claims = machine.proof_store.claims_for_upper_record_for_test(target);
        assert_eq!(
            claim_roots(
                &machine,
                target_claims
                    .iter()
                    .copied()
                    .filter(|claim| {
                        let root = machine
                            .proof_store
                            .claim_coverage_root(*claim)
                            .expect("CPK claim root");
                        machine
                            .proof_store
                            .live_coverage_states_for_test(root)
                            .is_none_or(FxHashSet::is_empty)
                    })
                    .collect()
            ),
            roots[..5]
        );
        assert_eq!(
            claim_roots(
                &machine,
                target_claims
                    .iter()
                    .copied()
                    .filter(|claim| {
                        let root = machine
                            .proof_store
                            .claim_coverage_root(*claim)
                            .expect("CPK claim root");
                        machine
                            .proof_store
                            .live_coverage_states_for_test(root)
                            .is_some_and(|states| !states.is_empty())
                    })
                    .collect()
            ),
            roots[5..]
        );
        let lower = machine.alloc_pos(Pos::Var(TypeVar(73)));
        let replay_parent_roots = machine
            .proof_store
            .prepared_upper_replay_parents_for_test(
                target,
                matches!(machine.types.pos(lower), Pos::Var(_)),
            )
            .expect("CPK prepared upper-parent assertion")
            .iter()
            .map(|parent| parent.coverage_root)
            .collect::<Vec<_>>();
        assert_eq!(replay_parent_roots, roots);
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

        assert!(machine.proof_store.upper_claims_for_test().is_empty());
        assert_eq!(
            machine
                .proof_store
                .projection_clause_storage_census_for_test(),
            (0, 0, 0, 0),
        );
        assert!(machine.proof_store.dependency_entries().next().is_none());
    }

    #[test]
    fn dpn_b_cycle_guard_self_cycle_is_not_a_proof() {
        let mut machine = ConstraintMachine::new();
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
        let mut canonical_baseline = None;
        for standalone_first in [false, true] {
            let mut machine = ConstraintMachine::new();
            let (source, cycle_support) = dpn_b_synthetic_projection_record(&mut machine, 3);
            let (dependent, dependent_support) = dpn_b_synthetic_projection_record(&mut machine, 7);
            let standalone_carrier = ProjectionProofCarrier::Incomplete;
            let standalone_support = SchemeProjectionProofSupport::Independent(standalone_carrier);
            let mutation = machine
                .try_prepare_scheme_projection_mutation(
                    source,
                    &[],
                    &[ProjectionProofCarrier::Incomplete],
                )
                .expect("test projection support mutation must have capacity");
            machine.apply_scheme_projection_mutation(mutation);
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
            let epochs_before = (machine.epoch, machine.provenance_epoch);
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

            let (projectable, _) = machine.scheme_projection_cycle_guard_snapshot(source);
            assert!(
                projectable,
                "the independent OR arm remains a complete proof"
            );
            assert!(
                machine.scheme_projection_cycle_guard_snapshot(dependent).0,
                "a dependent route reaches the independent source through the cycle"
            );

            for roots in [[source, dependent], [dependent, source]] {
                let fresh = roots.map(|record| {
                    proof::CpkProjectionEvaluator::new(&machine, &machine.proof_store)
                        .eval_record(record)
                });
                let mut shared = CpkPublicationEvaluationRound::new(&machine);
                let shared_results = roots.map(|record| shared.eval_record(record));
                assert_eq!(shared_results, fresh, "fresh/shared CPK decisions");
                if shared.sharing_disabled {
                    assert!(
                        roots.into_iter().any(|record| {
                            let mut evaluator =
                                proof::CpkProjectionEvaluator::new(&machine, &machine.proof_store);
                            evaluator.eval_record(record);
                            evaluator.cycle_cuts() != 0
                        }),
                        "sharing is disabled only after an observed cycle cut"
                    );
                }
            }

            let snapshot = (
                machine
                    .proof_store
                    .projection_formula_for_test(source)
                    .expect("mixed source has a projection formula")
                    .to_vec(),
                projectable,
                (
                    machine.epoch.as_u64() - epochs_before.0.as_u64(),
                    machine.provenance_epoch.as_u64() - epochs_before.1.as_u64(),
                ),
            );
            if let Some(baseline) = &canonical_baseline {
                assert_eq!(
                    &snapshot, baseline,
                    "CPK formula, decision, and publication epochs ignore admission order"
                );
            } else {
                canonical_baseline = Some(snapshot);
            }
        }
    }

    #[test]
    fn dpn_b_cycle_guard_mixed_record_constraint_cycle_is_not_a_proof() {
        let mut machine = ConstraintMachine::new();
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
        machine.admit_projection_target_for_test(
            proof::ProjectionTarget::Constraint(constraint),
            record,
        );
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
    fn exact_clause_link_duplicate_preflight_keeps_new_support_distinct() {
        let mut machine = ConstraintMachine::new();
        let (record, support) = dpn_b_synthetic_projection_record(&mut machine, 30);
        let clause = RecordProofClause::DerivedUnary {
            carrier: dpn_b_synthetic_unary_carrier(30),
            premise: ProofPremise::Record(record),
        };

        assert!(
            !machine
                .proof_store
                .projection_clause_link_is_registered(record, support, clause)
        );
        machine.register_record_proof_clause_link(
            record,
            RecordProofClauseLinkAdmission::independent(support, clause),
        );
        assert_eq!(
            machine.proof_store.projection_clauses_for_test(record),
            vec![clause]
        );
        assert!(
            machine
                .proof_store
                .projection_clause_link_is_registered(record, support, clause)
        );

        let other_support =
            SchemeProjectionProofSupport::Independent(ProjectionProofCarrier::ConstraintOrigin {
                constraint: ConstraintRecordId(10_031),
                origin: OriginId::unknown_internal(),
            });
        assert!(
            !machine.proof_store.projection_clause_link_is_registered(
                record,
                other_support,
                clause
            ),
            "an existing clause with a new support is a new attribution, not a duplicate"
        );
        machine.register_record_proof_clause_link(
            record,
            RecordProofClauseLinkAdmission::independent(other_support, clause),
        );
        assert_eq!(
            machine.proof_store.projection_clauses_for_test(record),
            vec![clause]
        );
        assert!(machine.proof_store.projection_clause_link_is_registered(
            record,
            other_support,
            clause
        ));
        assert_eq!(
            machine
                .proof_store
                .projection_clause_links_for_test(record)
                .len(),
            2,
        );
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
        let proof = SchemeProjectionProof {
            lower_record: record,
            support: SchemeProjectionProofSupport::Independent(carrier),
        };
        machine
            .proof_store
            .record_projection_supports(record, &[proof]);
        (record, SchemeProjectionProofSupport::Independent(carrier))
    }

    fn dpn_b_register_synthetic_clause(
        machine: &mut ConstraintMachine,
        record: BoundRecordId,
        support: SchemeProjectionProofSupport,
        clause: RecordProofClause,
    ) {
        let clauses_before = machine
            .proof_store
            .projection_clauses_for_test(record)
            .len();
        machine.register_record_proof_clause_link(
            record,
            RecordProofClauseLinkAdmission::independent(support, clause),
        );
        assert_eq!(
            machine
                .proof_store
                .projection_clauses_for_test(record)
                .len(),
            clauses_before + 1
        );
    }

    fn dpn_b_synthetic_unary_carrier(ordinal: u32) -> DerivedUnaryCarrier {
        DerivedUnaryCarrier::Structural(StructuralDerivation {
            parent: ConstraintRecordId(20_000 + ordinal),
            rule: StructuralDerivationRule::FunctionReturn,
        })
    }

    #[cfg(debug_assertions)]
    #[test]
    fn cpk_0b_captures_canonical_logical_proof_surfaces_end_to_end() {
        let mut fixture = cpk_mirrored_cdm_replay_claim_fixture();
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        assert_eq!(
            fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                fixture.result,
                replay,
                fixture.parent.claim,
            ),
            1,
            "the fixture must exercise canonical-duplicate replay admission",
        );
        let mutation = fixture
            .machine
            .try_prepare_scheme_projection_mutation(
                fixture.lower_record,
                &[],
                &[ProjectionProofCarrier::Origin(OriginId::unknown_internal())],
            )
            .expect("test projection support mutation must have capacity");
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
        assert!(
            snapshot
                .claim_relation
                .windows(2)
                .all(|pair| pair[0] <= pair[1])
        );
        assert!(!snapshot.projection.is_empty());
        assert!(
            snapshot
                .projection
                .iter()
                .any(|entry| !entry.supports.is_empty() && !entry.clauses.is_empty())
        );
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

        assert_eq!(
            fixture.machine.logical_proof_snapshot(),
            snapshot,
            "the CPK-only logical snapshot is stable across repeated construction",
        );
    }

    #[test]
    fn cpk_0c_fixture_matrix_captures_semantic_and_logical_baselines() {
        let mut fixture = with_semantic_execution_snapshot_capture_for_new_machines(|| {
            cpk_mirrored_cdm_replay_claim_fixture()
        });
        let replay = fixture.replay(ReplayRule::LowerBoundAdded);
        let apply_replay = |fixture: &mut CdmReplayClaimFixture| {
            fixture.machine.apply_cpk_replay_parent_arrival_for_test(
                fixture.result,
                replay,
                fixture.parent.claim,
            )
        };
        assert_eq!(apply_replay(&mut fixture), 1);

        let logical_before_noop = fixture.machine.logical_proof_snapshot();
        assert_eq!(apply_replay(&mut fixture), 1);
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
    struct CdmReplayClaimFixture {
        machine: ConstraintMachine,
        result: ConstraintRecordId,
        lower_record: BoundRecordId,
        upper_record: BoundRecordId,
        parent: SideTaggedReplayClaim,
        pivot: TypeVar,
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

    fn cpk_mirrored_cdm_replay_claim_fixture() -> CdmReplayClaimFixture {
        build_cdm_replay_claim_fixture(ConstraintMachine::new())
    }

    fn build_cdm_replay_claim_fixture(mut machine: ConstraintMachine) -> CdmReplayClaimFixture {
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
        let registration = machine.original_upper_replay_claim(
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
            parent: SideTaggedReplayClaim {
                claim: coverage_root,
                parent_side: ReplayClaimParentSide::Lower,
            },
            pivot: source,
        }
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

        fn admit_inert_fixture_constraint(
            machine: &mut ConstraintMachine,
            lower: PosId,
            upper: NegId,
        ) -> ConstraintRecordId {
            assert!(machine.enqueue_subtype(lower, ConstraintWeights::empty(), upper));
            let record = machine
                .constraint_record_id(lower, ConstraintWeights::empty(), upper)
                .expect("fixture constraint is canonical");
            assert!(machine.queue.pop_back().is_some(), "fixture removes only its pending work");
            record
        }

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
                let result = admit_inert_fixture_constraint(&mut machine, lower, upper);
                let producers = ["a", "b"].map(|suffix| {
                    let producer_lower = machine.alloc_pos(Pos::Con(
                        vec!["rcpf-d3b-producer".into(), suffix.into()], Vec::new(),
                    ));
                    let producer_upper = machine.alloc_neg(Neg::Con(
                        vec!["rcpf-d3b-result".into(), suffix.into()], Vec::new(),
                    ));
                    admit_inert_fixture_constraint(&mut machine, producer_lower, producer_upper)
                });
                let roots = producers.map(|producer| {
                    machine.add_upper_bound(
                        TypeVar(2), upper, ConstraintWeights::empty(),
                        BoundDerivation::Constraint(producer),
                    );
                    machine.proof_store.upper_claims.iter()
                        .find(|claim| {
                            claim.producer == producer
                                && claim.lineage == proof::ProjectionLineage::Original
                        })
                        .expect("CPK producer root")
                        .claim
                });
                let parent_record = machine.proof_store.upper_claim(roots[0])
                    .expect("CPK replay parent claim").current_record;
                machine.add_lower_bound(
                    target, lower, ConstraintWeights::empty(), BoundDerivation::Constraint(result),
                );
                let lower_record = machine.proof_store
                    .projection_lower_record_for_constraint(result)
                    .expect("CPK projection target");
                assert!(machine
                    .proof_store
                    .projection_supports_for_record(lower_record)
                    .is_empty());
                assert!(machine
                    .proof_store
                    .projection_formula_for_record(lower_record)
                    .is_empty());
                let source_origins = (0..independent_count).map(|index| machine.alloc_source_boundary(
                    if index % 2 == 0 { ConstraintOriginKind::Field } else { ConstraintOriginKind::Return },
                )).collect::<Vec<_>>();
                let origins = source_origins.iter().map(|source| source.origin()).collect();
                let boundaries = source_origins.iter().map(|source| source.boundary()).collect();
                let row = machine.intern_row_derivation(
                    RowDerivationRule::UnweightedReduction,
                    vec![RowDerivationParent::Constraint(producers[1])],
                    Vec::new(),
                );
                Self {
                    machine, result, lower_record, source, target, upper,
                    replay: BinaryReplayDerivation {
                        pivot: target, lower: lower_record, upper: parent_record,
                        rule: ReplayRule::LowerBoundAdded,
                    },
                    row, roots, origins, boundaries,
                }
            }

            fn add_claimed_source_origins(
                &mut self,
                kinds: [ConstraintOriginKind; 2],
            ) -> [SourceBoundaryId; 2] {
                let sources = kinds.map(|kind| self.machine.alloc_source_boundary(kind));
                for (producer, source) in [ConstraintRecordId(1), ConstraintRecordId(2)]
                    .into_iter().zip(sources)
                {
                    assert!(self.machine.attach_root_origin_to_existing_subtype(
                        self.machine.constraint_records[producer.0 as usize].key.lower,
                        self.machine.constraint_records[producer.0 as usize].key.upper,
                        source.origin(),
                    ));
                }
                sources.map(|source| source.boundary())
            }

            fn admit(&mut self, event: Event) {
                match event {
                    Event::Replay => {
                        assert_eq!(self.machine.merge_replay_derivation(self.result, self.replay), ReplayDerivationInsert::Inserted);
                        assert_eq!(
                            self.machine.apply_cpk_replay_parent_arrival_for_test(
                                self.result,
                                self.replay,
                                self.roots[0],
                            ),
                            1,
                        );
                    }
                    Event::NonReplay => {
                        let key = self.machine.constraint_records[self.result.0 as usize]
                            .key
                            .clone();
                        assert!(!self.machine.enqueue_row_derived_subtype(
                            key.lower,
                            key.weights,
                            key.upper,
                            self.row,
                        ));
                        self.machine.register_reduction_route_claim_parent(self.result, self.row, self.roots[1]);
                    }
                    Event::Independent(index) => self.machine.add_lower_bound(
                        self.target, self.machine.constraint_records[self.result.0 as usize].key.lower,
                        ConstraintWeights::empty(), BoundDerivation::Origin(self.origins[index]),
                    ),
                }
            }

            fn root(&self, claim: UpperReplayClaimId) -> UpperReplayClaimId {
                self.machine.proof_store.upper_claim(claim)
                    .expect("CPK claim")
                    .coverage_root
            }

            fn snapshot(&self) -> (Vec<UpperReplayClaimId>, Vec<SchemeProjectionProofSupport>, Vec<Key>) {
                let supports = self.machine.proof_store
                    .projection_supports_for_record(self.lower_record).to_vec();
                let claims = supports.iter().filter_map(|support| match support {
                    SchemeProjectionProofSupport::Claimed(claim) => Some(*claim),
                    SchemeProjectionProofSupport::Independent(_) => None,
                }).collect::<Vec<_>>();
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

            fn assert_cpk_projection_is_canonical(&self) {
                let (_, _, keys) = self.snapshot();
                assert_eq!(keys, canonical_projection_key::normalize_clone(&keys));
            }

            fn consumer_snapshot(&self) -> ConsumerSnapshot {
                let entry = self.machine.scheme_projectable_lowers(self.target)
                    .find(|entry| entry.record == self.lower_record)
                    .expect("isolated lower remains projectable");
                let qualified = entry.reason.clone();
                let projection_evidence = entry
                    .projection_evidence
                    .expect("qualified lower retains its projection evidence");
                let (drafts, completeness) = self.capture_witnesses();
                let parents = drafts.iter().flat_map(|draft| &draft.incoming)
                    .flat_map(|edge| &edge.parents).cloned().collect();
                ConsumerSnapshot {
                    qualified,
                    projection_evidence,
                    drafts,
                    parents,
                    completeness,
                }
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

            fn claimed_constraint_roots(&self) -> Vec<PortableProvenanceExportRoot> {
                self.roots
                    .iter()
                    .map(|claim| {
                        PortableProvenanceExportRoot::Constraint(
                            self.machine
                                .proof_store
                                .upper_claim(*claim)
                                .expect("RCPF fixture claim")
                                .producer,
                        )
                    })
                    .collect()
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
            fn new() -> Self {
                Self::from_machine(ConstraintMachine::new())
            }

            fn from_machine(mut machine: ConstraintMachine) -> Self {
                let source = TypeVar(0);
                let target = TypeVar(1);
                let pivot = TypeVar(2);
                let lower = machine.alloc_pos(Pos::Var(source));
                let upper = machine.alloc_neg(Neg::Var(target));
                let result = admit_inert_fixture_constraint(&mut machine, lower, upper);
                let producers = ["a", "b"].map(|suffix| {
                    let producer_lower = machine.alloc_pos(Pos::Con(
                        vec!["target-late-producer".into(), suffix.into()], Vec::new(),
                    ));
                    let producer_upper = machine.alloc_neg(Neg::Con(
                        vec!["target-late-result".into(), suffix.into()], Vec::new(),
                    ));
                    admit_inert_fixture_constraint(&mut machine, producer_lower, producer_upper)
                });
                let sources = [ConstraintOriginKind::Annotation, ConstraintOriginKind::Pattern]
                    .map(|kind| machine.alloc_source_boundary(kind));
                for (producer, source) in producers.into_iter().zip(sources) {
                    let key = machine.constraint_records[producer.0 as usize].key.clone();
                    assert!(machine.attach_root_origin_to_existing_subtype(
                        key.lower, key.upper, source.origin(),
                    ));
                }
                let roots = producers.map(|producer| {
                    machine.add_upper_bound(
                        pivot, upper, ConstraintWeights::empty(),
                        BoundDerivation::Constraint(producer),
                    );
                    machine.proof_store.upper_claims.iter()
                        .find(|claim| {
                            claim.producer == producer
                                && claim.lineage == proof::ProjectionLineage::Original
                        })
                        .expect("CPK target-late producer root")
                        .claim
                });
                let parent_upper = machine.proof_store.upper_claim(roots[0])
                    .expect("CPK target-late parent claim").current_record;
                let rows = producers.map(|producer| machine.intern_row_derivation(
                    RowDerivationRule::UnweightedReduction,
                    vec![RowDerivationParent::Constraint(producer)],
                    Vec::new(),
                ));
                let replay_lower = machine.bounds.add_lower(
                    pivot, lower, ConstraintWeights::empty(), BoundDerivation::Origin(OriginId::unknown_internal()),
                ).id;
                Self {
                    machine, result, source, target, lower, upper,
                    replay: BinaryReplayDerivation {
                        pivot, lower: replay_lower, upper: parent_upper, rule: ReplayRule::LowerBoundAdded,
                    },
                    roots, rows,
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
                self.machine
                    .apply_cpk_replay_parent_arrival_without_materialization_for_test(
                        self.result,
                        self.replay,
                        self.roots[0],
                    );
            }

            fn admit_non_replay(&mut self, index: usize) {
                let row = self.rows[index];
                let key = self.machine.constraint_records[self.result.0 as usize]
                    .key
                    .clone();
                assert!(!self.machine.enqueue_row_derived_subtype(
                    key.lower,
                    key.weights,
                    key.upper,
                    row,
                ));
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
                let supports = self.machine.proof_store
                    .projection_supports_for_record(lower_record);
                let lower_claimed_roots = supports.iter().filter_map(|support| match support {
                    SchemeProjectionProofSupport::Claimed(claim) => Some(
                        self.machine.proof_store.upper_claim(*claim)
                            .expect("CPK target-late claim")
                            .coverage_root,
                    ),
                    SchemeProjectionProofSupport::Independent(_) => None,
                }).collect::<Vec<_>>();
                let lower_proof_keys = supports.iter().map(|support| match support {
                    SchemeProjectionProofSupport::Claimed(claim) => Key::Claimed(
                        self.machine.proof_store.upper_claim(*claim)
                            .expect("CPK target-late claim")
                            .coverage_root,
                    ),
                    SchemeProjectionProofSupport::Independent(carrier) =>
                        Key::Independent(*carrier),
                }).collect::<Vec<_>>();
                let upper_replay_parents = self.machine.proof_store
                    .prepared_upper_replay_parents_for_test(
                        upper_record,
                        matches!(self.machine.types.pos(self.lower), Pos::Var(_)),
                    )
                    .expect("CPK target-late prepared upper parents")
                    .iter()
                    .map(|parent| SideTaggedReplayClaim {
                        claim: parent.representative_claim,
                        parent_side: parent.side,
                    })
                    .collect::<ReplayClaimParents>();
                let replay_parent_roots = upper_replay_parents.iter().map(|parent| {
                    self.machine.proof_store.upper_claim(parent.claim)
                        .expect("CPK target-late replay parent")
                        .coverage_root
                }).collect::<Vec<_>>();
                let lower_replay_parents =
                    self.machine.lower_record_replay_claim_parents(lower_record);
                let entry = self.machine.scheme_projectable_lowers(self.target)
                    .find(|entry| entry.record == lower_record)
                    .expect("target-late lower remains projectable");
                let qualified = entry.reason.clone();
                let projection_evidence = entry
                    .projection_evidence
                    .expect("target-late qualified lower retains projection evidence");
                let generalized = GeneralizedCompactRoot {
                    compact: CompactRoot::default(), role_predicates: Vec::new(), quantifiers: Vec::new(),
                    stack_quantifiers: Vec::new(), substitutions: Vec::new(), sandwiches: Vec::new(),
                };
                let (drafts, completeness) = capture_generalized_witnesses(
                    &self.machine, self.target, &generalized,
                );
                let parents = drafts.iter().flat_map(|draft| &draft.incoming)
                    .flat_map(|edge| &edge.parents).cloned().collect::<Vec<_>>();
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
                        let Some(carriers) = self.machine.generalization_parent_carriers(parent) else {
                            continue;
                        };
                        let candidates = match carriers {
                            GeneralizationParentCarriers::Constraint(id) =>
                                vec![PortableProvenanceExportRoot::Constraint(id)],
                            GeneralizationParentCarriers::Bound(id) =>
                                vec![PortableProvenanceExportRoot::Bound(id)],
                            GeneralizationParentCarriers::ClaimedProjection { bound, proof } =>
                                vec![PortableProvenanceExportRoot::ClaimedProjection {
                                    bound,
                                    proof,
                                }],
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
                    target_claims: self.machine.proof_store
                        .claims_for_upper_record_for_test(upper_record).to_vec(),
                    upper_replay_parents,
                    lower_replay_parents,
                    lower_claims: self.machine.proof_store
                        .projection_claims_for_record(lower_record).to_vec(),
                    lower_proofs: self.machine.proof_store
                        .projection_supports_for_record(lower_record).iter().copied()
                        .map(|support| SchemeProjectionProof { lower_record, support })
                        .collect(),
                    claim_arena: self.machine.proof_store.upper_claims_for_test().to_vec(),
                    final_epoch: self.epoch_checkpoint(),
                };
                TargetLateMaterialized {
                    roots: self.roots,
                    consumer: TargetLateConsumerSnapshot {
                        lower_record,
                        replay_parent_roots,
                        lower_claimed_roots,
                        lower_proof_keys,
                        generalized: ConsumerSnapshot {
                            qualified,
                            projection_evidence,
                            drafts,
                            parents,
                            completeness,
                        },
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
            claim_arena: Vec<proof::UpperClaimOccurrence>,
            final_epoch: TargetLateEpochCheckpoint,
        }

        struct TargetLateMaterialized {
            roots: [UpperReplayClaimId; 2],
            consumer: TargetLateConsumerSnapshot,
            publication: TargetLatePublicationSnapshot,
        }

        fn run_target_late_cpk(
            replay_wins_same_root: bool,
            root_a_before_root_b: bool,
        ) -> (Vec<TargetLateEpochCheckpoint>, TargetLateMaterialized) {
            let mut fixture = TargetLateFixture::new();
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
            let winner = fixture.machine.proof_store
                .first_qualified_parent_source(fixture.result, fixture.roots[0]);
            assert_eq!(
                matches!(winner, Some(proof::FirstQualifiedParentSource::Replay)),
                replay_wins_same_root,
            );
            let materialized = fixture.materialize();
            epochs.push(materialized.publication.final_epoch);
            (epochs, materialized)
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct ConsumerSnapshot {
            qualified: SchemeProjectableLowerReason,
            projection_evidence: proof::ProjectionEvidence,
            drafts: Vec<GeneralizedWitnessDraft>,
            parents: Vec<GeneralizationParent>,
            completeness: ProvenanceCompleteness,
        }

        #[derive(Debug, Clone, PartialEq, Eq)]
        struct PortableConsumerSnapshot {
            export: PortableProvenanceExport,
            explanation: DiagnosticSubtypeExplanation,
        }

        fn qualified_parents(
            reason: &SchemeProjectableLowerReason,
            evidence: proof::ProjectionEvidence,
            bound: BoundRecordId,
        ) -> Vec<GeneralizationParent> {
            let SchemeProjectableLowerReason::Qualified { uncovered_claims, independent_supports } = reason else {
                panic!("canonical projection fixture must remain qualified")
            };
            let mut parents = match evidence {
                proof::ProjectionEvidence::DecisiveClaimedArm(proof) => {
                    vec![GeneralizationParent::BoundClaimProjectionProof {
                        bound,
                        coverage_root: proof.coverage_root(),
                        representative_claim: proof.representative_claim(),
                        proof: Box::new(proof),
                    }]
                }
                proof::ProjectionEvidence::ExactWithoutClaimedArm
                | proof::ProjectionEvidence::FailOpenIncomplete => Vec::new(),
            };
            parents.extend(independent_supports.iter().map(|carrier| {
                GeneralizationParent::BoundProjectionProof {
                    bound,
                    carrier: *carrier,
                }
            }));
            debug_assert!(
                !uncovered_claims.is_empty() || !parents.is_empty(),
                "the RCPF fixture keeps either a qualified claim or an independent parent",
            );
            parents
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
                    max_anchors: 1, max_nodes_per_anchor: 1, ..full
                }, PortableProvenanceTruncation::NodeBudget { limit: 1 }, [true, false]),
                ("per-anchor edges", PortableProvenanceExportBudget {
                    max_anchors: 1, max_edges_per_anchor: 0, ..full
                }, PortableProvenanceTruncation::EdgeBudget { limit: 0 }, [true, false]),
                ("global nodes", PortableProvenanceExportBudget { max_nodes: 2, ..full },
                    PortableProvenanceTruncation::NodeBudget { limit: 2 }, [true, false]),
                ("global edges", PortableProvenanceExportBudget { max_edges: 1, ..full },
                    PortableProvenanceTruncation::EdgeBudget { limit: 1 }, [true, true]),
                ("parent fan-in", PortableProvenanceExportBudget { max_parents_per_edge: 0, ..full },
                    PortableProvenanceTruncation::ParentFanInBudget { limit: 0 }, [true, true]),
            ]
        }

        fn explanation_budget_ladder() -> Vec<(
            &'static str, PortableExplanationBudget, DiagnosticExplanationTruncationReason,
        )> {
            let full = PortableExplanationBudget::default();
            vec![
                ("query nodes", PortableExplanationBudget { max_nodes: 2, ..full },
                    DiagnosticExplanationTruncationReason::NodeBudget { limit: 2 }),
                ("query edges", PortableExplanationBudget { max_edges: 1, ..full },
                    DiagnosticExplanationTruncationReason::EdgeBudget { limit: 1 }),
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
                    let (_, materialized) =
                        run_target_late_cpk(replay_wins_same_root, root_a_before_root_b);
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
                    let decisive = lower_draft(&snapshot.generalized).incoming.iter()
                        .flat_map(|edge| &edge.parents).cloned().collect::<Vec<_>>();
                    let [GeneralizationParent::BoundClaimProjectionProof {
                        bound,
                        coverage_root,
                        representative_claim,
                        proof,
                    }] = decisive.as_slice() else {
                        panic!("target-late lower must retain one decisive claimed certificate")
                    };
                    assert_eq!(*bound, snapshot.lower_record);
                    assert!(roots.contains(coverage_root));
                    assert_eq!(proof.bound(), *bound);
                    assert_eq!(proof.coverage_root(), *coverage_root);
                    assert_eq!(proof.representative_claim(), *representative_claim);
                    assert_eq!(snapshot.generalized.parents.len(), 2,
                        "the root lower and recursive-lower drafts retain the same decisive parent");
                    assert!(snapshot.generalized.parents.chunks(1)
                        .all(|parents| parents == decisive));
                    assert_eq!(snapshot.generalized.completeness, ProvenanceCompleteness::Incomplete);
                    assert!(snapshot.generalized.drafts.iter()
                        .all(|draft| draft.completeness == ProvenanceCompleteness::Complete));
                    assert_eq!(snapshot.occurrence_roots.len(), snapshot.occurrence_anchors.len());
                    assert_eq!(snapshot.portable.export.root_anchors.len(),
                        snapshot.occurrence_roots.iter().map(Vec::len).sum::<usize>());
                    let occurrence_pair = [PortableProvenanceExportRoot::ClaimedProjection {
                        bound: *bound,
                        proof: **proof,
                    }];
                    assert!(snapshot.occurrence_roots.iter()
                        .all(|occurrence| occurrence.as_slice() == occurrence_pair));
                    assert!(snapshot.occurrence_anchors.iter().all(|anchors| {
                        anchors.len() == 1 && anchors.iter().all(Option::is_some)
                    }));
                    assert_eq!(snapshot.portable.export.snapshot.completeness(), PortableCompleteness::Complete);
                    assert_eq!(snapshot.portable.export.snapshot.truncation(), None);
                    assert_eq!(snapshot.portable.export.snapshot.source_sites().len(), 1);
                    let lower_roles = snapshot.portable.explanation.lower_sites.iter()
                        .map(|cause| cause.role).collect::<Vec<_>>();
                    assert!(matches!(lower_roles.as_slice(),
                        [DiagnosticTypeCauseRole::RequiredByAnnotation]
                        | [DiagnosticTypeCauseRole::RequiredByPattern]));
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
                    assert_eq!(snapshot.duplicate_causes.len(), 1);
                    assert_eq!(snapshot.duplicate_causes.iter()
                        .map(|cause| cause.role).collect::<Vec<_>>(), lower_roles);
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
                fixture.assert_cpk_projection_is_canonical();
                let snapshot = fixture.consumer_snapshot();
                let parents = qualified_parents(
                    &snapshot.qualified,
                    snapshot.projection_evidence,
                    fixture.lower_record,
                );
                assert_eq!(
                    snapshot.projection_evidence,
                    proof::ProjectionEvidence::ExactWithoutClaimedArm,
                    "the canonical Standalone independent clause is this fixture's decisive arm",
                );
                assert_eq!(parents, vec![
                    GeneralizationParent::BoundProjectionProof { bound: fixture.lower_record,
                        carrier: ProjectionProofCarrier::Origin(fixture.origins[0]) },
                    GeneralizationParent::BoundProjectionProof { bound: fixture.lower_record,
                        carrier: ProjectionProofCarrier::Origin(fixture.origins[1]) },
                ]);
                assert_eq!(lower_draft(&snapshot).incoming.iter().flat_map(|edge| &edge.parents)
                    .cloned().collect::<Vec<_>>(), parents);
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
                    let keys = fixture.machine.proof_store
                        .projection_supports_for_record(fixture.lower_record)
                        .iter().copied().map(|support| fixture.key(support)).collect::<Vec<_>>();
                    assert_eq!(keys, canonical_projection_key::normalize_clone(&keys));
                }
                let supports = fixture.machine.proof_store
                    .projection_supports_for_record(fixture.lower_record);
                claim_lengths.push(supports.iter().filter(|support| {
                    matches!(support, SchemeProjectionProofSupport::Claimed(_))
                }).count());
                proof_lengths.push(supports.len());
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
                fixture.assert_cpk_projection_is_canonical();
                let snapshot = fixture.consumer_snapshot();
                let parents = qualified_parents(
                    &snapshot.qualified,
                    snapshot.projection_evidence,
                    fixture.lower_record,
                );
                assert_eq!(
                    snapshot.projection_evidence,
                    proof::ProjectionEvidence::ExactWithoutClaimedArm,
                    "the canonical Standalone independent clause is this fixture's decisive arm",
                );
                let draft = lower_draft(&snapshot);
                assert_eq!(parents.len(), 258);
                assert_eq!(draft.incoming.len(), 256);
                assert_eq!(draft.completeness, ProvenanceCompleteness::Incomplete);
                assert_eq!(snapshot.completeness, ProvenanceCompleteness::Incomplete);
                let prefix = draft.incoming.iter().flat_map(|edge| &edge.parents).cloned().collect::<Vec<_>>();
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
                fixture.assert_cpk_projection_is_canonical();
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
                fixture.assert_cpk_projection_is_canonical();
                // rev.2 intentionally transports only the decisive projection arm. This fixture's
                // decisive Standalone arm is independent, so include the claimed producer roots
                // explicitly: this oracle is about portable diagnostic ordering across source
                // roles, not about reintroducing non-decisive claims as witness parents.
                let mut roots = fixture.claimed_constraint_roots();
                roots.extend(fixture.record_witness_roots());
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
                fixture.assert_cpk_projection_is_canonical();
                let roots = fixture.record_witness_roots();
                let full = fixture.portable_consumer_snapshot(&roots, PortableProvenanceExportBudget::default());
                assert!(full.export.snapshot.nodes().len() > 3);
                assert!(full.export.snapshot.edges().len() > 1);
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
                fixture.assert_cpk_projection_is_canonical();
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
