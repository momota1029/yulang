use super::*;

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
        let insertion = self
            .bounds
            .add_lower(target, pos, weights.clone(), derivation.clone());
        self.record_bound_provenance(insertion, BoundDirection::Lower, false);
        self.record_bound_disposition(
            BoundDirection::Lower,
            target,
            BoundEndpoint::Lower(pos),
            weights.clone(),
            Some(derivation),
            if insertion.semantic_changed {
                BoundDisposition::Inserted(insertion.id)
            } else {
                BoundDisposition::EquivalentTo(insertion.id)
            },
            None,
        );
        if insertion.provenance_changed {
            self.register_lower_projection_proofs(insertion.id, producer);
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
        self.apply_prefiltered_replay_provenance(replay.duplicate_actions, replay.trivial_actions);
        let apply = self.apply_bound_replay_actions(replay.actions);
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
        let record = &mut self.bounds.records[id.0 as usize];
        let considered = derivations.len();
        let mut inserted = 0usize;
        for derivation in derivations {
            let derivation = BoundDerivation::SchemeInstantiation(derivation);
            if !record.derivations.contains(&derivation) {
                record.derivations.push(derivation);
                inserted += 1;
            }
        }
        let coverage = &mut self.timing.scheme_instantiations;
        coverage.edges_considered += considered;
        coverage.edges_inserted += inserted;
        coverage.edges_deduplicated += considered.saturating_sub(inserted);
        coverage.max_incoming_edges_per_record = coverage.max_incoming_edges_per_record.max(
            record
                .derivations
                .iter()
                .filter(|edge| matches!(edge, BoundDerivation::SchemeInstantiation(_)))
                .count(),
        );
        if inserted != 0 {
            self.bump_provenance_epoch();
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
        self.apply_prefiltered_replay_provenance(replay.duplicate_actions, replay.trivial_actions);
        let apply = self.apply_bound_replay_actions(replay.actions);
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
            .bounds
            .claim_parents_by_constraint
            .get(&producer)
            .cloned()
            .unwrap_or_default();
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
            let registration = match parent {
                ClaimQualifiedParent::ReplayConstraint {
                    parent_side,
                    replay,
                    ..
                } => self.bounds.derived_upper_replay_claim(
                    record,
                    parent_claim,
                    producer,
                    |depth| UpperReplayClaimLineage::ReplayConstraint {
                        parent_claim,
                        parent_side,
                        result: producer,
                        replay,
                        depth,
                    },
                ),
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
            self.apply_scheme_projection_mutation(registration.scheme_projection_mutation);
            let claim = registration.claim;
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
        claims
    }

    pub(in crate::constraints) fn register_existing_constraint_lower_projection_proofs(
        &mut self,
        producer: ConstraintRecordId,
    ) {
        let Some(record) = self.lower_record_for_constraint(producer) else {
            return;
        };
        self.register_lower_projection_proofs(record, Some(producer));
    }

    fn lower_record_for_constraint(&self, producer: ConstraintRecordId) -> Option<BoundRecordId> {
        if let Some(record) = self
            .bounds
            .scheme_projection_lower_record_by_constraint
            .get(&producer)
            .copied()
        {
            return Some(record);
        }
        let constraint = &self.constraint_records[producer.0 as usize].key;
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

    fn register_lower_projection_proofs(
        &mut self,
        lower_record: BoundRecordId,
        producer: Option<ConstraintRecordId>,
    ) {
        let claim_parents = producer
            .and_then(|producer| {
                self.bounds
                    .claim_parents_by_constraint
                    .get(&producer)
                    .cloned()
            })
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
            self.independent_projection_supports(lower_record, producer, &claim_parents);
        let mutation = self.bounds.update_scheme_projection_proofs(
            lower_record,
            &claims,
            &independent_supports,
        );
        self.apply_scheme_projection_mutation(mutation);
    }

    fn independent_projection_supports(
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
                    supports.extend(
                        constraint
                            .scheme_instantiation_derivations
                            .iter()
                            .cloned()
                            .map(|derivation| {
                                ProjectionProofCarrier::SchemeInstantiationConstraint {
                                    result: *producer,
                                    source_witness: derivation.source_witness,
                                }
                            }),
                    );
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

    fn register_replay_claim_parents(
        &mut self,
        result: ConstraintRecordId,
        replay: BinaryReplayDerivation,
        parents: &[SideTaggedReplayClaim],
        materialize_existing_target: bool,
    ) {
        if parents.is_empty()
            || !self.constraint_records[result.0 as usize]
                .replay_derivations
                .contains(&replay)
        {
            return;
        }
        let target_record = self.var_var_upper_record_for_constraint(result);
        let mut inserted = false;
        for parent in parents {
            let coverage_root =
                self.bounds.upper_replay_claims[parent.claim.0 as usize].coverage_root;
            let key = ReplayClaimParentKey {
                result,
                coverage_root,
                parent_side: parent.parent_side,
            };
            if !self.bounds.replay_claim_parent_keys.insert(key) {
                continue;
            }
            let parent = ClaimQualifiedParent::ReplayConstraint {
                parent_claim: parent.claim,
                parent_side: parent.parent_side,
                replay,
            };
            let entries = self
                .bounds
                .claim_parents_by_constraint
                .entry(result)
                .or_default();
            entries.push(parent);
            inserted = true;
        }
        // Newly enqueued constraints consume this metadata during their bound admission.
        // Queue-suppressed duplicates need the eager path because no later admission will run.
        if inserted && materialize_existing_target {
            if let Some(record) = target_record {
                self.register_constraint_upper_replay_claims(record, Some(result));
            }
            self.register_existing_constraint_lower_projection_proofs(result);
        }
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
        let entries = self
            .bounds
            .claim_parents_by_constraint
            .entry(result)
            .or_default();
        if entries.contains(&parent) {
            return;
        }
        entries.push(parent);
        if let Some(record) = self.var_var_upper_record_for_constraint(result) {
            self.register_constraint_upper_replay_claims(record, Some(result));
        }
        self.register_existing_constraint_lower_projection_proofs(result);
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
        if !self.constraint_records[record.0 as usize]
            .row_derivations
            .contains(&derivation)
        {
            self.constraint_records[record.0 as usize]
                .row_derivations
                .push(derivation);
            self.bump_provenance_epoch();
        }
        if let Some(parent_claim) = parent_claim {
            self.register_reduction_route_claim_parent(record, derivation, parent_claim);
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
        let attempted = SubtypeConstraintKey {
            lower,
            upper,
            weights: weights.clone(),
        };
        let duplicate_profile = self.replay_duplicate_profile(lower, &weights, upper);
        let canonicalization_disposition =
            self.terminal_weight_erasure_disposition(lower, &weights, upper);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
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

    fn apply_bound_replay_actions(&mut self, actions: BoundReplayActions) -> BoundReplayApplyStats {
        let mut stats = BoundReplayApplyStats::default();
        for action in actions {
            let constraint = action.constraint.clone();
            let (enqueued, disposition) =
                self.enqueue_replay_subtype(action.constraint, action.derivation);
            if disposition != ReplayDerivationInsert::Incomplete {
                let result = self.canonical_constraints[&constraint];
                self.register_replay_claim_parents(
                    result,
                    action.derivation,
                    &action.claim_parents,
                    !enqueued,
                );
            }
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
                stats.accepted += 1;
            } else {
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
                }
            }
            self.timing.record_replay_derivation_edge(
                evidence_complete && (lower_edge_inserted || upper_edge_inserted),
                evidence_complete && !(lower_edge_inserted || upper_edge_inserted),
                !evidence_complete,
                false,
            );
        }
    }

    fn apply_prefiltered_replay_provenance(
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
                self.register_replay_claim_parents(
                    result,
                    action.derivation,
                    &action.claim_parents,
                    true,
                );
            }
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
            let disposition = self.intern_replay_drop(ReplayDropRecord {
                attempted: action.constraint,
                derivation: action.derivation,
            });
            self.timing.record_replay_derivation_edge(
                disposition == ReplayDerivationInsert::Inserted,
                disposition == ReplayDerivationInsert::Duplicate,
                disposition == ReplayDerivationInsert::Incomplete,
                false,
            );
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
