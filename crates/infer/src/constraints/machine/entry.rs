use super::*;

use crate::time::Instant;

impl ConstraintMachine {
    pub fn new() -> Self {
        Self::new_with_read_authorities(
            ReplayReadAuthority::Factored,
            proof::ProofReadAuthority::Cpk,
        )
    }

    pub(crate) fn new_with_replay_read_authority(
        replay_read_authority: ReplayReadAuthority,
    ) -> Self {
        Self::new_with_read_authorities(
            replay_read_authority,
            proof::ProofReadAuthority::Cpk,
        )
    }

    pub(crate) fn new_with_read_authorities(
        replay_read_authority: ReplayReadAuthority,
        proof_read_authority: proof::ProofReadAuthority,
    ) -> Self {
        ensure_replay_soak_telemetry_header();
        #[cfg(test)]
        let replay_result_summary = {
            let mut summary = ReplayResultSummary::default();
            if replay_read_authority.writes_factored_shadow() {
                summary.enable_evaluator_oracle();
            }
            summary
        };
        #[cfg(not(test))]
        let replay_result_summary = ReplayResultSummary::default();
        Self {
            types: TypeArena::new(),
            queue: VecDeque::new(),
            bounds: TypeBounds::new(),
            replay_parent_sets: ParentSetArena::new(),
            replay_occurrences: ReplayOccurrenceStore::default(),
            replay_result_summary,
            replay_clause_projection: ReplayClauseProjection::default(),
            non_replay_claim_parents_by_constraint: NonReplayClaimParentStore::default(),
            proof_store: proof::ProofOccurrenceStore::default(),
            proof_read_authority,
            proof_terminal_failure: RefCell::new(None),
            #[cfg(test)]
            cpk_proof_oracle_active: false,
            replay_read_authority,
            replay_factored_shadow_status: Cell::new(ReplayFactoredShadowStatus::Active),
            var_adjacency: FxHashMap::default(),
            subtracts: SubtractTable::new(),
            levels: TypeLevels::new(),
            next_internal_type_var: 0,
            row_residuals: FxHashMap::default(),
            row_residual_record_ids: FxHashMap::default(),
            row_residual_records: Vec::new(),
            unweighted_row_reductions_by_source: FxHashMap::default(),
            unweighted_row_reduction_owners_by_upper: FxHashMap::default(),
            unweighted_row_reduction_records: Vec::new(),
            row_derivations: Vec::new(),
            row_derivation_index: FxHashMap::default(),
            bound_dispositions: Vec::new(),
            declared_subtracts: FxHashMap::default(),
            effect_family_paths: FxHashSet::default(),
            row_tail_vars: FxHashSet::default(),
            pre_pop_effect_families: FxHashMap::default(),
            lower_filters: FxHashMap::default(),
            lower_filter_record_ids: FxHashMap::default(),
            lower_filter_records: Vec::new(),
            effect_filter_violations: FxHashSet::default(),
            canonical_constraints: FxHashMap::default(),
            constraint_records: Vec::new(),
            replay_drop_records: Vec::new(),
            replay_drop_index: FxHashMap::default(),
            replay_derivation_budget: ReplayDerivationBudget::default(),
            replay_derivation_storage: ReplayDerivationStorage::default(),
            origins: vec![
                OriginRecord {
                    kind: ConstraintOriginKind::Internal,
                    source_boundary: None,
                },
                OriginRecord {
                    kind: ConstraintOriginKind::UnknownInternal,
                    source_boundary: None,
                },
            ],
            source_boundaries: Vec::new(),
            generalized_schemes: Vec::new(),
            generalized_witnesses: Vec::new(),
            scheme_instantiations: Vec::new(),
            scheme_instantiation_index: FxHashMap::default(),
            events: Vec::new(),
            method_role_mutations: MethodRoleMutationOutbox::new(),
            timing: ConstraintTiming::default(),
            epoch: ConstraintEpoch::default(),
            provenance_epoch: ProvenanceEpoch::default(),
            role_solve_supplemental_epoch: RoleSolveSupplementalEpoch::default(),
            replay_frontier_shadow: ReplayFrontierShadow::from_env(),
            replay_routing_shadow: ReplayRoutingShadow::from_env().map(RefCell::new),
            #[cfg(test)]
            cdm_lower_delta_census: CdmLowerDeltaCensus::default(),
            #[cfg(test)]
            semantic_execution_trace:
                semantic_execution_snapshot::trace_cell_for_new_constraint_machine(),
        }
    }

    pub(crate) fn replay_read_authority(&self) -> ReplayReadAuthority {
        self.replay_read_authority
    }

    pub(crate) fn proof_read_authority(&self) -> &proof::ProofReadAuthority {
        &self.proof_read_authority
    }

    pub(crate) fn proof_terminal_failure(&self) -> Option<proof::ProofFailure> {
        self.proof_terminal_failure.borrow().clone()
    }

    pub(in crate::constraints) fn mark_proof_terminal_failure(
        &self,
        operation: proof::ProofOperation,
        failure: proof::ProofFailure,
    ) {
        let mut terminal = self.proof_terminal_failure.borrow_mut();
        if terminal.is_none() {
            record_proof_terminal_failure(operation, &failure);
            *terminal = Some(failure);
        }
    }

    pub(crate) fn replay_factored_terminal_failure(&self) -> Option<ReplayFactoredShadowFailure> {
        match self.replay_factored_shadow_status.get() {
            ReplayFactoredShadowStatus::Active => None,
            ReplayFactoredShadowStatus::Failed(failure) => Some(failure),
        }
    }

    pub(in crate::constraints) fn mark_replay_factored_failure(
        &self,
        failure: ReplayFactoredShadowFailure,
        operation: ReplayFactoredFailureOperation,
    ) {
        let first_terminal_failure = matches!(
            self.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        );
        record_replay_factored_failure(failure, operation, first_terminal_failure);
        if first_terminal_failure {
            self.replay_factored_shadow_status
                .set(ReplayFactoredShadowStatus::Failed(failure));
        }
    }

    #[cfg(test)]
    pub(crate) fn inject_replay_factored_read_failure_for_test(
        &self,
        failure: ReplayFactoredShadowFailure,
    ) {
        self.mark_replay_factored_failure(failure, ReplayFactoredFailureOperation::Read);
    }

    pub(in crate::constraints) fn replay_factored_writes_enabled(&self) -> bool {
        #[cfg(test)]
        if !self.replay_read_authority.writes_factored_shadow() {
            return false;
        }
        matches!(
            self.replay_factored_shadow_status.get(),
            ReplayFactoredShadowStatus::Active
        )
    }

    pub fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.observe_pos(&pos);
        self.types.alloc_pos(pos)
    }

    pub fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.observe_neg(&neg);
        self.types.alloc_neg(neg)
    }

    pub fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.observe_neu(&neu);
        self.types.alloc_neu(neu)
    }

    pub fn types(&self) -> &TypeArena {
        &self.types
    }

    pub fn bounds(&self) -> &TypeBounds {
        &self.bounds
    }

    #[allow(dead_code)] // Debug inspection now; consumed by same-session instantiation in PUSP-D.
    pub(crate) fn generalized_scheme_record(
        &self,
        id: GeneralizedSchemeRecordId,
    ) -> Option<&GeneralizedSchemeRecord> {
        self.generalized_schemes.get(id.0 as usize)
    }

    pub(crate) fn generalized_scheme_records_iter(
        &self,
    ) -> impl Iterator<Item = (GeneralizedSchemeRecordId, &GeneralizedSchemeRecord)> {
        self.generalized_schemes
            .iter()
            .enumerate()
            .map(|(index, record)| (GeneralizedSchemeRecordId(index as u32), record))
    }

    pub(crate) fn generalized_scheme_witness(
        &self,
        id: GeneralizedSchemeWitnessId,
    ) -> Option<&GeneralizedSchemeWitness> {
        self.generalized_witnesses.get(id.0 as usize)
    }

    #[allow(dead_code)] // Debug inspection surface; PUSP-E consumes this record directly.
    pub(crate) fn scheme_instantiation_record(
        &self,
        id: SchemeInstantiationId,
    ) -> Option<&SchemeInstantiationRecord> {
        self.scheme_instantiations.get(id.0 as usize)
    }

    pub(crate) fn intern_scheme_instantiation(
        &mut self,
        source: GeneralizedSchemeRecordId,
        owner: DefId,
        target: DefId,
        use_value: TypeVar,
        completeness: ProvenanceCompleteness,
    ) -> SchemeInstantiationId {
        let key = SchemeInstantiationKey {
            source,
            owner,
            target,
            use_value,
        };
        if let Some(id) = self.scheme_instantiation_index.get(&key).copied() {
            return id;
        }
        let id = SchemeInstantiationId(
            u32::try_from(self.scheme_instantiations.len())
                .expect("scheme instantiation id fits u32"),
        );
        self.scheme_instantiation_index.insert(key, id);
        self.scheme_instantiations.push(SchemeInstantiationRecord {
            source,
            owner,
            target,
            use_value,
            completeness,
        });
        self.proof_store.record_scheme_instantiation_record(
            id,
            self.scheme_instantiations[id.0 as usize].clone(),
        );
        self.timing.scheme_instantiations.records += 1;
        self.bump_provenance_epoch();
        id
    }

    pub(crate) fn record_scheme_instantiation_use(
        &mut self,
        local: bool,
        imported: bool,
        mapped_witnesses: usize,
    ) {
        let coverage = &mut self.timing.scheme_instantiations;
        if imported {
            coverage.imported_without_bridge += 1;
        } else if local {
            coverage.same_session_local += 1;
        } else {
            coverage.same_session_batch += 1;
        }
        coverage.max_mapped_witnesses_per_instantiation = coverage
            .max_mapped_witnesses_per_instantiation
            .max(mapped_witnesses);
    }

    pub(crate) fn alloc_generalized_scheme_record(
        &mut self,
        owner: DefId,
        generation: u32,
        drafts: Vec<GeneralizedWitnessDraft>,
        completeness: ProvenanceCompleteness,
    ) -> GeneralizedSchemeRecordId {
        let scheme = GeneralizedSchemeRecordId(
            u32::try_from(self.generalized_schemes.len()).expect("generalized scheme id fits u32"),
        );
        let mut witness_ids = Vec::with_capacity(drafts.len());
        for mut draft in drafts {
            let considered = draft
                .incoming
                .iter()
                .map(|edge| edge.parents.len())
                .sum::<usize>();
            let before = draft.incoming.len();
            let mut seen = FxHashSet::default();
            draft.incoming.retain(|edge| seen.insert(edge.clone()));
            let inserted = draft
                .incoming
                .iter()
                .map(|edge| edge.parents.len())
                .sum::<usize>();
            let id = GeneralizedSchemeWitnessId(
                u32::try_from(self.generalized_witnesses.len())
                    .expect("generalized witness id fits u32"),
            );
            let coverage = &mut self.timing.generalized_schemes;
            coverage.witnesses += 1;
            match draft.role {
                GeneralizedWitnessRole::ConstraintRelation => coverage.constraint_relations += 1,
                GeneralizedWitnessRole::LowerBound => coverage.lower_bounds += 1,
                GeneralizedWitnessRole::UpperBound => coverage.upper_bounds += 1,
                GeneralizedWitnessRole::RecursiveLowerBound => coverage.recursive_lower_bounds += 1,
                GeneralizedWitnessRole::RecursiveUpperBound => coverage.recursive_upper_bounds += 1,
            }
            if let Some(slot) = coverage.witnesses_by_depth.get_mut(draft.path.depth()) {
                *slot += 1;
            } else {
                coverage.witnesses_deeper_than_15 += 1;
            }
            coverage.incoming_edges_considered += considered;
            coverage.incoming_edges_inserted += inserted;
            coverage.incoming_edges_deduplicated += before.saturating_sub(draft.incoming.len());
            if draft.completeness == ProvenanceCompleteness::Incomplete {
                coverage.incomplete_witnesses += 1;
            }
            self.generalized_witnesses.push(GeneralizedSchemeWitness {
                scheme,
                path: draft.path,
                role: draft.role,
                incoming: draft.incoming,
                completeness: draft.completeness,
            });
            witness_ids.push(id);
        }
        self.generalized_schemes.push(GeneralizedSchemeRecord {
            owner,
            generation,
            witnesses: witness_ids,
            completeness,
        });
        self.timing.generalized_schemes.records += 1;
        scheme
    }

    pub(crate) fn var_neighbors(&self, var: TypeVar) -> impl Iterator<Item = TypeVar> + '_ {
        #[cfg(test)]
        crate::analysis::record_owner_neighbor_read(var);
        self.var_adjacency
            .get(&var)
            .into_iter()
            .flat_map(|neighbors| neighbors.keys().copied())
    }

    pub fn subtracts(&self) -> &SubtractTable {
        &self.subtracts
    }

    pub fn register_type_var(&mut self, var: TypeVar, level: TypeLevel) {
        if self.levels.register_recording_change(var, level) {
            self.bump_role_solve_supplemental_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations.record_many([
                    DependencyKey::ConstraintLevel(var),
                    DependencyKey::ConstraintBirthLevel(var),
                ]);
            }
        }
        self.next_internal_type_var = self.next_internal_type_var.max(var.0.saturating_add(1));
    }

    pub fn level_of(&self, var: TypeVar) -> TypeLevel {
        #[cfg(test)]
        crate::analysis::record_owner_level_read(var);
        self.levels.level_of(var)
    }

    pub fn birth_level_of(&self, var: TypeVar) -> TypeLevel {
        #[cfg(test)]
        crate::analysis::record_owner_birth_level_read(var);
        self.levels.birth_level_of(var)
    }

    pub fn next_type_var(&self) -> u32 {
        self.next_internal_type_var
    }

    pub fn events(&self) -> &[ConstraintEvent] {
        &self.events
    }

    pub fn replay_provenance_completeness(&self) -> ProvenanceCompleteness {
        self.replay_derivation_storage.completeness
    }

    pub fn constraint_replay_provenance(
        &self,
        record: ConstraintRecordId,
    ) -> Option<ProvenanceCompleteness> {
        self.constraint_records
            .get(record.0 as usize)
            .map(|record| record.replay_provenance)
    }

    #[cfg(test)]
    pub(crate) fn set_replay_derivation_budget_for_test(
        &mut self,
        max_bytes_proxy: usize,
        max_incoming_per_record: usize,
    ) {
        assert_eq!(self.replay_derivation_storage.bytes_proxy, 0);
        self.replay_derivation_budget = ReplayDerivationBudget {
            max_bytes_proxy,
            max_incoming_per_record,
        };
    }

    pub fn timing(&self) -> ConstraintTiming {
        let mut timing = self.timing;
        timing.epoch = self.epoch.as_u64();
        timing.provenance_epoch = self.provenance_epoch.as_u64();
        timing.canonical_subtype_constraints = self.canonical_constraint_count();
        timing.type_var_count = self.next_internal_type_var as usize;
        timing.row_tail_var_count = self.row_tail_vars.len();
        timing.pos_node_count = self.types.pos_len();
        timing.neg_node_count = self.types.neg_len();
        timing.neu_node_count = self.types.neu_len();
        timing.type_node_count = self.types.node_len();
        timing.replay_derivation_storage = ReplayDerivationStorageMetrics {
            bytes_proxy: self.replay_derivation_storage.bytes_proxy,
            max_incoming_per_record: self.replay_derivation_storage.max_incoming_per_record,
            incomplete_records: self.replay_derivation_storage.incomplete_records,
            session_incomplete: self.replay_derivation_storage.completeness
                == ProvenanceCompleteness::Incomplete,
        };
        if let Some(shadow) = &self.replay_frontier_shadow {
            timing.replay_frontier_shadow_lower_var_var = shadow.lower_var_var;
            timing.replay_frontier_shadow_upper_var_var = shadow.upper_var_var;
        }
        if let Some(shadow) = &self.replay_routing_shadow {
            let shadow = shadow.borrow();
            timing.replay_routing_shadow_var_var = shadow.metrics;
            if let Some(weighted) = &shadow.weighted {
                timing.replay_weighted_routing_shadow_var_var = weighted.metrics;
            }
        }
        timing
    }

    pub fn epoch(&self) -> ConstraintEpoch {
        self.epoch
    }

    pub fn provenance_epoch(&self) -> ProvenanceEpoch {
        self.provenance_epoch
    }

    pub fn role_solve_supplemental_epoch(&self) -> RoleSolveSupplementalEpoch {
        self.role_solve_supplemental_epoch
    }

    pub fn take_events(&mut self) -> Vec<ConstraintEvent> {
        #[cfg(test)]
        self.record_semantic_publication_events();
        std::mem::take(&mut self.events)
    }

    pub(crate) fn activate_method_role_mutations(&self) -> MethodRoleMutationActivation {
        self.method_role_mutations.activate()
    }

    pub(crate) fn method_role_mutation_generation(&self) -> MutationGeneration {
        self.method_role_mutations.generation()
    }

    pub(crate) fn method_role_mutation_emission_generation(&self) -> MutationGeneration {
        self.method_role_mutations.emission_generation()
    }

    pub(crate) fn set_method_role_mutation_subscriptions(
        &mut self,
        subscriptions: MethodRoleMutationSubscriptions,
    ) {
        self.method_role_mutations.set_subscriptions(subscriptions);
    }

    pub(crate) fn drain_method_role_mutations_into(
        &mut self,
        target: &mut MethodRoleMutationOutbox,
    ) -> bool {
        self.method_role_mutations.drain_into(target)
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutation_journal_active(&self) -> bool {
        self.method_role_mutations.is_active()
    }

    pub(crate) fn pending_constraint_work(&self) -> usize {
        self.queue.len()
    }

    pub fn alloc_source_boundary(&mut self, kind: ConstraintOriginKind) -> SourceBoundaryOrigin {
        assert!(
            kind.is_source(),
            "internal origins do not have source boundaries"
        );
        let boundary = SourceBoundaryId(self.source_boundaries.len() as u32);
        let origin = OriginId(self.origins.len() as u32);
        self.origins.push(OriginRecord {
            kind,
            source_boundary: Some(boundary),
        });
        self.source_boundaries.push(SourceBoundaryRecord {
            origin,
            location_recorded: false,
        });
        if let ConstraintOriginKind::BodyRequirement(kind) = kind {
            self.timing.record_body_requirement_origin(kind);
        }
        SourceBoundaryOrigin { boundary, origin }
    }

    pub fn record_source_boundary_location(&mut self, boundary: SourceBoundaryId) {
        let record = self
            .source_boundaries
            .get_mut(boundary.0 as usize)
            .expect("source-boundary location refers to an allocated boundary");
        assert!(
            !record.location_recorded,
            "each source boundary records location at most once"
        );
        let origin = &self.origins[record.origin.0 as usize];
        record.location_recorded = true;
        if matches!(origin.kind, ConstraintOriginKind::BodyRequirement(_)) {
            self.timing.record_body_requirement_location();
        }
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutations(&self) -> &[MethodRoleMutation] {
        self.method_role_mutations.mutations()
    }

    #[cfg(test)]
    pub(crate) fn method_role_owner_eligibility(&self) -> bool {
        self.method_role_mutations.owner_eligibility()
    }

    #[cfg(test)]
    pub(crate) fn take_method_role_mutations(&mut self) -> Vec<MethodRoleMutation> {
        self.method_role_mutations.take()
    }

    #[cfg(test)]
    pub(crate) fn invalidate_method_role_mutations_for_test(
        &mut self,
        reason: InvalidateAllReason,
    ) {
        self.method_role_mutations.invalidate_all(reason);
    }

    pub fn subtype(&mut self, lower: PosId, upper: NegId, origin: OriginId) {
        self.timing.record_subtype_call();
        if self.enqueue_root_subtype(lower, ConstraintWeights::empty(), upper, origin)
            || !self.queue.is_empty()
        {
            self.drain();
        }
    }

    /// Add an alternate root explanation to a semantic constraint that was already admitted.
    ///
    /// This is provenance-only: it neither records a second subtype admission nor enqueues work.
    pub(crate) fn attach_root_origin_to_existing_subtype(
        &mut self,
        lower: PosId,
        upper: NegId,
        origin: OriginId,
    ) -> bool {
        let Some(key) = self.canonical_subtype_constraint(lower, ConstraintWeights::empty(), upper)
        else {
            return false;
        };
        let Some(record) = self.canonical_constraints.get(&key).copied() else {
            return false;
        };
        self.record_root_origin(origin);
        let roots = &mut self.constraint_records[record.0 as usize].root_origins;
        if roots.contains(&origin) {
            return false;
        }
        roots.push(origin);
        self.proof_store.record_constraint_root(record, origin);
        self.register_constraint_projection_carrier_delta(
            record,
            &[],
            ProjectionProofCarrier::ConstraintOrigin {
                constraint: record,
                origin,
            },
        );
        self.bump_provenance_epoch();
        true
    }

    pub(crate) fn subtype_many(
        &mut self,
        constraints: impl IntoIterator<Item = (PosId, NegId)>,
        origin: OriginId,
    ) {
        self.subtype_many_with_origins(
            constraints
                .into_iter()
                .map(|(lower, upper)| (lower, upper, origin)),
        );
    }

    pub(crate) fn subtype_many_with_origins(
        &mut self,
        constraints: impl IntoIterator<Item = (PosId, NegId, OriginId)>,
    ) {
        let mut item_count = 0usize;
        let mut queued = false;
        for (lower, upper, origin) in constraints {
            item_count += 1;
            queued |= self.enqueue_root_subtype(lower, ConstraintWeights::empty(), upper, origin);
        }
        self.timing.record_subtype_many_call(item_count);
        if queued || !self.queue.is_empty() {
            self.drain();
        }
    }

    pub(crate) fn subtype_many_with_scheme_instantiation_routes(
        &mut self,
        constraints: impl IntoIterator<Item = (PosId, NegId, OriginId, Vec<SchemeInstantiationRoute>)>,
    ) {
        let mut item_count = 0usize;
        let mut queued = false;
        for (lower, upper, origin, routes) in constraints {
            item_count += 1;
            queued |= self.enqueue_root_subtype(lower, ConstraintWeights::empty(), upper, origin);
            if let Some(key) =
                self.canonical_subtype_constraint(lower, ConstraintWeights::empty(), upper)
                && let Some(record) = self.canonical_constraints.get(&key).copied()
            {
                self.merge_scheme_instantiation_routes(record, routes);
            }
        }
        self.timing.record_subtype_many_call(item_count);
        if queued || !self.queue.is_empty() {
            self.drain();
        }
    }

    pub fn weighted_subtype(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        origin: OriginId,
    ) {
        self.timing.record_weighted_subtype_call();
        if self.enqueue_root_subtype(lower, weights, upper, origin) || !self.queue.is_empty() {
            self.drain();
        }
    }

    pub(crate) fn derive_nominal_record_fields(
        &mut self,
        parent: ConstraintRecordId,
        fields: impl IntoIterator<Item = (usize, NegId, PosId, NegId)>,
    ) {
        let owner = self.constraint_records[parent.0 as usize].key.lower;
        let weights = self.constraint_records[parent.0 as usize]
            .key
            .weights
            .clone();
        let mut queued = false;
        for (index, projection_receiver, projection_result, required_field) in fields {
            let rule = StructuralDerivationRule::RecordField {
                index: StructuralIndex::from_usize(index),
            };
            queued |= self.enqueue_derived_subtype(
                owner,
                weights.clone(),
                projection_receiver,
                parent,
                rule,
            );
            queued |= self.enqueue_derived_subtype(
                projection_result,
                weights.clone(),
                required_field,
                parent,
                rule,
            );
        }
        if queued || !self.queue.is_empty() {
            self.drain();
        }
    }

    pub(crate) fn constrain_subtype(
        &mut self,
        lower: PosId,
        upper: NegId,
        origin: OriginId,
    ) -> bool {
        self.timing.record_constrain_subtype_call();
        let constraint_count = self.canonical_constraint_count();
        if self.enqueue_root_subtype(lower, ConstraintWeights::empty(), upper, origin)
            || !self.queue.is_empty()
        {
            self.drain();
        }
        self.canonical_constraint_count() != constraint_count
    }

    pub(crate) fn constrain_invariant_neu(
        &mut self,
        lower: NeuId,
        upper: NeuId,
        origin: OriginId,
    ) -> bool {
        self.constrain_invariant_neus([(lower, upper)], origin)
    }

    pub(crate) fn constrain_invariant_neus(
        &mut self,
        pairs: impl IntoIterator<Item = (NeuId, NeuId)>,
        origin: OriginId,
    ) -> bool {
        let constraint_count = self.canonical_constraint_count();
        for (lower, upper) in pairs {
            self.timing.record_constrain_invariant_neu_call();
            self.enqueue_root_invariant_neu(lower, upper, ConstraintWeights::empty(), origin);
        }
        if !self.queue.is_empty() {
            self.drain();
        }
        self.canonical_constraint_count() != constraint_count
    }

    pub(crate) fn constrain_var_var_pairs_direct(
        &mut self,
        pairs: impl IntoIterator<Item = (TypeVar, TypeVar)>,
        origin: OriginId,
    ) -> bool {
        let mut pair_count = 0usize;
        let constraint_count = self.canonical_constraint_count();
        let mut queued = false;
        for (lower, upper) in pairs {
            pair_count += 1;
            if lower == upper {
                continue;
            }
            let lower_pos = self.alloc_pos(Pos::Var(lower));
            let upper_neg = self.alloc_neg(Neg::Var(upper));
            queued |=
                self.enqueue_root_subtype(lower_pos, ConstraintWeights::empty(), upper_neg, origin);
        }
        self.timing.record_constrain_var_var_direct_call(pair_count);
        if queued || !self.queue.is_empty() {
            self.drain();
        }
        self.canonical_constraint_count() != constraint_count
    }

    #[allow(dead_code)] // Origin-only sibling retained for non-instantiation entrypoints.
    pub(crate) fn constrain_pos_to_var_direct_many(
        &mut self,
        bounds: impl IntoIterator<Item = (PosId, TypeVar)>,
        origin: OriginId,
    ) {
        self.constrain_pos_to_var_direct_many_with_origins(
            bounds
                .into_iter()
                .map(|(lower, target)| (lower, target, origin)),
        );
    }

    #[allow(dead_code)] // Origin-only sibling retained for non-instantiation entrypoints.
    pub(crate) fn constrain_pos_to_var_direct_many_with_origins(
        &mut self,
        bounds: impl IntoIterator<Item = (PosId, TypeVar, OriginId)>,
    ) {
        for (lower, target, origin) in bounds {
            self.record_root_origin(origin);
            self.timing.record_constrain_pos_var_direct_call();
            self.add_lower_bound(
                target,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            );
        }
        if !self.queue.is_empty() {
            self.drain();
        }
    }

    pub(crate) fn constrain_pos_to_var_direct_many_with_scheme_instantiations(
        &mut self,
        bounds: impl IntoIterator<Item = (PosId, TypeVar, OriginId, Vec<SchemeInstantiationDerivation>)>,
    ) {
        for (lower, target, origin, derivations) in bounds {
            self.record_root_origin(origin);
            self.timing.record_constrain_pos_var_direct_call();
            self.add_lower_bound(
                target,
                lower,
                ConstraintWeights::empty(),
                BoundDerivation::Origin(origin),
            );
            self.merge_scheme_instantiations_into_lower_bound(target, lower, derivations);
        }
        if !self.queue.is_empty() {
            self.drain();
        }
    }

    fn merge_scheme_instantiation_routes(
        &mut self,
        record: ConstraintRecordId,
        routes: Vec<SchemeInstantiationRoute>,
    ) {
        let considered = routes.len();
        let mut inserted_derivations = Vec::new();
        let mut inserted_routes = Vec::new();
        let (inserted, incoming) = {
            let mut inserted = 0usize;
            let target = &mut self.constraint_records[record.0 as usize];
            for route in routes {
                if route.remaining.0.is_empty() {
                    if !target
                        .scheme_instantiation_derivations
                        .contains(&route.derivation)
                    {
                        target
                            .scheme_instantiation_derivations
                            .push(route.derivation.clone());
                        inserted_derivations.push(route.derivation);
                        inserted += 1;
                    }
                } else if !target.scheme_instantiation_routes.contains(&route) {
                    inserted_routes.push(route.clone());
                    target.scheme_instantiation_routes.push(route);
                    inserted += 1;
                }
            }
            (
                inserted,
                target.scheme_instantiation_derivations.len()
                    + target.scheme_instantiation_routes.len(),
            )
        };
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
            self.proof_store
                .record_scheme_instantiation_derivation(record, derivation.clone());
            self.register_constraint_projection_carrier_delta(
                record,
                &[],
                ProjectionProofCarrier::SchemeInstantiationConstraint {
                    result: record,
                    source_witness: derivation.source_witness,
                },
            );
        }
        for route in &inserted_routes {
            self.proof_store
                .record_scheme_instantiation_route(record, route.clone());
        }
    }

    #[cfg(test)]
    pub(in crate::constraints) fn merge_scheme_instantiation_routes_for_test(
        &mut self,
        record: ConstraintRecordId,
        routes: Vec<SchemeInstantiationRoute>,
    ) {
        self.merge_scheme_instantiation_routes(record, routes);
    }

    fn structural_scheme_routes(
        &self,
        parent: ConstraintRecordId,
        rule: StructuralDerivationRule,
    ) -> Vec<SchemeInstantiationRoute> {
        self.constraint_records[parent.0 as usize]
            .scheme_instantiation_routes
            .iter()
            .filter_map(|route| {
                let advance = matches!(
                    (route.remaining.0.first(), rule),
                    (
                        Some(GeneralizedTypePathStep::FunctionArgument),
                        StructuralDerivationRule::FunctionArgument
                    )
                );
                let passthrough = matches!(
                    rule,
                    StructuralDerivationRule::LowerStackNormalization
                        | StructuralDerivationRule::LowerNonSubtractNormalization
                        | StructuralDerivationRule::UpperStackNormalization
                );
                (advance || passthrough).then(|| SchemeInstantiationRoute {
                    derivation: route.derivation.clone(),
                    remaining: if advance {
                        route.remaining.without_first()
                    } else {
                        route.remaining.clone()
                    },
                })
            })
            .collect()
    }

    pub(in crate::constraints) fn scheme_instantiation_derivations_for_constraint(
        &self,
        parent: ConstraintRecordId,
    ) -> Vec<SchemeInstantiationDerivation> {
        self.constraint_records[parent.0 as usize]
            .scheme_instantiation_routes
            .iter()
            .map(|route| route.derivation.clone())
            .chain(
                self.constraint_records[parent.0 as usize]
                    .scheme_instantiation_derivations
                    .iter()
                    .cloned(),
            )
            .collect()
    }

    pub fn subtract_fact(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    ) {
        self.timing.record_subtract_fact_call();
        self.observe_type_var(effect);
        let work = ConstraintWork::SubtractFact(QueuedSubtractFact {
            effect,
            fact: SubtractFact {
                id,
                subtractability,
            },
            derivation: SubtractFactDerivation::Internal(OriginId::unknown_internal()),
        });
        #[cfg(test)]
        self.record_semantic_queue_enqueue(&work);
        self.queue.push_back(work);
        self.drain();
    }

    /// 注釈・データ宣言が直接導入した subtract fact。scheme 量化はこの宣言由来 id
    /// だけを保持対象とし、instantiate の clone で再登録される fact（推論残差）は
    /// 量化境界で表示から消える。
    pub fn declared_subtract_fact(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    ) {
        self.declared_subtract_fact_with_origin(
            effect,
            id,
            subtractability,
            OriginId::unknown_internal(),
        );
    }

    pub fn declared_subtract_fact_with_origin(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
        origin: OriginId,
    ) {
        let origins = self.declared_subtracts.entry(id).or_default();
        let first_declaration = origins.is_empty();
        if !origins.contains(&origin) {
            origins.push(origin);
        }
        if first_declaration {
            self.bump_epoch();
        }
        self.timing.record_subtract_fact_call();
        self.observe_type_var(effect);
        let work = ConstraintWork::SubtractFact(QueuedSubtractFact {
            effect,
            fact: SubtractFact {
                id,
                subtractability,
            },
            derivation: SubtractFactDerivation::Declaration(origin),
        });
        #[cfg(test)]
        self.record_semantic_queue_enqueue(&work);
        self.queue.push_back(work);
        self.drain();
    }

    pub fn subtract_declared(&self, id: SubtractId) -> bool {
        self.declared_subtracts.contains_key(&id)
    }

    pub fn subtract_declaration_origins(&self, id: SubtractId) -> &[OriginId] {
        self.declared_subtracts
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn register_effect_family_path(&mut self, path: Vec<String>) {
        self.effect_family_paths.insert(path);
    }

    pub(crate) fn pre_pop_effect_families(&self, var: TypeVar) -> &[ConstraintEffectFamily] {
        #[cfg(test)]
        crate::analysis::record_owner_pre_pop_read(var);
        self.pre_pop_effect_families
            .get(&var)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn drain(&mut self) {
        let start = Instant::now();
        let initial_queue = self.queue.len();
        let mut work_items = 0usize;
        let mut subtype_work_items = 0usize;
        let mut subtract_work_items = 0usize;
        let mut trace = ConstraintDrainTrace::from_env(self);
        while self.replay_factored_terminal_failure().is_none()
            && self.proof_terminal_failure().is_none()
        {
            let Some(work) = self.queue.pop_front() else {
                break;
            };
            #[cfg(test)]
            self.record_semantic_queue_dequeue(&work);
            trace.work(&work, self);
            work_items += 1;
            match &work {
                ConstraintWork::Subtype(_) => subtype_work_items += 1,
                ConstraintWork::SubtractFact(_) => subtract_work_items += 1,
            }
            self.step(work);
        }
        trace.finish(self);
        self.timing.record_drain(
            start.elapsed(),
            initial_queue,
            work_items,
            subtype_work_items,
            subtract_work_items,
        );
    }

    pub(in crate::constraints) fn enqueue_subtype(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> bool {
        matches!(
            self.enqueue_subtype_classified(lower, weights, upper),
            EnqueueSubtypeResult::Enqueued
        )
    }

    pub(in crate::constraints) fn enqueue_root_subtype(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        origin: OriginId,
    ) -> bool {
        self.record_root_origin(origin);
        matches!(
            self.enqueue_subtype_classified_with_origin(lower, weights, upper, Some(origin)),
            EnqueueSubtypeResult::Enqueued
        )
    }

    fn enqueue_root_invariant_neu(
        &mut self,
        lower: NeuId,
        upper: NeuId,
        weights: ConstraintWeights,
        origin: OriginId,
    ) {
        let (lower_pos, lower_neg) = self.neu_bounds(lower);
        let (upper_pos, upper_neg) = self.neu_bounds(upper);
        self.enqueue_root_subtype(lower_pos, weights.clone(), upper_neg, origin);
        self.enqueue_root_subtype(upper_pos, weights.swapped(), lower_neg, origin);
    }

    pub(in crate::constraints) fn enqueue_subtype_classified(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> EnqueueSubtypeResult {
        self.enqueue_subtype_classified_with_origin(lower, weights, upper, None)
    }

    fn enqueue_subtype_classified_with_origin(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        origin: Option<OriginId>,
    ) -> EnqueueSubtypeResult {
        #[cfg(test)]
        let semantic_attempt = self.semantic_subtype_admission_attempt(
            lower,
            &weights,
            upper,
            None,
            semantic_execution_snapshot::SemanticAdmissionSource::Ordinary,
        );
        let disposition = self.terminal_weight_erasure_disposition(lower, &weights, upper);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            self.timing.record_subtype_trivial_admission();
            #[cfg(test)]
            self.record_semantic_subtype_admission(
                semantic_attempt,
                semantic_execution_snapshot::SemanticAdmissionOutcome::Trivial,
            );
            return EnqueueSubtypeResult::Trivial;
        };
        let enqueued = self.enqueue_canonical_subtype_with_origin(constraint.clone(), origin);
        self.merge_constraint_canonicalization_disposition(&constraint, disposition);
        #[cfg(test)]
        self.record_semantic_subtype_admission(
            semantic_attempt,
            if enqueued {
                semantic_execution_snapshot::SemanticAdmissionOutcome::Enqueued
            } else {
                semantic_execution_snapshot::SemanticAdmissionOutcome::CanonicalDuplicate
            },
        );
        if enqueued {
            EnqueueSubtypeResult::Enqueued
        } else {
            EnqueueSubtypeResult::Duplicate
        }
    }

    pub(in crate::constraints) fn canonical_subtype_constraint(
        &self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> Option<SubtypeConstraintKey> {
        if matches!(self.types.pos(lower), Pos::Bot) || matches!(self.types.neg(upper), Neg::Top) {
            return None;
        }
        if matches!(
            (self.types.pos(lower), self.types.neg(upper)),
            (Pos::Var(lower), Neg::Var(upper)) if lower == upper
        ) {
            return None;
        }
        let weights = self.terminal_subtype_weights(lower, upper, weights);
        let weights = if self.is_var_var_replay(lower, upper) {
            weights.normalize_for_var_var_replay_key()
        } else {
            weights
        };
        Some(SubtypeConstraintKey {
            lower,
            upper,
            weights,
        })
    }

    pub(in crate::constraints) fn terminal_weight_erasure_disposition(
        &self,
        lower: PosId,
        weights: &ConstraintWeights,
        upper: NegId,
    ) -> Option<ConstraintCanonicalizationDisposition> {
        (!weights.is_empty() && self.has_terminal_subtype_endpoint(lower, upper)).then(|| {
            ConstraintCanonicalizationDisposition::TerminalWeightErasure {
                attempted_weights: weights.clone(),
            }
        })
    }

    pub(in crate::constraints) fn merge_constraint_canonicalization_disposition(
        &mut self,
        constraint: &SubtypeConstraintKey,
        disposition: Option<ConstraintCanonicalizationDisposition>,
    ) {
        let Some(disposition) = disposition else {
            return;
        };
        let Some(record_id) = self.canonical_constraints.get(constraint).copied() else {
            return;
        };
        let dispositions =
            &mut self.constraint_records[record_id.0 as usize].canonicalization_dispositions;
        if !dispositions.contains(&disposition) {
            dispositions.push(disposition.clone());
            self.proof_store
                .record_constraint_disposition(record_id, disposition.clone());
            self.bump_provenance_epoch();
        }
    }

    pub(in crate::constraints) fn canonical_constraint_count(&self) -> usize {
        self.canonical_constraints.len()
    }

    pub(in crate::constraints) fn has_canonical_constraint(
        &self,
        constraint: &SubtypeConstraintKey,
    ) -> bool {
        self.canonical_constraints.contains_key(constraint)
    }

    pub(in crate::constraints) fn enqueue_replay_subtype(
        &mut self,
        constraint: SubtypeConstraintKey,
        derivation: BinaryReplayDerivation,
    ) -> (bool, ReplayDerivationInsert) {
        #[cfg(test)]
        let semantic_attempt = self.semantic_subtype_admission_attempt(
            constraint.lower,
            &constraint.weights,
            constraint.upper,
            None,
            semantic_execution_snapshot::SemanticAdmissionSource::Replay,
        );
        let record_id = match self.canonical_constraints.entry(constraint.clone()) {
            Entry::Occupied(entry) => {
                let record_id = *entry.get();
                let inserted = self.merge_replay_derivation(record_id, derivation);
                self.timing.record_subtype_duplicate_admission();
                #[cfg(test)]
                self.record_semantic_subtype_admission(
                    semantic_attempt,
                    match inserted {
                        ReplayDerivationInsert::Inserted => {
                            semantic_execution_snapshot::SemanticAdmissionOutcome::EvidenceOnly
                        }
                        ReplayDerivationInsert::Duplicate => {
                            semantic_execution_snapshot::SemanticAdmissionOutcome::CanonicalDuplicate
                        }
                        ReplayDerivationInsert::Incomplete => {
                            semantic_execution_snapshot::SemanticAdmissionOutcome::Rejected
                        }
                    },
                );
                return (false, inserted);
            }
            Entry::Vacant(entry) => {
                let record_id = ConstraintRecordId(self.constraint_records.len() as u32);
                entry.insert(record_id);
                record_id
            }
        };
        self.observe_routing_shadow(&constraint);
        let inserted = if self
            .replay_derivation_budget_allows(std::mem::size_of::<BinaryReplayDerivation>(), 1)
        {
            self.replay_derivation_storage.bytes_proxy +=
                std::mem::size_of::<BinaryReplayDerivation>();
            self.replay_derivation_storage.max_incoming_per_record = self
                .replay_derivation_storage
                .max_incoming_per_record
                .max(1);
            ReplayDerivationInsert::Inserted
        } else {
            self.record_replay_budget_drop(None);
            self.replay_derivation_storage.incomplete_records += 1;
            ReplayDerivationInsert::Incomplete
        };
        self.constraint_records.push(ConstraintRecord {
            key: constraint.clone(),
            root_origins: Vec::new(),
            structural_derivations: Vec::new(),
            row_derivations: Vec::new(),
            replay_derivations: if matches!(inserted, ReplayDerivationInsert::Inserted) {
                vec![derivation]
            } else {
                Vec::new()
            },
            scheme_instantiation_derivations: Vec::new(),
            scheme_instantiation_routes: Vec::new(),
            canonicalization_dispositions: Vec::new(),
            replay_provenance: if matches!(inserted, ReplayDerivationInsert::Inserted) {
                ProvenanceCompleteness::Complete
            } else {
                ProvenanceCompleteness::Incomplete
            },
        });
        self.bump_provenance_epoch();
        let work = ConstraintWork::Subtype(record_id);
        #[cfg(test)]
        self.record_semantic_queue_enqueue(&work);
        self.queue.push_back(work);
        #[cfg(test)]
        self.record_semantic_subtype_admission(
            semantic_attempt,
            if inserted == ReplayDerivationInsert::Incomplete {
                semantic_execution_snapshot::SemanticAdmissionOutcome::EnqueuedWithRejectedEvidence
            } else {
                semantic_execution_snapshot::SemanticAdmissionOutcome::Enqueued
            },
        );
        (true, inserted)
    }

    pub(in crate::constraints) fn merge_replay_derivation(
        &mut self,
        result: ConstraintRecordId,
        derivation: BinaryReplayDerivation,
    ) -> ReplayDerivationInsert {
        let record = &self.constraint_records[result.0 as usize];
        if record.replay_derivations.contains(&derivation) {
            return ReplayDerivationInsert::Duplicate;
        }
        let incoming = record.replay_derivations.len().saturating_add(1);
        if !self.replay_derivation_budget_allows(
            std::mem::size_of::<BinaryReplayDerivation>(),
            incoming,
        ) {
            self.record_replay_budget_drop(Some(result));
            return ReplayDerivationInsert::Incomplete;
        }
        self.replay_derivation_storage.bytes_proxy += std::mem::size_of::<BinaryReplayDerivation>();
        self.replay_derivation_storage.max_incoming_per_record = self
            .replay_derivation_storage
            .max_incoming_per_record
            .max(incoming);
        self.constraint_records[result.0 as usize]
            .replay_derivations
            .push(derivation);
        self.bump_provenance_epoch();
        ReplayDerivationInsert::Inserted
    }

    pub(in crate::constraints) fn intern_replay_drop(
        &mut self,
        record: ReplayDropRecord,
    ) -> ReplayDerivationInsert {
        if self.replay_drop_index.contains_key(&record) {
            return ReplayDerivationInsert::Duplicate;
        }
        let bytes =
            std::mem::size_of::<ReplayDropRecord>() * 2 + std::mem::size_of::<ReplayDropRecordId>();
        if !self.replay_derivation_session_budget_allows(bytes) {
            self.record_replay_budget_drop(None);
            return ReplayDerivationInsert::Incomplete;
        }
        self.replay_derivation_storage.bytes_proxy += bytes;
        let id = ReplayDropRecordId(self.replay_drop_records.len() as u32);
        self.replay_drop_index.insert(record.clone(), id);
        self.replay_drop_records.push(record);
        self.bump_provenance_epoch();
        ReplayDerivationInsert::Inserted
    }

    pub(in crate::constraints) fn replay_derivation_budget_allows(
        &self,
        bytes: usize,
        incoming_for_record: usize,
    ) -> bool {
        incoming_for_record <= self.replay_derivation_budget.max_incoming_per_record
            && self.replay_derivation_session_budget_allows(bytes)
    }

    pub(in crate::constraints) fn replay_derivation_session_budget_allows(
        &self,
        bytes: usize,
    ) -> bool {
        self.replay_derivation_storage
            .bytes_proxy
            .checked_add(bytes)
            .is_some_and(|total| total <= self.replay_derivation_budget.max_bytes_proxy)
    }

    pub(in crate::constraints) fn charge_replay_derivation_bytes(&mut self, bytes: usize) {
        self.replay_derivation_storage.bytes_proxy += bytes;
    }

    pub(in crate::constraints) fn record_replay_budget_drop(
        &mut self,
        record: Option<ConstraintRecordId>,
    ) {
        let mut changed = false;
        if self.replay_derivation_storage.completeness == ProvenanceCompleteness::Complete {
            self.replay_derivation_storage.completeness = ProvenanceCompleteness::Incomplete;
            changed = true;
        }
        if let Some(record) = record {
            let record = &mut self.constraint_records[record.0 as usize];
            if record.replay_provenance == ProvenanceCompleteness::Complete {
                record.replay_provenance = ProvenanceCompleteness::Incomplete;
                self.replay_derivation_storage.incomplete_records += 1;
                changed = true;
            }
        }
        if changed {
            self.bump_provenance_epoch();
        }
    }

    fn enqueue_canonical_subtype_with_origin(
        &mut self,
        constraint: SubtypeConstraintKey,
        origin: Option<OriginId>,
    ) -> bool {
        let record_id = match self.canonical_constraints.entry(constraint.clone()) {
            Entry::Occupied(entry) => {
                let existing_record_id = *entry.get();
                let mut inserted_origin = None;
                if let Some(origin) = origin {
                    // A second root explains the existing fact without replaying semantic work.
                    let roots =
                        &mut self.constraint_records[existing_record_id.0 as usize].root_origins;
                    if !roots.contains(&origin) {
                        roots.push(origin);
                        inserted_origin = Some(origin);
                    }
                }
                if let Some(origin) = inserted_origin {
                    self.proof_store
                        .record_constraint_root(existing_record_id, origin);
                    self.register_constraint_projection_carrier_delta(
                        existing_record_id,
                        &[],
                        ProjectionProofCarrier::ConstraintOrigin {
                            constraint: existing_record_id,
                            origin,
                        },
                    );
                    self.bump_provenance_epoch();
                }
                self.timing.record_subtype_duplicate_admission();
                return false;
            }
            Entry::Vacant(entry) => {
                let record_id = ConstraintRecordId(self.constraint_records.len() as u32);
                entry.insert(record_id);
                record_id
            }
        };
        self.observe_routing_shadow(&constraint);
        self.constraint_records.push(ConstraintRecord {
            key: constraint.clone(),
            root_origins: origin.into_iter().collect(),
            structural_derivations: Vec::new(),
            row_derivations: Vec::new(),
            replay_derivations: Vec::new(),
            scheme_instantiation_derivations: Vec::new(),
            scheme_instantiation_routes: Vec::new(),
            canonicalization_dispositions: Vec::new(),
            replay_provenance: ProvenanceCompleteness::Complete,
        });
        if let Some(origin) = origin {
            self.proof_store.record_constraint_root(record_id, origin);
        }
        if origin.is_some() {
            self.bump_provenance_epoch();
        }
        let work = ConstraintWork::Subtype(record_id);
        #[cfg(test)]
        self.record_semantic_queue_enqueue(&work);
        self.queue.push_back(work);
        true
    }

    pub(in crate::constraints) fn enqueue_derived_subtype(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        parent: ConstraintRecordId,
        rule: StructuralDerivationRule,
    ) -> bool {
        #[cfg(test)]
        let semantic_attempt = self.semantic_subtype_admission_attempt(
            lower,
            &weights,
            upper,
            Some(parent),
            semantic_execution_snapshot::SemanticAdmissionSource::Structural,
        );
        self.timing.record_structural_derivation(rule);
        let scheme_routes = self.structural_scheme_routes(parent, rule);
        let disposition = self.terminal_weight_erasure_disposition(lower, &weights, upper);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            self.timing.record_subtype_trivial_admission();
            #[cfg(test)]
            self.record_semantic_subtype_admission(
                semantic_attempt,
                semantic_execution_snapshot::SemanticAdmissionOutcome::Trivial,
            );
            return false;
        };
        let derivation = StructuralDerivation { parent, rule };
        let record_id = match self.canonical_constraints.entry(constraint.clone()) {
            Entry::Occupied(entry) => {
                let record_id = *entry.get();
                let mut derivation_inserted = false;
                let derivations =
                    &mut self.constraint_records[record_id.0 as usize].structural_derivations;
                if !derivations.contains(&derivation) {
                    derivations.push(derivation);
                    derivation_inserted = true;
                }
                if derivation_inserted {
                    self.proof_store.record_structural(record_id, derivation);
                }
                let parent_changed =
                    self.merge_structural_claim_parents(record_id, derivation, derivation_inserted);
                let provenance_changed = derivation_inserted || parent_changed;
                if provenance_changed {
                    self.bump_provenance_epoch();
                }
                self.merge_scheme_instantiation_routes(record_id, scheme_routes);
                self.merge_constraint_canonicalization_disposition(&constraint, disposition);
                self.timing.record_subtype_duplicate_admission();
                #[cfg(test)]
                self.record_semantic_subtype_admission(
                    semantic_attempt,
                    if provenance_changed {
                        semantic_execution_snapshot::SemanticAdmissionOutcome::EvidenceOnly
                    } else {
                        semantic_execution_snapshot::SemanticAdmissionOutcome::CanonicalDuplicate
                    },
                );
                return false;
            }
            Entry::Vacant(entry) => {
                let record_id = ConstraintRecordId(self.constraint_records.len() as u32);
                entry.insert(record_id);
                record_id
            }
        };
        self.observe_routing_shadow(&constraint);
        self.constraint_records.push(ConstraintRecord {
            key: constraint.clone(),
            root_origins: Vec::new(),
            structural_derivations: vec![derivation],
            row_derivations: Vec::new(),
            replay_derivations: Vec::new(),
            scheme_instantiation_derivations: Vec::new(),
            scheme_instantiation_routes: Vec::new(),
            canonicalization_dispositions: Vec::new(),
            replay_provenance: ProvenanceCompleteness::Complete,
        });
        self.proof_store.record_structural(record_id, derivation);
        self.merge_structural_claim_parents(record_id, derivation, true);
        self.merge_scheme_instantiation_routes(record_id, scheme_routes);
        self.merge_constraint_canonicalization_disposition(&constraint, disposition);
        self.bump_provenance_epoch();
        let work = ConstraintWork::Subtype(record_id);
        #[cfg(test)]
        self.record_semantic_queue_enqueue(&work);
        self.queue.push_back(work);
        #[cfg(test)]
        self.record_semantic_subtype_admission(
            semantic_attempt,
            semantic_execution_snapshot::SemanticAdmissionOutcome::Enqueued,
        );
        true
    }

    pub(in crate::constraints) fn merge_structural_derivation(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        parent: ConstraintRecordId,
        rule: StructuralDerivationRule,
    ) {
        // Aggregate row decomposition can give one semantic child several unary explanations.
        // The first edge performs normal admission; later edges only extend record metadata so
        // semantic duplicate/trivial counters and queueing remain byte-identical.
        self.timing.record_structural_derivation(rule);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            return;
        };
        let Some(record_id) = self.canonical_constraints.get(&constraint).copied() else {
            debug_assert!(
                false,
                "a secondary derivation must follow semantic admission"
            );
            return;
        };
        let derivation = StructuralDerivation { parent, rule };
        let mut derivation_inserted = false;
        let derivations = &mut self.constraint_records[record_id.0 as usize].structural_derivations;
        if !derivations.contains(&derivation) {
            derivations.push(derivation);
            derivation_inserted = true;
        }
        if derivation_inserted {
            self.proof_store.record_structural(record_id, derivation);
        }
        let parent_changed =
            self.merge_structural_claim_parents(record_id, derivation, derivation_inserted);
        let provenance_changed = derivation_inserted || parent_changed;
        if provenance_changed {
            self.bump_provenance_epoch();
        }
    }

    fn merge_structural_claim_parents(
        &mut self,
        result: ConstraintRecordId,
        derivation: StructuralDerivation,
        derivation_inserted: bool,
    ) -> bool {
        let parents = self
            .bounds
            .claim_parents_by_constraint
            .get(&derivation.parent)
            .cloned()
            .unwrap_or_default();
        let mut inserted_parents = Vec::new();
        for parent in parents {
            let parent_claim = parent.parent_claim();
            let parent = ClaimQualifiedParent::StructuralConstraint {
                parent_claim,
                derivation,
            };
            inserted_parents.push(parent);
        }
        self.register_structural_claim_parent_admission(
            result,
            &inserted_parents,
            derivation,
            derivation_inserted,
        )
    }

    pub(in crate::constraints) fn intern_row_derivation(
        &mut self,
        rule: RowDerivationRule,
        parents: Vec<RowDerivationParent>,
        retained_items: Vec<NegId>,
    ) -> RowDerivationId {
        let derivation = RowDerivation {
            rule,
            parents,
            retained_items,
        };
        if let Some(id) = self.row_derivation_index.get(&derivation).copied() {
            self.timing.record_row_derivation(rule, false);
            return id;
        }
        let id = RowDerivationId(self.row_derivations.len() as u32);
        self.row_derivation_index.insert(derivation.clone(), id);
        self.row_derivations.push(derivation.clone());
        self.proof_store
            .record_row_definition(id, derivation.clone());
        self.timing.record_row_derivation(rule, true);
        self.bump_provenance_epoch();
        id
    }

    pub(in crate::constraints) fn enqueue_row_derived_subtype(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        derivation: RowDerivationId,
    ) -> bool {
        #[cfg(test)]
        let semantic_attempt = self.semantic_subtype_admission_attempt(
            lower,
            &weights,
            upper,
            None,
            semantic_execution_snapshot::SemanticAdmissionSource::Row,
        );
        let disposition = self.terminal_weight_erasure_disposition(lower, &weights, upper);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            self.timing.record_subtype_trivial_admission();
            #[cfg(test)]
            self.record_semantic_subtype_admission(
                semantic_attempt,
                semantic_execution_snapshot::SemanticAdmissionOutcome::Trivial,
            );
            return false;
        };
        let record_id = match self.canonical_constraints.entry(constraint.clone()) {
            Entry::Occupied(entry) => {
                let record_id = *entry.get();
                let mut derivation_inserted = false;
                let derivations =
                    &mut self.constraint_records[record_id.0 as usize].row_derivations;
                if !derivations.contains(&derivation) {
                    derivations.push(derivation);
                    derivation_inserted = true;
                    self.bump_provenance_epoch();
                }
                if derivation_inserted {
                    self.proof_store
                        .record_row_constraint(record_id, derivation);
                }
                self.merge_constraint_canonicalization_disposition(&constraint, disposition);
                self.timing.record_subtype_duplicate_admission();
                #[cfg(test)]
                self.record_semantic_subtype_admission(
                    semantic_attempt,
                    if derivation_inserted {
                        semantic_execution_snapshot::SemanticAdmissionOutcome::EvidenceOnly
                    } else {
                        semantic_execution_snapshot::SemanticAdmissionOutcome::CanonicalDuplicate
                    },
                );
                return false;
            }
            Entry::Vacant(entry) => {
                let record_id = ConstraintRecordId(self.constraint_records.len() as u32);
                entry.insert(record_id);
                record_id
            }
        };
        self.observe_routing_shadow(&constraint);
        self.constraint_records.push(ConstraintRecord {
            key: constraint.clone(),
            root_origins: Vec::new(),
            structural_derivations: Vec::new(),
            row_derivations: vec![derivation],
            replay_derivations: Vec::new(),
            scheme_instantiation_derivations: Vec::new(),
            scheme_instantiation_routes: Vec::new(),
            canonicalization_dispositions: Vec::new(),
            replay_provenance: ProvenanceCompleteness::Complete,
        });
        self.proof_store
            .record_row_constraint(record_id, derivation);
        self.merge_constraint_canonicalization_disposition(&constraint, disposition);
        self.bump_provenance_epoch();
        let work = ConstraintWork::Subtype(record_id);
        #[cfg(test)]
        self.record_semantic_queue_enqueue(&work);
        self.queue.push_back(work);
        #[cfg(test)]
        self.record_semantic_subtype_admission(
            semantic_attempt,
            semantic_execution_snapshot::SemanticAdmissionOutcome::Enqueued,
        );
        true
    }

    fn record_root_origin(&mut self, origin: OriginId) {
        let record = self
            .origins
            .get(origin.0 as usize)
            .expect("root origin belongs to this constraint session");
        debug_assert_eq!(
            record
                .source_boundary
                .map(|boundary| self.source_boundaries[boundary.0 as usize].origin),
            record.source_boundary.map(|_| origin),
        );
        self.timing.record_root_origin(record.kind);
    }

    pub(crate) fn constraint_record_id(
        &self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> Option<ConstraintRecordId> {
        let key = self.canonical_subtype_constraint(lower, weights, upper)?;
        self.canonical_constraints.get(&key).copied()
    }

    #[cfg(test)]
    pub(crate) fn debug_constraint_record_id(
        &self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> Option<ConstraintRecordId> {
        self.constraint_record_id(lower, weights, upper)
    }

    #[cfg(test)]
    pub(crate) fn debug_trace_constraint(
        &self,
        start: ConstraintRecordId,
    ) -> Vec<DebugConstraintTraceNode> {
        let mut pending = vec![start];
        let mut visited = FxHashSet::default();
        let mut trace = Vec::new();
        while let Some(record_id) = pending.pop() {
            if !visited.insert(record_id) {
                continue;
            }
            let record = &self.constraint_records[record_id.0 as usize];
            for derivation in record.structural_derivations.iter().rev() {
                pending.push(derivation.parent);
            }
            trace.push(DebugConstraintTraceNode {
                record: record_id,
                key: record.key.clone(),
                root_origins: record.root_origins.clone(),
                structural_derivations: record.structural_derivations.clone(),
                row_derivations: record.row_derivations.clone(),
                replay_derivations: record.replay_derivations.clone(),
                canonicalization_dispositions: record.canonicalization_dispositions.clone(),
                replay_provenance: record.replay_provenance,
            });
        }
        trace
    }

    fn observe_routing_shadow(&mut self, constraint: &SubtypeConstraintKey) {
        let Some(shadow) = &self.replay_routing_shadow else {
            return;
        };
        let (Pos::Var(source), Neg::Var(target)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return;
        };
        shadow
            .borrow_mut()
            .observe_var_var_edge(*source, *target, &constraint.weights);
    }

    pub(in crate::constraints) fn terminal_subtype_weights(
        &self,
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
    ) -> ConstraintWeights {
        // Terminal subtype checks do not forward weights into child constraints.
        // Canonicalizing them here keeps the queue/semantic index finite without
        // changing bounds or row-subtraction state.
        if self.has_terminal_subtype_endpoint(lower, upper) {
            ConstraintWeights::empty()
        } else {
            weights
        }
    }

    pub(in crate::constraints) fn has_terminal_subtype_endpoint(
        &self,
        lower: PosId,
        upper: NegId,
    ) -> bool {
        match (self.types.pos(lower), self.types.neg(upper)) {
            (Pos::Bot, _) | (_, Neg::Top) => true,
            (Pos::Con(path, args), _) if self.is_non_effect_terminal_con(path, args) => true,
            (_, Neg::Con(path, args)) if self.is_non_effect_terminal_con(path, args) => true,
            _ => false,
        }
    }

    pub(in crate::constraints) fn is_non_effect_terminal_con(
        &self,
        path: &[String],
        args: &[NeuId],
    ) -> bool {
        args.is_empty() && !self.effect_family_paths.contains(path)
    }

    pub(in crate::constraints) fn step(&mut self, work: ConstraintWork) {
        match work {
            ConstraintWork::Subtype(record_id) => {
                self.step_subtype(record_id);
            }
            ConstraintWork::SubtractFact(fact) => {
                self.record_subtract_fact(fact.effect, fact.fact, fact.derivation);
            }
        }
    }

    pub(in crate::constraints) fn record_subtract_fact(
        &mut self,
        effect: TypeVar,
        fact: SubtractFact,
        derivation: SubtractFactDerivation,
    ) {
        let id = fact.id;
        let insertion = self.subtracts.insert(effect, fact, derivation);
        if insertion.provenance_changed {
            self.proof_store.record_subtract(insertion.id, derivation);
        }
        if insertion.provenance_changed {
            self.bump_provenance_epoch();
        }
        self.timing.record_subtract_fact_record(
            insertion.semantic_changed,
            insertion.provenance_changed && !insertion.semantic_changed,
        );
        if insertion.semantic_changed {
            self.timing.record_subtract_fact_added();
            self.bump_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintSubtractFacts(effect));
            }
            self.events.push(ConstraintEvent::SubtractFactAdded {
                record: insertion.id,
                effect,
                id,
            });
        }
    }

    pub(in crate::constraints) fn record_pre_pop_effect_families(
        &mut self,
        target: TypeVar,
        weight: &StackWeight,
    ) {
        let families = self.pre_pop_effect_families.entry(target).or_default();
        let mut changed = false;
        for family in weight
            .active_stack_items()
            .flat_map(subtractability_families)
        {
            let family = ConstraintEffectFamily {
                path: family.path,
                args: family.args,
            };
            if !families.contains(&family) {
                families.push(family);
                changed = true;
            }
        }
        if changed {
            self.bump_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintPrePopFamilies(target));
            }
        }
    }

    pub(in crate::constraints) fn bump_epoch(&mut self) -> ConstraintEpoch {
        self.epoch.bump();
        #[cfg(test)]
        self.record_semantic_epoch_event(
            semantic_execution_snapshot::SemanticEpochKind::Constraint,
        );
        self.epoch
    }

    pub(in crate::constraints) fn bump_provenance_epoch(&mut self) -> ProvenanceEpoch {
        self.provenance_epoch.bump();
        #[cfg(test)]
        self.record_semantic_epoch_event(
            semantic_execution_snapshot::SemanticEpochKind::Provenance,
        );
        self.provenance_epoch
    }

    pub(in crate::constraints) fn bump_role_solve_supplemental_epoch(
        &mut self,
    ) -> RoleSolveSupplementalEpoch {
        self.role_solve_supplemental_epoch.bump();
        #[cfg(test)]
        self.record_semantic_epoch_event(
            semantic_execution_snapshot::SemanticEpochKind::RoleSolveSupplemental,
        );
        self.role_solve_supplemental_epoch
    }

    pub(in crate::constraints) fn fresh_internal_type_var_at(
        &mut self,
        level: TypeLevel,
    ) -> TypeVar {
        let var = TypeVar(self.next_internal_type_var);
        self.next_internal_type_var = self.next_internal_type_var.saturating_add(1);
        self.register_type_var(var, level);
        var
    }

    pub(in crate::constraints) fn observe_type_var(&mut self, var: TypeVar) {
        self.next_internal_type_var = self.next_internal_type_var.max(var.0.saturating_add(1));
    }

    pub(in crate::constraints) fn observe_pos(&mut self, pos: &Pos) {
        match pos {
            Pos::Bot => {}
            Pos::Var(var) => self.observe_type_var(*var),
            Pos::Con(_, args) => {
                for arg in args {
                    self.observe_neu_id(*arg);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.observe_neg_id(*arg);
                self.observe_neg_id(*arg_eff);
                self.observe_pos_id(*ret_eff);
                self.observe_pos_id(*ret);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.observe_pos_id(field.value);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.observe_pos_id(field.value);
                }
                self.observe_pos_id(*tail);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.observe_pos_id(*tail);
                for field in fields {
                    self.observe_pos_id(field.value);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.observe_pos_id(*payload);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.observe_pos_id(*item);
                }
            }
            Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
                self.observe_pos_id(*inner);
            }
            Pos::Union(left, right) => {
                self.observe_pos_id(*left);
                self.observe_pos_id(*right);
            }
        }
    }

    pub(in crate::constraints) fn observe_neg(&mut self, neg: &Neg) {
        match neg {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => self.observe_type_var(*var),
            Neg::Con(_, args) => {
                for arg in args {
                    self.observe_neu_id(*arg);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.observe_pos_id(*arg);
                self.observe_pos_id(*arg_eff);
                self.observe_neg_id(*ret_eff);
                self.observe_neg_id(*ret);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.observe_neg_id(field.value);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.observe_neg_id(*payload);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.observe_neg_id(*item);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.observe_neg_id(*item);
                }
                self.observe_row_tail(*tail);
            }
            Neg::Stack { inner, .. } => self.observe_neg_id(*inner),
            Neg::Intersection(left, right) => {
                self.observe_neg_id(*left);
                self.observe_neg_id(*right);
            }
        }
    }

    pub(in crate::constraints) fn observe_neu(&mut self, neu: &Neu) {
        match neu {
            Neu::Bounds(lower, upper) => {
                self.observe_pos_id(*lower);
                self.observe_neg_id(*upper);
            }
            Neu::Con(_, args) => {
                for arg in args {
                    self.observe_neu_id(*arg);
                }
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.observe_neu_id(*arg);
                self.observe_neu_id(*arg_eff);
                self.observe_neu_id(*ret_eff);
                self.observe_neu_id(*ret);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.observe_neu_id(field.value);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.observe_neu_id(*payload);
                    }
                }
            }
            Neu::Tuple(items) => {
                for item in items {
                    self.observe_neu_id(*item);
                }
            }
        }
    }

    pub(in crate::constraints) fn observe_pos_id(&mut self, id: PosId) {
        let pos = self.types.pos(id).clone();
        self.observe_pos(&pos);
    }

    pub(in crate::constraints) fn observe_neg_id(&mut self, id: NegId) {
        let neg = self.types.neg(id).clone();
        self.observe_neg(&neg);
    }

    pub(in crate::constraints) fn observe_neu_id(&mut self, id: NeuId) {
        let neu = self.types.neu(id).clone();
        self.observe_neu(&neu);
    }

    fn observe_row_tail(&mut self, tail: NegId) {
        let neg = self.types.neg(tail).clone();
        if let Neg::Var(var) = &neg {
            self.row_tail_vars.insert(*var);
        }
        self.observe_neg(&neg);
    }
}
