use super::*;

impl AnalysisSession {
    pub fn new(poly: PolyArena) -> Self {
        Self::new_with_imported_boundary(poly, &crate::CompiledBoundaryInterface::empty())
    }

    pub(crate) fn new_with_imported_boundary(
        poly: PolyArena,
        boundary: &crate::CompiledBoundaryInterface,
    ) -> Self {
        let mut infer = InferArena::new();
        let imported_boundary = seed_imported_boundary(&poly.typ, &mut infer, boundary);
        let mut session = Self {
            poly,
            application_provenance: ApplicationProvenanceTable::default(),
            infer,
            local_defs: LocalDefUseTable::new(),
            refs: RefUseTable::new(),
            selections: SelectionUseTable::new(),
            roles: RoleConstraintTable::new(),
            role_impls: IndexedRoleImplTable::new(),
            casts: CastTable::new(),
            methods: TypeMethodTable::new(),
            effect_methods: EffectMethodTable::new(),
            role_methods: RoleMethodTable::new(),
            role_input_variances: RoleInputVarianceTable::new(),
            local_methods: CompanionMethodTable::new(),
            scc: SccMachine::new(),
            role_impl_members: FxHashMap::default(),
            role_impl_member_sets: FxHashMap::default(),
            role_impl_member_simplifications: FxHashMap::default(),
            role_impl_member_projections: FxHashMap::default(),
            role_impl_member_residual_prerequisites: FxHashMap::default(),
            applied_method_role_resolutions: FxHashSet::default(),
            method_role_mutations: MethodRoleMutationOutbox::new(),
            last_audited_constraint_epoch: ConstraintEpoch::default(),
            last_audited_constraint_mutation_generation: MutationGeneration::default(),
            last_audited_constraint_mutation_emission_generation: MutationGeneration::default(),
            last_audited_role_epoch: RoleEpoch::default(),
            last_audited_role_mutation_generation: MutationGeneration::default(),
            last_audited_role_mutation_emission_generation: MutationGeneration::default(),
            last_audited_candidate_mutation_generation: MutationGeneration::default(),
            last_audited_candidate_mutation_emission_generation: MutationGeneration::default(),
            method_role_input_generation: 0,
            last_no_progress_method_role_pass: None,
            cache_interface_applied_merge_constraints: FxHashSet::default(),
            cache_interface_applied_subtype_constraints: FxHashSet::default(),
            candidate_settlements: FxHashMap::default(),
            candidate_settlement_complete: false,
            #[cfg(test)]
            candidate_settlement_safety_witness: None,
            #[cfg(test)]
            shadow_dirty_oracle: ShadowDirtyOracle::for_new_session(),
            #[cfg(test)]
            generalize_snapshot_characterization:
                GeneralizeSnapshotCharacterizationOracle::for_new_session(),
            generalize_role_snapshot_reuse_enabled:
                generalize_role_snapshot_reuse_enabled_for_new_session(),
            owner_dirty_scheduler: MethodRoleOwnerDirtyScheduler::for_new_session(),
            owner_dirty_scheduler_journal: None,
            #[cfg(test)]
            stage0_quantify_watch: FxHashSet::default(),
            #[cfg(test)]
            stage0_quantify_events: Vec::new(),
            schemes: FxHashMap::default(),
            binding_fetches: FxHashMap::default(),
            diagnostics: Vec::new(),
            scc_events: Vec::new(),
            work: VecDeque::new(),
            pending_ocast_requests: Vec::new(),
            pending_ocast_producer_set: FxHashSet::default(),
            ocast_eligibility_shadow: Vec::new(),
            ocast_eligibility_metrics: OcastEligibilityMetrics::default(),
            generalize_compact_shadow: GeneralizeCompactShadow::from_env(),
            generalize_compact_cache: GeneralizeCompactCache::from_env(),
            generalize_role_view_shadow: GeneralizeRoleViewShadow::from_env(),
            timing: AnalysisTiming::default(),
            instantiated_targets: FxHashSet::default(),
            def_parent_map: DefParentMapCache::default(),
            imported_boundary,
            imported_scheme_defs: FxHashSet::default(),
            imported_scheme_validations: FxHashMap::default(),
            imported_scheme_instantiation_failures: Vec::new(),
        };
        session.route_constraint_events();
        session.seed_existing_poly_surface();
        session
    }

    #[cfg(test)]
    pub(crate) fn imported_boundary_var(&self, source: TypeVar) -> Option<TypeVar> {
        self.imported_boundary.get(source)
    }

    /// Import already-finalized definitions and lookup surfaces from a cached `poly` prefix.
    ///
    /// A prefix is not part of the current SCC graph: its schemes are final, while root source
    /// added later can still instantiate those definitions, casts, and role implementations.
    fn seed_existing_poly_surface(&mut self) {
        let quantified_defs = self
            .poly
            .defs
            .iter()
            .filter_map(|(def, item)| match item {
                Def::Let {
                    scheme: Some(_), ..
                } => Some(def),
                Def::Mod { .. } | Def::Let { .. } | Def::Arg => None,
            })
            .collect::<Vec<_>>();
        self.imported_scheme_defs
            .extend(quantified_defs.iter().copied());
        for def in quantified_defs {
            self.scc.seed_quantified_def(def);
        }

        for rule in &self.poly.cast_rules {
            match rule.kind {
                poly::expr::CastRuleKind::Value => self.casts.insert_value(
                    rule.def,
                    rule.source.clone(),
                    rule.target.clone(),
                    rule.scheme.clone(),
                ),
                poly::expr::CastRuleKind::EffectUp => self.casts.insert_effect_up(
                    rule.def,
                    rule.source.clone(),
                    rule.target.clone(),
                    rule.scheme.clone(),
                ),
            }
        }

        let role_impls = self.poly.role_impls.iter().cloned().collect::<Vec<_>>();
        for candidate in role_impls {
            let candidate = freshen_role_impl_candidate(
                &self.poly.typ,
                &mut self.infer,
                &candidate,
                &self.imported_boundary,
            );
            self.register_role_impl_candidate(candidate);
        }
    }

    /// Queue a unit of analysis work without draining it immediately.
    pub fn enqueue(&mut self, work: AnalysisWork) {
        self.work.push_back(work);
    }

    /// Register a selection use-site and schedule its initial method probe.
    pub fn register_selection_use(&mut self, select_id: SelectId, use_site: SelectionUse) {
        let previous = self.selections.insert(select_id, use_site);
        if self.method_role_mutations.is_active() {
            match previous {
                Some(previous) => self.method_role_mutations.record_many([
                    DependencyKey::Selection(select_id),
                    DependencyKey::OwnerSelections(previous.parent),
                    DependencyKey::OwnerSelections(use_site.parent),
                ]),
                None => self.method_role_mutations.record_many([
                    DependencyKey::Selection(select_id),
                    DependencyKey::OwnerSelections(use_site.parent),
                ]),
            }
        }
        self.mark_method_role_input_changed();
        self.enqueue(AnalysisWork::Scc(SccInput::MethodDependencyAdded {
            parent: use_site.parent,
        }));
        self.enqueue(AnalysisWork::ProbeSelect(select_id));
    }

    pub(super) fn remove_unresolved_selection(
        &mut self,
        select_id: SelectId,
    ) -> Option<SelectionUse> {
        let removed = self.selections.remove(select_id);
        if let Some(use_site) = removed {
            if self.method_role_mutations.is_active() {
                self.method_role_mutations.record_many([
                    DependencyKey::Selection(select_id),
                    DependencyKey::OwnerSelections(use_site.parent),
                ]);
            }
            self.mark_method_role_input_changed();
            if !self
                .selections
                .iter()
                .any(|(_, remaining)| remaining.parent == use_site.parent)
            {
                self.owner_dirty_scheduler_remove_owner(use_site.parent);
            }
        }
        removed
    }

    /// Register a role implementation visible to role solving.
    pub fn register_role_impl_candidate(&mut self, candidate: RoleImplCandidate) {
        #[cfg(test)]
        let shadow_role = candidate.role.clone();
        self.role_impls.insert(candidate);
        #[cfg(test)]
        self.shadow_dirty_oracle_candidate_inserted(shadow_role);
        self.mark_method_role_input_changed();
    }

    /// Add residual prerequisites to an already registered role implementation.
    pub(super) fn extend_role_impl_prerequisites(
        &mut self,
        impl_def: DefId,
        prerequisites: impl IntoIterator<Item = RoleConstraint>,
    ) {
        let prerequisites = prerequisites.into_iter().collect::<Vec<_>>();
        if prerequisites.is_empty() {
            return;
        }
        self.role_impls
            .extend_prerequisites_for_impl(impl_def, prerequisites);
        #[cfg(test)]
        self.shadow_dirty_oracle_prerequisites_extended(impl_def);
        self.mark_method_role_input_changed();
    }

    /// Add a globally visible value receiver method and re-probe pending selections.
    pub fn register_value_type_method(
        &mut self,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.methods.insert_value(receiver, method, def);
        self.enqueue_unresolved_selection_probes();
    }

    /// Add a globally visible reference receiver method and re-probe pending selections.
    pub fn register_ref_type_method(
        &mut self,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.methods.insert_ref(receiver, method, def);
        self.enqueue_unresolved_selection_probes();
    }

    /// Add a globally visible effect-row method and re-probe pending selections.
    pub fn register_effect_method(
        &mut self,
        effect: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.effect_methods.insert(effect, method, def);
        self.enqueue_unresolved_selection_probes();
    }

    /// Add a globally visible role method name for fallback selection resolution.
    pub fn register_role_method(
        &mut self,
        role: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.role_methods.insert(role, method, def);
    }

    /// Store variance information used when role predicates are generalized.
    pub fn register_role_input_variances(
        &mut self,
        role: impl Into<Vec<String>>,
        variances: Vec<RoleInputVariance>,
    ) {
        self.role_input_variances.insert(role, variances);
    }

    /// Record that a role impl member belongs to an impl definition.
    pub fn register_role_impl_member(&mut self, member: DefId, impl_def: DefId) {
        self.role_impl_members.insert(member, impl_def);
        let members = self.role_impl_member_sets.entry(impl_def).or_default();
        if !members.contains(&member) {
            members.push(member);
            members.sort_by_key(|def| def.0);
        }
    }

    /// Record the role method definition that an impl member must satisfy.
    pub(crate) fn register_role_impl_member_requirement(
        &mut self,
        member: DefId,
        role_method: DefId,
    ) {
        self.enqueue(AnalysisWork::Scc(SccInput::DependencyAdded {
            parent: member,
            target: role_method,
        }));
    }

    /// Store a compact simplification learned while checking an impl member.
    pub(crate) fn register_role_impl_member_simplification(
        &mut self,
        member: DefId,
        simplification: CompactSimplification,
    ) {
        if simplification.substitutions.is_empty() && simplification.sandwiches.is_empty() {
            return;
        }
        self.role_impl_member_simplifications
            .entry(member)
            .or_default()
            .push(simplification);
    }

    /// Store the requirement projection used to align an impl member with its role method.
    pub(crate) fn register_role_impl_member_projection(
        &mut self,
        member: DefId,
        projection: CompactRoot,
    ) {
        self.role_impl_member_projections.insert(member, projection);
    }

    /// Add a module-local value receiver method visible only in the given scope.
    pub fn register_local_value_type_method(
        &mut self,
        scope: crate::ModuleId,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_value_type_method(scope, receiver, method, def);
    }

    /// Add a module-local reference receiver method visible only in the given scope.
    pub fn register_local_ref_type_method(
        &mut self,
        scope: crate::ModuleId,
        receiver: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_ref_type_method(scope, receiver, method, def);
    }

    /// Add a module-local effect method visible only in the given scope.
    pub fn register_local_effect_method(
        &mut self,
        scope: crate::ModuleId,
        effect: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_effect_method(scope, effect, method, def);
    }

    /// Add a module-local role method visible only in the given scope.
    pub fn register_local_role_method(
        &mut self,
        scope: crate::ModuleId,
        role: impl Into<Vec<String>>,
        method: impl Into<String>,
        def: DefId,
    ) {
        self.local_methods
            .insert_role_method(scope, role, method, def);
    }

    /// Return the pending analysis work queue for tests and diagnostics.
    pub fn work(&self) -> &VecDeque<AnalysisWork> {
        &self.work
    }

    /// Report whether either analysis work or routed constraint events remain.
    pub fn has_pending_work(&self) -> bool {
        !self.work.is_empty() || !self.infer.constraints().events().is_empty()
    }

    /// Convert constraint-machine events into analysis work and cast constraints.
    pub fn route_constraint_events(&mut self) -> Duration {
        let start = Instant::now();
        if self.method_role_mutations.is_active() {
            if self.owner_dirty_scheduler.is_some() {
                self.owner_dirty_scheduler_drain_journal();
            } else {
                self.sync_method_role_mutation_outboxes();
            }
        }
        let events = self.infer.constraints_mut().take_events();
        let event_count = events.len();
        trace_constraint_events(&events);
        for event in events {
            match event {
                ConstraintEvent::LowerBoundAdded { var, .. } => {
                    for select in self.selections.pending_for_lower_bound(var) {
                        self.enqueue(AnalysisWork::ProbeSelect(select));
                    }
                }
                ConstraintEvent::UpperBoundAdded { var, .. } => {
                    for select in self.selections.pending_for_upper_bound(var) {
                        self.enqueue(AnalysisWork::ProbeSelect(select));
                    }
                }
                ConstraintEvent::NominalCastNeeded {
                    lower,
                    upper,
                    source,
                    target,
                    weights,
                    producer,
                } => {
                    if self.pending_ocast_producer_set.insert(producer) {
                        self.pending_ocast_requests.push(PendingNominalCastRequest {
                            producer,
                            lower,
                            upper,
                            source: source.clone(),
                            target: target.clone(),
                            weights: weights.clone(),
                        });
                    }
                    self.constrain_nominal_cast(lower, upper, &source, &target, weights);
                }
                ConstraintEvent::SubtractFactAdded { effect, .. } => {
                    for select in self.selections.pending_for_effect_fact(effect) {
                        self.enqueue(AnalysisWork::ProbeSelect(select));
                    }
                }
                ConstraintEvent::EffectFilterViolation { effect, filter } => {
                    self.diagnostics
                        .push(AnalysisDiagnostic::EffectFilterViolation { effect, filter });
                }
            }
        }
        let elapsed = start.elapsed();
        self.timing.record_route_constraints(elapsed, event_count);
        elapsed
    }

    pub(crate) fn classify_pending_ocast_eligibility_at_quiescence(
        &mut self,
    ) -> Vec<ClassifiedNominalCastRequest> {
        debug_assert!(
            !self.has_pending_work(),
            "OCAST eligibility classification requires constraint quiescence"
        );
        let start = Instant::now();
        let mut classified = Vec::with_capacity(self.pending_ocast_requests.len());
        for request in self.pending_ocast_requests.drain(..) {
            let classification = self.infer.constraints().classify_ocast_eligibility(
                request.producer,
                crate::constraints::explain::ExplanationBudget::ocast_classifier(),
            );
            let eligibility = classification.state();
            self.ocast_eligibility_metrics.record(&classification);
            self.ocast_eligibility_shadow.push(classification);
            classified.push(ClassifiedNominalCastRequest::new(request, eligibility));
        }
        self.pending_ocast_producer_set.clear();
        self.ocast_eligibility_metrics.elapsed += start.elapsed();
        classified
    }

    #[allow(dead_code, reason = "debug-only CPROV-I shadow query")]
    pub(crate) fn ocast_eligibility_shadow(&self) -> &[OcastEligibilityClassification] {
        &self.ocast_eligibility_shadow
    }

    pub fn ocast_eligibility_metrics(&self) -> OcastEligibilityMetrics {
        self.ocast_eligibility_metrics
    }

    pub(super) fn activate_method_role_mutation_journal(
        &mut self,
    ) -> MethodRoleMutationJournalActivation {
        // Inactive work is intentionally outside the contract window. Establish fresh audit
        // baselines before opening every outbox, so old coarse epochs cannot be mistaken for a
        // missing mutation in this forced pass.
        self.last_audited_constraint_epoch = self.infer.constraints().epoch();
        self.last_audited_constraint_mutation_generation =
            self.infer.constraints().method_role_mutation_generation();
        self.last_audited_constraint_mutation_emission_generation = self
            .infer
            .constraints()
            .method_role_mutation_emission_generation();
        self.last_audited_role_epoch = self.roles.epoch();
        self.last_audited_role_mutation_generation = self.roles.method_role_mutation_generation();
        self.last_audited_role_mutation_emission_generation =
            self.roles.method_role_mutation_emission_generation();
        self.last_audited_candidate_mutation_generation =
            self.role_impls.method_role_mutation_generation();
        self.last_audited_candidate_mutation_emission_generation =
            self.role_impls.method_role_mutation_emission_generation();

        let activation = MethodRoleMutationJournalActivation {
            session: self.method_role_mutations.activate(),
            constraints: self.infer.constraints().activate_method_role_mutations(),
            roles: self.roles.activate_method_role_mutations(),
            candidates: self.role_impls.activate_method_role_mutations(),
        };
        self.owner_dirty_scheduler_begin_journal_window();
        activation
    }

    fn finish_method_role_mutation_journal(
        &mut self,
        activation: MethodRoleMutationJournalActivation,
    ) {
        self.sync_method_role_mutation_outboxes();
        self.owner_dirty_scheduler_finish_journal_window();
        activation.finish();
    }

    fn sync_method_role_mutation_outboxes(&mut self) {
        debug_assert!(self.method_role_mutations.is_active());

        let constraint_epoch = self.infer.constraints().epoch();
        let constraint_generation = self.infer.constraints().method_role_mutation_generation();
        let constraint_emission_generation = self
            .infer
            .constraints()
            .method_role_mutation_emission_generation();
        let constraint_mutations_drained = self
            .infer
            .constraints_mut()
            .drain_method_role_mutations_into(&mut self.method_role_mutations);
        if constraint_epoch != self.last_audited_constraint_epoch
            && constraint_generation == self.last_audited_constraint_mutation_generation
        {
            self.method_role_mutations.invalidate_all(
                InvalidateAllReason::AuditFenceDisagreement {
                    site: "ConstraintMachine::epoch",
                },
            );
        }
        self.audit_drained_source_outbox(
            constraint_emission_generation,
            self.last_audited_constraint_mutation_emission_generation,
            constraint_mutations_drained,
            "ConstraintMachine::mutation_outbox",
        );
        self.last_audited_constraint_epoch = constraint_epoch;
        self.last_audited_constraint_mutation_generation = constraint_generation;
        self.last_audited_constraint_mutation_emission_generation = constraint_emission_generation;

        let role_epoch = self.roles.epoch();
        let role_generation = self.roles.method_role_mutation_generation();
        let role_emission_generation = self.roles.method_role_mutation_emission_generation();
        let role_mutations_drained = self
            .roles
            .drain_method_role_mutations_into(&mut self.method_role_mutations);
        if role_epoch != self.last_audited_role_epoch
            && role_generation == self.last_audited_role_mutation_generation
        {
            self.method_role_mutations.invalidate_all(
                InvalidateAllReason::AuditFenceDisagreement {
                    site: "RoleConstraintTable::epoch",
                },
            );
        }
        self.audit_drained_source_outbox(
            role_emission_generation,
            self.last_audited_role_mutation_emission_generation,
            role_mutations_drained,
            "RoleConstraintTable::mutation_outbox",
        );
        self.last_audited_role_epoch = role_epoch;
        self.last_audited_role_mutation_generation = role_generation;
        self.last_audited_role_mutation_emission_generation = role_emission_generation;

        let candidate_generation = self.role_impls.method_role_mutation_generation();
        let candidate_emission_generation =
            self.role_impls.method_role_mutation_emission_generation();
        let candidate_mutations_drained = self
            .role_impls
            .drain_method_role_mutations_into(&mut self.method_role_mutations);
        self.audit_drained_source_outbox(
            candidate_emission_generation,
            self.last_audited_candidate_mutation_emission_generation,
            candidate_mutations_drained,
            "IndexedRoleImplTable::mutation_outbox",
        );
        self.last_audited_candidate_mutation_generation = candidate_generation;
        self.last_audited_candidate_mutation_emission_generation = candidate_emission_generation;
    }

    fn audit_drained_source_outbox(
        &mut self,
        emission_generation: MutationGeneration,
        last_emission_generation: MutationGeneration,
        had_mutations: bool,
        site: &'static str,
    ) {
        if emission_generation != last_emission_generation && !had_mutations {
            self.method_role_mutations
                .invalidate_all(InvalidateAllReason::AuditFenceDisagreement { site });
        }
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "Stage 3 drains the production journal for scheduling"
        )
    )]
    pub(crate) fn take_method_role_mutations(&mut self) -> Vec<MethodRoleMutation> {
        if self.method_role_mutations.is_active() {
            self.sync_method_role_mutation_outboxes();
        }
        self.method_role_mutations.take()
    }

    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "Stage 3 gates owner eligibility on the mutation contract"
        )
    )]
    pub(crate) fn method_role_owner_eligibility(&self) -> bool {
        self.method_role_mutations.owner_eligibility()
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutation_journal_active(&self) -> bool {
        self.method_role_mutations.is_active()
    }

    /// Drain queued analysis work until method-role solving reaches a fixed point.
    pub fn drain_work(&mut self) {
        let mut trace = AnalysisDrainTrace::from_env(self.work.len());
        // A terminal record can outlive one `drain_work` call while lowering continues to mutate
        // constraints. The production scheduler therefore keeps activation alive after the first
        // forced pass and drains it at ordinary routing boundaries. A test-only disabled session
        // retains Stage 2's one-forced-pass activation exactly.
        let persistent_scheduler_journal = self.owner_dirty_scheduler.is_some();
        let mut mutation_journal = None;
        loop {
            while self.step_traced(&mut trace) {}
            if !self.method_role_pass_inputs_changed() {
                self.timing.record_method_role_whole_pass_skip();
                break;
            }
            self.begin_method_role_pass();
            if self.owner_dirty_scheduler.is_some() && self.owner_dirty_scheduler_journal.is_none()
            {
                self.owner_dirty_scheduler_install_mutation_subscriptions();
                let activation = self.activate_method_role_mutation_journal();
                self.owner_dirty_scheduler_journal = Some(activation);
            }
            if !persistent_scheduler_journal {
                if mutation_journal.is_none() {
                    mutation_journal = Some(self.activate_method_role_mutation_journal());
                }
            }
            trace.before_role_pass(self.selections.unresolved().count(), self.work.len());
            let role_start = Instant::now();
            let progressed = self.resolve_roles_for_unresolved_methods();
            if mutation_journal.is_some() {
                self.finish_method_role_mutation_journal(
                    mutation_journal
                        .take()
                        .expect("forced method-role pass has an active journal"),
                );
            }
            self.timing
                .record_role_pass(role_start.elapsed(), progressed);
            trace.after_role_pass(
                progressed,
                self.selections.unresolved().count(),
                self.work.len(),
            );
            if !progressed {
                self.record_no_progress_method_role_pass();
                break;
            }
        }
        if let Some(mutation_journal) = mutation_journal {
            self.finish_method_role_mutation_journal(mutation_journal);
        }
        trace.finish(self.work.len());
    }

    /// Settle method-selection work for one owner without finalizing unrelated definitions.
    pub(crate) fn drain_selection_work_for_parent(&mut self, parent: DefId) {
        loop {
            self.route_constraint_events();
            let mut deferred = VecDeque::new();
            let mut progressed = false;
            let pending = self.work.len();
            for _ in 0..pending {
                let Some(work) = self.work.pop_front() else {
                    break;
                };
                if self.selection_settle_work_matches_parent(&work, parent) {
                    let timing_kind = AnalysisWorkTimingKind::from_work(&work);
                    let start = Instant::now();
                    self.apply_work(work);
                    self.timing
                        .record_work(timing_kind, start.elapsed(), self.work.len());
                    self.route_scc_events();
                    progressed = true;
                } else {
                    deferred.push_back(work);
                }
            }
            deferred.append(&mut self.work);
            self.work = deferred;
            if !progressed {
                break;
            }
        }
    }

    fn selection_settle_work_matches_parent(&self, work: &AnalysisWork, parent: DefId) -> bool {
        match work {
            AnalysisWork::ResolveRef(ref_id) => self
                .refs
                .get(*ref_id)
                .is_some_and(|use_site| use_site.parent == parent),
            AnalysisWork::ApplyRefResolution { ref_id, .. } => self
                .refs
                .get(*ref_id)
                .is_some_and(|use_site| use_site.parent == parent),
            AnalysisWork::ProbeSelect(select_id) => self
                .selection_parent(*select_id)
                .is_some_and(|selection_parent| selection_parent == parent),
            AnalysisWork::ApplySelectionResolution { select_id, target } => {
                if !self
                    .selection_parent(*select_id)
                    .is_some_and(|selection_parent| selection_parent == parent)
                {
                    return false;
                }
                match target {
                    SelectionTarget::RecordField => false,
                    SelectionTarget::Method { def } | SelectionTarget::EffectMethod { def } => {
                        self.scc.is_quantified(*def)
                    }
                    SelectionTarget::TypeclassMethod { member } => self.scc.is_quantified(*member),
                }
            }
            AnalysisWork::Scc(SccInput::RegisterDef { def, .. })
            | AnalysisWork::Scc(SccInput::DefFetchRecorded { def, .. }) => *def == parent,
            AnalysisWork::Scc(SccInput::UseResolved {
                parent: use_parent, ..
            })
            | AnalysisWork::Scc(SccInput::MethodDependencyAdded { parent: use_parent })
            | AnalysisWork::Scc(SccInput::MethodDependencyResolved { parent: use_parent }) => {
                *use_parent == parent
            }
            AnalysisWork::Scc(SccInput::ConformancePending { member })
            | AnalysisWork::Scc(SccInput::ConformanceReleased { member }) => *member == parent,
            AnalysisWork::Scc(SccInput::DefFinished { .. })
            | AnalysisWork::Scc(SccInput::DependencyAdded { .. }) => false,
        }
    }

    fn selection_parent(&self, select_id: SelectId) -> Option<DefId> {
        self.selections
            .get(select_id)
            .map(|use_site| use_site.parent)
    }

    /// Resolve still-unresolved selections as record fields once their SCC is ready.
    pub fn resolve_unresolved_selections_as_record_fields(&mut self) {
        loop {
            self.drain_work();
            if self.enqueue_ready_structured_selection_resolutions() {
                continue;
            }

            self.enqueue_unresolved_selection_probes();
            self.drain_work();
            if self.enqueue_ready_structured_selection_resolutions() {
                continue;
            }

            let record_fields = self.ready_record_field_selections();
            if record_fields.is_empty() {
                break;
            }
            self.apply_record_field_selection_batch(record_fields);
        }
    }

    fn enqueue_ready_structured_selection_resolutions(&mut self) -> bool {
        let ready = self.collect_ready_structured_selection_resolutions();
        self.enqueue_structured_selection_resolutions(ready)
    }

    fn collect_ready_structured_selection_resolutions(&self) -> Vec<(SelectId, SelectionTarget)> {
        let mut ready = self
            .selections
            .iter()
            .filter_map(|(select_id, use_site)| {
                if !self.scc.selection_fallback_ready(use_site.parent) {
                    return None;
                }
                if self.selections.has_unprobed_receiver_upper(select_id) {
                    return None;
                }
                let name = self.poly.select(select_id).name.clone();
                let target = self.role_method_for_select(select_id, &name)?;
                Some((select_id, target))
            })
            .collect::<Vec<_>>();
        ready.sort_by_key(|(select_id, _)| select_id.0);
        ready
    }

    pub(super) fn enqueue_structured_selection_resolutions(
        &mut self,
        ready: Vec<(SelectId, SelectionTarget)>,
    ) -> bool {
        let Some((select_id, target)) = ready.first().cloned() else {
            return false;
        };
        if self.fallback_target_can_batch(&target) {
            let batch = ready
                .into_iter()
                .filter(|(_, target)| self.fallback_target_can_batch(target))
                .collect::<Vec<_>>();
            for (select_id, target) in batch {
                self.enqueue(AnalysisWork::ApplySelectionResolution { select_id, target });
            }
        } else {
            // Unquantified role-method fallback can introduce an SCC edge. Keep those
            // one-by-one so the next readiness decision sees the updated graph.
            self.enqueue(AnalysisWork::ApplySelectionResolution { select_id, target });
        }
        true
    }

    fn ready_record_field_selections(&self) -> Vec<SelectId> {
        let mut ready = self
            .selections
            .iter()
            .filter_map(|(select_id, use_site)| {
                if !self.scc.selection_fallback_ready(use_site.parent) {
                    return None;
                }
                if self.selections.has_unprobed_receiver_upper(select_id) {
                    return None;
                }
                let name = self.poly.select(select_id).name.clone();
                if self.role_method_for_select(select_id, &name).is_some() {
                    return None;
                }
                Some(select_id)
            })
            .collect::<Vec<_>>();
        ready.sort_by_key(|select_id| select_id.0);
        ready
    }

    fn fallback_target_can_batch(&self, target: &SelectionTarget) -> bool {
        match target {
            // Record fallback adds receiver shape constraints. Keep it out of
            // method fallback batches so freshly selected methods can finish
            // instantiating receiver bounds before record projection is chosen.
            SelectionTarget::RecordField => false,
            SelectionTarget::TypeclassMethod { member } => self.scc.is_quantified(*member),
            SelectionTarget::Method { .. } | SelectionTarget::EffectMethod { .. } => false,
        }
    }

    fn apply_record_field_selection_batch(
        &mut self,
        selections: impl IntoIterator<Item = SelectId>,
    ) {
        let start = Instant::now();
        let mut constraints = Vec::new();
        let mut resolved_parents = Vec::new();
        let mut selection_count = 0usize;
        for select_id in selections {
            selection_count += 1;
            if self.poly.select(select_id).resolution.is_some() {
                self.remove_unresolved_selection(select_id);
                continue;
            }
            let name = self.poly.select(select_id).name.clone();
            self.poly
                .resolve_select(select_id, SelectionTarget::RecordField.resolution());
            let Some(use_site) = self.remove_unresolved_selection(select_id) else {
                continue;
            };
            self.selections.insert_resolved(select_id, use_site.into());
            self.trace_selection_bounds(select_id, &name, use_site);
            constraints
                .extend(self.record_field_selection_constraints(use_site.method_value, &name));
            resolved_parents.push(use_site.parent);
        }
        let constraint_count = constraints.len();
        self.infer.subtypes(
            constraints,
            crate::constraints::OriginId::unknown_internal(),
        );
        for parent in resolved_parents {
            self.apply_scc_input(SccInput::MethodDependencyResolved { parent });
        }
        self.route_scc_events();
        self.timing
            .record_field_fallback(start.elapsed(), selection_count, constraint_count);
    }

    pub(super) fn enqueue_unresolved_selection_probes(&mut self) {
        let unresolved = self
            .selections
            .iter()
            .map(|(select_id, _)| select_id)
            .collect::<Vec<_>>();
        for select_id in unresolved {
            self.enqueue(AnalysisWork::ProbeSelect(select_id));
        }
    }

    /// Execute one queued analysis item after routing pending constraint events.
    pub fn step(&mut self) -> bool {
        self.route_constraint_events();
        let Some(work) = self.work.pop_front() else {
            return false;
        };
        let timing_kind = AnalysisWorkTimingKind::from_work(&work);
        let start = Instant::now();
        self.apply_work(work);
        self.timing
            .record_work(timing_kind, start.elapsed(), self.work.len());
        self.route_scc_events();
        true
    }

    pub(super) fn step_traced(&mut self, trace: &mut AnalysisDrainTrace) -> bool {
        trace.route_start();
        let route_elapsed = self.route_constraint_events();
        trace.route(route_elapsed, self.work.len());
        trace.route_done(self.work.len());
        let Some(work) = self.work.pop_front() else {
            return false;
        };
        let kind = analysis_work_kind(&work);
        trace.work(&work, self.work.len());
        if trace.mode == AnalysisTraceMode::Verbose {
            self.trace_work_detail(&work);
        }
        let timing_kind = AnalysisWorkTimingKind::from_work(&work);
        let work_start = Instant::now();
        self.apply_work(work);
        let work_elapsed = work_start.elapsed();
        self.timing
            .record_work(timing_kind, work_elapsed, self.work.len());
        self.route_scc_events();
        trace.work_done(kind, work_elapsed, self.work.len());
        true
    }

    pub(super) fn trace_work_detail(&self, work: &AnalysisWork) {
        match work {
            AnalysisWork::ProbeSelect(select_id) => {
                let name = self.poly.select(*select_id).name.as_str();
                eprintln!("[analysis] work detail: select={select_id:?} name=.{name}");
            }
            AnalysisWork::ApplySelectionResolution { select_id, target } => {
                let name = self.poly.select(*select_id).name.as_str();
                eprintln!(
                    "[analysis] work detail: select={select_id:?} name=.{name} target={target:?}"
                );
            }
            AnalysisWork::ResolveRef(_)
            | AnalysisWork::ApplyRefResolution { .. }
            | AnalysisWork::Scc(_) => {}
        }
    }

    /// Drain SCC events and return the events visible to callers/tests.
    pub fn take_scc_events(&mut self) -> Vec<SccEvent> {
        self.route_scc_events();
        std::mem::take(&mut self.scc_events)
    }

    /// Record how a binding was fetched so generalization can pick the right boundary.
    pub fn record_binding_fetch(&mut self, def: DefId, fetch: BindingFetch) {
        self.binding_fetches.insert(def, fetch);
        self.enqueue(AnalysisWork::Scc(SccInput::DefFetchRecorded { def, fetch }));
    }

    /// Take accumulated analysis diagnostics.
    pub fn take_diagnostics(&mut self) -> Vec<AnalysisDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    #[cfg(test)]
    pub(in crate::analysis) fn take_imported_scheme_instantiation_failures(
        &mut self,
    ) -> Vec<ImportedSchemeInstantiationFailure> {
        std::mem::take(&mut self.imported_scheme_instantiation_failures)
    }

    pub fn timing(&self) -> AnalysisTiming {
        let mut timing = self.timing;
        timing.record_scc_stats(self.scc.stats());
        if let Some(scheduler) = &self.owner_dirty_scheduler {
            scheduler.record_timing(&mut timing);
        }
        timing
    }

    pub(super) fn apply_work(&mut self, work: AnalysisWork) {
        match work {
            AnalysisWork::ResolveRef(_) => {}
            AnalysisWork::ProbeSelect(select_id) => self.probe_select(select_id),
            AnalysisWork::ApplyRefResolution { ref_id, target } => {
                self.poly.resolve_ref(ref_id, target);
                if let Some(use_site) = self.refs.get(ref_id).cloned() {
                    self.apply_scc_input(SccInput::UseResolved {
                        parent: use_site.parent,
                        target,
                        use_value: use_site.value,
                    });
                }
            }
            AnalysisWork::ApplySelectionResolution { select_id, target } => {
                if self.poly.select(select_id).resolution.is_some() {
                    self.remove_unresolved_selection(select_id);
                    return;
                }
                let name = self.poly.select(select_id).name.clone();
                self.poly.resolve_select(select_id, target.resolution());
                let Some(use_site) = self.remove_unresolved_selection(select_id) else {
                    return;
                };
                self.selections.insert_resolved(select_id, use_site.into());
                self.trace_selection_bounds(select_id, &name, use_site);
                match target {
                    SelectionTarget::RecordField => {
                        self.constrain_record_field_selection(use_site.method_value, &name);
                    }
                    SelectionTarget::Method { def } => {
                        self.apply_selection_method_use(use_site, def);
                    }
                    SelectionTarget::EffectMethod { def } => {
                        self.apply_selection_method_use(use_site, def);
                    }
                    SelectionTarget::TypeclassMethod { member } => {
                        self.apply_selection_method_use(use_site, member);
                    }
                }
                self.apply_scc_input(SccInput::MethodDependencyResolved {
                    parent: use_site.parent,
                });
            }
            AnalysisWork::Scc(input) => self.apply_scc_input(input),
        }
    }

    fn apply_selection_method_use(&mut self, use_site: SelectionUse, target: DefId) {
        if target == use_site.parent
            && let Some(self_value) = use_site.recursive_self_value
        {
            self.constrain_open_use(self_value, use_site.method_value);
            return;
        }
        self.apply_scc_input(SccInput::UseResolved {
            parent: use_site.parent,
            target,
            use_value: use_site.method_value,
        });
    }

    pub(super) fn trace_selection_bounds(
        &self,
        select_id: SelectId,
        name: &str,
        use_site: SelectionUse,
    ) {
        if !trace_select_requested(select_id) {
            return;
        }
        let types = self.infer.constraints().types();
        let Some(bounds) = self.infer.constraints().bounds().of(use_site.method_value) else {
            eprintln!(
                "[analysis] select {select_id:?} .{name}: method_value={:?} has no bounds",
                use_site.method_value
            );
            return;
        };
        eprintln!(
            "[analysis] select {select_id:?} .{name}: parent={:?} method_value={:?} receiver_value={:?} receiver_effect={:?} lowers={} uppers={}",
            use_site.parent,
            use_site.method_value,
            use_site.receiver_value,
            use_site.receiver_effect,
            bounds.lowers().len(),
            bounds.uppers().len()
        );
        let limit = trace_select_bound_limit();
        for (index, lower) in bounds.lowers().iter().take(limit).enumerate() {
            eprintln!(
                "[analysis] select {select_id:?} lower[{index}]: pos={:?} {:?} weights={:?}",
                lower.pos,
                types.pos(lower.pos),
                lower.weights
            );
            self.trace_pos_args(select_id, lower.pos);
        }
        for (index, upper) in bounds.uppers().iter().take(limit).enumerate() {
            eprintln!(
                "[analysis] select {select_id:?} upper[{index}]: neg={:?} {:?} weights={:?}",
                upper.neg,
                types.neg(upper.neg),
                upper.weights
            );
        }
        self.trace_var_bounds(
            select_id,
            "receiver",
            use_site.receiver_value,
            trace_select_bound_limit(),
        );
    }

    pub(super) fn trace_var_bounds(
        &self,
        select_id: SelectId,
        label: &str,
        var: TypeVar,
        limit: usize,
    ) {
        let types = self.infer.constraints().types();
        let Some(bounds) = self.infer.constraints().bounds().of(var) else {
            eprintln!("[analysis] select {select_id:?} {label} {var:?}: no bounds");
            return;
        };
        eprintln!(
            "[analysis] select {select_id:?} {label} {var:?}: lowers={} uppers={}",
            bounds.lowers().len(),
            bounds.uppers().len()
        );
        for (index, lower) in bounds.lowers().iter().take(limit).enumerate() {
            eprintln!(
                "[analysis] select {select_id:?} {label} lower[{index}]: pos={:?} {:?} weights={:?}",
                lower.pos,
                types.pos(lower.pos),
                lower.weights
            );
            self.trace_pos_args(select_id, lower.pos);
        }
        for (index, upper) in bounds.uppers().iter().take(limit).enumerate() {
            eprintln!(
                "[analysis] select {select_id:?} {label} upper[{index}]: neg={:?} {:?} weights={:?}",
                upper.neg,
                types.neg(upper.neg),
                upper.weights
            );
        }
    }

    pub(super) fn trace_pos_args(&self, select_id: SelectId, pos: PosId) {
        let types = self.infer.constraints().types();
        let Pos::Con(_, args) = types.pos(pos) else {
            return;
        };
        for (index, arg) in args.iter().enumerate() {
            match types.neu(*arg) {
                Neu::Bounds(lower, upper) => {
                    eprintln!(
                        "[analysis] select {select_id:?} pos {pos:?} arg[{index}] {arg:?}: Bounds({lower:?} {:?}, {upper:?} {:?})",
                        types.pos(*lower),
                        types.neg(*upper)
                    );
                }
                neu => {
                    eprintln!(
                        "[analysis] select {select_id:?} pos {pos:?} arg[{index}] {arg:?}: {neu:?}"
                    );
                }
            }
        }
    }
}
