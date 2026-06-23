use super::*;

impl AnalysisSession {
    pub fn new(poly: PolyArena) -> Self {
        let mut session = Self {
            poly,
            infer: InferArena::new(),
            local_defs: LocalDefUseTable::new(),
            refs: RefUseTable::new(),
            selections: SelectionUseTable::new(),
            roles: RoleConstraintTable::new(),
            role_impls: RoleImplTable::new(),
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
            applied_method_role_resolutions: FxHashSet::default(),
            schemes: FxHashMap::default(),
            binding_fetches: FxHashMap::default(),
            diagnostics: Vec::new(),
            scc_events: Vec::new(),
            work: VecDeque::new(),
            timing: AnalysisTiming::default(),
            instantiated_targets: FxHashSet::default(),
            def_parent_map: DefParentMapCache::default(),
        };
        session.seed_existing_poly_surface();
        session
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
        for def in quantified_defs {
            self.scc.seed_quantified_def(def);
        }

        for rule in &self.poly.cast_rules {
            self.casts.insert(
                rule.source.clone(),
                rule.target.clone(),
                rule.scheme.clone(),
            );
        }

        let role_impls = self.poly.role_impls.iter().cloned().collect::<Vec<_>>();
        for candidate in role_impls {
            let candidate =
                freshen_role_impl_candidate(&self.poly.typ, &mut self.infer, &candidate);
            self.role_impls.insert(candidate);
        }
    }

    /// Queue a unit of analysis work without draining it immediately.
    pub fn enqueue(&mut self, work: AnalysisWork) {
        self.work.push_back(work);
    }

    /// Register a selection use-site and schedule its initial method probe.
    pub fn register_selection_use(&mut self, select_id: SelectId, use_site: SelectionUse) {
        self.selections.insert(select_id, use_site);
        self.enqueue(AnalysisWork::Scc(SccInput::MethodDependencyAdded {
            parent: use_site.parent,
        }));
        self.enqueue(AnalysisWork::ProbeSelect(select_id));
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
                ConstraintEvent::NominalCastNeeded {
                    lower,
                    upper,
                    source,
                    target,
                    weights,
                } => {
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
                ConstraintEvent::UpperBoundAdded { .. } => {}
            }
        }
        let elapsed = start.elapsed();
        self.timing.record_route_constraints(elapsed, event_count);
        elapsed
    }

    /// Drain queued analysis work until method-role solving reaches a fixed point.
    pub fn drain_work(&mut self) {
        let mut trace = AnalysisDrainTrace::from_env(self.work.len());
        loop {
            while self.step_traced(&mut trace) {}
            trace.before_role_pass(self.selections.unresolved().count(), self.work.len());
            let role_start = Instant::now();
            let progressed = self.resolve_roles_for_unresolved_methods();
            self.timing
                .record_role_pass(role_start.elapsed(), progressed);
            trace.after_role_pass(
                progressed,
                self.selections.unresolved().count(),
                self.work.len(),
            );
            if !progressed {
                break;
            }
        }
        trace.finish(self.work.len());
    }

    /// Resolve still-unresolved selections as record fields once their SCC is ready.
    pub fn resolve_unresolved_selections_as_record_fields(&mut self) {
        loop {
            self.drain_work();
            let mut ready = self
                .selections
                .iter()
                .filter_map(|(select_id, use_site)| {
                    if !self.scc.selection_fallback_ready(use_site.parent) {
                        return None;
                    }
                    let name = self.poly.select(select_id).name.clone();
                    let target = self
                        .role_method_for_select(select_id, &name)
                        .unwrap_or(SelectionTarget::RecordField);
                    Some((select_id, target))
                })
                .collect::<Vec<_>>();
            ready.sort_by_key(|(select_id, _)| select_id.0);
            let record_fields = ready
                .iter()
                .filter_map(|(select_id, target)| {
                    matches!(target, SelectionTarget::RecordField).then_some(*select_id)
                })
                .collect::<Vec<_>>();
            if !record_fields.is_empty() {
                self.apply_record_field_selection_batch(record_fields);
                continue;
            }
            let Some((select_id, target)) = ready.first().cloned() else {
                break;
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
        }
    }

    fn fallback_target_can_batch(&self, target: &SelectionTarget) -> bool {
        match target {
            SelectionTarget::RecordField => true,
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
                self.selections.remove(select_id);
                continue;
            }
            let name = self.poly.select(select_id).name.clone();
            self.poly
                .resolve_select(select_id, SelectionTarget::RecordField.resolution());
            let Some(use_site) = self.selections.remove(select_id) else {
                continue;
            };
            self.trace_selection_bounds(select_id, &name, use_site);
            constraints
                .extend(self.record_field_selection_constraints(use_site.method_value, &name));
            resolved_parents.push(use_site.parent);
        }
        let constraint_count = constraints.len();
        self.infer.subtypes(constraints);
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

    pub fn timing(&self) -> AnalysisTiming {
        let mut timing = self.timing;
        timing.record_scc_stats(self.scc.stats());
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
                    self.selections.remove(select_id);
                    return;
                }
                let name = self.poly.select(select_id).name.clone();
                self.poly.resolve_select(select_id, target.resolution());
                let Some(use_site) = self.selections.remove(select_id) else {
                    return;
                };
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
        self.route_scc_events();
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
