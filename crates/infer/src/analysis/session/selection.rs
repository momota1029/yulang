use super::*;

impl AnalysisSession {
    pub(super) fn apply_scc_input(&mut self, input: SccInput) {
        match &input {
            SccInput::DefFinished { def } => self.add_unready_role_impl_dependencies(*def),
            SccInput::MethodDependencyResolved { parent } => {
                self.add_unready_role_impl_dependencies(*parent)
            }
            SccInput::UseResolved { .. }
            | SccInput::DependencyAdded { .. }
            | SccInput::RegisterDef { .. }
            | SccInput::DefFetchRecorded { .. }
            | SccInput::MethodDependencyAdded { .. } => {}
        }
        self.apply_scc_to_machine(input);
    }

    pub(super) fn apply_scc_to_machine(&mut self, input: SccInput) {
        let start = Instant::now();
        self.scc.apply(input);
        self.timing.record_scc_apply(start.elapsed());
    }

    pub(super) fn add_unready_role_impl_dependencies(&mut self, parent: DefId) {
        let start = Instant::now();
        let input_count = self.roles.for_owner(parent).len();
        let mut edge_count = 0usize;
        let roles = self
            .roles
            .for_owner(parent)
            .iter()
            .filter(|role| {
                role_constraint_could_resolve(&compact_role_constraint(
                    self.infer.constraints(),
                    role,
                ))
            })
            .map(|role| role.role.clone())
            .collect::<FxHashSet<_>>();
        for role in roles {
            let candidates = self.role_impls.candidates(&role).to_vec();
            for candidate in candidates {
                let Some(impl_def) = candidate.impl_def else {
                    continue;
                };
                for member in self.unready_role_impl_members(impl_def) {
                    edge_count += 1;
                    self.apply_scc_to_machine(SccInput::DependencyAdded {
                        parent,
                        target: member,
                    });
                }
            }
        }
        self.timing
            .record_unready_role_dependency_scan(start.elapsed(), input_count, edge_count);
    }

    pub(super) fn unready_role_impl_members(&self, impl_def: DefId) -> Vec<DefId> {
        self.role_impl_member_sets
            .get(&impl_def)
            .into_iter()
            .flat_map(|members| members.iter().copied())
            .filter(|member| !self.schemes.contains_key(member))
            .collect()
    }

    pub(super) fn probe_select(&mut self, select_id: SelectId) {
        if self.poly.select(select_id).resolution.is_some() {
            self.selections.remove(select_id);
            return;
        }
        let Some(use_site) = self.selections.get(select_id).copied() else {
            return;
        };
        self.selections.mark_receiver_uppers_probed(select_id);
        let name = self.poly.select(select_id).name.clone();
        let receiver_effect = self.infer.alloc_pos(Pos::Var(use_site.receiver_effect));
        let target = self
            .probe_effect_select_pos(select_id, receiver_effect, &name, &mut FxHashSet::default())
            .or_else(|| {
                self.probe_method_value(
                    select_id,
                    use_site.method_value,
                    &name,
                    &mut FxHashSet::default(),
                )
            });
        let Some(target) = target else { return };
        self.enqueue(AnalysisWork::ApplySelectionResolution { select_id, target });
    }

    pub(super) fn resolve_roles_for_unresolved_methods(&mut self) -> bool {
        let mut parents = self
            .selections
            .iter()
            .map(|(_, use_site)| use_site.parent)
            .collect::<Vec<_>>();
        parents.sort_by_key(|def| def.0);
        parents.dedup();
        if parents.is_empty() {
            return false;
        }

        let method_taint_start = Instant::now();
        let method_taint = build_method_taint_index(self);
        self.timing
            .record_method_taint(method_taint_start.elapsed());
        if method_taint.is_empty() {
            return false;
        }

        let mut progressed = false;
        let role_solve_start = Instant::now();
        for def in parents {
            let Some(root) = self.scc.root_of(def) else {
                continue;
            };
            if self.resolve_method_tainted_roles_for_def(def, root, &method_taint) {
                progressed = true;
            }
        }
        self.timing
            .record_method_role_solve(role_solve_start.elapsed());

        if progressed {
            self.route_constraint_events();
            let enqueue_start = Instant::now();
            self.enqueue_unresolved_selection_probes();
            self.timing
                .record_enqueue_selection_probes(enqueue_start.elapsed());
        }
        progressed
    }

    pub(super) fn resolve_method_tainted_roles_for_def(
        &mut self,
        def: DefId,
        root: TypeVar,
        method_taint: &MethodTaintIndex,
    ) -> bool {
        let mut progressed = false;
        let mut applied_merge_constraints = FxHashSet::<CompactMergeConstraintKey>::default();
        loop {
            let (mut compact, merge_constraints) =
                compact_type_var_recording_merge_constraints(self.infer.constraints(), root);
            if apply_compact_merge_constraints(
                self.infer.constraints_mut(),
                merge_constraints,
                &mut applied_merge_constraints,
            ) {
                self.route_constraint_events();
                progressed = true;
                continue;
            }
            normalize_compact_casts(&mut compact, &FxHashSet::default());
            let (roles, role_merge_constraints) =
                self.method_tainted_role_constraints_recording_merge_constraints(def, method_taint);
            if apply_compact_merge_constraints(
                self.infer.constraints_mut(),
                role_merge_constraints,
                &mut applied_merge_constraints,
            ) {
                self.route_constraint_events();
                progressed = true;
                continue;
            }
            let output = resolve_role_constraints_with_method_taint_stats(
                self.infer.constraints(),
                &compact,
                &roles,
                &self.role_impls,
                &self.applied_method_role_resolutions,
                method_taint,
            );
            self.timing.record_role_resolve_stats(output.stats);
            if output.resolutions.is_empty() {
                break;
            }

            for resolution in output.resolutions {
                self.applied_method_role_resolutions
                    .insert(resolution.key.clone());
                self.constrain_role_resolution(def, &resolution);
                progressed = true;
            }
            self.route_constraint_events();
        }
        progressed
    }

    pub(super) fn method_tainted_role_constraints_recording_merge_constraints(
        &self,
        def: DefId,
        method_taint: &MethodTaintIndex,
    ) -> (
        Vec<CompactRoleConstraint>,
        Vec<crate::compact::CompactMergeConstraint>,
    ) {
        let mut merge_constraints = Vec::new();
        let compact = self
            .roles
            .for_owner(def)
            .iter()
            .filter_map(|constraint| {
                let (constraint, constraints) = compact_role_constraint_recording_merge_constraints(
                    self.infer.constraints(),
                    constraint,
                );
                if compact_role_constraint_has_method_taint(&constraint, method_taint) {
                    merge_constraints.extend(constraints);
                    Some(constraint)
                } else {
                    None
                }
            })
            .collect();
        let (roles, coalesce_constraints) =
            coalesce_role_constraints_recording_merge_constraints(compact);
        merge_constraints.extend(coalesce_constraints);
        (roles, merge_constraints)
    }

    pub(super) fn probe_method_value(
        &mut self,
        select_id: SelectId,
        method_value: TypeVar,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        if !visited.insert(method_value) {
            return None;
        }
        let bounds = self.infer.constraints().bounds().of(method_value)?;
        let uppers = bounds
            .uppers()
            .iter()
            .map(|bound| bound.neg)
            .collect::<Vec<_>>();
        for upper in uppers {
            if let Some(target) = self.probe_method_upper(select_id, upper, name, visited) {
                return Some(target);
            }
        }
        None
    }

    pub(super) fn probe_method_upper(
        &mut self,
        select_id: SelectId,
        upper: NegId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        match self.infer.constraints().types().neg(upper).clone() {
            Neg::Var(var) => self.probe_method_value(select_id, var, name, visited),
            Neg::Fun { arg, arg_eff, .. } => self
                .probe_effect_select_pos(select_id, arg_eff, name, &mut FxHashSet::default())
                .or_else(|| self.probe_select_pos(select_id, arg, name, &mut FxHashSet::default())),
            Neg::Intersection(left, right) => self
                .probe_method_upper(select_id, left, name, visited)
                .or_else(|| self.probe_method_upper(select_id, right, name, visited)),
            Neg::Stack { inner, .. } => self.probe_method_upper(select_id, inner, name, visited),
            Neg::Top
            | Neg::Bot
            | Neg::Con(_, _)
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_)
            | Neg::Row(_, _) => None,
        }
    }

    pub(super) fn probe_effect_select_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        let mut paths = Vec::new();
        self.collect_effect_paths_from_pos(select_id, pos, visited, &mut paths);
        self.effect_method_for_paths(select_id, &paths, name)
    }

    pub(super) fn probe_effect_select_stack_weight(
        &self,
        select_id: SelectId,
        weight: &crate::constraints::ConstraintWeight,
        name: &str,
    ) -> Option<SelectionTarget> {
        let mut paths = Vec::new();
        collect_stack_weight_effect_paths(weight, &mut paths);
        self.effect_method_for_paths(select_id, &paths, name)
    }

    pub(super) fn collect_effect_paths_from_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        visited: &mut FxHashSet<TypeVar>,
        out: &mut Vec<Vec<String>>,
    ) {
        match self.infer.constraints().types().pos(pos).clone() {
            Pos::Con(path, _) => push_unique_path(out, path),
            Pos::Row(items) => {
                for item in items {
                    self.collect_effect_paths_from_pos(select_id, item, visited, out);
                }
            }
            Pos::Var(var) => {
                self.probe_effect_select_var_collect(select_id, var, visited, out);
            }
            Pos::Union(left, right) => {
                self.collect_effect_paths_from_pos(select_id, left, visited, out);
                self.collect_effect_paths_from_pos(select_id, right, visited, out);
            }
            Pos::NonSubtract(pos, _) => {
                self.collect_effect_paths_from_pos(select_id, pos, visited, out)
            }
            Pos::Stack { inner, weight } => {
                collect_stack_weight_effect_paths(&weight, out);
                self.collect_effect_paths_from_pos(select_id, inner, visited, out)
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

    pub(super) fn probe_effect_select_var_collect(
        &mut self,
        select_id: SelectId,
        effect: TypeVar,
        visited: &mut FxHashSet<TypeVar>,
        out: &mut Vec<Vec<String>>,
    ) {
        if !visited.insert(effect) {
            return;
        }
        self.selections.watch_effect(effect, select_id);
        for fact in self.infer.constraints().subtracts().facts(effect) {
            collect_subtractability_effect_paths(&fact.subtractability, out);
        }
        if let Some(bounds) = self.infer.constraints().bounds().of(effect) {
            let lowers = bounds
                .lowers()
                .iter()
                .map(|bound| {
                    let mut weighted_paths = Vec::new();
                    collect_constraint_weight_effect_paths(&bound.weights, &mut weighted_paths);
                    (bound.pos, weighted_paths)
                })
                .collect::<Vec<_>>();
            for (lower, weighted_paths) in lowers {
                for path in weighted_paths {
                    push_unique_path(out, path);
                }
                self.collect_effect_paths_from_pos(select_id, lower, visited, out);
            }
        }
    }

    pub(super) fn probe_select_var(
        &mut self,
        select_id: SelectId,
        var: TypeVar,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        if !visited.insert(var) {
            return None;
        }
        self.selections.watch_receiver(var, select_id);
        let lowers = self
            .infer
            .constraints()
            .bounds()
            .of(var)?
            .lowers()
            .iter()
            .map(|bound| {
                let mut weighted_paths = Vec::new();
                collect_constraint_weight_effect_paths(&bound.weights, &mut weighted_paths);
                (bound.pos, weighted_paths)
            })
            .collect::<Vec<_>>();
        let lowers_is_empty = lowers.is_empty();
        for (lower, weighted_paths) in lowers {
            if let Some(target) = self.effect_method_for_paths(select_id, &weighted_paths, name) {
                return Some(target);
            }
            if let Some(target) = self.probe_select_pos(select_id, lower, name, visited) {
                return Some(target);
            }
        }
        if lowers_is_empty {
            let uppers = self
                .infer
                .constraints()
                .bounds()
                .of(var)?
                .uppers()
                .iter()
                .map(|bound| bound.neg)
                .collect::<Vec<_>>();
            return self.probe_select_upper_bounds(select_id, &uppers, name, visited);
        }
        None
    }

    fn probe_select_upper_bounds(
        &mut self,
        select_id: SelectId,
        uppers: &[NegId],
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        let [upper] = uppers else {
            return None;
        };
        let mut targets = Vec::new();
        self.collect_select_upper_targets(select_id, *upper, name, visited, &mut targets);
        match targets.as_slice() {
            [target] => Some(target.clone()),
            [] | [_, ..] => None,
        }
    }

    fn collect_select_upper_targets(
        &mut self,
        select_id: SelectId,
        upper: NegId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
        out: &mut Vec<SelectionTarget>,
    ) {
        match self.infer.constraints().types().neg(upper).clone() {
            Neg::Var(var) => {
                if let Some(target) = self.probe_select_var(select_id, var, name, visited) {
                    if !out.contains(&target) {
                        out.push(target);
                    }
                }
            }
            Neg::Con(path, args) if crate::std_paths::is_control_var_ref_type(&path) => {
                if let Some(target) = self.value_method_for_receiver(select_id, &path, name) {
                    if !out.contains(&target) {
                        out.push(target);
                    }
                    return;
                }
                let Some(payload) = self.ref_payload_probe(&args) else {
                    return;
                };
                if let Some(var) = payload.var {
                    self.selections.watch_ref_payload(var, select_id);
                }
                if let Some(target) = self
                    .probe_ref_select_pos(select_id, payload.lower, name, visited)
                    .or_else(|| {
                        payload.var.and_then(|var| {
                            self.probe_ref_select_var(select_id, var, name, visited)
                        })
                    })
                {
                    if !out.contains(&target) {
                        out.push(target);
                    }
                }
            }
            Neg::Con(path, _) => {
                if let Some(target) = self.value_method_for_receiver(select_id, &path, name) {
                    if !out.contains(&target) {
                        out.push(target);
                    }
                }
            }
            Neg::Intersection(left, right) => {
                self.collect_select_upper_targets(select_id, left, name, visited, out);
                self.collect_select_upper_targets(select_id, right, name, visited, out);
            }
            Neg::Stack { inner, .. } => {
                self.collect_select_upper_targets(select_id, inner, name, visited, out);
            }
            Neg::Top
            | Neg::Bot
            | Neg::Fun { .. }
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_)
            | Neg::Row(_, _) => {}
        }
    }

    pub(super) fn probe_select_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        match self.infer.constraints().types().pos(pos).clone() {
            Pos::Var(var) => self.probe_select_var(select_id, var, name, visited),
            Pos::Con(path, args) if crate::std_paths::is_control_var_ref_type(&path) => {
                if let Some(target) = self.value_method_for_receiver(select_id, &path, name) {
                    return Some(target);
                }
                let payload = self.ref_payload_probe(&args)?;
                if let Some(var) = payload.var {
                    self.selections.watch_ref_payload(var, select_id);
                }
                self.probe_ref_select_pos(select_id, payload.lower, name, visited)
                    .or_else(|| {
                        payload.var.and_then(|var| {
                            self.probe_ref_select_var(select_id, var, name, visited)
                        })
                    })
            }
            Pos::Con(path, _) => self.value_method_for_receiver(select_id, &path, name),
            Pos::Union(left, right) => self
                .probe_select_pos(select_id, left, name, visited)
                .or_else(|| self.probe_select_pos(select_id, right, name, visited)),
            Pos::NonSubtract(pos, _) => self.probe_select_pos(select_id, pos, name, visited),
            Pos::Stack { inner, weight } => self
                .probe_effect_select_stack_weight(select_id, &weight, name)
                .or_else(|| self.probe_select_pos(select_id, inner, name, visited)),
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_) => None,
        }
    }

    pub(super) fn probe_ref_select_var(
        &mut self,
        select_id: SelectId,
        var: TypeVar,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        if !visited.insert(var) {
            return None;
        }
        let lowers = self
            .infer
            .constraints()
            .bounds()
            .of(var)?
            .lowers()
            .iter()
            .map(|bound| bound.pos)
            .collect::<Vec<_>>();
        for lower in lowers {
            if let Some(target) = self.probe_ref_select_pos(select_id, lower, name, visited) {
                return Some(target);
            }
        }
        None
    }

    pub(super) fn probe_ref_select_pos(
        &mut self,
        select_id: SelectId,
        pos: PosId,
        name: &str,
        visited: &mut FxHashSet<TypeVar>,
    ) -> Option<SelectionTarget> {
        match self.infer.constraints().types().pos(pos).clone() {
            Pos::Var(var) => self.probe_ref_select_var(select_id, var, name, visited),
            Pos::Con(path, _) => self.ref_method_for_receiver(select_id, &path, name),
            Pos::Union(left, right) => self
                .probe_ref_select_pos(select_id, left, name, visited)
                .or_else(|| self.probe_ref_select_pos(select_id, right, name, visited)),
            Pos::NonSubtract(pos, _) => self.probe_ref_select_pos(select_id, pos, name, visited),
            Pos::Stack { inner, .. } => self.probe_ref_select_pos(select_id, inner, name, visited),
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_) => None,
        }
    }

    pub(super) fn value_method_for_receiver(
        &self,
        select_id: SelectId,
        receiver: &[String],
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            let candidates = self
                .local_methods
                .value_type_candidates(scope, receiver, name);
            if let Some(target) = method_target_from_candidates(candidates) {
                return Some(target);
            }
        }
        let candidates = self.methods.value_candidates(receiver, name);
        method_target_from_candidates(candidates)
    }

    pub(super) fn ref_method_for_receiver(
        &self,
        select_id: SelectId,
        receiver: &[String],
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            let candidates = self
                .local_methods
                .ref_type_candidates(scope, receiver, name);
            if let Some(target) = method_target_from_candidates(candidates) {
                return Some(target);
            }
        }
        let candidates = self.methods.ref_candidates(receiver, name);
        method_target_from_candidates(candidates)
    }

    pub(super) fn effect_method_for_paths(
        &self,
        select_id: SelectId,
        effects: &[Vec<String>],
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            let candidates = self
                .local_methods
                .effect_candidates(scope, name)
                .iter()
                .filter(|candidate| effects.iter().any(|effect| effect == &candidate.effect))
                .collect::<Vec<_>>();
            if let Some(target) = effect_method_target_from_candidates(&candidates) {
                return Some(target);
            }
        }
        let candidates = self
            .effect_methods
            .candidates(name)
            .iter()
            .filter(|candidate| effects.iter().any(|effect| effect == &candidate.effect))
            .collect::<Vec<_>>();
        effect_method_target_from_candidates(&candidates)
    }

    pub(super) fn role_method_for_select(
        &self,
        select_id: SelectId,
        name: &str,
    ) -> Option<SelectionTarget> {
        if let Some(scope) = self.local_method_scope(select_id) {
            match self.local_methods.role_candidates(scope, name) {
                [candidate] => {
                    return Some(SelectionTarget::TypeclassMethod {
                        member: candidate.def,
                    });
                }
                [] | [_, ..] => {}
            }
        }
        match self.role_methods.candidates(name) {
            [candidate] => Some(SelectionTarget::TypeclassMethod {
                member: candidate.def,
            }),
            [] | [_, ..] => None,
        }
    }

    pub(super) fn local_method_scope(&self, select_id: SelectId) -> Option<crate::ModuleId> {
        self.selections
            .get(select_id)
            .and_then(|use_site| use_site.local_method_scope)
    }

    pub(super) fn ref_payload_probe(
        &mut self,
        args: &[poly::types::NeuId],
    ) -> Option<RefPayloadProbe> {
        let payload = args.get(1)?;
        match self.infer.constraints().types().neu(*payload).clone() {
            Neu::Bounds(lower, upper) => Some(RefPayloadProbe {
                lower,
                var: self.bounds_common_var(lower, upper),
            }),
            neu => Some(RefPayloadProbe {
                lower: self.pos_from_neu(neu),
                var: None,
            }),
        }
    }

    pub(super) fn bounds_common_var(&self, lower: PosId, upper: NegId) -> Option<TypeVar> {
        let types = self.infer.constraints().types();
        let mut lower_vars = Vec::new();
        collect_pos_top_vars(types, lower, &mut lower_vars);
        lower_vars.sort_by_key(|var| var.0);
        lower_vars.dedup();
        let mut upper_vars = Vec::new();
        collect_neg_top_vars(types, upper, &mut upper_vars);
        upper_vars.sort_by_key(|var| var.0);
        upper_vars.dedup();
        let common = lower_vars
            .into_iter()
            .filter(|var| upper_vars.contains(var))
            .collect::<Vec<_>>();
        (common.len() == 1).then(|| common[0])
    }

    pub(super) fn constrain_record_field_selection(&mut self, method_value: TypeVar, name: &str) {
        let constraints = self.record_field_selection_constraints(method_value, name);
        self.infer.subtypes(constraints);
    }

    pub(super) fn record_field_selection_constraints(
        &mut self,
        method_value: TypeVar,
        name: &str,
    ) -> Vec<(PosId, NegId)> {
        let mut constraints = Vec::new();
        self.collect_record_field_selection_constraints(method_value, name, &mut constraints);
        constraints
    }

    fn collect_record_field_selection_constraints(
        &mut self,
        method_value: TypeVar,
        name: &str,
        out: &mut Vec<(PosId, NegId)>,
    ) {
        let Some(bounds) = self.infer.constraints().bounds().of(method_value) else {
            return;
        };
        let uppers = bounds
            .uppers()
            .iter()
            .map(|bound| bound.neg)
            .collect::<Vec<_>>();
        for upper in uppers {
            self.collect_record_field_selection_constraints_from_method_upper(upper, name, out);
        }
    }

    fn collect_record_field_selection_constraints_from_method_upper(
        &mut self,
        upper: NegId,
        name: &str,
        out: &mut Vec<(PosId, NegId)>,
    ) {
        match self.infer.constraints().types().neg(upper).clone() {
            Neg::Var(var) => self.collect_record_field_selection_constraints(var, name, out),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => self.collect_record_field_call_constraints(arg, arg_eff, ret_eff, ret, name, out),
            Neg::Intersection(left, right) => {
                self.collect_record_field_selection_constraints_from_method_upper(left, name, out);
                self.collect_record_field_selection_constraints_from_method_upper(right, name, out);
            }
            Neg::Stack { inner, .. } => {
                self.collect_record_field_selection_constraints_from_method_upper(inner, name, out);
            }
            Neg::Top
            | Neg::Bot
            | Neg::Con(_, _)
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_)
            | Neg::Row(_, _) => {}
        }
    }

    fn collect_record_field_call_constraints(
        &mut self,
        receiver: PosId,
        receiver_effect: PosId,
        result_effect: NegId,
        result: NegId,
        name: &str,
        out: &mut Vec<(PosId, NegId)>,
    ) {
        let field = RecordField {
            name: name.to_string(),
            value: result,
            optional: false,
        };
        let record = self.infer.alloc_neg(Neg::Record(vec![field]));
        out.push((receiver, record));
        out.push((receiver_effect, result_effect));
    }

    pub(super) fn route_scc_events(&mut self) {
        let route_start = Instant::now();
        let events = self.scc.take_events();
        let event_count = events.len();
        self.record_instantiate_event_runs(&events);
        let mut events = events.into_iter().peekable();
        while let Some(event) = events.next() {
            let kind = scc_event_timing_kind(&event);
            let event_start = Instant::now();
            match event {
                SccEvent::InstantiateUse {
                    parent,
                    target,
                    use_value,
                } => {
                    let mut batch = vec![SccInstantiateUse {
                        parent,
                        target,
                        use_value,
                    }];
                    while matches!(events.peek(), Some(SccEvent::InstantiateUse { .. })) {
                        let Some(SccEvent::InstantiateUse {
                            parent,
                            target,
                            use_value,
                        }) = events.next()
                        else {
                            unreachable!("peeked instantiate use event");
                        };
                        batch.push(SccInstantiateUse {
                            parent,
                            target,
                            use_value,
                        });
                    }
                    for use_site in &batch {
                        let was_new = self.instantiated_targets.insert(use_site.target);
                        self.timing.record_instantiate_target(was_new);
                    }
                    let batch_len = batch.len();
                    self.instantiate_use_batch(&batch);
                    for use_site in batch {
                        self.scc_events.push(SccEvent::InstantiateUse {
                            parent: use_site.parent,
                            target: use_site.target,
                            use_value: use_site.use_value,
                        });
                    }
                    self.timing.record_route_scc_event_batch(
                        kind,
                        event_start.elapsed(),
                        batch_len,
                    );
                    continue;
                }
                SccEvent::OpenUse {
                    target,
                    target_root,
                    use_value,
                } => {
                    self.constrain_open_use(target_root, use_value);
                    self.scc_events.push(SccEvent::OpenUse {
                        target,
                        target_root,
                        use_value,
                    });
                }
                SccEvent::QuantifyComponent { component, roots } => {
                    self.quantify_component(&component, &roots);
                    self.scc_events
                        .push(SccEvent::QuantifyComponent { component, roots });
                }
                SccEvent::ComputedFetchCycle {
                    component,
                    parent,
                    target,
                } => {
                    self.diagnostics
                        .push(AnalysisDiagnostic::ComputedFetchCycle {
                            component: component.clone(),
                            parent,
                            target,
                        });
                    self.scc_events.push(SccEvent::ComputedFetchCycle {
                        component,
                        parent,
                        target,
                    });
                }
                other => self.scc_events.push(other),
            }
            self.timing
                .record_route_scc_event(kind, event_start.elapsed());
        }
        self.timing
            .record_route_scc_events(route_start.elapsed(), event_count);
    }

    fn record_instantiate_event_runs(&mut self, events: &[SccEvent]) {
        let mut run_len = 0usize;
        for event in events {
            if matches!(event, SccEvent::InstantiateUse { .. }) {
                run_len += 1;
                continue;
            }
            self.timing.record_instantiate_event_run(run_len);
            run_len = 0;
        }
        self.timing.record_instantiate_event_run(run_len);
    }
}

fn scc_event_timing_kind(event: &SccEvent) -> AnalysisSccEventTimingKind {
    match event {
        SccEvent::OpenUse { .. } => AnalysisSccEventTimingKind::OpenUse,
        SccEvent::QuantifyComponent { .. } => AnalysisSccEventTimingKind::Quantify,
        SccEvent::InstantiateUse { .. } => AnalysisSccEventTimingKind::Instantiate,
        SccEvent::ComponentEdgeAdded { .. }
        | SccEvent::MergeComponents { .. }
        | SccEvent::ComputedFetchCycle { .. } => AnalysisSccEventTimingKind::Other,
    }
}
