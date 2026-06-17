use super::*;

impl AnalysisSession {
    pub(in crate::analysis) fn generalize_root_with_prepasses(
        &mut self,
        def: DefId,
        root: TypeVar,
    ) -> GeneralizedCompactRoot {
        let trace = analysis_trace_mode();
        let start = Instant::now();
        let quantification_boundary = self.generalize_boundary(def);
        let simplification_boundary = TypeLevel::root().child();
        let mut applied_casts = FxHashSet::<CompactCastKey>::default();
        let mut applied_roles = self.applied_method_role_resolutions.clone();
        let mut applied_role_demands = self
            .applied_method_role_resolutions
            .iter()
            .map(|key| key.demand.clone())
            .collect::<FxHashSet<_>>();
        let mut applied_merge_constraints = FxHashSet::<CompactMergeConstraintKey>::default();
        let mut applied_subtype_constraints = FxHashSet::<CompactSubtypeConstraintKey>::default();
        let mut compact;
        let coalesced_roles = loop {
            self.timing.record_generalize_iteration();
            let phase = Instant::now();
            let (next_compact, mut merge_constraints) =
                compact_type_var_recording_merge_constraints_for_scheme(
                    self.infer.constraints(),
                    root,
                );
            let elapsed = phase.elapsed();
            self.timing.record_generalize_compact(elapsed);
            trace_generalize_phase(trace, "compact", def, elapsed, start);
            let phase = Instant::now();
            let role_input_count = self.roles.for_owner(def).len();
            let (role_constraints, role_collect_constraints) = if role_input_count == 0 {
                (Vec::new(), Vec::new())
            } else {
                compact_reachable_role_constraints_recording_merge_constraints(
                    self.infer.constraints(),
                    &next_compact,
                    self.roles.for_owner(def),
                )
            };
            let reachable_role_count = role_constraints.len();
            let (coalesced_role_constraints, role_coalesce_constraints) =
                coalesce_role_constraints_recording_merge_constraints(role_constraints);
            self.timing.record_generalize_role_constraints(
                role_input_count,
                reachable_role_count,
                coalesced_role_constraints.len(),
            );
            let elapsed = phase.elapsed();
            self.timing.record_generalize_collect_roles(elapsed);
            trace_generalize_phase(trace, "collect roles", def, elapsed, start);
            merge_constraints.extend(role_collect_constraints);
            merge_constraints.extend(role_coalesce_constraints);
            compact = next_compact;
            let phase = Instant::now();
            let merge_constraint_count = merge_constraints.len();
            if apply_compact_merge_constraints(
                self.infer.constraints_mut(),
                merge_constraints,
                &mut applied_merge_constraints,
            ) {
                self.timing.record_generalize_merge_restart();
                let elapsed = phase.elapsed();
                self.timing
                    .record_generalize_apply_merge(elapsed, merge_constraint_count);
                trace_generalize_phase(trace, "apply merge constraints", def, elapsed, start);
                trace_generalize_count(
                    trace,
                    "merge constraints",
                    def,
                    merge_constraint_count,
                    elapsed,
                    start,
                );
                self.route_constraint_events();
                continue;
            }
            let elapsed = phase.elapsed();
            self.timing
                .record_generalize_apply_merge(elapsed, merge_constraint_count);
            trace_generalize_phase(trace, "apply merge constraints", def, elapsed, start);
            trace_generalize_count(
                trace,
                "merge constraints",
                def,
                merge_constraint_count,
                elapsed,
                start,
            );
            let phase = Instant::now();
            let mut dominance_compact = compact.clone();
            let mut dominance_roles = coalesced_role_constraints.clone();
            self.timing
                .record_generalize_dominance_roles(dominance_roles.len());
            simplify_compact_root_with_roles_and_non_generic(
                self.infer.constraints(),
                simplification_boundary,
                &mut dominance_compact,
                &mut dominance_roles,
                &FxHashSet::default(),
            );
            coalesce_floor_interval_equalities(
                self.infer.constraints(),
                TypeLevel::root(),
                &mut dominance_compact,
                &mut dominance_roles,
            );
            let subtype_constraints =
                collect_interval_dominance_constraints(&dominance_compact, &dominance_roles);
            let subtype_constraint_count = subtype_constraints.len();
            let elapsed = phase.elapsed();
            self.timing.record_generalize_collect_dominance(elapsed);
            trace_generalize_phase(trace, "collect dominance", def, elapsed, start);
            let phase = Instant::now();
            if apply_compact_subtype_constraints(
                self.infer.constraints_mut(),
                subtype_constraints,
                &mut applied_subtype_constraints,
            ) {
                self.timing.record_generalize_subtype_restart();
                let elapsed = phase.elapsed();
                self.timing
                    .record_generalize_apply_subtype(elapsed, subtype_constraint_count);
                trace_generalize_phase(trace, "apply subtype constraints", def, elapsed, start);
                self.route_constraint_events();
                continue;
            }
            let elapsed = phase.elapsed();
            self.timing
                .record_generalize_apply_subtype(elapsed, subtype_constraint_count);
            trace_generalize_phase(trace, "apply subtype constraints", def, elapsed, start);
            let phase = Instant::now();
            normalize_compact_casts(&mut compact, &applied_casts);
            if let Some(batch) = find_next_compact_cast(&compact, &self.casts, &applied_casts) {
                let application_count = batch.applications.len();
                for application in &batch.applications {
                    self.constrain_compact_cast(application);
                }
                self.timing.record_generalize_cast_restart();
                self.timing
                    .record_generalize_cast(phase.elapsed(), 1, application_count);
                applied_casts.insert(batch.key);
                self.route_constraint_events();
                continue;
            }
            self.timing.record_generalize_cast(phase.elapsed(), 0, 0);

            let phase = Instant::now();
            let resolutions = self
                .simplified_coalesced_role_constraints(
                    &compact,
                    &coalesced_role_constraints,
                    simplification_boundary,
                )
                .map(|(role_compact, roles)| {
                    self.timing
                        .record_generalize_role_resolve_inputs(roles.len());
                    resolve_role_constraints(
                        self.infer.constraints(),
                        &role_compact,
                        &roles,
                        &self.role_impls,
                        &applied_roles,
                    )
                })
                .unwrap_or_default();
            let resolution_count = resolutions.len();
            let elapsed = phase.elapsed();
            self.timing
                .record_generalize_resolve_roles(elapsed, resolution_count);
            trace_generalize_phase(trace, "resolve roles", def, elapsed, start);
            if !resolutions.is_empty() {
                self.timing.record_generalize_role_restart();
                for resolution in resolutions {
                    applied_roles.insert(resolution.key.clone());
                    self.collect_resolved_role_demands(&resolution, &mut applied_role_demands);
                    self.constrain_role_resolution(def, &resolution);
                }
                self.route_constraint_events();
                continue;
            }
            break coalesced_role_constraints;
        };

        let applied_role_candidates = applied_roles
            .iter()
            .map(|key| key.candidate.clone())
            .collect::<FxHashSet<_>>();
        // ループ中に適用した demand は簡約済みビューの表記なので、生の述語と一致しない
        // ことがある。再判定はループ末尾と同じ「主型＋全 role」一括簡約ビューで行う。
        // role 単独で簡約すると共起が減って併合が強く効きすぎ、ループでは適用されなかった
        // 解決をここで初めて作ってしまう（制約を注入せずに述語だけ消える）恐れがある。
        let phase = Instant::now();
        let applied_in_simplified_view =
            if applied_role_candidates.is_empty() && applied_role_demands.is_empty() {
                vec![false; coalesced_roles.len()]
            } else {
                self.simplified_role_predicates_already_applied(
                    &compact,
                    &coalesced_roles,
                    &applied_role_candidates,
                    &applied_role_demands,
                    simplification_boundary,
                )
            };
        let mut role_predicates: Vec<CompactRoleConstraint> = coalesced_roles
            .into_iter()
            .zip(applied_in_simplified_view)
            .filter_map(|(role, applied)| {
                (!applied && !applied_role_demands.contains(&role)).then_some(role)
            })
            .collect();
        self.timing.record_generalize_final_roles(phase.elapsed());

        let phase = Instant::now();
        let simplifications = self
            .role_impl_member_simplifications
            .get(&def)
            .cloned()
            .unwrap_or_default();
        apply_compact_simplifications_to_root_and_roles(
            &mut compact,
            &mut role_predicates,
            &simplifications,
        );
        // simplify の level 保護（boundary.child()）が触れない床下の変数は、不変区間の
        // 両側出現で等値が確定しているものだけ、世代化の確定直前にここで併合する。
        let floor_substitutions = coalesce_floor_interval_equalities(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut compact,
            &mut role_predicates,
        );
        let floor_variable_substitutions = coalesce_floor_variable_sandwiches(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut compact,
            &mut role_predicates,
        );
        let floor_redundant_substitutions = eliminate_floor_redundant_variables(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut compact,
            &mut role_predicates,
        );
        let elapsed = phase.elapsed();
        self.timing.record_generalize_final_cleanup(elapsed);
        trace_generalize_phase(trace, "final compact cleanup", def, elapsed, start);
        if !role_predicates.is_empty()
            && (!applied_role_candidates.is_empty() || !applied_role_demands.is_empty())
        {
            let phase = Instant::now();
            let applied_after_final_simplification = self
                .simplified_role_predicates_already_applied(
                    &compact,
                    &role_predicates,
                    &applied_role_candidates,
                    &applied_role_demands,
                    simplification_boundary,
                );
            role_predicates = role_predicates
                .into_iter()
                .zip(applied_after_final_simplification)
                .filter_map(|(role, applied)| {
                    (!applied && !applied_role_demands.contains(&role)).then_some(role)
                })
                .collect();
            let elapsed = phase.elapsed();
            self.timing.record_generalize_filter_roles(elapsed);
            trace_generalize_phase(trace, "filter applied roles", def, elapsed, start);
        }

        let phase = Instant::now();
        let mut generalized = generalize_prepared_compact_root_with_role_variances_and_boundaries(
            self.infer.constraints(),
            quantification_boundary,
            simplification_boundary,
            compact,
            role_predicates,
            &self.role_input_variances,
            &FxHashSet::default(),
        );
        let elapsed = phase.elapsed();
        self.timing.record_generalize_prepared(elapsed);
        trace_generalize_phase(trace, "generalize prepared", def, elapsed, start);
        if !floor_substitutions.is_empty()
            || !floor_variable_substitutions.is_empty()
            || !floor_redundant_substitutions.is_empty()
        {
            let mut combined = floor_substitutions;
            combined.extend(floor_variable_substitutions);
            combined.extend(floor_redundant_substitutions);
            combined.extend(generalized.substitutions);
            generalized.substitutions = normalize_var_substitutions(combined);
        }
        generalized
    }

    #[cfg(test)]
    pub(in crate::analysis) fn simplified_reachable_role_constraints(
        &self,
        def: DefId,
        compact: &crate::compact::CompactRoot,
        simplification_boundary: TypeLevel,
    ) -> Option<(crate::compact::CompactRoot, Vec<CompactRoleConstraint>)> {
        if self.roles.for_owner(def).is_empty() {
            return None;
        }
        let mut roles = coalesce_role_constraints(compact_reachable_role_constraints(
            self.infer.constraints(),
            compact,
            self.roles.for_owner(def),
        ));
        if roles.is_empty() {
            return None;
        }
        let mut role_compact = compact.clone();
        simplify_compact_root_with_roles_and_non_generic(
            self.infer.constraints(),
            simplification_boundary,
            &mut role_compact,
            &mut roles,
            &FxHashSet::default(),
        );
        coalesce_floor_interval_equalities(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut role_compact,
            &mut roles,
        );
        eliminate_floor_redundant_variables(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut role_compact,
            &mut roles,
        );
        Some((role_compact, roles))
    }

    fn simplified_coalesced_role_constraints(
        &self,
        compact: &crate::compact::CompactRoot,
        coalesced_roles: &[CompactRoleConstraint],
        simplification_boundary: TypeLevel,
    ) -> Option<(crate::compact::CompactRoot, Vec<CompactRoleConstraint>)> {
        if coalesced_roles.is_empty() {
            return None;
        }
        let mut role_compact = compact.clone();
        let mut roles = coalesced_roles.to_vec();
        simplify_compact_root_with_roles_and_non_generic(
            self.infer.constraints(),
            simplification_boundary,
            &mut role_compact,
            &mut roles,
            &FxHashSet::default(),
        );
        coalesce_floor_interval_equalities(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut role_compact,
            &mut roles,
        );
        eliminate_floor_redundant_variables(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut role_compact,
            &mut roles,
        );
        Some((role_compact, roles))
    }

    /// 世代化の最終出力から落としてよい残置述語を、入力 role と同じ並びの bool 列で返す。
    /// true は簡約済み全体ビューで「適用済み demand と一致する」か
    /// 「適用済み impl 候補へ一意に解決する」。
    pub(super) fn simplified_role_predicates_already_applied(
        &self,
        compact: &crate::compact::CompactRoot,
        role_predicates: &[CompactRoleConstraint],
        applied_candidates: &FxHashSet<CompactRoleConstraint>,
        applied_demands: &FxHashSet<CompactRoleConstraint>,
        simplification_boundary: TypeLevel,
    ) -> Vec<bool> {
        let mut role_compact = compact.clone();
        let mut simplified_roles = role_predicates.to_vec();
        simplify_compact_root_with_roles_and_non_generic(
            self.infer.constraints(),
            simplification_boundary,
            &mut role_compact,
            &mut simplified_roles,
            &FxHashSet::default(),
        );
        if applied_candidates.is_empty() {
            return simplified_roles
                .iter()
                .map(|role| applied_demands.contains(role))
                .collect();
        }
        let resolved_demands = resolve_role_constraints(
            self.infer.constraints(),
            &role_compact,
            &simplified_roles,
            &self.role_impls,
            &FxHashSet::default(),
        )
        .into_iter()
        .filter(|resolution| {
            applied_candidates.iter().any(|candidate| {
                Self::same_role_candidate_identity(candidate, &resolution.candidate)
            })
        })
        .map(|resolution| resolution.demand)
        .collect::<FxHashSet<_>>();
        simplified_roles
            .iter()
            .map(|role| applied_demands.contains(role) || resolved_demands.contains(role))
            .collect()
    }

    pub(super) fn generalize_boundary(&self, def: DefId) -> TypeLevel {
        self.binding_fetch(def)
            .generalize_boundary(TypeLevel::root())
    }

    pub(super) fn binding_fetch(&self, def: DefId) -> BindingFetch {
        self.binding_fetches
            .get(&def)
            .copied()
            .unwrap_or_else(|| self.scc.fetch_of(def))
    }

    pub(super) fn collect_resolved_role_demands(
        &self,
        resolution: &RoleResolution,
        out: &mut FxHashSet<crate::compact::CompactRoleConstraint>,
    ) {
        out.insert(resolution.demand.clone());
        for prerequisite in &resolution.solved_prerequisites {
            self.collect_resolved_role_demands(prerequisite, out);
        }
    }

    pub(super) fn same_role_candidate_identity(
        left: &CompactRoleConstraint,
        right: &CompactRoleConstraint,
    ) -> bool {
        left.role == right.role && left.inputs == right.inputs
    }

    pub(super) fn constrain_role_resolution(&mut self, def: DefId, resolution: &RoleResolution) {
        for prerequisite in &resolution.solved_prerequisites {
            self.constrain_role_resolution(def, prerequisite);
        }
        for prerequisite in &resolution.residual_prerequisites {
            self.insert_residual_role_constraint(def, prerequisite);
        }
        for (demand, candidate) in resolution
            .demand
            .inputs
            .iter()
            .zip(&resolution.candidate.inputs)
        {
            self.constrain_role_arg_equal(demand, candidate);
        }
        for demand in &resolution.demand.associated {
            let Some(candidate) = resolution
                .candidate
                .associated
                .iter()
                .find(|candidate| candidate.name == demand.name)
            else {
                continue;
            };
            self.constrain_role_arg_equal(&demand.value, &candidate.value);
        }
    }

    pub(super) fn insert_residual_role_constraint(
        &mut self,
        def: DefId,
        constraint: &crate::compact::CompactRoleConstraint,
    ) {
        let constraint = self.finalize_compact_role_constraint(constraint);
        if !self.roles.for_owner(def).contains(&constraint) {
            self.roles.insert(def, constraint);
        }
    }

    pub(super) fn finalize_compact_role_constraint(
        &mut self,
        constraint: &crate::compact::CompactRoleConstraint,
    ) -> RoleConstraint {
        RoleConstraint {
            role: constraint.role.clone(),
            inputs: constraint
                .inputs
                .iter()
                .map(|arg| self.finalize_compact_role_arg(arg))
                .collect(),
            associated: constraint
                .associated
                .iter()
                .map(|associated| RoleAssociatedConstraint {
                    name: associated.name.clone(),
                    value: self.finalize_compact_role_arg(&associated.value),
                })
                .collect(),
        }
    }

    pub(super) fn finalize_compact_role_arg(&mut self, arg: &CompactRoleArg) -> RoleConstraintArg {
        let neu = finalize_compact_bounds_to_constraint(self.infer.constraints_mut(), &arg.bounds);
        self.role_arg_from_neu(neu)
    }

    pub(super) fn constrain_role_arg_equal(
        &mut self,
        demand: &CompactRoleArg,
        candidate: &CompactRoleArg,
    ) {
        let (candidate, demand) = {
            let constraints = self.infer.constraints_mut();
            let candidate = finalize_compact_bounds_to_constraint(constraints, &candidate.bounds);
            let demand = finalize_compact_bounds_to_constraint(constraints, &demand.bounds);
            (candidate, demand)
        };
        self.infer
            .constraints_mut()
            .constrain_invariant_neu(candidate, demand);
    }

    pub(super) fn constrain_compact_cast(&mut self, application: &CompactCastApplication) {
        let lower = finalize_compact_type_to_pos_constraint(
            self.infer.constraints_mut(),
            &application.source,
        );
        let upper = finalize_compact_type_to_neg_constraint(
            self.infer.constraints_mut(),
            &application.target,
        );
        self.constrain_nominal_cast(
            lower,
            upper,
            &application.key.source,
            &application.key.target,
            ConstraintWeights::empty(),
        );
    }

    pub(super) fn constrain_nominal_cast(
        &mut self,
        lower: PosId,
        upper: NegId,
        source: &[String],
        target: &[String],
        weights: crate::constraints::ConstraintWeights,
    ) {
        let candidates = self.casts.candidates(source, target).to_vec();
        if candidates.is_empty() {
            return;
        }
        for candidate in candidates {
            let predicate = instantiate_scheme(
                &self.poly.typ,
                &mut self.infer,
                TypeLevel::secondary(),
                &candidate.scheme,
            );
            let arg_eff = self.infer.alloc_pos(Pos::Bot);
            let ret_eff = self.infer.alloc_neg(Neg::Top);
            let expected_cast = self.infer.alloc_neg(Neg::Fun {
                arg: lower,
                arg_eff,
                ret_eff,
                ret: upper,
            });
            self.infer
                .weighted_subtype(predicate, weights.clone(), expected_cast);
        }
    }

    pub(super) fn scheme_ancestors(
        &self,
        def: DefId,
        parents: &FxHashMap<DefId, DefId>,
    ) -> Vec<GeneralizedCompactRoot> {
        let mut chain = Vec::new();
        let mut current = def;
        while let Some(parent) = parents.get(&current).copied() {
            chain.push(parent);
            current = parent;
        }
        chain.reverse();
        chain
            .into_iter()
            .filter_map(|ancestor| self.schemes.get(&ancestor).cloned())
            .collect()
    }

    pub(super) fn set_def_scheme(&mut self, def: DefId, scheme: poly::types::Scheme) {
        let Some(Def::Let { scheme: target, .. }) = self.poly.defs.get_mut(def) else {
            return;
        };
        *target = Some(scheme);
    }
}

fn trace_generalize_phase(
    trace: AnalysisTraceMode,
    phase: &str,
    def: DefId,
    elapsed: Duration,
    start: Instant,
) {
    if trace == AnalysisTraceMode::Off {
        return;
    }
    if trace == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50) {
        eprintln!(
            "[analysis] generalize {phase}: def={def:?} elapsed={:.3}ms total={:.3}ms",
            elapsed.as_secs_f64() * 1000.0,
            start.elapsed().as_secs_f64() * 1000.0
        );
    }
}

fn trace_generalize_count(
    trace: AnalysisTraceMode,
    label: &str,
    def: DefId,
    count: usize,
    elapsed: Duration,
    start: Instant,
) {
    if trace == AnalysisTraceMode::Off {
        return;
    }
    if trace == AnalysisTraceMode::Verbose || elapsed >= Duration::from_millis(50) {
        eprintln!(
            "[analysis] generalize {label}: def={def:?} count={} elapsed={:.3}ms total={:.3}ms",
            count,
            elapsed.as_secs_f64() * 1000.0,
            start.elapsed().as_secs_f64() * 1000.0
        );
    }
}
