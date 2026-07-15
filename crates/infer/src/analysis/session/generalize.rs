use super::*;

impl AnalysisSession {
    #[cfg(test)]
    pub(in crate::analysis) fn generalize_root_with_prepasses(
        &mut self,
        def: DefId,
        root: TypeVar,
    ) -> GeneralizedCompactRoot {
        self.generalize_root_with_prepasses_and_metrics(def, root).0
    }

    pub(super) fn generalize_root_with_prepasses_and_metrics(
        &mut self,
        def: DefId,
        root: TypeVar,
    ) -> (GeneralizedCompactRoot, GeneralizeRootMetrics) {
        let trace = analysis_trace_mode();
        let start = Instant::now();
        let mut metrics = GeneralizeRootMetrics::default();
        metrics.record_constraint_epoch_start(self.infer.constraints().epoch());
        metrics.record_role_epoch_start(self.roles.epoch_for_owner(def));
        let quantification_boundary = self.generalize_boundary(def);
        let simplification_boundary = TypeLevel::root().child();
        let mut applied_casts = FxHashSet::<CompactCastKey>::default();
        let has_initial_role_inputs = !self.roles.for_owner(def).is_empty();
        let mut applied_roles = if has_initial_role_inputs {
            self.applied_method_role_resolutions.clone()
        } else {
            FxHashSet::default()
        };
        let mut applied_role_demands = if has_initial_role_inputs {
            self.applied_method_role_resolutions
                .iter()
                .map(|key| key.demand.clone())
                .collect::<FxHashSet<_>>()
        } else {
            FxHashSet::default()
        };
        let mut applied_merge_constraints = FxHashSet::<CompactMergeConstraintKey>::default();
        let mut applied_subtype_constraints = FxHashSet::<CompactSubtypeConstraintKey>::default();
        let mut compact;
        let final_role_solve = loop {
            self.timing.record_generalize_iteration();
            let compact_epoch = self.infer.constraints().epoch();
            if let Some(shadow) = self.generalize_compact_shadow.as_mut() {
                let hit = shadow.observe(root, compact_epoch);
                self.timing.record_generalize_compact_shadow(hit);
            }
            let phase = Instant::now();
            let (next_compact, mut merge_constraints) = self.compact_root_for_generalize(root);
            let elapsed = phase.elapsed();
            self.timing.record_generalize_compact(elapsed);
            metrics.record_compact_iteration(&next_compact);
            trace_generalize_phase(trace, "compact", def, elapsed, start);
            let phase = Instant::now();
            let role_input_count = self.roles.for_owner(def).len();
            let (role_constraints, role_collect_constraints) = if role_input_count == 0 {
                (Vec::new(), Vec::new())
            } else {
                compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints(
                    self.infer.constraints(),
                    &next_compact,
                    &[root],
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
            metrics.record_role_constraints(
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
                metrics.record_merge_restart();
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
            self.timing
                .record_generalize_dominance_roles(coalesced_role_constraints.len());
            metrics.record_dominance_input(coalesced_role_constraints.len());
            let mut simplified_role_view = None;
            let subtype_constraints =
                if compact_root_has_interval_bounds(&compact, &coalesced_role_constraints) {
                    let view = self.simplified_coalesced_role_view_for_generalize(
                        def,
                        root,
                        &compact,
                        &coalesced_role_constraints,
                        simplification_boundary,
                    );
                    let (constraints, dominance) =
                        collect_interval_dominance_constraints_with_metrics(&view.0, &view.1);
                    self.timing.record_generalize_dominance_scan(dominance);
                    metrics.record_dominance_scan(dominance);
                    simplified_role_view = Some(view);
                    constraints
                } else {
                    Vec::new()
                };
            let subtype_constraint_count = subtype_constraints.len();
            metrics.record_dominance_constraints(subtype_constraint_count);
            let elapsed = phase.elapsed();
            self.timing.record_generalize_collect_dominance(elapsed);
            trace_generalize_phase(trace, "collect dominance", def, elapsed, start);
            let phase = Instant::now();
            if apply_compact_subtype_constraints(
                self.infer.constraints_mut(),
                subtype_constraints,
                &mut applied_subtype_constraints,
            ) {
                metrics.record_subtype_restart();
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
                metrics.record_cast_restart();
                self.timing.record_generalize_cast_restart();
                self.timing
                    .record_generalize_cast(phase.elapsed(), 1, application_count);
                applied_casts.insert(batch.key);
                self.route_constraint_events();
                continue;
            }
            self.timing.record_generalize_cast(phase.elapsed(), 0, 0);

            let phase = Instant::now();
            let (resolutions, solved_view) = if coalesced_role_constraints.is_empty() {
                (Vec::new(), None)
            } else {
                let (mut role_compact, mut roles, floor_interval_noop) =
                    simplified_role_view.take().unwrap_or_else(|| {
                        self.simplified_coalesced_role_view_for_generalize(
                            def,
                            root,
                            &compact,
                            &coalesced_role_constraints,
                            simplification_boundary,
                        )
                    });
                normalize_role_resolution_floor(
                    self.infer.constraints(),
                    &mut role_compact,
                    &mut roles,
                    Some(floor_interval_noop),
                );
                let (resolutions, dispositions) = if roles.is_empty() {
                    (Vec::new(), Vec::new())
                } else {
                    self.timing
                        .record_generalize_role_resolve_inputs(roles.len());
                    metrics.record_role_resolve_inputs(roles.len());
                    let resolved = resolve_role_constraints_with_stats_and_dispositions(
                        self.infer.constraints(),
                        &role_compact,
                        &roles,
                        &self.role_impls,
                        &applied_roles,
                    );
                    self.timing.record_role_resolve_stats(resolved.output.stats);
                    (resolved.output.resolutions, resolved.dispositions)
                };
                (
                    resolutions,
                    Some(FinalRoleSolvedView {
                        role_compact,
                        normalized_roles: roles,
                        dispositions,
                    }),
                )
            };
            let resolution_count = resolutions.len();
            metrics.record_role_resolutions(resolution_count);
            let elapsed = phase.elapsed();
            self.timing
                .record_generalize_resolve_roles(elapsed, resolution_count);
            trace_generalize_phase(trace, "resolve roles", def, elapsed, start);
            if !resolutions.is_empty() {
                metrics.record_role_restart();
                self.timing.record_generalize_role_restart();
                for resolution in resolutions {
                    applied_roles.insert(resolution.key.clone());
                    self.collect_resolved_role_demands(&resolution, &mut applied_role_demands);
                    self.constrain_role_resolution(def, &resolution);
                }
                self.route_constraint_events();
                continue;
            }
            break FinalRoleSolveSnapshot {
                coalesced_roles: coalesced_role_constraints,
                solved_view,
                constraint_epoch: self.infer.constraints().epoch(),
                role_epoch: self.roles.epoch_for_owner(def),
                raw_role_count: role_input_count,
            };
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
                vec![false; final_role_solve.coalesced_roles.len()]
            } else {
                let rebuilt_view = final_role_solve
                    .inputs_match(
                        self.infer.constraints().epoch(),
                        self.roles.epoch_for_owner(def),
                        self.roles.for_owner(def).len(),
                    )
                    .then(|| {
                        // A floor rewrite may be harmless for this solve without being a no-op.
                        // Rebuild the exact final-filter view and compare both solver inputs before
                        // trusting the prior per-demand dispositions.
                        self.normalized_role_view(
                            &compact,
                            &final_role_solve.coalesced_roles,
                            simplification_boundary,
                        )
                    });
                let reused = rebuilt_view.as_ref().and_then(|(role_compact, roles)| {
                    final_role_solve.applied_flags_if_view_is_exact(
                        role_compact,
                        roles,
                        &applied_roles,
                        &applied_role_demands,
                    )
                });
                if let Some(reused) = reused {
                    reused
                } else if let Some((role_compact, roles)) = rebuilt_view {
                    self.normalized_role_predicates_already_applied(
                        &role_compact,
                        &roles,
                        &applied_role_candidates,
                        &applied_role_demands,
                    )
                } else {
                    self.simplified_role_predicates_already_applied(
                        &compact,
                        &final_role_solve.coalesced_roles,
                        &applied_role_candidates,
                        &applied_role_demands,
                        simplification_boundary,
                    )
                }
            };
        let mut role_predicates: Vec<CompactRoleConstraint> = final_role_solve
            .coalesced_roles
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
        let prepared = prepare_alias_expanded_compact_root_with_role_variances(
            self.infer.constraints(),
            simplification_boundary,
            compact,
            role_predicates,
            &self.role_input_variances,
            &FxHashSet::default(),
        );
        // Alias expansion is one transitive traversal over the retained component. It can widen an
        // interval after the solve loop's last dominance scan, so route the corresponding keys once
        // against the same applied set. This is the bounded companion pass for that one expansion;
        // it must not restart generalization or introduce a second settle loop.
        let (post_alias_constraints, dominance) =
            if compact_root_has_interval_bounds(&prepared.compact, &prepared.role_predicates) {
                collect_interval_dominance_constraints_with_metrics(
                    &prepared.compact,
                    &prepared.role_predicates,
                )
            } else {
                (Vec::new(), IntervalDominanceMetrics::default())
            };
        self.timing.record_generalize_dominance_scan(dominance);
        metrics.record_dominance_scan(dominance);
        let post_alias_constraint_count = post_alias_constraints.len();
        metrics.record_dominance_constraints(post_alias_constraint_count);
        let post_alias_changed = apply_compact_subtype_constraints(
            self.infer.constraints_mut(),
            post_alias_constraints,
            &mut applied_subtype_constraints,
        );
        if post_alias_changed {
            self.route_constraint_events();
        }
        let cleaned = prepare_stack_cleaned_alias_expanded_compact_root(
            self.infer.constraints(),
            quantification_boundary,
            prepared,
            &FxHashSet::default(),
        );
        // Stack-weight cleanup can erase a spent weight after the post-alias scan, changing the
        // exact structural key of an invariant interval. Route the cleaned key once through the
        // same bounded consistency/dominance lane. Like the alias companion pass above, this must
        // not restart generalization or grow into a second settle loop.
        let (post_cleanup_constraints, dominance) =
            if compact_root_has_interval_bounds(&cleaned.compact, &cleaned.role_predicates) {
                collect_interval_dominance_constraints_with_metrics(
                    &cleaned.compact,
                    &cleaned.role_predicates,
                )
            } else {
                (Vec::new(), IntervalDominanceMetrics::default())
            };
        self.timing.record_generalize_dominance_scan(dominance);
        metrics.record_dominance_scan(dominance);
        let post_cleanup_constraint_count = post_cleanup_constraints.len();
        metrics.record_dominance_constraints(post_cleanup_constraint_count);
        let post_cleanup_changed = apply_compact_subtype_constraints(
            self.infer.constraints_mut(),
            post_cleanup_constraints,
            &mut applied_subtype_constraints,
        );
        if post_cleanup_changed {
            self.route_constraint_events();
        }
        let mut generalized = generalize_stack_cleaned_compact_root(
            self.infer.constraints(),
            quantification_boundary,
            cleaned,
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
        metrics.record_constraint_epoch_end(self.infer.constraints().epoch());
        metrics.record_role_epoch_end(self.roles.epoch_for_owner(def));
        self.cache_interface_applied_merge_constraints
            .extend(applied_merge_constraints);
        self.cache_interface_applied_subtype_constraints
            .extend(applied_subtype_constraints);
        (generalized, metrics)
    }

    fn compact_root_for_generalize(
        &mut self,
        root: TypeVar,
    ) -> (CompactRoot, Vec<CompactMergeConstraint>) {
        let compact_epoch = self.infer.constraints().epoch();
        if let Some(cache) = self.generalize_compact_cache.as_ref() {
            if let Some(cached) = cache.get(root, compact_epoch) {
                self.timing.record_generalize_compact_cache(true);
                return cached;
            }
        }

        if self.generalize_compact_cache.is_some() {
            self.timing.record_generalize_compact_cache(false);
        }
        let out =
            compact_type_var_recording_merge_constraints_for_scheme(self.infer.constraints(), root);
        if let Some(cache) = self.generalize_compact_cache.as_mut() {
            cache.insert(root, compact_epoch, &out.0, &out.1);
            self.timing.record_generalize_compact_cache_insert();
        }
        out
    }

    fn simplified_coalesced_role_view_for_generalize(
        &mut self,
        def: DefId,
        root: TypeVar,
        compact: &crate::compact::CompactRoot,
        coalesced_roles: &[CompactRoleConstraint],
        simplification_boundary: TypeLevel,
    ) -> (
        crate::compact::CompactRoot,
        Vec<CompactRoleConstraint>,
        bool,
    ) {
        if let Some(shadow) = self.generalize_role_view_shadow.as_mut() {
            let hit = shadow.observe(
                def,
                root,
                self.infer.constraints().epoch(),
                self.roles.epoch_for_owner(def),
                coalesced_roles.len(),
                simplification_boundary,
            );
            self.timing.record_generalize_role_view_shadow(hit);
        }
        self.simplified_coalesced_role_view(compact, coalesced_roles, simplification_boundary)
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
        normalize_role_resolution_floor(
            self.infer.constraints(),
            &mut role_compact,
            &mut roles,
            None,
        );
        Some((role_compact, roles))
    }

    fn simplified_coalesced_role_view(
        &self,
        compact: &crate::compact::CompactRoot,
        coalesced_roles: &[CompactRoleConstraint],
        simplification_boundary: TypeLevel,
    ) -> (
        crate::compact::CompactRoot,
        Vec<CompactRoleConstraint>,
        bool,
    ) {
        let mut role_compact = compact.clone();
        let mut roles = coalesced_roles.to_vec();
        simplify_compact_root_with_roles_and_non_generic(
            self.infer.constraints(),
            simplification_boundary,
            &mut role_compact,
            &mut roles,
            &FxHashSet::default(),
        );
        let floor_interval_substitutions = coalesce_floor_interval_equalities(
            self.infer.constraints(),
            TypeLevel::root(),
            &mut role_compact,
            &mut roles,
        );
        (role_compact, roles, floor_interval_substitutions.is_empty())
    }

    /// 世代化の最終出力から落としてよい残置述語を、入力 role と同じ並びの bool 列で返す。
    /// true は簡約済み全体ビューで「適用済み demand と一致する」か
    /// 「適用済み impl 候補へ一意に解決する」。
    pub(in crate::analysis) fn simplified_role_predicates_already_applied(
        &self,
        compact: &crate::compact::CompactRoot,
        role_predicates: &[CompactRoleConstraint],
        applied_candidates: &FxHashSet<CompactRoleConstraint>,
        applied_demands: &FxHashSet<CompactRoleConstraint>,
        simplification_boundary: TypeLevel,
    ) -> Vec<bool> {
        let (role_compact, simplified_roles) =
            self.normalized_role_view(compact, role_predicates, simplification_boundary);
        self.normalized_role_predicates_already_applied(
            &role_compact,
            &simplified_roles,
            applied_candidates,
            applied_demands,
        )
    }

    fn normalized_role_view(
        &self,
        compact: &crate::compact::CompactRoot,
        role_predicates: &[CompactRoleConstraint],
        simplification_boundary: TypeLevel,
    ) -> (crate::compact::CompactRoot, Vec<CompactRoleConstraint>) {
        let (mut role_compact, mut roles, floor_interval_noop) =
            self.simplified_coalesced_role_view(compact, role_predicates, simplification_boundary);
        normalize_role_resolution_floor(
            self.infer.constraints(),
            &mut role_compact,
            &mut roles,
            Some(floor_interval_noop),
        );
        (role_compact, roles)
    }

    fn normalized_role_predicates_already_applied(
        &self,
        role_compact: &crate::compact::CompactRoot,
        simplified_roles: &[CompactRoleConstraint],
        applied_candidates: &FxHashSet<CompactRoleConstraint>,
        applied_demands: &FxHashSet<CompactRoleConstraint>,
    ) -> Vec<bool> {
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

    pub(in crate::analysis) fn generalize_boundary(&self, def: DefId) -> TypeLevel {
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
        let input_pairs = resolution
            .demand
            .inputs
            .iter()
            .zip(&resolution.candidate.inputs);
        let associated_pairs = resolution.demand.associated.iter().filter_map(|demand| {
            resolution
                .candidate
                .associated
                .iter()
                .find(|candidate| candidate.name == demand.name)
                .map(|candidate| (&demand.value, &candidate.value))
        });
        self.constrain_role_args_equal(input_pairs.chain(associated_pairs));
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

    pub(super) fn constrain_role_args_equal<'a>(
        &mut self,
        pairs: impl IntoIterator<Item = (&'a CompactRoleArg, &'a CompactRoleArg)>,
    ) {
        let pairs = {
            let constraints = self.infer.constraints_mut();
            pairs
                .into_iter()
                .map(|(demand, candidate)| {
                    let candidate =
                        finalize_compact_bounds_to_constraint(constraints, &candidate.bounds);
                    let demand = finalize_compact_bounds_to_constraint(constraints, &demand.bounds);
                    (candidate, demand)
                })
                .collect::<Vec<_>>()
        };
        self.infer.constraints_mut().constrain_invariant_neus(pairs);
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

    pub(super) fn scheme_ancestors_for_current_poly(
        &mut self,
        def: DefId,
    ) -> Vec<GeneralizedCompactRoot> {
        self.def_parent_map.refresh(&self.poly);
        let mut chain = Vec::new();
        let mut current = def;
        while let Some(parent) = self.def_parent_map.parents.get(&current).copied() {
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

struct FinalRoleSolveSnapshot {
    coalesced_roles: Vec<CompactRoleConstraint>,
    solved_view: Option<FinalRoleSolvedView>,
    constraint_epoch: ConstraintEpoch,
    role_epoch: RoleEpoch,
    raw_role_count: usize,
}

struct FinalRoleSolvedView {
    role_compact: crate::compact::CompactRoot,
    normalized_roles: Vec<CompactRoleConstraint>,
    dispositions: Vec<crate::role_solve::RoleDemandDisposition>,
}

impl FinalRoleSolveSnapshot {
    fn inputs_match(
        &self,
        constraint_epoch: ConstraintEpoch,
        role_epoch: RoleEpoch,
        raw_role_count: usize,
    ) -> bool {
        self.constraint_epoch == constraint_epoch
            && self.role_epoch == role_epoch
            && self.raw_role_count == raw_role_count
            && self.solved_view.as_ref().is_some_and(|view| {
                view.normalized_roles.len() == self.coalesced_roles.len()
                    && view.dispositions.len() == self.coalesced_roles.len()
            })
    }

    fn applied_flags_if_view_is_exact(
        &self,
        role_compact: &crate::compact::CompactRoot,
        normalized_roles: &[CompactRoleConstraint],
        applied_roles: &FxHashSet<crate::role_solve::RoleResolutionKey>,
        applied_demands: &FxHashSet<CompactRoleConstraint>,
    ) -> Option<Vec<bool>> {
        let solved_view = self.solved_view.as_ref()?;
        if solved_view.role_compact != *role_compact
            || solved_view.normalized_roles != normalized_roles
        {
            return None;
        }
        // The solve loop cannot terminate with a newly resolved demand. Checking that invariant,
        // the disposition-to-demand alignment, and membership in the unchanged applied-key set
        // makes malformed or stale snapshots fail closed into the ordinary resolver.
        solved_view
            .normalized_roles
            .iter()
            .zip(&solved_view.dispositions)
            .map(|(role, disposition)| match disposition {
                crate::role_solve::RoleDemandDisposition::AlreadyApplied { key }
                    if key.demand == *role && applied_roles.contains(key) =>
                {
                    Some(true)
                }
                crate::role_solve::RoleDemandDisposition::Unresolved { .. } => {
                    Some(applied_demands.contains(role))
                }
                crate::role_solve::RoleDemandDisposition::NewlyResolved { .. }
                | crate::role_solve::RoleDemandDisposition::AlreadyApplied { .. } => None,
            })
            .collect()
    }
}

/// role resolve 用の床正規化を完了し、全 pass が no-op だったかを返す。
///
/// solve loop は interval pass 後の view を dominance scan にも使うため、そこだけ pipeline が
/// 二段に分かれる。`floor_interval_noop` が `Some` なら interval pass は実行済み、`None` なら
/// fallback 用にここで interval → redundant elimination の全順序を通す。
fn normalize_role_resolution_floor(
    machine: &crate::constraints::ConstraintMachine,
    compact: &mut crate::compact::CompactRoot,
    roles: &mut [CompactRoleConstraint],
    floor_interval_noop: Option<bool>,
) -> bool {
    let floor_interval_noop = floor_interval_noop.unwrap_or_else(|| {
        coalesce_floor_interval_equalities(machine, TypeLevel::root(), compact, roles).is_empty()
    });
    let floor_redundant_noop =
        eliminate_floor_redundant_variables(machine, TypeLevel::root(), compact, roles).is_empty();
    floor_interval_noop && floor_redundant_noop
}

#[cfg(test)]
mod final_role_reuse_tests {
    use super::*;
    use crate::compact::{CompactBounds, compact_reachable_role_constraints, compact_type_var};
    use crate::role_solve::{
        RoleResolutionKey, coalesce_role_constraints, resolve_role_constraints,
        resolve_role_constraints_with_stats_and_dispositions,
    };
    use crate::roles::{RoleConstraint, RoleConstraintArg, RoleImplCandidate};
    use poly::expr::Arena as PolyArena;
    use poly::types::{Neg, Neu, Pos, TypeVar};

    #[test]
    fn exact_post_floor_view_reuses_dispositions_and_matches_full_resolve() {
        let fixture = exact_reuse_fixture();

        assert!(fixture.snapshot.inputs_match(
            fixture.session.infer.constraints().epoch(),
            fixture.session.roles.epoch_for_owner(fixture.owner),
            fixture.session.roles.for_owner(fixture.owner).len(),
        ));
        let reused = fixture
            .snapshot
            .applied_flags_if_view_is_exact(
                &fixture.normalized_compact,
                &fixture.normalized_roles,
                &fixture.applied_roles,
                &fixture.applied_demands,
            )
            .expect("an exact post-floor view must reuse the terminal dispositions");
        let full = fixture.session.simplified_role_predicates_already_applied(
            &fixture.compact,
            &fixture.coalesced_roles,
            &fixture.applied_candidates,
            &fixture.applied_demands,
            TypeLevel::root().child(),
        );

        assert_eq!(reused, full);
        assert_eq!(reused, vec![true, false]);
    }

    #[test]
    fn relevant_post_floor_demand_change_rejects_reuse_and_full_resolve_keeps_it() {
        let fixture = exact_reuse_fixture();
        let changed_compact = crate::compact::CompactRoot::default();
        assert_ne!(fixture.normalized_compact, changed_compact);
        assert!(
            fixture
                .snapshot
                .applied_flags_if_view_is_exact(
                    &changed_compact,
                    &fixture.normalized_roles,
                    &fixture.applied_roles,
                    &fixture.applied_demands,
                )
                .is_none(),
            "a structurally changed post-floor main view must fail closed"
        );

        let mut changed_roles = fixture.normalized_roles.clone();
        let document = changed_roles
            .iter_mut()
            .find(|role| role.role == vec!["Document".to_string()])
            .expect("document demand");
        document.inputs[1].bounds = CompactBounds::Con {
            path: vec!["other_node".into()],
            args: Vec::new(),
        };

        assert!(
            fixture
                .snapshot
                .applied_flags_if_view_is_exact(
                    &fixture.normalized_compact,
                    &changed_roles,
                    &fixture.applied_roles,
                    &fixture.applied_demands,
                )
                .is_none(),
            "a structurally changed normalized demand must fail closed"
        );
        let full = fixture.session.normalized_role_predicates_already_applied(
            &fixture.normalized_compact,
            &changed_roles,
            &fixture.applied_candidates,
            &fixture.applied_demands,
        );
        let document_index = changed_roles
            .iter()
            .position(|role| role.role == vec!["Document".to_string()])
            .expect("document demand");

        assert!(!full[document_index]);
    }

    #[test]
    fn terminal_disposition_mismatch_rejects_reuse() {
        let mut fixture = exact_reuse_fixture();
        let key = fixture
            .applied_roles
            .iter()
            .next()
            .expect("applied document key")
            .clone();
        let view = fixture
            .snapshot
            .solved_view
            .as_mut()
            .expect("terminal solved view");
        let document_index = view
            .normalized_roles
            .iter()
            .position(|role| role.role == vec!["Document".to_string()])
            .expect("document demand");
        view.dispositions[document_index] =
            crate::role_solve::RoleDemandDisposition::NewlyResolved { key };

        assert!(
            fixture
                .snapshot
                .applied_flags_if_view_is_exact(
                    &fixture.normalized_compact,
                    &fixture.normalized_roles,
                    &fixture.applied_roles,
                    &fixture.applied_demands,
                )
                .is_none(),
            "a terminal snapshot cannot contain a newly resolved demand"
        );
    }

    #[test]
    fn changed_epoch_or_role_count_rejects_reuse_before_view_comparison() {
        let mut fixture = exact_reuse_fixture();
        let snapshot_constraint_epoch = fixture.session.infer.constraints().epoch();
        let snapshot_role_epoch = fixture.session.roles.epoch_for_owner(fixture.owner);
        let snapshot_role_count = fixture.session.roles.for_owner(fixture.owner).len();

        assert!(!fixture.snapshot.inputs_match(
            snapshot_constraint_epoch,
            snapshot_role_epoch,
            snapshot_role_count + 1,
        ));

        let changed = fixture.session.infer.fresh_type_var();
        let lower = fixture
            .session
            .infer
            .alloc_pos(Pos::Con(vec!["epoch_change".into()], Vec::new()));
        let upper = fixture.session.infer.alloc_neg(Neg::Var(changed));
        fixture.session.infer.subtype(lower, upper);
        let changed_constraint_epoch = fixture.session.infer.constraints().epoch();
        assert_ne!(snapshot_constraint_epoch, changed_constraint_epoch);
        assert!(!fixture.snapshot.inputs_match(
            changed_constraint_epoch,
            snapshot_role_epoch,
            snapshot_role_count,
        ));

        fixture.session.roles.insert(
            fixture.owner,
            RoleConstraint {
                role: vec!["Noise".into()],
                inputs: Vec::new(),
                associated: Vec::new(),
            },
        );
        assert!(!fixture.snapshot.inputs_match(
            snapshot_constraint_epoch,
            fixture.session.roles.epoch_for_owner(fixture.owner),
            snapshot_role_count,
        ));
    }

    struct ExactReuseFixture {
        session: AnalysisSession,
        owner: DefId,
        compact: crate::compact::CompactRoot,
        coalesced_roles: Vec<CompactRoleConstraint>,
        normalized_compact: crate::compact::CompactRoot,
        normalized_roles: Vec<CompactRoleConstraint>,
        applied_roles: FxHashSet<RoleResolutionKey>,
        applied_candidates: FxHashSet<CompactRoleConstraint>,
        applied_demands: FxHashSet<CompactRoleConstraint>,
        snapshot: FinalRoleSolveSnapshot,
    }

    fn exact_reuse_fixture() -> ExactReuseFixture {
        let document_role = vec!["Document".to_string()];
        let children_role = vec!["Children".to_string()];
        let node_path = vec!["node".to_string()];
        let owner = DefId(0);
        let mut session = AnalysisSession::new(PolyArena::new());
        let root = session.infer.fresh_type_var();
        let first = session.infer.fresh_type_var();
        let second = session.infer.fresh_type_var();
        let candidate_item = session.infer.fresh_type_var();

        session.roles.insert(
            owner,
            RoleConstraint {
                role: document_role.clone(),
                inputs: vec![
                    role_unary_con_var_and_extra_arg(
                        &mut session.infer,
                        node_path.clone(),
                        first,
                        second,
                    ),
                    role_unary_con_var_arg(&mut session.infer, node_path.clone(), second),
                ],
                associated: Vec::new(),
            },
        );
        session.roles.insert(
            owner,
            RoleConstraint {
                role: children_role.clone(),
                inputs: vec![role_var_arg(&mut session.infer, first)],
                associated: Vec::new(),
            },
        );
        session.role_impls.insert(RoleImplCandidate {
            impl_def: None,
            role: document_role.clone(),
            inputs: vec![
                role_unary_con_var_arg(&mut session.infer, node_path.clone(), candidate_item),
                role_unary_con_var_arg(&mut session.infer, node_path, candidate_item),
            ],
            associated: Vec::new(),
            prerequisites: vec![RoleConstraint {
                role: children_role,
                inputs: vec![role_var_arg(&mut session.infer, candidate_item)],
                associated: Vec::new(),
            }],
            methods: Vec::new(),
        });
        constrain_root_to_vars(&mut session, root, &[first]);

        let compact = compact_type_var(session.infer.constraints(), root);
        let coalesced_roles = coalesce_role_constraints(compact_reachable_role_constraints(
            session.infer.constraints(),
            &compact,
            session.roles.for_owner(owner),
        ));
        let (mut normalized_compact, mut normalized_roles, floor_interval_noop) = session
            .simplified_coalesced_role_view(&compact, &coalesced_roles, TypeLevel::root().child());
        let floor_noop = normalize_role_resolution_floor(
            session.infer.constraints(),
            &mut normalized_compact,
            &mut normalized_roles,
            Some(floor_interval_noop),
        );
        assert!(!floor_noop, "fixture must exercise the old rejected path");

        let applied = resolve_role_constraints(
            session.infer.constraints(),
            &normalized_compact,
            &normalized_roles,
            &session.role_impls,
            &FxHashSet::default(),
        )
        .into_iter()
        .find(|resolution| resolution.demand.role == document_role)
        .expect("floor-normalized document demand must resolve");
        let applied_roles = FxHashSet::from_iter([applied.key.clone()]);
        let terminal = resolve_role_constraints_with_stats_and_dispositions(
            session.infer.constraints(),
            &normalized_compact,
            &normalized_roles,
            &session.role_impls,
            &applied_roles,
        );
        assert!(terminal.output.resolutions.is_empty());
        let applied_candidates = FxHashSet::from_iter([applied.candidate]);
        let applied_demands = FxHashSet::from_iter([applied.demand]);
        let snapshot = FinalRoleSolveSnapshot {
            coalesced_roles: coalesced_roles.clone(),
            solved_view: Some(FinalRoleSolvedView {
                role_compact: normalized_compact.clone(),
                normalized_roles: normalized_roles.clone(),
                dispositions: terminal.dispositions,
            }),
            constraint_epoch: session.infer.constraints().epoch(),
            role_epoch: session.roles.epoch_for_owner(owner),
            raw_role_count: session.roles.for_owner(owner).len(),
        };

        ExactReuseFixture {
            session,
            owner,
            compact,
            coalesced_roles,
            normalized_compact,
            normalized_roles,
            applied_roles,
            applied_candidates,
            applied_demands,
            snapshot,
        }
    }

    fn constrain_root_to_vars(session: &mut AnalysisSession, root: TypeVar, vars: &[TypeVar]) {
        let items = vars
            .iter()
            .map(|var| session.infer.alloc_pos(Pos::Var(*var)))
            .collect();
        let lower = session.infer.alloc_pos(Pos::Tuple(items));
        let upper = session.infer.alloc_neg(Neg::Var(root));
        session.infer.subtype(lower, upper);
    }

    fn role_var_arg(infer: &mut crate::arena::Arena, var: TypeVar) -> RoleConstraintArg {
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Var(var)),
            upper: infer.alloc_neg(Neg::Var(var)),
        }
    }

    fn role_unary_con_var_arg(
        infer: &mut crate::arena::Arena,
        path: Vec<String>,
        item: TypeVar,
    ) -> RoleConstraintArg {
        let lower = infer.alloc_pos(Pos::Var(item));
        let upper = infer.alloc_neg(Neg::Var(item));
        let item = infer.alloc_neu(Neu::Bounds(lower, upper));
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
            upper: infer.alloc_neg(Neg::Con(path, vec![item])),
        }
    }

    fn role_unary_con_var_and_extra_arg(
        infer: &mut crate::arena::Arena,
        path: Vec<String>,
        item: TypeVar,
        extra: TypeVar,
    ) -> RoleConstraintArg {
        let item_lower = infer.alloc_pos(Pos::Var(item));
        let extra_lower = infer.alloc_pos(Pos::Var(extra));
        let lower = infer.alloc_pos(Pos::Union(item_lower, extra_lower));
        let item_upper = infer.alloc_neg(Neg::Var(item));
        let extra_upper = infer.alloc_neg(Neg::Var(extra));
        let upper = infer.alloc_neg(Neg::Intersection(item_upper, extra_upper));
        let item = infer.alloc_neu(Neu::Bounds(lower, upper));
        RoleConstraintArg {
            lower: infer.alloc_pos(Pos::Con(path.clone(), vec![item])),
            upper: infer.alloc_neg(Neg::Con(path, vec![item])),
        }
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
