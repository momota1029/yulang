use super::*;

impl AnalysisSession {
    pub(super) fn generalize_root_with_prepasses(
        &mut self,
        def: DefId,
        root: TypeVar,
    ) -> GeneralizedCompactRoot {
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
        loop {
            let (next_compact, mut merge_constraints) =
                compact_type_var_recording_merge_constraints(self.infer.constraints(), root);
            let (role_constraints, role_collect_constraints) =
                compact_reachable_role_constraints_recording_merge_constraints(
                    self.infer.constraints(),
                    &next_compact,
                    self.roles.for_owner(def),
                );
            let (coalesced_role_constraints, role_coalesce_constraints) =
                coalesce_role_constraints_recording_merge_constraints(role_constraints);
            merge_constraints.extend(role_collect_constraints);
            merge_constraints.extend(role_coalesce_constraints);
            compact = next_compact;
            if apply_compact_merge_constraints(
                self.infer.constraints_mut(),
                merge_constraints,
                &mut applied_merge_constraints,
            ) {
                self.route_constraint_events();
                continue;
            }
            let mut dominance_compact = compact.clone();
            let mut dominance_roles = coalesced_role_constraints.clone();
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
            if apply_compact_subtype_constraints(
                self.infer.constraints_mut(),
                subtype_constraints,
                &mut applied_subtype_constraints,
            ) {
                self.route_constraint_events();
                continue;
            }
            normalize_compact_casts(&mut compact, &applied_casts);
            if let Some(batch) = find_next_compact_cast(&compact, &self.casts, &applied_casts) {
                for application in &batch.applications {
                    self.constrain_compact_cast(application);
                }
                applied_casts.insert(batch.key);
                self.route_constraint_events();
                continue;
            }

            let (role_compact, roles) =
                self.simplified_reachable_role_constraints(def, &compact, simplification_boundary);
            let resolutions = resolve_role_constraints(
                self.infer.constraints(),
                &role_compact,
                &roles,
                &self.role_impls,
                &applied_roles,
            );
            if !resolutions.is_empty() {
                for resolution in resolutions {
                    applied_roles.insert(resolution.key.clone());
                    self.collect_resolved_role_demands(&resolution, &mut applied_role_demands);
                    self.constrain_role_resolution(def, &resolution);
                }
                self.route_constraint_events();
                continue;
            }
            break;
        }

        let applied_role_candidates = applied_roles
            .iter()
            .map(|key| key.candidate.clone())
            .collect::<FxHashSet<_>>();
        // ループ中に適用した demand は簡約済みビューの表記なので、生の述語と一致しない
        // ことがある。再判定はループ末尾と同じ「主型＋全 role」一括簡約ビューで行う。
        // role 単独で簡約すると共起が減って併合が強く効きすぎ、ループでは適用されなかった
        // 解決をここで初めて作ってしまう（制約を注入せずに述語だけ消える）恐れがある。
        let coalesced_roles = coalesce_role_constraints(compact_reachable_role_constraints(
            self.infer.constraints(),
            &compact,
            self.roles.for_owner(def),
        ));
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
        if !role_predicates.is_empty()
            && (!applied_role_candidates.is_empty() || !applied_role_demands.is_empty())
        {
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
        }

        let mut generalized = generalize_prepared_compact_root_with_role_variances_and_boundaries(
            self.infer.constraints(),
            quantification_boundary,
            simplification_boundary,
            compact,
            role_predicates,
            &self.role_input_variances,
            &FxHashSet::default(),
        );
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

    pub(super) fn simplified_reachable_role_constraints(
        &self,
        def: DefId,
        compact: &crate::compact::CompactRoot,
        simplification_boundary: TypeLevel,
    ) -> (crate::compact::CompactRoot, Vec<CompactRoleConstraint>) {
        let mut role_compact = compact.clone();
        let mut roles = coalesce_role_constraints(compact_reachable_role_constraints(
            self.infer.constraints(),
            compact,
            self.roles.for_owner(def),
        ));
        if roles.is_empty() {
            return (compact.clone(), roles);
        }
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
        (role_compact, roles)
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

    pub(super) fn def_scheme(&self, def: DefId) -> Option<&Scheme> {
        let Some(Def::Let { scheme, .. }) = self.poly.defs.get(def) else {
            return None;
        };
        scheme.as_ref()
    }

    pub(super) fn scheme_ancestors(&self, def: DefId) -> Vec<GeneralizedCompactRoot> {
        let parents = def_parent_map(&self.poly);
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
