use crate::profile::ProfileClock as Instant;
use std::collections::HashSet;

use crate::ast::expr::TypedExpr;
use crate::diagnostic::TypeErrorKind;
use crate::ids::{DefId, TypeVar};
use crate::scc::{
    CommitReadyProfile, commit_ready_components_in_set_with_refs_by_def_profiled,
    component_closure_from_defs, component_closure_from_defs_with_refs_by_owner,
    compress_components, compute_component_sccs, refs_by_def, refs_by_owner,
    share_type_vars_within_sccs_with_refs_by_owner,
};
use crate::scheme::{
    close_non_generic_vars_over_compact_scheme, collect_compact_role_constraint_free_vars,
    collect_low_level_vars_in_scheme, collect_var_levels, compact_pos_type,
    freeze_compact_scheme_owned_with_exact_non_generic_and_extra_vars,
};
use crate::simplify::compact::{
    CompactType, CompactTypeScheme, coalesce_nested_tail_function_effect_residuals_in_scheme,
    compact_type_var, expose_negative_row_tail_vars, expose_positive_row_tails,
};
use crate::simplify::cooccur::{
    CoalesceRound, CompactRoleConstraint,
    coalesce_by_co_occurrence_with_role_constraint_input_candidates_report,
    coalesce_by_co_occurrence_with_role_constraint_inputs_report, rewrite_scheme_with_subst,
};
use crate::simplify::role_constraints::rewrite_role_constraints_with_role_arg_inputs;
use crate::solve::selection::{role_candidate_input_subst, select_most_specific_role_candidates};
use crate::types::Neg;

use super::super::{FinalizeCompactProfile, FinalizeCompactResults};
use super::{
    LowerState, RoleCandidatePrerequisiteStatus, apply_role_output_replacements_to_constraints,
    apply_role_output_replacements_to_scheme, collect_role_default_replacements_if_disappeared,
    collect_role_output_replacements, concrete_selected_role_input_types, constructor_arg_variance,
    expand_role_constraint_with_scheme_bounds, path_string, projection_target_var,
    remove_disappearing_noncenter_role_vars, render_role_constraint_args_for_diagnostic,
    role_candidate_prerequisite_status, role_candidate_previews, role_constraint_arg_indices,
    role_constraint_is_observationally_empty, role_input_concrete_type_for_target,
};

impl LowerState {
    /// 現在の推論状態から compact/coalesced 済みの最終型結果を確定する。
    /// SCC 圧縮・SCC 内共有・ready component の compact 化までをまとめて行う。
    pub fn finalize_compact_results(&mut self) -> Vec<DefId> {
        self.finalize_compact_results_profiled().finalized_defs
    }

    fn role_arg_input_flags(&self, role: &crate::symbols::Path) -> Option<Vec<bool>> {
        let infos = self.infer.role_arg_infos_of(role);
        (!infos.is_empty()).then(|| infos.into_iter().map(|info| info.is_input).collect())
    }

    pub fn finalize_compact_results_profiled(&mut self) -> FinalizeCompactResults {
        let target_defs = self.observable_binding_defs();
        self.finalize_compact_results_for_target_defs_profiled(&target_defs, false)
    }

    pub fn finalize_compact_results_for_defs(
        &mut self,
        target_defs: &HashSet<DefId>,
    ) -> Vec<DefId> {
        self.finalize_compact_results_for_defs_profiled(target_defs)
            .finalized_defs
    }

    pub fn finalize_compact_results_for_defs_profiled(
        &mut self,
        target_defs: &HashSet<DefId>,
    ) -> FinalizeCompactResults {
        self.finalize_compact_results_for_target_defs_profiled(target_defs, false)
    }

    fn finalize_compact_results_for_target_defs_profiled(
        &mut self,
        target_defs: &HashSet<DefId>,
        follow_owner_refs: bool,
    ) -> FinalizeCompactResults {
        let total_start = Instant::now();
        let mut profile = FinalizeCompactProfile::default();
        let mut finalized = target_defs
            .iter()
            .copied()
            .filter(|def| self.infer.compact_schemes.borrow().get(def).is_some())
            .collect::<Vec<_>>();
        finalized.sort_by_key(|def| def.0);
        let mut finalized_seen = finalized.iter().copied().collect::<HashSet<_>>();
        let mut pending_target_defs = target_defs
            .iter()
            .copied()
            .filter(|def| !finalized_seen.contains(def))
            .collect::<HashSet<_>>();
        let mut newly_finalized = Vec::new();
        loop {
            if pending_target_defs.is_empty() {
                break;
            }
            self.refresh_selection_environment();
            let refs_by_def = refs_by_def(&self.ctx.refs);
            let refs_by_owner = refs_by_owner(&self.ctx.refs);
            profile.iterations += 1;
            self.infer.flush_compact_lower_instances();
            let scc_compute_start = Instant::now();
            let sccs = compute_component_sccs(&self.infer);
            profile.scc_compute += scc_compute_start.elapsed();

            let scc_compress_start = Instant::now();
            compress_components(&mut self.infer, &sccs);
            profile.scc_compress += scc_compress_start.elapsed();

            let scc_share_start = Instant::now();
            share_type_vars_within_sccs_with_refs_by_owner(&self.infer, &refs_by_owner, &sccs);
            profile.scc_share += scc_share_start.elapsed();

            let relevant_components = if follow_owner_refs {
                component_closure_from_defs_with_refs_by_owner(
                    &self.infer,
                    &refs_by_owner,
                    &pending_target_defs,
                )
            } else {
                component_closure_from_defs(&self.infer, &pending_target_defs)
            };
            let mut commit_profile = CommitReadyProfile::default();
            let ready_components = commit_ready_components_in_set_with_refs_by_def_profiled(
                &self.infer,
                &refs_by_def,
                &relevant_components,
                &pending_target_defs,
                &mut commit_profile,
            );
            profile.commit_ready.merge(&commit_profile);

            if ready_components.is_empty() {
                if self
                    .resolve_pending_method_role_constraints_before_defaulting(&relevant_components)
                {
                    continue;
                }
                break;
            }

            for component_idx in ready_components {
                for &def in &self.infer.components[component_idx] {
                    if pending_target_defs.remove(&def) && finalized_seen.insert(def) {
                        finalized.push(def);
                        newly_finalized.push(def);
                    }
                }
            }
        }

        profile.total = total_start.elapsed();
        let top_level_resolution_defs =
            self.top_level_role_resolution_defs(&finalized, &newly_finalized);
        self.resolve_top_level_compact_results_for_defs(&top_level_resolution_defs);
        self.inherit_finalized_role_var_alias_schemes(&newly_finalized);
        let post_alias_resolution_defs = self.top_level_role_resolution_defs(&finalized, &[]);
        self.resolve_top_level_compact_results_for_defs(&post_alias_resolution_defs);
        FinalizeCompactResults {
            finalized_defs: finalized,
            profile,
        }
    }

    fn top_level_role_resolution_defs(
        &self,
        finalized: &[DefId],
        newly_finalized: &[DefId],
    ) -> Vec<DefId> {
        let mut defs = newly_finalized.to_vec();
        defs.extend(finalized.iter().copied().filter(|def| {
            !self.infer.compact_role_constraints_of(*def).is_empty()
                || self.infer.has_role_constraints(*def)
                || self.infer.has_deferred_role_method_call_for_owner(*def)
        }));
        defs.sort_by_key(|def| def.0);
        defs.dedup();
        defs
    }

    pub fn compact_scheme_of(&self, def: DefId) -> Option<CompactTypeScheme> {
        self.infer.compact_schemes.borrow().get(&def).cloned()
    }

    pub fn surface_compact_scheme_of(&self, def: DefId) -> Option<CompactTypeScheme> {
        let mut scheme = self.compact_scheme_of(def)?;
        expose_positive_row_tails(&mut scheme);
        expose_negative_row_tail_vars(&mut scheme);
        Some(scheme)
    }

    fn resolve_top_level_compact_results_for_defs(&mut self, defs: &[DefId]) {
        for &def in defs {
            let Some(scheme) = self.compact_scheme_of(def) else {
                continue;
            };
            let has_deferred_role_method_call =
                self.infer.has_deferred_role_method_call_for_owner(def);
            let mut constraints = if has_deferred_role_method_call {
                self.infer
                    .add_deferred_role_method_constraints_for_owner(def);
                crate::lower::role::compact_role_constraints(&self.infer, def)
            } else {
                self.infer.compact_role_constraints_of(def)
            };
            if constraints.is_empty() && self.infer.has_role_constraints(def) {
                constraints = crate::lower::role::compact_role_constraints(&self.infer, def);
            }
            if constraints.is_empty() {
                continue;
            }
            let options = RoleConstraintResolutionOptions {
                allow_expansive_defaulting: self.binding_allows_role_defaulting(def),
                resolve_input_concretizations: true,
                rewrite_effect_metadata: true,
                report_errors: true,
            };
            let resolved =
                self.resolve_compact_role_constraints_for_def(def, scheme, constraints, options);
            self.infer.store_compact_scheme(def, resolved.scheme);
            self.infer
                .store_compact_role_constraints(def, resolved.constraints);
        }
    }

    fn store_finalized_compact_result(
        &mut self,
        def: DefId,
        mut scheme: CompactTypeScheme,
        constraints: Vec<CompactRoleConstraint>,
    ) {
        let exposed_boundary_vars =
            coalesce_nested_tail_function_effect_residuals_in_scheme(&mut scheme);
        let extra_quantified = collect_compact_role_constraint_free_vars(&constraints);
        let boundary = self.infer.def_level_of(def);
        let mut non_generic = collect_low_level_vars_in_scheme(&self.infer, &scheme, boundary);
        non_generic.extend(exposed_boundary_vars);
        close_non_generic_vars_over_compact_scheme(&scheme, &mut non_generic);
        let frozen = freeze_compact_scheme_owned_with_exact_non_generic_and_extra_vars(
            &self.infer,
            scheme.clone(),
            extra_quantified.as_slice(),
            &non_generic,
        );
        self.infer.store_compact_scheme(def, scheme);
        self.infer.store_compact_role_constraints(def, constraints);
        self.infer.store_frozen_scheme(def, frozen);
    }

    fn apply_coalesce_rounds_to_descendant_results(
        &mut self,
        owner: DefId,
        rounds: &[CoalesceRound],
    ) {
        if rounds.is_empty() {
            return;
        }
        let descendants = self.descendant_defs_of(owner);
        for round in rounds {
            if round.subst.is_empty() {
                continue;
            }
            for &def in &descendants {
                self.apply_compact_subst_to_stored_result(def, &round.subst);
            }
        }
    }

    fn apply_compact_subst_to_stored_result(
        &mut self,
        def: DefId,
        subst: &std::collections::HashMap<TypeVar, Option<TypeVar>>,
    ) -> bool {
        let Some(scheme) = self.compact_scheme_of(def) else {
            return false;
        };
        let constraints = self.infer.compact_role_constraints_of(def);
        let rewritten_scheme = rewrite_scheme_with_subst(&scheme, subst);
        let rewritten_constraints = rewrite_role_constraints_with_role_arg_inputs(
            &rewritten_scheme,
            &constraints,
            subst,
            &|role| self.role_arg_input_flags(role),
        );
        if rewritten_scheme == scheme && rewritten_constraints == constraints {
            return false;
        }
        self.store_finalized_compact_result(def, rewritten_scheme, rewritten_constraints);
        true
    }

    fn apply_role_output_replacements_to_descendant_results(
        &mut self,
        owner: DefId,
        replacements: &[(TypeVar, CompactType)],
    ) {
        if replacements.is_empty() {
            return;
        }
        for def in self.descendant_defs_of(owner) {
            let Some(scheme) = self.compact_scheme_of(def) else {
                continue;
            };
            let constraints = self.infer.compact_role_constraints_of(def);
            let rewritten_scheme = apply_role_output_replacements_to_scheme(&scheme, replacements);
            let rewritten_constraints =
                apply_role_output_replacements_to_constraints(&constraints, replacements);
            if rewritten_scheme == scheme && rewritten_constraints == constraints {
                continue;
            }
            self.store_finalized_compact_result(def, rewritten_scheme, rewritten_constraints);
        }
    }

    fn descendant_defs_of(&self, owner: DefId) -> Vec<DefId> {
        let mut defs = self
            .def_owners
            .keys()
            .copied()
            .filter(|def| *def != owner && self.def_is_nested_under(*def, owner))
            .collect::<Vec<_>>();
        defs.sort_by_key(|def| def.0);
        defs
    }

    fn def_is_nested_under(&self, def: DefId, ancestor: DefId) -> bool {
        let mut current = self.def_owner(def);
        for _ in 0..=self.def_owners.len() {
            let Some(owner) = current else {
                return false;
            };
            if owner == ancestor {
                return true;
            }
            current = self.def_owner(owner);
        }
        false
    }

    fn resolve_pending_method_role_constraints_before_defaulting(
        &mut self,
        relevant_components: &HashSet<usize>,
    ) -> bool {
        let mut components = relevant_components.iter().copied().collect::<Vec<_>>();
        components.sort_unstable();

        let mut changed_live_graph = false;
        for component_idx in components {
            if self.component_pending_selection_count(component_idx) == 0 {
                continue;
            }
            let defs = self
                .infer
                .components
                .get(component_idx)
                .map(|component| component.iter().copied().collect::<Vec<_>>())
                .unwrap_or_default();
            for def in defs {
                changed_live_graph |=
                    self.resolve_pending_method_role_constraints_for_def_before_defaulting(def);
            }
        }
        changed_live_graph
    }

    fn resolve_pending_method_role_constraints_for_def_before_defaulting(
        &mut self,
        def: DefId,
    ) -> bool {
        self.infer
            .add_deferred_role_method_constraints_for_owner(def);

        let mut constraints = crate::lower::role::compact_role_constraints(&self.infer, def);
        if constraints.is_empty() {
            constraints = self.infer.compact_role_constraints_of(def);
        }
        if constraints.is_empty() {
            return false;
        }

        let Some(tv) = self.infer.def_tvs.borrow().get(&def).copied() else {
            return false;
        };
        let mut scheme = self
            .compact_scheme_of(def)
            .unwrap_or_else(|| compact_type_var(&self.infer, tv));
        coalesce_nested_tail_function_effect_residuals_in_scheme(&mut scheme);

        let level_boundary = self.infer.def_level_of(def).saturating_add(1);
        let var_levels = collect_var_levels(&self.infer, &scheme);
        let coalesced = coalesce_by_co_occurrence_with_role_constraint_inputs_report(
            &scheme,
            &constraints,
            |role| self.role_arg_input_flags(role),
            &var_levels,
            level_boundary,
        );
        // ここは method selection を進めるための仮 pass で、SCC はまだ commit していない。
        // effect metadata の rewrite は最終 compact 側に任せる。

        let resolved = self.resolve_compact_role_constraints_for_def(
            def,
            coalesced.scheme,
            coalesced.constraints,
            RoleConstraintResolutionOptions {
                allow_expansive_defaulting: false,
                resolve_input_concretizations: false,
                rewrite_effect_metadata: false,
                report_errors: false,
            },
        );
        resolved.changed_live_graph
    }

    fn component_pending_selection_count(&self, component_idx: usize) -> usize {
        self.infer
            .component_pending_selections
            .get(component_idx)
            .map(|pending| *pending.borrow())
            .unwrap_or(0)
    }

    fn resolve_compact_role_constraints_for_def(
        &mut self,
        def: DefId,
        mut scheme: CompactTypeScheme,
        mut constraints: Vec<CompactRoleConstraint>,
        options: RoleConstraintResolutionOptions,
    ) -> RoleConstraintResolution {
        let mut changed_live_graph = false;
        // 明示計算で親/グローバル(level 0)へ上がった role 制約変数は、この def の commit
        // (boundary = def_level + 1) では simplify 対象外で残る。ここで boundary 0 の
        // グローバル相当 simplify を一度かけ、共起する変数を中心変数へ畳む。
        {
            let candidate_vars = role_constraint_projection_candidate_vars(&constraints);
            let coalesced = coalesce_by_co_occurrence_with_role_constraint_input_candidates_report(
                &scheme,
                &constraints,
                |role| self.role_arg_input_flags(role),
                &std::collections::HashMap::new(),
                0,
                &candidate_vars,
            );
            if options.rewrite_effect_metadata {
                for round in &coalesced.rounds {
                    self.infer
                        .rewrite_effect_subtract_metadata_vars(&round.subst);
                }
            }
            self.apply_coalesce_rounds_to_descendant_results(def, &coalesced.rounds);
            scheme = coalesced.scheme;
            constraints = coalesced.constraints;
        }
        if options.resolve_input_concretizations {
            // §決定1: 通常引数が具体型1つに定まり、中心変数が主型の反対方向に現れない
            // role は、その中心変数を具体型へ確定する。impl の有無は問わない（impl が無ければ
            // role 制約は具体型のまま浮き、後で実装が見つかったときに消える）。
            let mut concretizations = Vec::<(TypeVar, CompactType)>::new();
            let main_polarity = super::main_type_polarity(&scheme, &|path, index| {
                constructor_arg_variance(&self.infer, path, index)
            });
            for constraint in &constraints {
                let resolved_constraint =
                    expand_role_constraint_with_scheme_bounds(constraint, &scheme);
                let arg_infos = self.infer.role_arg_infos_of(&constraint.role);
                let (input_indices, _) =
                    role_constraint_arg_indices(&arg_infos, constraint.args.len());
                for &i in &input_indices {
                    let Some(original_arg) = constraint.args.get(i) else {
                        continue;
                    };
                    let Some(resolved_arg) = resolved_constraint.args.get(i) else {
                        continue;
                    };
                    let Some(target) = projection_target_var(original_arg)
                        .or_else(|| projection_target_var(resolved_arg))
                    else {
                        continue;
                    };
                    let Some(concrete) = role_input_concrete_type_for_target(
                        resolved_arg,
                        Some(target),
                        &main_polarity,
                        false,
                    ) else {
                        continue;
                    };
                    concretizations.push((target, concrete));
                }
            }
            if !concretizations.is_empty() {
                changed_live_graph |=
                    self.apply_role_output_replacements_to_live_graph(&concretizations);
                scheme = apply_role_output_replacements_to_scheme(&scheme, &concretizations);
                constraints =
                    apply_role_output_replacements_to_constraints(&constraints, &concretizations);
                self.apply_role_output_replacements_to_descendant_results(def, &concretizations);
                let candidate_vars = role_constraint_projection_candidate_vars(&constraints);
                let rewritten =
                    coalesce_by_co_occurrence_with_role_constraint_input_candidates_report(
                        &scheme,
                        &constraints,
                        |role| self.role_arg_input_flags(role),
                        &std::collections::HashMap::new(),
                        0,
                        &candidate_vars,
                    );
                if options.rewrite_effect_metadata {
                    for round in &rewritten.rounds {
                        self.infer
                            .rewrite_effect_subtract_metadata_vars(&round.subst);
                    }
                }
                self.apply_coalesce_rounds_to_descendant_results(def, &rewritten.rounds);
                scheme = rewritten.scheme;
                constraints = rewritten.constraints;
            }
        }
        loop {
            let mut progressed = false;
            let mut replacements = Vec::<(TypeVar, CompactType)>::new();
            let mut remaining = Vec::new();
            let current_constraints = constraints.clone();
            for (constraint_index, constraint) in current_constraints.iter().cloned().enumerate() {
                let resolved_constraint =
                    expand_role_constraint_with_scheme_bounds(&constraint, &scheme);
                let arg_infos = self.infer.role_arg_infos_of(&constraint.role);
                let (input_indices, output_indices) =
                    role_constraint_arg_indices(&arg_infos, constraint.args.len());
                let main_polarity = super::main_type_polarity(&scheme, &|path, index| {
                    constructor_arg_variance(&self.infer, path, index)
                });
                let Some(concrete_inputs) = concrete_selected_role_input_types(
                    &constraint,
                    &resolved_constraint,
                    &input_indices,
                    &main_polarity,
                    options.allow_expansive_defaulting,
                ) else {
                    if options.allow_expansive_defaulting
                        && role_constraint_is_observationally_empty(&constraint)
                    {
                        progressed = true;
                        continue;
                    }
                    remaining.push(constraint);
                    continue;
                };
                let rendered_args = render_role_constraint_args_for_diagnostic(
                    &resolved_constraint,
                    &output_indices,
                    &arg_infos,
                );

                let candidates = self.infer.role_impl_candidates_of(&constraint.role);
                let head_matches = candidates
                    .iter()
                    .filter(|candidate| {
                        role_candidate_input_subst(candidate, &input_indices, &concrete_inputs)
                            .is_some()
                    })
                    .collect::<Vec<_>>();
                let mut prerequisite_failure = None;
                let viable_matches = head_matches
                    .iter()
                    .copied()
                    .filter(|candidate| {
                        let Some(subst) =
                            role_candidate_input_subst(candidate, &input_indices, &concrete_inputs)
                        else {
                            return false;
                        };
                        match role_candidate_prerequisite_status(
                            &self.infer,
                            candidate,
                            &subst,
                            &mut Vec::new(),
                        ) {
                            RoleCandidatePrerequisiteStatus::Satisfied => true,
                            failure => {
                                prerequisite_failure.get_or_insert(failure);
                                false
                            }
                        }
                    })
                    .collect::<Vec<_>>();
                let matches = select_most_specific_role_candidates(viable_matches, &input_indices);
                if matches.len() == 1 {
                    let subst =
                        role_candidate_input_subst(matches[0], &input_indices, &concrete_inputs)
                            .unwrap_or_default();
                    progressed = true;
                    for (target, ty) in collect_role_output_replacements(
                        &constraint,
                        matches[0],
                        &subst,
                        &output_indices,
                    ) {
                        replacements.push((target, ty));
                    }
                    if options.allow_expansive_defaulting {
                        for (target, ty) in collect_role_default_replacements_if_disappeared(
                            &scheme,
                            &current_constraints,
                            constraint_index,
                            &constraint,
                            matches[0],
                            &subst,
                            &input_indices,
                            &|role| self.role_arg_input_flags(role),
                        ) {
                            replacements.push((target, ty));
                        }
                    }
                    continue;
                }

                if !options.report_errors {
                    remaining.push(constraint);
                    continue;
                }

                let role = path_string(&constraint.role);
                if matches.is_empty() && !head_matches.is_empty() {
                    match prerequisite_failure {
                        Some(RoleCandidatePrerequisiteStatus::MissingImpl {
                            role: prerequisite_role,
                            args: prerequisite_args,
                            origins,
                        }) => self
                            .infer
                            .report_synthetic_type_error_with_cause_and_origins(
                                TypeErrorKind::MissingImplPrerequisite {
                                    role,
                                    args: rendered_args,
                                    prerequisite_role,
                                    prerequisite_args,
                                },
                                format!("def {}", def.0),
                                crate::diagnostic::ConstraintCause::unknown(),
                                origins,
                            ),
                        Some(RoleCandidatePrerequisiteStatus::AmbiguousImpl {
                            role: prerequisite_role,
                            args: prerequisite_args,
                            candidates,
                            previews,
                            origins,
                        }) => self
                            .infer
                            .report_synthetic_type_error_with_cause_and_origins(
                                TypeErrorKind::AmbiguousImplPrerequisite {
                                    role,
                                    args: rendered_args,
                                    prerequisite_role,
                                    prerequisite_args,
                                    candidates,
                                    previews,
                                },
                                format!("def {}", def.0),
                                crate::diagnostic::ConstraintCause::unknown(),
                                origins,
                            ),
                        _ => self.infer.report_synthetic_type_error(
                            TypeErrorKind::MissingImpl {
                                role,
                                args: rendered_args,
                            },
                            format!("def {}", def.0),
                        ),
                    }
                } else if matches.is_empty() {
                    self.infer.report_synthetic_type_error(
                        TypeErrorKind::MissingImpl {
                            role,
                            args: rendered_args,
                        },
                        format!("def {}", def.0),
                    );
                } else {
                    self.infer.report_synthetic_type_error(
                        TypeErrorKind::AmbiguousImpl {
                            role,
                            args: rendered_args,
                            candidates: matches.len(),
                            previews: role_candidate_previews(matches),
                        },
                        format!("def {}", def.0),
                    );
                }
                progressed = true;
            }

            if !replacements.is_empty() {
                changed_live_graph |=
                    self.apply_role_output_replacements_to_live_graph(&replacements);
                scheme = apply_role_output_replacements_to_scheme(&scheme, &replacements);
                remaining =
                    apply_role_output_replacements_to_constraints(&remaining, &replacements);
                self.apply_role_output_replacements_to_descendant_results(def, &replacements);
                let candidate_vars = role_constraint_projection_candidate_vars(&remaining);
                let rewritten =
                    coalesce_by_co_occurrence_with_role_constraint_input_candidates_report(
                        &scheme,
                        &remaining,
                        |role| self.role_arg_input_flags(role),
                        &std::collections::HashMap::new(),
                        0,
                        &candidate_vars,
                    );
                if options.rewrite_effect_metadata {
                    for round in &rewritten.rounds {
                        self.infer
                            .rewrite_effect_subtract_metadata_vars(&round.subst);
                    }
                }
                self.apply_coalesce_rounds_to_descendant_results(def, &rewritten.rounds);
                scheme = rewritten.scheme;
                constraints = rewritten.constraints;
                progressed = true;
            } else {
                constraints = remaining;
            }

            if !progressed {
                break;
            }
        }
        let (scheme, constraints) =
            remove_disappearing_noncenter_role_vars(&scheme, &constraints, &|role| {
                self.role_arg_input_flags(role)
            });
        RoleConstraintResolution {
            scheme,
            constraints,
            changed_live_graph,
        }
    }

    fn binding_allows_role_defaulting(&self, def: DefId) -> bool {
        let Some(body) = self.principal_bodies.get(&def) else {
            return false;
        };
        let stripped = self.strip_transparent_expansive_wrappers(body);
        !self.is_syntactic_value_expr(stripped)
    }
}

fn role_constraint_projection_candidate_vars(
    constraints: &[CompactRoleConstraint],
) -> HashSet<TypeVar> {
    constraints
        .iter()
        .flat_map(|constraint| constraint.args.iter())
        .filter_map(projection_target_var)
        .collect()
}

impl LowerState {
    fn apply_role_output_replacements_to_live_graph(
        &mut self,
        replacements: &[(TypeVar, CompactType)],
    ) -> bool {
        let empty_scheme = CompactTypeScheme::default();
        let mut changed = false;
        for (target, ty) in replacements {
            let pos = compact_pos_type(&self.infer.arena, ty, &empty_scheme, false);
            let pos = self.infer.extrude_pos(pos, self.infer.level_of(*target));
            changed |= !self.infer.lower_members.borrow().contains(&(*target, pos));
            self.infer.constrain(pos, Neg::Var(*target));
        }
        changed
    }

    fn strip_transparent_expansive_wrappers<'a>(&'a self, expr: &'a TypedExpr) -> &'a TypedExpr {
        match &expr.kind {
            crate::ast::expr::ExprKind::Lam(def, body) if self.lambda_has_unit_pat(*def) => {
                self.strip_transparent_expansive_wrappers(body)
            }
            crate::ast::expr::ExprKind::Coerce { expr, .. }
            | crate::ast::expr::ExprKind::PackForall(_, expr) => {
                self.strip_transparent_expansive_wrappers(expr)
            }
            _ => expr,
        }
    }

    fn lambda_has_unit_pat(&self, def: DefId) -> bool {
        self.lambda_param_pats.get(&def).is_some_and(|pat| {
            matches!(
                pat.kind,
                crate::ast::expr::PatKind::Lit(crate::ast::expr::Lit::Unit)
            )
        })
    }

    fn is_syntactic_value_expr(&self, expr: &TypedExpr) -> bool {
        match &expr.kind {
            crate::ast::expr::ExprKind::Lit(_)
            | crate::ast::expr::ExprKind::PrimitiveOp(_)
            | crate::ast::expr::ExprKind::Var(_)
            | crate::ast::expr::ExprKind::Ref(_)
            | crate::ast::expr::ExprKind::Lam(_, _) => true,
            crate::ast::expr::ExprKind::Tuple(items) => {
                items.iter().all(|item| self.is_syntactic_value_expr(item))
            }
            crate::ast::expr::ExprKind::Record { fields, spread } => {
                fields
                    .iter()
                    .all(|(_, value)| self.is_syntactic_value_expr(value))
                    && spread.is_none()
            }
            crate::ast::expr::ExprKind::PolyVariant(_, payloads, _) => payloads
                .iter()
                .all(|payload| self.is_syntactic_value_expr(payload)),
            crate::ast::expr::ExprKind::Coerce { expr, .. }
            | crate::ast::expr::ExprKind::PackForall(_, expr) => self.is_syntactic_value_expr(expr),
            crate::ast::expr::ExprKind::BindHere(_) => false,
            crate::ast::expr::ExprKind::App { .. }
            | crate::ast::expr::ExprKind::RefSet { .. }
            | crate::ast::expr::ExprKind::Select { .. }
            | crate::ast::expr::ExprKind::Match(_, _)
            | crate::ast::expr::ExprKind::Catch(_, _)
            | crate::ast::expr::ExprKind::Block(_) => false,
        }
    }

    fn observable_binding_defs(&self) -> HashSet<DefId> {
        self.ctx
            .collect_observable_binding_paths()
            .into_iter()
            .filter(|(path, _)| {
                path.segments
                    .first()
                    .map(|name| name.0.as_str() != "std")
                    .unwrap_or(true)
            })
            .map(|(_, def)| def)
            .collect()
    }
}

#[derive(Clone, Copy)]
struct RoleConstraintResolutionOptions {
    allow_expansive_defaulting: bool,
    resolve_input_concretizations: bool,
    rewrite_effect_metadata: bool,
    report_errors: bool,
}

struct RoleConstraintResolution {
    scheme: CompactTypeScheme,
    constraints: Vec<CompactRoleConstraint>,
    changed_live_graph: bool,
}
