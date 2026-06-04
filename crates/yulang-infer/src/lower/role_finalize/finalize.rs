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
use crate::scheme::compact_pos_type;
use crate::simplify::compact::{
    CompactType, CompactTypeScheme, expose_negative_row_tail_vars, expose_positive_row_tails,
};
use crate::simplify::cooccur::coalesce_by_co_occurrence_with_role_constraint_inputs;
use crate::solve::selection::{role_candidate_input_subst, select_most_specific_role_candidates};
use crate::types::Neg;

use super::super::{FinalizeCompactProfile, FinalizeCompactResults};
use super::{
    LowerState, RoleCandidatePrerequisiteStatus, apply_role_output_replacements_to_constraints,
    apply_role_output_replacements_to_scheme, collect_role_default_replacements_if_disappeared,
    collect_role_output_replacements, concrete_bounds_repr, concrete_selected_input_types,
    expand_role_constraint_with_scheme_bounds, path_string, projection_target_var,
    remove_disappearing_noncenter_role_vars, render_role_constraint_args_for_diagnostic,
    render_selected_concrete_args, role_candidate_prerequisite_status, role_candidate_previews,
    role_constraint_arg_indices, role_constraint_is_observationally_empty,
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
                break;
            }

            for component_idx in ready_components {
                for &def in &self.infer.components[component_idx] {
                    if pending_target_defs.remove(&def) && finalized_seen.insert(def) {
                        finalized.push(def);
                    }
                }
            }
        }

        profile.total = total_start.elapsed();
        self.resolve_concrete_role_constraints_for_defs(&finalized);
        self.inherit_finalized_role_var_alias_schemes(&finalized);
        FinalizeCompactResults {
            finalized_defs: finalized,
            profile,
        }
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

    fn resolve_concrete_role_constraints_for_defs(&mut self, defs: &[DefId]) {
        for &def in defs {
            let Some(mut scheme) = self.compact_scheme_of(def) else {
                continue;
            };
            let mut constraints = self.infer.compact_role_constraints_of(def);
            if constraints.is_empty() {
                continue;
            }
            // 明示計算で親/グローバル(level 0)へ上がった role 制約変数は、この def の commit
            // (boundary = def_level + 1) では simplify 対象外で残る。ここで boundary 0 の
            // グローバル相当 simplify を一度かけ、共起する変数を中心変数へ畳む。
            {
                let (coalesced_scheme, coalesced_constraints) =
                    coalesce_by_co_occurrence_with_role_constraint_inputs(
                        &scheme,
                        &constraints,
                        |role| self.role_arg_input_flags(role),
                        &std::collections::HashMap::new(),
                        0,
                    );
                scheme = coalesced_scheme;
                constraints = coalesced_constraints;
            }
            // §決定1: 通常引数が具体型1つに定まった role は、その中心変数を具体型へ確定する。
            // impl の有無は問わない（impl が無ければ role 制約は具体型のまま浮き、後で実装が
            // 見つかったときに消える）。関数など非 expansive な束縛は量化したい変数を潰さない
            // よう、allow_boundary を expansive / 関連型ありのときだけ立てる。
            {
                let expansive = self.binding_allows_role_defaulting(def);
                let mut concretizations = Vec::<(TypeVar, CompactType)>::new();
                for constraint in &constraints {
                    let arg_infos = self.infer.role_arg_infos_of(&constraint.role);
                    let (input_indices, output_indices) =
                        role_constraint_arg_indices(&arg_infos, constraint.args.len());
                    let allow_boundary = expansive || !output_indices.is_empty();
                    for &i in &input_indices {
                        let Some(arg) = constraint.args.get(i) else {
                            continue;
                        };
                        let Some(target) = projection_target_var(arg) else {
                            continue;
                        };
                        let Some(concrete) = concrete_bounds_repr(arg, allow_boundary) else {
                            continue;
                        };
                        concretizations.push((target, concrete));
                    }
                }
                if !concretizations.is_empty() {
                    self.apply_role_output_replacements_to_live_graph(&concretizations);
                    scheme = apply_role_output_replacements_to_scheme(&scheme, &concretizations);
                    constraints = apply_role_output_replacements_to_constraints(
                        &constraints,
                        &concretizations,
                    );
                    let (rewritten_scheme, rewritten_constraints) =
                        coalesce_by_co_occurrence_with_role_constraint_inputs(
                            &scheme,
                            &constraints,
                            |role| self.role_arg_input_flags(role),
                            &std::collections::HashMap::new(),
                            0,
                        );
                    scheme = rewritten_scheme;
                    constraints = rewritten_constraints;
                }
            }
            loop {
                let mut progressed = false;
                let mut replacements = Vec::<(TypeVar, CompactType)>::new();
                let mut remaining = Vec::new();
                let expansive_defaulting = self.binding_allows_role_defaulting(def);
                let current_constraints = constraints.clone();
                for (constraint_index, constraint) in
                    current_constraints.iter().cloned().enumerate()
                {
                    let resolved_constraint =
                        expand_role_constraint_with_scheme_bounds(&constraint, &scheme);
                    let arg_infos = self.infer.role_arg_infos_of(&constraint.role);
                    let (input_indices, output_indices) =
                        role_constraint_arg_indices(&arg_infos, constraint.args.len());
                    let allow_boundary_inputs = expansive_defaulting || !output_indices.is_empty();
                    let Some(_rendered_inputs) = render_selected_concrete_args(
                        &resolved_constraint,
                        &input_indices,
                        allow_boundary_inputs,
                    ) else {
                        if expansive_defaulting
                            && role_constraint_is_observationally_empty(&constraint)
                        {
                            progressed = true;
                            continue;
                        }
                        remaining.push(constraint);
                        continue;
                    };
                    let Some(concrete_inputs) = concrete_selected_input_types(
                        &resolved_constraint,
                        &input_indices,
                        allow_boundary_inputs,
                    ) else {
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
                            let Some(subst) = role_candidate_input_subst(
                                candidate,
                                &input_indices,
                                &concrete_inputs,
                            ) else {
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
                    let matches =
                        select_most_specific_role_candidates(viable_matches, &input_indices);
                    if matches.len() == 1 {
                        let subst = role_candidate_input_subst(
                            matches[0],
                            &input_indices,
                            &concrete_inputs,
                        )
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
                        if expansive_defaulting {
                            for (target, ty) in collect_role_default_replacements_if_disappeared(
                                &scheme,
                                &current_constraints,
                                constraint_index,
                                &constraint,
                                matches[0],
                                &subst,
                                &input_indices,
                            ) {
                                replacements.push((target, ty));
                            }
                        }
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
                    self.apply_role_output_replacements_to_live_graph(&replacements);
                    scheme = apply_role_output_replacements_to_scheme(&scheme, &replacements);
                    remaining =
                        apply_role_output_replacements_to_constraints(&remaining, &replacements);
                    let (rewritten_scheme, rewritten_constraints) =
                        coalesce_by_co_occurrence_with_role_constraint_inputs(
                            &scheme,
                            &remaining,
                            |role| self.role_arg_input_flags(role),
                            &std::collections::HashMap::new(),
                            0,
                        );
                    scheme = rewritten_scheme;
                    constraints = rewritten_constraints;
                    progressed = true;
                } else {
                    constraints = remaining;
                }

                if !progressed {
                    break;
                }
            }
            let (scheme, constraints) =
                remove_disappearing_noncenter_role_vars(&scheme, &constraints);
            self.infer.store_compact_scheme(def, scheme);
            self.infer.store_compact_role_constraints(def, constraints);
        }
    }

    fn binding_allows_role_defaulting(&self, def: DefId) -> bool {
        let Some(body) = self.principal_bodies.get(&def) else {
            return false;
        };
        let stripped = self.strip_transparent_expansive_wrappers(body);
        !self.is_syntactic_value_expr(stripped)
    }

    fn apply_role_output_replacements_to_live_graph(
        &mut self,
        replacements: &[(TypeVar, CompactType)],
    ) {
        let empty_scheme = CompactTypeScheme::default();
        for (target, ty) in replacements {
            let pos = compact_pos_type(&self.infer.arena, ty, &empty_scheme, false);
            self.infer.constrain(pos, Neg::Var(*target));
        }
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
        self.lambda_param_pats.get(&def).map_or(true, |pat| {
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
