use crate::ids::DefId;
use crate::scheme::{
    SmallSubst, close_non_generic_vars_over_compact_scheme,
    collect_compact_role_constraint_free_vars, collect_low_level_vars_in_scheme,
    collect_var_levels, freeze_compact_scheme_owned_with_exact_non_generic_and_extra_vars,
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars, instantiate_as_view_with_subst,
};
use crate::simplify::compact::{
    coalesce_nested_tail_function_effect_residuals_in_scheme, compact_type_var,
    subst_compact_bounds, subst_compact_scheme, subst_lookup_small,
};
use crate::simplify::cooccur::CompactRoleConstraint;
use crate::simplify::cooccur::coalesce_by_co_occurrence_with_role_constraint_inputs;

use super::LowerState;

impl LowerState {
    pub(crate) fn finalize_pending_role_var_alias_schemes(&mut self) {
        let pending = self
            .pending_role_var_alias_schemes
            .iter()
            .copied()
            .collect::<Vec<_>>();
        for alias in pending {
            if self.try_finalize_role_var_alias_scheme(alias) {
                self.pending_role_var_alias_schemes.remove(&alias);
            }
        }
    }

    pub(crate) fn inherit_finalized_role_var_alias_schemes(&mut self, defs: &[DefId]) {
        for &alias in defs {
            let Some(target) = self.principal_var_alias_target(alias) else {
                continue;
            };
            if !self.alias_target_has_role_surface(target) {
                continue;
            }
            self.inherit_role_alias_scheme(alias, target);
        }
    }

    fn try_finalize_role_var_alias_scheme(&mut self, alias: DefId) -> bool {
        if self.alias_has_compact_and_frozen_scheme(alias) {
            return true;
        }
        let Some(target) = self.principal_var_alias_target(alias) else {
            return true;
        };

        if !self.alias_target_has_role_surface(target) {
            return true;
        }
        self.refresh_role_alias_target_owner(target);
        if !self.ensure_role_alias_target_scheme(target) {
            return false;
        }

        self.inherit_role_alias_scheme(alias, target)
    }

    fn ensure_role_alias_target_scheme(&mut self, target: DefId) -> bool {
        if self.infer.compact_schemes.borrow().contains_key(&target)
            && self.infer.frozen_schemes.borrow().contains_key(&target)
        {
            return true;
        }

        self.store_local_role_alias_target_scheme(target);
        self.infer.compact_schemes.borrow().contains_key(&target)
            && self.infer.frozen_scheme_of(target).is_some()
    }

    fn store_local_role_alias_target_scheme(&mut self, target: DefId) -> bool {
        let Some(&tv) = self.def_tvs.get(&target) else {
            return false;
        };
        let constraints = crate::lower::role::compact_role_constraints(&self.infer, target);
        if constraints.is_empty() {
            return false;
        }

        let mut compact = compact_type_var(&self.infer, tv);
        let exposed_boundary_vars =
            coalesce_nested_tail_function_effect_residuals_in_scheme(&mut compact);
        let level_boundary = self.infer.def_level_of(target).saturating_add(1);
        let var_levels = collect_var_levels(&self.infer, &compact);
        let (scheme, constraints) = coalesce_by_co_occurrence_with_role_constraint_inputs(
            &compact,
            &constraints,
            |role| {
                let infos = self.infer.role_arg_infos_of(role);
                (!infos.is_empty()).then(|| infos.into_iter().map(|info| info.is_input).collect())
            },
            &var_levels,
            level_boundary,
        );
        let extra_quantified = collect_compact_role_constraint_free_vars(&constraints);
        let boundary = self.infer.def_level_of(target);
        let mut non_generic = collect_low_level_vars_in_scheme(&self.infer, &scheme, boundary);
        non_generic.extend(exposed_boundary_vars);
        close_non_generic_vars_over_compact_scheme(&scheme, &mut non_generic);
        let frozen = freeze_compact_scheme_owned_with_exact_non_generic_and_extra_vars(
            &self.infer,
            scheme.clone(),
            extra_quantified.as_slice(),
            &non_generic,
        );

        self.infer.store_compact_scheme(target, scheme);
        self.infer
            .store_compact_role_constraints(target, constraints);
        self.infer.store_frozen_scheme(target, frozen);
        true
    }

    fn refresh_role_alias_target_owner(&mut self, target: DefId) {
        if self.selection_lookup_dirty {
            self.infer.rebuild_type_methods(&self.ctx.modules);
            self.selection_lookup_dirty = false;
        }
        self.infer
            .add_deferred_role_method_constraints_for_owner(target);
    }

    fn inherit_role_alias_scheme(&mut self, alias: DefId, target: DefId) -> bool {
        let Some(target_frozen) = self.infer.frozen_scheme_of(target) else {
            return false;
        };
        let target_constraints = self.infer.compact_role_constraints_of(target);
        if target_constraints.is_empty() {
            return false;
        }

        let alias_level = self.infer.def_level_of(alias).saturating_add(1);
        let instance =
            instantiate_as_view_with_subst(&self.infer, &target_frozen, alias_level, &[]);
        let (scheme_subst, role_subst) = self.role_alias_inheritance_substs(
            alias_level,
            &target_frozen,
            &target_constraints,
            instance.subst,
        );
        let compact = subst_compact_scheme(&target_frozen.compact, scheme_subst.as_slice());
        let constraints = target_constraints
            .into_iter()
            .map(|constraint| CompactRoleConstraint {
                role: constraint.role,
                args: constraint
                    .args
                    .iter()
                    .map(|arg| subst_compact_bounds(arg, role_subst.as_slice()))
                    .collect(),
            })
            .collect::<Vec<_>>();
        let extra_quantified = collect_compact_role_constraint_free_vars(&constraints);
        let frozen = freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
            &self.infer,
            compact.clone(),
            extra_quantified.as_slice(),
            &self.infer.non_generic_vars_of(alias),
        );

        self.infer.store_compact_scheme(alias, compact);
        self.infer
            .store_compact_role_constraints(alias, constraints);
        self.infer.store_frozen_scheme(alias, frozen);
        true
    }

    fn role_alias_inheritance_substs(
        &self,
        alias_level: u32,
        target_frozen: &crate::scheme::FrozenScheme,
        target_constraints: &[CompactRoleConstraint],
        mut scheme_subst: SmallSubst,
    ) -> (SmallSubst, SmallSubst) {
        let mut role_subst = SmallSubst::new();
        for (source, frozen) in &target_frozen.quantified_sources {
            let fresh = subst_lookup_small(scheme_subst.as_slice(), *frozen);
            push_subst(&mut role_subst, *source, fresh);
        }

        let compact_vars = collect_var_levels(&self.infer, &target_frozen.compact)
            .keys()
            .copied()
            .collect::<Vec<_>>();
        for var in compact_vars {
            if subst_lookup_opt(scheme_subst.as_slice(), var).is_some() {
                continue;
            }
            let fresh = self.fresh_tv_at(alias_level);
            push_subst(&mut scheme_subst, var, fresh);
            push_subst(&mut role_subst, var, fresh);
        }

        for var in collect_compact_role_constraint_free_vars(target_constraints) {
            if subst_lookup_opt(role_subst.as_slice(), var).is_some() {
                continue;
            }
            let fresh = subst_lookup_opt(scheme_subst.as_slice(), var).unwrap_or_else(|| {
                let fresh = self.fresh_tv_at(alias_level);
                push_subst(&mut scheme_subst, var, fresh);
                fresh
            });
            push_subst(&mut role_subst, var, fresh);
        }

        (scheme_subst, role_subst)
    }

    fn alias_target_has_role_surface(&self, target: DefId) -> bool {
        self.infer.has_role_constraints(target)
            || !self.infer.compact_role_constraints_of(target).is_empty()
            || self.infer.has_deferred_role_method_call_for_owner(target)
    }

    fn alias_has_compact_and_frozen_scheme(&self, alias: DefId) -> bool {
        self.infer.compact_schemes.borrow().contains_key(&alias)
            && self.infer.frozen_schemes.borrow().contains_key(&alias)
    }
}

fn push_subst(subst: &mut SmallSubst, from: crate::ids::TypeVar, to: crate::ids::TypeVar) {
    if let Some((_, existing_to)) = subst
        .iter_mut()
        .find(|(existing_from, _)| *existing_from == from)
    {
        *existing_to = to;
    } else {
        subst.push((from, to));
    }
}

fn subst_lookup_opt(
    subst: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
    tv: crate::ids::TypeVar,
) -> Option<crate::ids::TypeVar> {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
}
