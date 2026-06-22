//! Compact result の量化計画を作る入口。
//!
//! collect / simplify は `compact` が持ち、ここでは「どの変数を scheme の quantifier にするか」
//! を compact 表現のまま決める。`poly::Scheme` への finalize は最後の出口として分ける。

use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RoleAssociatedType, RolePredicate,
    RolePredicateArg, Scheme, StackWeight, SubtractId, Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compact::{
    CompactBounds, CompactCon, CompactFun, CompactPolyVariant, CompactRecord, CompactRecordSpread,
    CompactRecursiveVar, CompactRoleArg, CompactRoleArgPolarity, CompactRoleConstraint,
    CompactRoot, CompactRow, CompactSandwich, CompactSandwichKind, CompactSimplification,
    CompactTuple, CompactType, CompactVar, CompactVarOrigin, CompactVarSubstitution,
    compact_con_entries, compact_row_item_entries, compact_type_var_for_scheme,
    finalize_compact_bounds, finalize_compact_bounds_lower, finalize_compact_bounds_upper,
    finalize_compact_root, merge_compact_types,
    simplify_compact_root_with_role_variance_table_and_non_generic,
    simplify_compact_root_with_roles_and_non_generic,
};
use crate::constraints::{ConstraintMachine, ConstraintWeights, TypeLevel};
use crate::roles::RoleInputVarianceTable;
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
};

mod core;
mod finalize;
mod simplification;
#[cfg(test)]
mod tests;

use core::*;
pub(crate) use finalize::{
    clone_role_impl_candidate_between_arenas, finalize_generalized_compact_root,
};
use simplification::apply_ancestor_simplifications;
pub(crate) use simplification::apply_compact_simplifications_to_root_and_roles;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GeneralizedCompactRoot {
    pub(crate) compact: CompactRoot,
    pub(crate) role_predicates: Vec<CompactRoleConstraint>,
    pub(crate) quantifiers: Vec<TypeVar>,
    pub(crate) stack_quantifiers: Vec<SubtractId>,
    pub(crate) substitutions: Vec<CompactVarSubstitution>,
    pub(crate) sandwiches: Vec<CompactSandwich>,
}

pub(crate) struct FinalizedGeneralizedCompactRoot {
    pub(crate) scheme: Scheme,
}

pub(crate) fn generalize_type_var_with_boundaries(
    machine: &ConstraintMachine,
    root: TypeVar,
    quantification_boundary: TypeLevel,
    simplification_boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    let compact = compact_type_var_for_scheme(machine, root);
    generalize_prepared_compact_root_with_roles_and_boundaries(
        machine,
        quantification_boundary,
        simplification_boundary,
        compact,
        Vec::new(),
        non_generic,
    )
}

pub(crate) fn generalize_prepared_compact_root_with_roles(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    compact: CompactRoot,
    role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    generalize_prepared_compact_root_with_roles_and_boundaries(
        machine,
        boundary,
        boundary.child(),
        compact,
        role_predicates,
        non_generic,
    )
}

fn generalize_prepared_compact_root_with_roles_and_boundaries(
    machine: &ConstraintMachine,
    quantification_boundary: TypeLevel,
    simplification_boundary: TypeLevel,
    mut compact: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    expand_positive_aliases_in_scheme_compact(machine, &mut compact, &mut role_predicates);
    let simplification = simplify_compact_root_with_roles_and_non_generic(
        machine,
        simplification_boundary,
        &mut compact,
        &mut role_predicates,
        non_generic,
    );
    generalize_compact_root_with_simplification(
        machine,
        quantification_boundary,
        compact,
        role_predicates,
        non_generic,
        simplification,
    )
}

pub(crate) fn generalize_prepared_compact_root_with_role_variances_and_boundaries(
    machine: &ConstraintMachine,
    quantification_boundary: TypeLevel,
    simplification_boundary: TypeLevel,
    mut compact: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    role_variances: &RoleInputVarianceTable,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    expand_positive_aliases_in_scheme_compact(machine, &mut compact, &mut role_predicates);
    let simplification = simplify_compact_root_with_role_variance_table_and_non_generic(
        machine,
        simplification_boundary,
        &mut compact,
        &mut role_predicates,
        role_variances,
        non_generic,
    );
    generalize_compact_root_with_simplification(
        machine,
        quantification_boundary,
        compact,
        role_predicates,
        non_generic,
        simplification,
    )
}

fn expand_positive_aliases_in_scheme_compact(
    machine: &ConstraintMachine,
    compact: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) {
    let allowed = compact_scheme_vars(compact, role_predicates);
    let mut cache = FxHashMap::default();
    let mut visiting = FxHashSet::default();
    expand_positive_aliases_in_type(
        machine,
        &allowed,
        &mut cache,
        &mut visiting,
        &mut compact.root,
        AliasPolarity::Positive,
    );
    for rec in &mut compact.rec_vars {
        expand_positive_aliases_in_bounds(
            machine,
            &allowed,
            &mut cache,
            &mut visiting,
            &mut rec.bounds,
            AliasPolarity::Positive,
        );
    }
    for role in role_predicates {
        for input in &mut role.inputs {
            expand_positive_aliases_in_bounds(
                machine,
                &allowed,
                &mut cache,
                &mut visiting,
                &mut input.bounds,
                AliasPolarity::Positive,
            );
        }
        for associated in &mut role.associated {
            expand_positive_aliases_in_bounds(
                machine,
                &allowed,
                &mut cache,
                &mut visiting,
                &mut associated.value.bounds,
                AliasPolarity::Positive,
            );
        }
    }
}

fn compact_scheme_vars(
    compact: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
) -> FxHashSet<TypeVar> {
    let mut vars = Vec::new();
    collect_root_free_vars(compact, &mut vars);
    for role in role_predicates {
        collect_role_free_vars(role, &mut vars);
    }
    vars.into_iter().collect()
}

#[derive(Clone, Copy)]
enum AliasPolarity {
    Positive,
    Negative,
}

impl AliasPolarity {
    fn flipped(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }

    fn is_positive(self) -> bool {
        matches!(self, Self::Positive)
    }
}

fn expand_positive_aliases_in_type(
    machine: &ConstraintMachine,
    allowed: &FxHashSet<TypeVar>,
    cache: &mut FxHashMap<TypeVar, Vec<TypeVar>>,
    visiting: &mut FxHashSet<TypeVar>,
    ty: &mut CompactType,
    polarity: AliasPolarity,
) {
    if polarity.is_positive() {
        let vars = ty.vars.clone();
        for var in vars {
            for alias in positive_aliases_within_scheme(machine, allowed, cache, visiting, var.var)
            {
                let alias_var = CompactVar::covariant(alias, var.weight.clone())
                    .with_origin(CompactVarOrigin::Secondary);
                push_compact_var_alias(&mut ty.vars, alias_var);
            }
        }
    }

    for args in ty.cons.values_mut() {
        for arg in args {
            expand_positive_aliases_in_bounds(machine, allowed, cache, visiting, arg, polarity);
        }
    }
    for fun in &mut ty.funs {
        expand_positive_aliases_in_type(
            machine,
            allowed,
            cache,
            visiting,
            &mut fun.arg,
            polarity.flipped(),
        );
        expand_positive_aliases_in_type(
            machine,
            allowed,
            cache,
            visiting,
            &mut fun.arg_eff,
            polarity.flipped(),
        );
        expand_positive_aliases_in_type(
            machine,
            allowed,
            cache,
            visiting,
            &mut fun.ret_eff,
            polarity,
        );
        expand_positive_aliases_in_type(machine, allowed, cache, visiting, &mut fun.ret, polarity);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            expand_positive_aliases_in_type(
                machine,
                allowed,
                cache,
                visiting,
                &mut field.value,
                polarity,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            expand_positive_aliases_in_type(
                machine,
                allowed,
                cache,
                visiting,
                &mut field.value,
                polarity,
            );
        }
        expand_positive_aliases_in_type(
            machine,
            allowed,
            cache,
            visiting,
            &mut spread.tail,
            polarity,
        );
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                expand_positive_aliases_in_type(
                    machine, allowed, cache, visiting, payload, polarity,
                );
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            expand_positive_aliases_in_type(machine, allowed, cache, visiting, item, polarity);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                expand_positive_aliases_in_bounds(machine, allowed, cache, visiting, arg, polarity);
            }
        }
        expand_positive_aliases_in_type(machine, allowed, cache, visiting, &mut row.tail, polarity);
    }
}

fn expand_positive_aliases_in_bounds(
    machine: &ConstraintMachine,
    allowed: &FxHashSet<TypeVar>,
    cache: &mut FxHashMap<TypeVar, Vec<TypeVar>>,
    visiting: &mut FxHashSet<TypeVar>,
    bounds: &mut CompactBounds,
    polarity: AliasPolarity,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            expand_positive_aliases_in_type(machine, allowed, cache, visiting, lower, polarity);
            expand_positive_aliases_in_type(
                machine,
                allowed,
                cache,
                visiting,
                upper,
                polarity.flipped(),
            );
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                expand_positive_aliases_in_bounds(machine, allowed, cache, visiting, arg, polarity);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            expand_positive_aliases_in_bounds(
                machine,
                allowed,
                cache,
                visiting,
                arg,
                polarity.flipped(),
            );
            expand_positive_aliases_in_bounds(
                machine,
                allowed,
                cache,
                visiting,
                arg_eff,
                polarity.flipped(),
            );
            expand_positive_aliases_in_bounds(machine, allowed, cache, visiting, ret_eff, polarity);
            expand_positive_aliases_in_bounds(machine, allowed, cache, visiting, ret, polarity);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                expand_positive_aliases_in_bounds(
                    machine,
                    allowed,
                    cache,
                    visiting,
                    &mut field.value,
                    polarity,
                );
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    expand_positive_aliases_in_bounds(
                        machine, allowed, cache, visiting, payload, polarity,
                    );
                }
            }
        }
    }
}

fn positive_aliases_within_scheme(
    machine: &ConstraintMachine,
    allowed: &FxHashSet<TypeVar>,
    cache: &mut FxHashMap<TypeVar, Vec<TypeVar>>,
    visiting: &mut FxHashSet<TypeVar>,
    var: TypeVar,
) -> Vec<TypeVar> {
    if let Some(cached) = cache.get(&var) {
        return cached.clone();
    }
    if !visiting.insert(var) {
        return Vec::new();
    }

    let mut out = Vec::new();
    if let Some(bounds) = machine.bounds().of(var) {
        for bound in bounds.lowers() {
            if !alias_neutral_constraint(&bound.weights) {
                continue;
            }
            let Pos::Var(next) = machine.types().pos(bound.pos) else {
                continue;
            };
            if !allowed.contains(next) {
                continue;
            }
            push_unique_var(&mut out, *next);
            for alias in positive_aliases_within_scheme(machine, allowed, cache, visiting, *next) {
                push_unique_var(&mut out, alias);
            }
        }
    }

    visiting.remove(&var);
    cache.insert(var, out.clone());
    out
}

fn alias_neutral_constraint(weights: &ConstraintWeights) -> bool {
    alias_neutral_weight(&weights.left.to_stack_weight())
}

fn alias_neutral_weight(weight: &StackWeight) -> bool {
    !weight.has_filter()
        && weight
            .entries()
            .iter()
            .all(|entry| entry.floor.is_empty() && entry.stack.is_empty())
}

fn push_compact_var_alias(vars: &mut Vec<CompactVar>, var: CompactVar) {
    if let Some(existing) = vars.iter_mut().find(|existing| existing.var == var.var) {
        existing.weight = existing.weight.parallel_union(&var.weight);
        existing.origin = existing.origin.merged(var.origin);
    } else {
        vars.push(var);
    }
}

fn push_unique_var(vars: &mut Vec<TypeVar>, var: TypeVar) {
    if !vars.contains(&var) {
        vars.push(var);
    }
}

#[cfg(test)]
pub(crate) fn generalize_prepared_compact_root_with_roles_and_simplifications(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut compact: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    simplifications: &[CompactSimplification],
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    apply_compact_simplifications_to_root_and_roles(
        &mut compact,
        &mut role_predicates,
        simplifications,
    );
    generalize_prepared_compact_root_with_roles(
        machine,
        boundary,
        compact,
        role_predicates,
        non_generic,
    )
}

#[cfg(test)]
pub(crate) fn generalize_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: CompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    generalize_prepared_compact_root_with_roles(machine, boundary, root, Vec::new(), non_generic)
}

fn generalize_compact_root_with_simplification(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut root: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
    simplification: CompactSimplification,
) -> GeneralizedCompactRoot {
    let substitutions = simplification.substitutions;
    let sandwiches = simplification.sandwiches;
    prune_unreachable_recursive_bounds(&mut root, &role_predicates);

    let mut quantifiers =
        quantified_vars_in_root_and_roles(machine, boundary, &root, &role_predicates, non_generic);
    prune_dead_quantified_subtract_weights(
        machine,
        &quantifiers,
        &substitutions,
        non_generic,
        &mut root,
        &mut role_predicates,
    );
    prune_unreachable_recursive_bounds(&mut root, &role_predicates);
    cleanup_stack_weights_in_root_and_roles(&mut root, &mut role_predicates);
    cleanup_empty_stack_entries_with_plain_negative_occurrence(&mut root, &mut role_predicates);
    cleanup_empty_only_stack_ids_in_root_and_roles(machine, &mut root, &mut role_predicates);
    quantifiers =
        quantified_vars_in_root_and_roles(machine, boundary, &root, &role_predicates, non_generic);
    let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let mut stack_quantifiers = sorted_stack_quantifiers(&root, &role_predicates, &quantifier_set);
    // scheme は stack model に残った id だけを量化する。量化されない id の weight は
    // compact から剥がし、使い切られた寿命境界が surface に漏れないようにする。
    let scheme_ids = stack_quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let stray_ids = all_stack_ids_in_root_and_roles(&root, &role_predicates)
        .difference(&scheme_ids)
        .copied()
        .collect::<FxHashSet<_>>();
    if !stray_ids.is_empty() {
        prune_dead_subtract_weights_in_root_and_roles(&mut root, &mut role_predicates, &stray_ids);
        quantifiers = quantified_vars_in_root_and_roles(
            machine,
            boundary,
            &root,
            &role_predicates,
            non_generic,
        );
        let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
        stack_quantifiers = sorted_stack_quantifiers(&root, &role_predicates, &quantifier_set);
    }
    GeneralizedCompactRoot {
        compact: root,
        role_predicates,
        quantifiers,
        stack_quantifiers,
        substitutions,
        sandwiches,
    }
}

pub(crate) fn finalize_generalized_compact_root_with_ancestors(
    types: &mut TypeArena,
    machine: &ConstraintMachine,
    root: &GeneralizedCompactRoot,
    ancestors: &[&GeneralizedCompactRoot],
) -> FinalizedGeneralizedCompactRoot {
    let mut root = root.clone();
    apply_ancestor_simplifications(&mut root, ancestors);
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(&mut root);
    cleanup_stack_weights_in_root_and_roles(&mut root.compact, &mut root.role_predicates);
    cleanup_empty_stack_entries_with_plain_negative_occurrence(
        &mut root.compact,
        &mut root.role_predicates,
    );
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(&mut root);
    let quantifier_set = root.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    root.stack_quantifiers =
        sorted_stack_quantifiers(&root.compact, &root.role_predicates, &quantifier_set);
    prune_unquantified_stack_weights(&mut root);
    finalize_generalized_compact_root(types, machine, &root)
}

#[cfg(test)]
pub(crate) fn quantified_vars(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<TypeVar> {
    quantified_vars_in_root_and_roles(machine, boundary, root, &[], non_generic)
}

fn quantified_vars_in_root_and_roles(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<TypeVar> {
    let mut vars = Vec::new();
    collect_root_free_vars(root, &mut vars);
    for role in role_predicates {
        collect_role_free_vars(role, &mut vars);
    }
    vars.retain(|var| machine.level_of(*var) > boundary && !non_generic.contains(var));
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    vars
}
