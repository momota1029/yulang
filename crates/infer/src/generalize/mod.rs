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
    CompactTuple, CompactType, CompactVar, CompactVarSubstitution, compact_con_entries,
    compact_row_item_entries, compact_type_var, finalize_compact_bounds,
    finalize_compact_bounds_lower, finalize_compact_bounds_upper, finalize_compact_root,
    merge_compact_types, simplify_compact_root_with_role_variance_table_and_non_generic,
    simplify_compact_root_with_roles_and_non_generic,
};
use crate::constraints::{ConstraintMachine, TypeLevel};
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
    let compact = compact_type_var(machine, root);
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
