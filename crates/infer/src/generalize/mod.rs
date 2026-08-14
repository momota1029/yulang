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
use crate::constraints::proof::ProjectionEvaluationRound;
use crate::constraints::{
    ConstraintMachine, ConstraintWeights, ProofFailure, ScopedLegacyProjectionQuery, TypeLevel,
};
use crate::roles::RoleInputVarianceTable;
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleImplCandidate,
};

mod core;
mod finalize;
mod provenance;
mod simplification;
#[cfg(test)]
mod tests;

use core::*;
pub(crate) use finalize::{
    clone_role_impl_candidate_between_arenas, finalize_compact_boundary_bounds,
    finalize_generalized_compact_root,
};
pub(crate) use provenance::capture_generalized_witnesses;
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

pub(crate) struct AliasExpandedCompactRoot {
    pub(crate) compact: CompactRoot,
    pub(crate) role_predicates: Vec<CompactRoleConstraint>,
    simplification: CompactSimplification,
}

pub(crate) struct StackCleanedCompactRoot {
    pub(crate) compact: CompactRoot,
    pub(crate) role_predicates: Vec<CompactRoleConstraint>,
    substitutions: Vec<CompactVarSubstitution>,
    sandwiches: Vec<CompactSandwich>,
}

pub(crate) struct FinalizedGeneralizedCompactRoot {
    pub(crate) scheme: Scheme,
}

pub(crate) fn generalize_type_var_with_boundaries(
    machine: &mut ConstraintMachine,
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
    machine: &mut ConstraintMachine,
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
    machine: &mut ConstraintMachine,
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

pub(crate) fn prepare_alias_expanded_compact_root_with_role_variances(
    machine: &mut ConstraintMachine,
    simplification_boundary: TypeLevel,
    mut compact: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    role_variances: &RoleInputVarianceTable,
    non_generic: &FxHashSet<TypeVar>,
) -> AliasExpandedCompactRoot {
    expand_positive_aliases_in_scheme_compact(machine, &mut compact, &mut role_predicates);
    let simplification = simplify_compact_root_with_role_variance_table_and_non_generic(
        machine,
        simplification_boundary,
        &mut compact,
        &mut role_predicates,
        role_variances,
        non_generic,
    );
    AliasExpandedCompactRoot {
        compact,
        role_predicates,
        simplification,
    }
}

pub(crate) fn prepare_stack_cleaned_alias_expanded_compact_root(
    machine: &ConstraintMachine,
    quantification_boundary: TypeLevel,
    prepared: AliasExpandedCompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> StackCleanedCompactRoot {
    prepare_stack_cleaned_compact_root(
        machine,
        quantification_boundary,
        prepared.compact,
        prepared.role_predicates,
        non_generic,
        prepared.simplification,
    )
}

pub(crate) fn generalize_stack_cleaned_compact_root(
    machine: &ConstraintMachine,
    quantification_boundary: TypeLevel,
    prepared: StackCleanedCompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    let StackCleanedCompactRoot {
        mut compact,
        mut role_predicates,
        substitutions,
        sandwiches,
    } = prepared;
    cleanup_empty_stack_entries_with_plain_negative_occurrence(&mut compact, &mut role_predicates);
    let mut quantifiers = quantified_vars_in_root_and_roles(
        machine,
        quantification_boundary,
        &compact,
        &role_predicates,
        non_generic,
    );
    let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let mut stack_quantifiers =
        sorted_stack_quantifiers(&compact, &role_predicates, &quantifier_set);
    extend_declared_all_stack_quantifiers(
        machine,
        &compact,
        &role_predicates,
        &mut stack_quantifiers,
    );
    // scheme は stack model に残った id だけを量化する。量化されない id の weight は
    // compact から剥がし、使い切られた寿命境界が surface に漏れないようにする。
    let scheme_ids = stack_quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let stray_ids = all_stack_ids_in_root_and_roles(&compact, &role_predicates)
        .difference(&scheme_ids)
        .copied()
        .collect::<FxHashSet<_>>();
    if !stray_ids.is_empty() {
        prune_dead_subtract_weights_in_root_and_roles(
            &mut compact,
            &mut role_predicates,
            &stray_ids,
        );
        quantifiers = quantified_vars_in_root_and_roles(
            machine,
            quantification_boundary,
            &compact,
            &role_predicates,
            non_generic,
        );
        let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
        stack_quantifiers = sorted_stack_quantifiers(&compact, &role_predicates, &quantifier_set);
        extend_declared_all_stack_quantifiers(
            machine,
            &compact,
            &role_predicates,
            &mut stack_quantifiers,
        );
    }
    GeneralizedCompactRoot {
        compact,
        role_predicates,
        quantifiers,
        stack_quantifiers,
        substitutions,
        sandwiches,
    }
}

#[allow(
    dead_code,
    reason = "Stage 2 ownership discovery is consumed by the pending cache-interface finalizer wiring"
)]
pub(crate) fn generalized_compact_boundary_vars(root: &GeneralizedCompactRoot) -> Vec<TypeVar> {
    let local = root
        .quantifiers
        .iter()
        .copied()
        .chain(root.compact.rec_vars.iter().map(|rec| rec.var))
        .collect::<FxHashSet<_>>();
    let mut vars = Vec::new();
    collect_root_free_vars(&root.compact, &mut vars);
    for role in &root.role_predicates {
        collect_role_free_vars(role, &mut vars);
    }
    vars.retain(|var| !local.contains(var));
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    vars
}

#[allow(
    dead_code,
    reason = "Stage 2 bound closure is consumed by the pending cache-interface finalizer wiring"
)]
pub(crate) fn compact_boundary_bound_vars(bounds: &CompactBounds) -> Vec<TypeVar> {
    let mut vars = Vec::new();
    collect_bounds_free_vars(bounds, &mut vars);
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    vars
}

pub(crate) fn prune_generalized_compact_root_for_cache(root: &mut GeneralizedCompactRoot) {
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(root);
}

fn expand_positive_aliases_in_scheme_compact(
    machine: &mut ConstraintMachine,
    compact: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) {
    let allowed = compact_scheme_vars(compact, role_predicates);
    let mut round_state = machine.new_projection_evaluation_round();
    // The entire root/recursive-variable/role walk shares one immutable legacy query scope. Its
    // proof-validation, alias cache, and visiting state all disappear before simplification can
    // resume through a shared machine reborrow.
    let _ = machine.with_legacy_projection_query(&mut round_state, |query| {
        let mut cache = FxHashMap::default();
        let mut visiting = FxHashSet::default();
        let mut projection_round = ProjectionEvaluationRound::new();
        expand_positive_aliases_in_type(
            &query,
            &allowed,
            &mut cache,
            &mut visiting,
            &mut projection_round,
            &mut compact.root,
            AliasPolarity::Positive,
        )?;
        for rec in &mut compact.rec_vars {
            expand_positive_aliases_in_bounds(
                &query,
                &allowed,
                &mut cache,
                &mut visiting,
                &mut projection_round,
                &mut rec.bounds,
                AliasPolarity::Positive,
            )?;
        }
        for role in role_predicates {
            for input in &mut role.inputs {
                expand_positive_aliases_in_bounds(
                    &query,
                    &allowed,
                    &mut cache,
                    &mut visiting,
                    &mut projection_round,
                    &mut input.bounds,
                    AliasPolarity::Positive,
                )?;
            }
            for associated in &mut role.associated {
                expand_positive_aliases_in_bounds(
                    &query,
                    &allowed,
                    &mut cache,
                    &mut visiting,
                    &mut projection_round,
                    &mut associated.value.bounds,
                    AliasPolarity::Positive,
                )?;
            }
        }
        Ok(query.complete(()))
    });
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

fn expand_positive_aliases_in_type<'scope>(
    query: &'scope ScopedLegacyProjectionQuery<'_>,
    allowed: &FxHashSet<TypeVar>,
    cache: &mut FxHashMap<TypeVar, Vec<TypeVar>>,
    visiting: &mut FxHashSet<TypeVar>,
    projection_round: &mut ProjectionEvaluationRound<'scope>,
    ty: &mut CompactType,
    polarity: AliasPolarity,
) -> Result<(), ProofFailure> {
    if polarity.is_positive() {
        let vars = ty.vars.clone();
        for var in vars {
            for alias in positive_aliases_within_scheme(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                var.var,
            )? {
                let alias_var = CompactVar::covariant(alias, var.weight.clone())
                    .with_origin(CompactVarOrigin::Secondary);
                push_compact_var_alias(&mut ty.vars, alias_var);
            }
        }
    }

    for args in ty.cons.values_mut() {
        for arg in args {
            expand_positive_aliases_in_bounds(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                arg,
                polarity,
            )?;
        }
    }
    for fun in &mut ty.funs {
        expand_positive_aliases_in_type(
            query,
            allowed,
            cache,
            visiting,
            projection_round,
            &mut fun.arg,
            polarity.flipped(),
        )?;
        expand_positive_aliases_in_type(
            query,
            allowed,
            cache,
            visiting,
            projection_round,
            &mut fun.arg_eff,
            polarity.flipped(),
        )?;
        expand_positive_aliases_in_type(
            query,
            allowed,
            cache,
            visiting,
            projection_round,
            &mut fun.ret_eff,
            polarity,
        )?;
        expand_positive_aliases_in_type(
            query,
            allowed,
            cache,
            visiting,
            projection_round,
            &mut fun.ret,
            polarity,
        )?;
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            expand_positive_aliases_in_type(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                &mut field.value,
                polarity,
            )?;
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            expand_positive_aliases_in_type(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                &mut field.value,
                polarity,
            )?;
        }
        expand_positive_aliases_in_type(
            query,
            allowed,
            cache,
            visiting,
            projection_round,
            &mut spread.tail,
            polarity,
        )?;
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                expand_positive_aliases_in_type(
                    query,
                    allowed,
                    cache,
                    visiting,
                    projection_round,
                    payload,
                    polarity,
                )?;
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            expand_positive_aliases_in_type(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                item,
                polarity,
            )?;
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                expand_positive_aliases_in_bounds(
                    query,
                    allowed,
                    cache,
                    visiting,
                    projection_round,
                    arg,
                    polarity,
                )?;
            }
        }
        expand_positive_aliases_in_type(
            query,
            allowed,
            cache,
            visiting,
            projection_round,
            &mut row.tail,
            polarity,
        )?;
    }
    Ok(())
}

fn expand_positive_aliases_in_bounds<'scope>(
    query: &'scope ScopedLegacyProjectionQuery<'_>,
    allowed: &FxHashSet<TypeVar>,
    cache: &mut FxHashMap<TypeVar, Vec<TypeVar>>,
    visiting: &mut FxHashSet<TypeVar>,
    projection_round: &mut ProjectionEvaluationRound<'scope>,
    bounds: &mut CompactBounds,
    polarity: AliasPolarity,
) -> Result<(), ProofFailure> {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            expand_positive_aliases_in_type(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                lower,
                polarity,
            )?;
            expand_positive_aliases_in_type(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                upper,
                polarity.flipped(),
            )?;
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                expand_positive_aliases_in_bounds(
                    query,
                    allowed,
                    cache,
                    visiting,
                    projection_round,
                    arg,
                    polarity,
                )?;
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            expand_positive_aliases_in_bounds(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                arg,
                polarity.flipped(),
            )?;
            expand_positive_aliases_in_bounds(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                arg_eff,
                polarity.flipped(),
            )?;
            expand_positive_aliases_in_bounds(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                ret_eff,
                polarity,
            )?;
            expand_positive_aliases_in_bounds(
                query,
                allowed,
                cache,
                visiting,
                projection_round,
                ret,
                polarity,
            )?;
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                expand_positive_aliases_in_bounds(
                    query,
                    allowed,
                    cache,
                    visiting,
                    projection_round,
                    &mut field.value,
                    polarity,
                )?;
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    expand_positive_aliases_in_bounds(
                        query,
                        allowed,
                        cache,
                        visiting,
                        projection_round,
                        payload,
                        polarity,
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn positive_aliases_within_scheme<'scope>(
    query: &'scope ScopedLegacyProjectionQuery<'_>,
    allowed: &FxHashSet<TypeVar>,
    cache: &mut FxHashMap<TypeVar, Vec<TypeVar>>,
    visiting: &mut FxHashSet<TypeVar>,
    projection_round: &mut ProjectionEvaluationRound<'scope>,
    var: TypeVar,
) -> Result<Vec<TypeVar>, ProofFailure> {
    if let Some(cached) = cache.get(&var) {
        return Ok(cached.clone());
    }
    if !visiting.insert(var) {
        return Ok(Vec::new());
    }

    let mut out = Vec::new();
    for entry in query.scheme_projectable_lowers_in_scope(var, projection_round)? {
        let bound = entry.bound;
        if !alias_neutral_constraint(&bound.weights) {
            continue;
        }
        let Some(next) = query.pos_var_in_scope(bound.pos) else {
            continue;
        };
        if !allowed.contains(&next) {
            continue;
        }
        push_unique_var(&mut out, next);
        for alias in
            positive_aliases_within_scheme(query, allowed, cache, visiting, projection_round, next)?
        {
            push_unique_var(&mut out, alias);
        }
    }

    visiting.remove(&var);
    cache.insert(var, out.clone());
    Ok(out)
}

#[cfg(test)]
pub(crate) fn positive_aliases_within_scheme_for_cpk_test(
    machine: &mut ConstraintMachine,
    allowed: impl IntoIterator<Item = TypeVar>,
    var: TypeVar,
) -> Vec<TypeVar> {
    let allowed = allowed.into_iter().collect();
    let mut round_state = machine.new_projection_evaluation_round();
    machine
        .with_legacy_projection_query(&mut round_state, |query| {
            let mut projection_round = ProjectionEvaluationRound::new();
            let aliases = positive_aliases_within_scheme(
                &query,
                &allowed,
                &mut FxHashMap::default(),
                &mut FxHashSet::default(),
                &mut projection_round,
                var,
            )?;
            Ok(query.complete(aliases))
        })
        .unwrap_or_default()
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
    machine: &mut ConstraintMachine,
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
    machine: &mut ConstraintMachine,
    boundary: TypeLevel,
    root: CompactRoot,
    non_generic: &FxHashSet<TypeVar>,
) -> GeneralizedCompactRoot {
    generalize_prepared_compact_root_with_roles(machine, boundary, root, Vec::new(), non_generic)
}

fn generalize_compact_root_with_simplification(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: CompactRoot,
    role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
    simplification: CompactSimplification,
) -> GeneralizedCompactRoot {
    let prepared = prepare_stack_cleaned_compact_root(
        machine,
        boundary,
        root,
        role_predicates,
        non_generic,
        simplification,
    );
    generalize_stack_cleaned_compact_root(machine, boundary, prepared, non_generic)
}

fn prepare_stack_cleaned_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut root: CompactRoot,
    mut role_predicates: Vec<CompactRoleConstraint>,
    non_generic: &FxHashSet<TypeVar>,
    simplification: CompactSimplification,
) -> StackCleanedCompactRoot {
    let substitutions = simplification.substitutions;
    let sandwiches = simplification.sandwiches;
    prune_unreachable_recursive_bounds(&mut root, &role_predicates);

    let quantifiers =
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
    cleanup_stack_weights_in_root_and_roles(machine, &mut root, &mut role_predicates);
    StackCleanedCompactRoot {
        compact: root,
        role_predicates,
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
    cleanup_stack_weights_in_root_and_roles(machine, &mut root.compact, &mut root.role_predicates);
    cleanup_empty_stack_entries_with_plain_negative_occurrence(
        &mut root.compact,
        &mut root.role_predicates,
    );
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(&mut root);
    let quantifier_set = root.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    root.stack_quantifiers =
        sorted_stack_quantifiers(&root.compact, &root.role_predicates, &quantifier_set);
    extend_declared_all_stack_quantifiers(
        machine,
        &root.compact,
        &root.role_predicates,
        &mut root.stack_quantifiers,
    );
    prune_unquantified_stack_weights(&mut root);
    finalize_generalized_compact_root(types, machine, &root)
}

fn extend_declared_all_stack_quantifiers(
    machine: &ConstraintMachine,
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
    stack_quantifiers: &mut Vec<SubtractId>,
) {
    let mut ids = all_stack_ids_in_root_and_roles(root, role_predicates)
        .into_iter()
        .filter(|id| {
            machine
                .subtracts()
                .fact_by_id(*id)
                .is_some_and(|fact| matches!(fact.subtractability, Subtractability::All))
        })
        .collect::<Vec<_>>();
    if ids.is_empty() {
        return;
    }
    stack_quantifiers.append(&mut ids);
    stack_quantifiers.sort_by_key(|id| id.0);
    stack_quantifiers.dedup();
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
