//! Reachable role constraints を compact 上で統合し、解ける role を制約へ戻す補助処理。
//!
//! role の通常引数は不変なので、同じ role で入力変数を共有する constraint は先に一つへ畳む。
//! その後、入力が concrete に一意決定し、登録済み impl candidate が一つに絞れる場合だけ解決する。

mod matchers;
mod rewrite;
mod taint;
mod vars;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compact::{
    CompactBounds, CompactCon, CompactConMap, CompactFun, CompactMergeConstraint,
    CompactPolyVariant, CompactRecord, CompactRecordSpread, CompactRoleArg,
    CompactRoleAssociatedType, CompactRoleConstraint, CompactRoot, CompactRow, CompactRowItemMap,
    CompactTuple, CompactType, compact_con_entries, compact_role_constraint,
    compact_row_item_entries, merge_compact_bounds_recording_merge_constraints,
    merge_compact_types, merge_cons, simplify_compact_root_with_roles_and_non_generic,
};
use crate::constraints::{ConstraintMachine, TypeLevel};
use crate::roles::{RoleConstraint, RoleImplCandidate, RoleImplTable};
use poly::expr::SelectId;
use poly::types::{BuiltinType, RecordField, TypeVar};

use matchers::*;
use rewrite::*;
use taint::*;
use vars::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct RoleResolutionKey {
    pub(crate) demand: CompactRoleConstraint,
    pub(crate) candidate: CompactRoleConstraint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RoleResolution {
    pub(crate) key: RoleResolutionKey,
    pub(crate) demand: CompactRoleConstraint,
    pub(crate) candidate: CompactRoleConstraint,
    pub(crate) solved_prerequisites: Vec<RoleResolution>,
    pub(crate) residual_prerequisites: Vec<CompactRoleConstraint>,
}

#[cfg(test)]
pub(crate) fn coalesce_role_constraints(
    constraints: Vec<CompactRoleConstraint>,
) -> Vec<CompactRoleConstraint> {
    coalesce_role_constraints_recording_merge_constraints(constraints).0
}

pub(crate) fn coalesce_role_constraints_recording_merge_constraints(
    constraints: Vec<CompactRoleConstraint>,
) -> (Vec<CompactRoleConstraint>, Vec<CompactMergeConstraint>) {
    let mut out = Vec::new();
    let mut merge_constraints = Vec::new();
    let mut visited = vec![false; constraints.len()];
    for index in 0..constraints.len() {
        if visited[index] {
            continue;
        }
        visited[index] = true;
        let mut component = vec![index];
        let mut cursor = 0;
        while cursor < component.len() {
            let current = component[cursor];
            cursor += 1;
            for other in 0..constraints.len() {
                if visited[other] {
                    continue;
                }
                if role_constraints_share_input_vars(&constraints[current], &constraints[other]) {
                    visited[other] = true;
                    component.push(other);
                }
            }
        }
        out.push(merge_role_constraint_component(
            component
                .into_iter()
                .map(|index| constraints[index].clone()),
            &mut merge_constraints,
        ));
    }
    (out, merge_constraints)
}

pub(crate) fn resolve_role_constraints(
    machine: &ConstraintMachine,
    main: &CompactRoot,
    constraints: &[CompactRoleConstraint],
    impls: &RoleImplTable,
    applied: &FxHashSet<RoleResolutionKey>,
) -> Vec<RoleResolution> {
    resolve_role_constraints_with_method_taint(
        machine,
        main,
        constraints,
        impls,
        applied,
        &FxHashMap::default(),
    )
}

pub(crate) fn resolve_role_constraints_with_method_taint(
    machine: &ConstraintMachine,
    main: &CompactRoot,
    constraints: &[CompactRoleConstraint],
    impls: &RoleImplTable,
    applied: &FxHashSet<RoleResolutionKey>,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> Vec<RoleResolution> {
    let mut out = Vec::new();
    let main_polarity = MainPolarity::collect(main);
    for constraint in constraints {
        let candidates = impls
            .candidates(&constraint.role)
            .iter()
            .filter_map(|candidate| {
                resolve_role_candidate(
                    machine,
                    constraint,
                    candidate,
                    &main_polarity,
                    method_taint,
                    impls,
                    &mut FxHashSet::default(),
                )
            })
            .collect::<Vec<_>>();
        if candidates.len() != 1 {
            continue;
        }
        let resolved = candidates.into_iter().next().expect("candidate");
        let key = RoleResolutionKey {
            demand: constraint.clone(),
            candidate: resolved.candidate.clone(),
        };
        if applied.contains(&key) {
            continue;
        }
        out.push(RoleResolution {
            key,
            demand: constraint.clone(),
            candidate: resolved.candidate,
            solved_prerequisites: resolved.solved_prerequisites,
            residual_prerequisites: resolved.residual_prerequisites,
        });
    }
    out
}

/// 入力がすべて concrete 成分を持つ時だけ true。
///
/// `resolve_role_constraints` は入力が concrete に一意決定しないと発火しないので、
/// 入力が純粋な変数のままの constraint は impl 側の準備（impl member の世代化順序）を
/// 必要としない。role method 宣言の `'a: Role` がここで弾かれないと、
/// method → 全 impl member の依存辺が impl body の method 使用と偽サイクルを閉じ、
/// SCC 融合で各 use site の receiver が signature へ union されてしまう。
pub(crate) fn role_constraint_could_resolve(constraint: &CompactRoleConstraint) -> bool {
    constraint
        .inputs
        .iter()
        .all(role_arg_has_concrete_component)
}

fn role_arg_has_concrete_component(arg: &CompactRoleArg) -> bool {
    compact_bounds_has_concrete_component(&arg.bounds)
}

fn compact_bounds_has_concrete_component(bounds: &CompactBounds) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            has_concrete_component(lower) || has_concrete_component(upper)
        }
        _ => compact_type_from_bounds(bounds).is_some_and(|ty| has_concrete_component(&ty)),
    }
}

fn has_concrete_component(ty: &CompactType) -> bool {
    ty.never
        || !ty.builtins.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

#[derive(Debug, Clone)]
struct ResolvedCandidate {
    candidate: CompactRoleConstraint,
    solved_prerequisites: Vec<RoleResolution>,
    residual_prerequisites: Vec<CompactRoleConstraint>,
}

#[derive(Debug, Clone)]
struct ResolvedPrerequisites {
    solved: Vec<RoleResolution>,
    residuals: Vec<CompactRoleConstraint>,
}

fn resolve_role_candidate(
    machine: &ConstraintMachine,
    constraint: &CompactRoleConstraint,
    candidate: &RoleImplCandidate,
    main_polarity: &MainPolarity,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
    impls: &RoleImplTable,
    stack: &mut FxHashSet<RoleResolutionKey>,
) -> Option<ResolvedCandidate> {
    if constraint.inputs.len() != candidate.inputs.len() {
        return None;
    }
    let raw_candidate = candidate;
    let candidate = compact_role_impl_candidate(machine, raw_candidate);
    let mut subst = TypeSubst::default();
    for (demand, candidate) in constraint.inputs.iter().zip(&candidate.inputs) {
        let demand = role_arg_concrete_type(demand, main_polarity, method_taint)?;
        if !match_role_arg_candidate(candidate, &demand, &mut subst) {
            return None;
        }
    }

    let candidate = rewrite_role_constraint(&candidate, &subst);
    let key = RoleResolutionKey {
        demand: constraint.clone(),
        candidate: candidate.clone(),
    };
    if !stack.insert(key.clone()) {
        return None;
    }
    let prerequisites = resolve_candidate_prerequisites(
        machine,
        &raw_candidate.prerequisites,
        &subst,
        impls,
        main_polarity,
        method_taint,
        stack,
    );
    stack.remove(&key);

    Some(ResolvedCandidate {
        candidate,
        solved_prerequisites: prerequisites.solved,
        residual_prerequisites: prerequisites.residuals,
    })
}

fn compact_role_impl_candidate(
    machine: &ConstraintMachine,
    candidate: &RoleImplCandidate,
) -> CompactRoleConstraint {
    let mut root = CompactRoot::default();
    let mut roles = vec![compact_role_constraint(machine, &candidate.as_constraint())];
    simplify_compact_root_with_roles_and_non_generic(
        machine,
        TypeLevel::root(),
        &mut root,
        &mut roles,
        &FxHashSet::default(),
    );
    roles.pop().expect("candidate role should remain present")
}

fn resolve_candidate_prerequisites(
    machine: &ConstraintMachine,
    prerequisites: &[RoleConstraint],
    subst: &TypeSubst,
    impls: &RoleImplTable,
    main_polarity: &MainPolarity,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
    stack: &mut FxHashSet<RoleResolutionKey>,
) -> ResolvedPrerequisites {
    let mut solved_prerequisites = Vec::new();
    let mut residual_prerequisites = Vec::new();
    for prerequisite in prerequisites {
        let prerequisite =
            rewrite_role_constraint(&compact_role_constraint(machine, prerequisite), subst);
        let candidates = impls
            .candidates(&prerequisite.role)
            .iter()
            .filter_map(|candidate| {
                resolve_role_candidate(
                    machine,
                    &prerequisite,
                    candidate,
                    main_polarity,
                    method_taint,
                    impls,
                    stack,
                )
            })
            .collect::<Vec<_>>();
        if candidates.len() == 1 {
            let resolved = candidates.into_iter().next().expect("candidate");
            solved_prerequisites.push(RoleResolution {
                key: RoleResolutionKey {
                    demand: prerequisite.clone(),
                    candidate: resolved.candidate.clone(),
                },
                demand: prerequisite,
                candidate: resolved.candidate,
                solved_prerequisites: resolved.solved_prerequisites,
                residual_prerequisites: resolved.residual_prerequisites,
            });
        } else {
            residual_prerequisites.push(prerequisite);
        }
    }
    ResolvedPrerequisites {
        solved: solved_prerequisites,
        residuals: residual_prerequisites,
    }
}

fn role_constraints_share_input_vars(
    lhs: &CompactRoleConstraint,
    rhs: &CompactRoleConstraint,
) -> bool {
    if lhs.role != rhs.role || lhs.inputs.len() != rhs.inputs.len() {
        return false;
    }
    if lhs == rhs {
        return true;
    }
    !lhs.inputs.is_empty()
        && lhs.inputs.iter().zip(&rhs.inputs).all(|(lhs, rhs)| {
            let lhs_vars = role_arg_vars(lhs);
            let rhs_vars = role_arg_vars(rhs);
            !lhs_vars.is_disjoint(&rhs_vars)
        })
}

fn merge_role_constraint_component(
    constraints: impl Iterator<Item = CompactRoleConstraint>,
    merge_constraints: &mut Vec<CompactMergeConstraint>,
) -> CompactRoleConstraint {
    let mut constraints = constraints.peekable();
    let mut merged = constraints
        .next()
        .expect("role component must not be empty");
    for constraint in constraints {
        merged.inputs = merged
            .inputs
            .into_iter()
            .zip(constraint.inputs)
            .map(|(lhs, rhs)| merge_role_arg(lhs, rhs, merge_constraints))
            .collect();
        for associated in constraint.associated {
            if let Some(existing) = merged
                .associated
                .iter_mut()
                .find(|existing| existing.name == associated.name)
            {
                existing.value =
                    merge_role_arg(existing.value.clone(), associated.value, merge_constraints);
            } else {
                merged.associated.push(associated);
            }
        }
    }
    merged
        .associated
        .sort_by(|lhs, rhs| lhs.name.cmp(&rhs.name));
    merged
}

fn merge_role_arg(
    lhs: CompactRoleArg,
    rhs: CompactRoleArg,
    merge_constraints: &mut Vec<CompactMergeConstraint>,
) -> CompactRoleArg {
    let polarity = if lhs.polarity == rhs.polarity {
        lhs.polarity
    } else {
        crate::compact::CompactRoleArgPolarity::Invariant
    };
    let (bounds, recorded) =
        merge_compact_bounds_recording_merge_constraints(true, lhs.bounds, rhs.bounds);
    merge_constraints.extend(recorded);
    CompactRoleArg::invariant(bounds).with_polarity(polarity)
}

fn role_arg_concrete_type(
    arg: &CompactRoleArg,
    main_polarity: &MainPolarity,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> Option<CompactType> {
    let lower_boundary = role_arg_boundary_type(arg, true);
    let lower = lower_boundary.as_ref().and_then(single_concrete_type);
    if let Some(lower_ty) = &lower
        && role_arg_lower_allowed(arg, lower_ty, main_polarity)
        && !role_arg_boundary_has_method_taint(arg, true, method_taint)
    {
        return lower;
    }
    let upper_boundary = role_arg_boundary_type(arg, false);
    let upper = upper_boundary.as_ref().and_then(single_concrete_type);
    if upper.is_some()
        && role_arg_allowed_by_main_polarity(arg, false, main_polarity)
        && !role_arg_boundary_has_method_taint(arg, false, method_taint)
    {
        return upper;
    }
    None
}

fn role_arg_boundary_type(arg: &CompactRoleArg, positive: bool) -> Option<CompactType> {
    match &arg.bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            Some(if positive { lower } else { upper }.clone())
        }
        bounds => compact_type_from_bounds(bounds),
    }
}
