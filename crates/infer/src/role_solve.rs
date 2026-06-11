//! Reachable role constraints を compact 上で統合し、解ける role を制約へ戻す補助処理。
//!
//! role の通常引数は不変なので、同じ role で入力変数を共有する constraint は先に一つへ畳む。
//! その後、入力が concrete に一意決定し、登録済み impl candidate が一つに絞れる場合だけ解決する。

use rustc_hash::{FxHashMap, FxHashSet};

use crate::compact::{
    CompactBounds, CompactCon, CompactFun, CompactPolyVariant, CompactRecord, CompactRecordSpread,
    CompactRoleArg, CompactRoleAssociatedType, CompactRoleConstraint, CompactRoot, CompactRow,
    CompactTuple, CompactType, compact_role_constraint, merge_compact_types,
};
use crate::constraints::ConstraintMachine;
use crate::roles::{RoleConstraint, RoleImplCandidate, RoleImplTable};
use poly::expr::SelectId;
use poly::types::{BuiltinType, RecordField, TypeVar};

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

pub(crate) fn coalesce_role_constraints(
    constraints: Vec<CompactRoleConstraint>,
) -> Vec<CompactRoleConstraint> {
    let mut out = Vec::new();
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
        ));
    }
    out
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
        .all(|arg| has_concrete_component(&arg.lower) || has_concrete_component(&arg.upper))
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
    let candidate = compact_role_constraint(machine, &raw_candidate.as_constraint());
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

#[derive(Default, Clone)]
struct TypeSubst {
    vars: FxHashMap<TypeVar, CompactType>,
}

impl TypeSubst {
    fn bind(&mut self, var: TypeVar, ty: CompactType) -> bool {
        let ty = canonical_substitution_type(ty);
        let Some(existing) = self.vars.get(&var) else {
            self.vars.insert(var, ty);
            return true;
        };
        existing == &ty
    }

    fn get(&self, var: TypeVar) -> Option<&CompactType> {
        self.vars.get(&var)
    }
}

fn match_role_arg_candidate(
    candidate: &CompactRoleArg,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    let mut matched = false;
    if !compact_type_is_empty(&candidate.lower) {
        if !match_type_pattern(&candidate.lower, demand, true, subst) {
            return false;
        }
        matched = true;
    }
    if !compact_type_is_empty(&candidate.upper) {
        if !match_type_pattern(&candidate.upper, demand, false, subst) {
            return false;
        }
        matched = true;
    }
    matched
}

fn match_type_pattern(
    pattern: &CompactType,
    demand: &CompactType,
    positive: bool,
    subst: &mut TypeSubst,
) -> bool {
    let mut matched = false;
    for var in &pattern.vars {
        if !subst.bind(var.var, demand.clone()) {
            return false;
        }
        matched = true;
    }
    if pattern.never {
        if !demand.never {
            return false;
        }
        matched = true;
    }
    for builtin in &pattern.builtins {
        if !demand_has_builtin(demand, *builtin) {
            return false;
        }
        matched = true;
    }
    for con in &pattern.cons {
        if !match_con_pattern(con, demand, subst) {
            return false;
        }
        matched = true;
    }
    for fun in &pattern.funs {
        if !match_fun_pattern(fun, demand, subst) {
            return false;
        }
        matched = true;
    }
    for record in &pattern.records {
        if !match_record_pattern(record, demand, subst) {
            return false;
        }
        matched = true;
    }
    for spread in &pattern.record_spreads {
        if !match_record_spread_pattern(spread, demand, subst) {
            return false;
        }
        matched = true;
    }
    for variant in &pattern.poly_variants {
        if !match_poly_variant_pattern(variant, demand, subst) {
            return false;
        }
        matched = true;
    }
    for tuple in &pattern.tuples {
        if !match_tuple_pattern(tuple, demand, subst) {
            return false;
        }
        matched = true;
    }
    for row in &pattern.rows {
        if !match_row_pattern(row, demand, subst) {
            return false;
        }
        matched = true;
    }
    matched || (compact_type_is_empty(pattern) && compact_type_is_empty(demand) && positive)
}

fn match_con_pattern(pattern: &CompactCon, demand: &CompactType, subst: &mut TypeSubst) -> bool {
    if pattern.args.is_empty()
        && let Some(builtin) = builtin_for_path(&pattern.path)
    {
        return demand_has_builtin(demand, builtin);
    }
    match_alternative(subst, demand.cons.iter(), |demand, subst| {
        pattern.path == demand.path
            && pattern.args.len() == demand.args.len()
            && pattern
                .args
                .iter()
                .zip(&demand.args)
                .all(|(pattern, demand)| match_bounds_pattern(pattern, demand, subst))
    })
}

fn match_fun_pattern(pattern: &CompactFun, demand: &CompactType, subst: &mut TypeSubst) -> bool {
    match_alternative(subst, demand.funs.iter(), |demand, subst| {
        match_type_pattern(&pattern.arg, &demand.arg, false, subst)
            && match_type_pattern(&pattern.arg_eff, &demand.arg_eff, false, subst)
            && match_type_pattern(&pattern.ret_eff, &demand.ret_eff, true, subst)
            && match_type_pattern(&pattern.ret, &demand.ret, true, subst)
    })
}

fn match_record_pattern(
    pattern: &CompactRecord,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.records.iter(), |demand, subst| {
        match_record_fields(&pattern.fields, &demand.fields, subst)
    })
}

fn match_record_spread_pattern(
    pattern: &CompactRecordSpread,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.record_spreads.iter(), |demand, subst| {
        pattern.tail_wins == demand.tail_wins
            && match_record_fields(&pattern.fields, &demand.fields, subst)
            && match_type_pattern(&pattern.tail, &demand.tail, true, subst)
    })
}

fn match_record_fields(
    pattern: &[RecordField<CompactType>],
    demand: &[RecordField<CompactType>],
    subst: &mut TypeSubst,
) -> bool {
    pattern.iter().all(|pattern| {
        demand
            .iter()
            .find(|demand| demand.name == pattern.name && demand.optional == pattern.optional)
            .is_some_and(|demand| match_type_pattern(&pattern.value, &demand.value, true, subst))
    })
}

fn match_poly_variant_pattern(
    pattern: &CompactPolyVariant,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.poly_variants.iter(), |demand, subst| {
        pattern.items.iter().all(|(name, pattern_payloads)| {
            demand
                .items
                .iter()
                .find(|(demand_name, _)| demand_name == name)
                .is_some_and(|(_, demand_payloads)| {
                    pattern_payloads.len() == demand_payloads.len()
                        && pattern_payloads
                            .iter()
                            .zip(demand_payloads)
                            .all(|(pattern, demand)| {
                                match_type_pattern(pattern, demand, true, subst)
                            })
                })
        })
    })
}

fn match_tuple_pattern(
    pattern: &CompactTuple,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.tuples.iter(), |demand, subst| {
        pattern.items.len() == demand.items.len()
            && pattern
                .items
                .iter()
                .zip(&demand.items)
                .all(|(pattern, demand)| match_type_pattern(pattern, demand, true, subst))
    })
}

fn match_row_pattern(pattern: &CompactRow, demand: &CompactType, subst: &mut TypeSubst) -> bool {
    match_alternative(subst, demand.rows.iter(), |demand, subst| {
        pattern.items.len() == demand.items.len()
            && pattern
                .items
                .iter()
                .zip(&demand.items)
                .all(|(pattern, demand)| match_type_pattern(pattern, demand, true, subst))
            && match_type_pattern(&pattern.tail, &demand.tail, true, subst)
    })
}

fn match_alternative<'a, T: 'a>(
    subst: &mut TypeSubst,
    alternatives: impl Iterator<Item = &'a T>,
    mut matches: impl FnMut(&'a T, &mut TypeSubst) -> bool,
) -> bool {
    for alternative in alternatives {
        let mut candidate_subst = subst.clone();
        if matches(alternative, &mut candidate_subst) {
            *subst = candidate_subst;
            return true;
        }
    }
    false
}

fn match_bounds_pattern(
    pattern: &CompactBounds,
    demand: &CompactBounds,
    subst: &mut TypeSubst,
) -> bool {
    match pattern {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            let Some(demand_ty) = compact_type_from_bounds(demand) else {
                return false;
            };
            if !subst.bind(*self_var, demand_ty.clone()) {
                return false;
            }
            match demand {
                CompactBounds::Interval {
                    lower: demand_lower,
                    upper: demand_upper,
                    ..
                } => {
                    (compact_type_is_empty(lower)
                        || match_type_pattern(lower, demand_lower, true, subst))
                        && (compact_type_is_empty(upper)
                            || match_type_pattern(upper, demand_upper, false, subst))
                }
                _ => {
                    (compact_type_is_empty(lower)
                        || match_type_pattern(lower, &demand_ty, true, subst))
                        && (compact_type_is_empty(upper)
                            || match_type_pattern(upper, &demand_ty, false, subst))
                }
            }
        }
        CompactBounds::Con { path, args } => {
            let pattern = CompactType::from_con(CompactCon {
                path: path.clone(),
                args: args.clone(),
            });
            let Some(demand) = compact_type_from_bounds(demand) else {
                return false;
            };
            match_type_pattern(&pattern, &demand, true, subst)
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let Some(arg) = compact_type_from_bounds(arg) else {
                return false;
            };
            let Some(arg_eff) = compact_type_from_bounds(arg_eff) else {
                return false;
            };
            let Some(ret_eff) = compact_type_from_bounds(ret_eff) else {
                return false;
            };
            let Some(ret) = compact_type_from_bounds(ret) else {
                return false;
            };
            let pattern = CompactType::from_fun(CompactFun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            });
            let Some(demand) = compact_type_from_bounds(demand) else {
                return false;
            };
            match_type_pattern(&pattern, &demand, true, subst)
        }
        CompactBounds::Record { fields } => {
            let Some(fields) = fields
                .iter()
                .map(|field| {
                    compact_type_from_bounds(&field.value).map(|value| RecordField {
                        name: field.name.clone(),
                        value,
                        optional: field.optional,
                    })
                })
                .collect::<Option<Vec<_>>>()
            else {
                return false;
            };
            let pattern = CompactType::from_record(CompactRecord { fields });
            let Some(demand) = compact_type_from_bounds(demand) else {
                return false;
            };
            match_type_pattern(&pattern, &demand, true, subst)
        }
        CompactBounds::PolyVariant { items } => {
            let Some(items) = items
                .iter()
                .map(|(name, payloads)| {
                    payloads
                        .iter()
                        .map(compact_type_from_bounds)
                        .collect::<Option<Vec<_>>>()
                        .map(|payloads| (name.clone(), payloads))
                })
                .collect::<Option<Vec<_>>>()
            else {
                return false;
            };
            let pattern = CompactType::from_poly_variant(CompactPolyVariant { items });
            let Some(demand) = compact_type_from_bounds(demand) else {
                return false;
            };
            match_type_pattern(&pattern, &demand, true, subst)
        }
        CompactBounds::Tuple { items } => {
            let Some(items) = items
                .iter()
                .map(compact_type_from_bounds)
                .collect::<Option<Vec<_>>>()
            else {
                return false;
            };
            let pattern = CompactType::from_tuple(CompactTuple { items });
            let Some(demand) = compact_type_from_bounds(demand) else {
                return false;
            };
            match_type_pattern(&pattern, &demand, true, subst)
        }
    }
}

fn demand_has_builtin(demand: &CompactType, builtin: BuiltinType) -> bool {
    demand.builtins.contains(&builtin)
        || demand
            .cons
            .iter()
            .any(|con| con.args.is_empty() && builtin_for_path(&con.path) == Some(builtin))
}

fn compact_type_from_bounds(bounds: &CompactBounds) -> Option<CompactType> {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => single_concrete_type(lower)
            .or_else(|| single_concrete_type(upper))
            .or_else(|| {
                Some(CompactType::from_var(crate::compact::CompactVar::plain(
                    *self_var,
                )))
            }),
        CompactBounds::Con { path, args } => {
            if args.is_empty()
                && let Some(builtin) = builtin_for_path(path)
            {
                return Some(CompactType::from_builtin(builtin));
            }
            Some(CompactType::from_con(CompactCon {
                path: path.clone(),
                args: args.clone(),
            }))
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Some(CompactType::from_fun(CompactFun {
            arg: compact_type_from_bounds(arg)?,
            arg_eff: compact_type_from_bounds(arg_eff)?,
            ret_eff: compact_type_from_bounds(ret_eff)?,
            ret: compact_type_from_bounds(ret)?,
        })),
        CompactBounds::Record { fields } => fields
            .iter()
            .map(|field| {
                compact_type_from_bounds(&field.value).map(|value| RecordField {
                    name: field.name.clone(),
                    value,
                    optional: field.optional,
                })
            })
            .collect::<Option<Vec<_>>>()
            .map(|fields| CompactType::from_record(CompactRecord { fields })),
        CompactBounds::PolyVariant { items } => items
            .iter()
            .map(|(name, payloads)| {
                payloads
                    .iter()
                    .map(compact_type_from_bounds)
                    .collect::<Option<Vec<_>>>()
                    .map(|payloads| (name.clone(), payloads))
            })
            .collect::<Option<Vec<_>>>()
            .map(|items| CompactType::from_poly_variant(CompactPolyVariant { items })),
        CompactBounds::Tuple { items } => items
            .iter()
            .map(compact_type_from_bounds)
            .collect::<Option<Vec<_>>>()
            .map(|items| CompactType::from_tuple(CompactTuple { items })),
    }
}

fn rewrite_role_constraint(
    constraint: &CompactRoleConstraint,
    subst: &TypeSubst,
) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: constraint.role.clone(),
        inputs: constraint
            .inputs
            .iter()
            .map(|arg| rewrite_role_arg(arg, subst))
            .collect(),
        associated: constraint
            .associated
            .iter()
            .map(|associated| CompactRoleAssociatedType {
                name: associated.name.clone(),
                value: rewrite_role_arg(&associated.value, subst),
            })
            .collect(),
    }
}

fn rewrite_role_arg(arg: &CompactRoleArg, subst: &TypeSubst) -> CompactRoleArg {
    CompactRoleArg {
        lower: rewrite_type(&arg.lower, subst, true),
        upper: rewrite_type(&arg.upper, subst, false),
    }
}

fn rewrite_type(ty: &CompactType, subst: &TypeSubst, positive: bool) -> CompactType {
    let mut out = CompactType {
        never: ty.never,
        builtins: ty.builtins.clone(),
        cons: ty.cons.iter().map(|con| rewrite_con(con, subst)).collect(),
        funs: ty
            .funs
            .iter()
            .map(|fun| CompactFun {
                arg: rewrite_type(&fun.arg, subst, !positive),
                arg_eff: rewrite_type(&fun.arg_eff, subst, !positive),
                ret_eff: rewrite_type(&fun.ret_eff, subst, positive),
                ret: rewrite_type(&fun.ret, subst, positive),
            })
            .collect(),
        records: ty
            .records
            .iter()
            .map(|record| CompactRecord {
                fields: record
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: rewrite_type(&field.value, subst, positive),
                        optional: field.optional,
                    })
                    .collect(),
            })
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: rewrite_type(&field.value, subst, positive),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(rewrite_type(&spread.tail, subst, positive)),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        poly_variants: ty
            .poly_variants
            .iter()
            .map(|variant| CompactPolyVariant {
                items: variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| rewrite_type(payload, subst, positive))
                                .collect(),
                        )
                    })
                    .collect(),
            })
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|tuple| CompactTuple {
                items: tuple
                    .items
                    .iter()
                    .map(|item| rewrite_type(item, subst, positive))
                    .collect(),
            })
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|row| CompactRow {
                items: row
                    .items
                    .iter()
                    .map(|item| rewrite_type(item, subst, positive))
                    .collect(),
                tail: Box::new(rewrite_type(&row.tail, subst, positive)),
            })
            .collect(),
        ..CompactType::default()
    };

    for var in &ty.vars {
        if let Some(replacement) = subst.get(var.var) {
            out = merge_compact_types(positive, out, replacement.clone());
        } else {
            out.vars.push(var.clone());
        }
    }
    canonical_substitution_type(out)
}

fn rewrite_con(con: &CompactCon, subst: &TypeSubst) -> CompactCon {
    CompactCon {
        path: con.path.clone(),
        args: con
            .args
            .iter()
            .map(|arg| rewrite_bounds(arg, subst))
            .collect(),
    }
}

fn rewrite_bounds(bounds: &CompactBounds, subst: &TypeSubst) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(replacement) = subst.get(*self_var).and_then(compact_bounds_from_type) {
                return replacement;
            }
            CompactBounds::Interval {
                self_var: *self_var,
                lower: rewrite_type(lower, subst, true),
                upper: rewrite_type(upper, subst, false),
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path: path.clone(),
            args: args.iter().map(|arg| rewrite_bounds(arg, subst)).collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(rewrite_bounds(arg, subst)),
            arg_eff: Box::new(rewrite_bounds(arg_eff, subst)),
            ret_eff: Box::new(rewrite_bounds(ret_eff, subst)),
            ret: Box::new(rewrite_bounds(ret, subst)),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: rewrite_bounds(&field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        },
        CompactBounds::PolyVariant { items } => CompactBounds::PolyVariant {
            items: items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| rewrite_bounds(payload, subst))
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .iter()
                .map(|item| rewrite_bounds(item, subst))
                .collect(),
        },
    }
}

fn compact_bounds_from_type(ty: &CompactType) -> Option<CompactBounds> {
    let ty = canonical_substitution_type(ty.clone());
    if ty.vars.len() == 1
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        let var = ty.vars[0].var;
        return Some(CompactBounds::Interval {
            self_var: var,
            lower: CompactType::from_var(crate::compact::CompactVar::plain(var)),
            upper: CompactType::from_var(crate::compact::CompactVar::plain(var)),
        });
    }
    if ty.builtins.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        return Some(CompactBounds::Con {
            path: vec![ty.builtins[0].surface_name().into()],
            args: Vec::new(),
        });
    }
    if ty.cons.len() == 1
        && ty.vars.is_empty()
        && !ty.never
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        let con = ty.cons[0].clone();
        return Some(CompactBounds::Con {
            path: con.path,
            args: con.args,
        });
    }
    None
}

fn canonical_substitution_type(ty: CompactType) -> CompactType {
    let mut out = CompactType {
        vars: ty.vars,
        never: ty.never,
        builtins: ty.builtins,
        cons: Vec::new(),
        funs: ty.funs,
        records: ty.records,
        record_spreads: ty.record_spreads,
        poly_variants: ty.poly_variants,
        tuples: ty.tuples,
        rows: ty.rows,
    };
    for con in ty.cons {
        if con.args.is_empty()
            && let Some(builtin) = builtin_for_path(&con.path)
        {
            if !out.builtins.contains(&builtin) {
                out.builtins.push(builtin);
            }
        } else if !out.cons.contains(&con) {
            out.cons.push(con);
        }
    }
    out
}

fn builtin_for_path(path: &[String]) -> Option<BuiltinType> {
    (path.len() == 1)
        .then(|| BuiltinType::from_surface_name(&path[0]))
        .flatten()
}

fn compact_type_is_empty(ty: &CompactType) -> bool {
    !ty.never
        && ty.vars.is_empty()
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
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
            .map(|(lhs, rhs)| merge_role_arg(lhs, rhs))
            .collect();
        for associated in constraint.associated {
            if let Some(existing) = merged
                .associated
                .iter_mut()
                .find(|existing| existing.name == associated.name)
            {
                existing.value = merge_role_arg(existing.value.clone(), associated.value);
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

fn merge_role_arg(lhs: CompactRoleArg, rhs: CompactRoleArg) -> CompactRoleArg {
    CompactRoleArg {
        lower: merge_compact_types(true, lhs.lower, rhs.lower),
        upper: merge_compact_types(false, lhs.upper, rhs.upper),
    }
}

fn role_arg_concrete_type(
    arg: &CompactRoleArg,
    main_polarity: &MainPolarity,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> Option<CompactType> {
    let lower = single_concrete_type(&arg.lower);
    if let Some(lower_ty) = &lower
        && role_arg_lower_allowed(arg, lower_ty, main_polarity)
        && !compact_type_has_method_taint(&arg.lower, method_taint)
    {
        return lower;
    }
    let upper = single_concrete_type(&arg.upper);
    if upper.is_some()
        && role_arg_allowed_by_main_polarity(arg, false, main_polarity)
        && !compact_type_has_method_taint(&arg.upper, method_taint)
    {
        return upper;
    }
    None
}

fn single_concrete_type(ty: &CompactType) -> Option<CompactType> {
    let mut found = Vec::new();
    if ty.never {
        found.push(CompactType::never());
    }
    found.extend(ty.builtins.iter().copied().map(CompactType::from_builtin));
    found.extend(ty.cons.iter().cloned().map(CompactType::from_con));
    found.extend(ty.funs.iter().cloned().map(CompactType::from_fun));
    found.extend(ty.records.iter().cloned().map(CompactType::from_record));
    found.extend(
        ty.record_spreads
            .iter()
            .cloned()
            .map(CompactType::from_record_spread),
    );
    found.extend(
        ty.poly_variants
            .iter()
            .cloned()
            .map(CompactType::from_poly_variant),
    );
    found.extend(ty.tuples.iter().cloned().map(CompactType::from_tuple));
    found.extend(ty.rows.iter().cloned().map(CompactType::from_row));
    (found.len() == 1).then(|| found.remove(0))
}

fn compact_type_has_method_taint(
    ty: &CompactType,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> bool {
    ty.vars.iter().any(|var| {
        method_taint
            .get(&var.var)
            .is_some_and(|selects| !selects.is_empty())
    }) || ty.cons.iter().any(|con| {
        con.args
            .iter()
            .any(|arg| compact_bounds_has_method_taint(arg, method_taint))
    }) || ty.funs.iter().any(|fun| {
        compact_type_has_method_taint(&fun.arg, method_taint)
            || compact_type_has_method_taint(&fun.arg_eff, method_taint)
            || compact_type_has_method_taint(&fun.ret_eff, method_taint)
            || compact_type_has_method_taint(&fun.ret, method_taint)
    }) || ty.records.iter().any(|record| {
        record
            .fields
            .iter()
            .any(|field| compact_type_has_method_taint(&field.value, method_taint))
    }) || ty.record_spreads.iter().any(|spread| {
        spread
            .fields
            .iter()
            .any(|field| compact_type_has_method_taint(&field.value, method_taint))
            || compact_type_has_method_taint(&spread.tail, method_taint)
    }) || ty.poly_variants.iter().any(|variant| {
        variant.items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| compact_type_has_method_taint(payload, method_taint))
        })
    }) || ty.tuples.iter().any(|tuple| {
        tuple
            .items
            .iter()
            .any(|item| compact_type_has_method_taint(item, method_taint))
    }) || ty.rows.iter().any(|row| {
        row.items
            .iter()
            .any(|item| compact_type_has_method_taint(item, method_taint))
            || compact_type_has_method_taint(&row.tail, method_taint)
    })
}

fn compact_bounds_has_method_taint(
    bounds: &CompactBounds,
    method_taint: &FxHashMap<TypeVar, Vec<SelectId>>,
) -> bool {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            method_taint
                .get(self_var)
                .is_some_and(|selects| !selects.is_empty())
                || compact_type_has_method_taint(lower, method_taint)
                || compact_type_has_method_taint(upper, method_taint)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => args
            .iter()
            .any(|arg| compact_bounds_has_method_taint(arg, method_taint)),
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            compact_bounds_has_method_taint(arg, method_taint)
                || compact_bounds_has_method_taint(arg_eff, method_taint)
                || compact_bounds_has_method_taint(ret_eff, method_taint)
                || compact_bounds_has_method_taint(ret, method_taint)
        }
        CompactBounds::Record { fields } => fields
            .iter()
            .any(|field| compact_bounds_has_method_taint(&field.value, method_taint)),
        CompactBounds::PolyVariant { items } => items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| compact_bounds_has_method_taint(payload, method_taint))
        }),
    }
}

fn role_arg_allowed_by_main_polarity(
    arg: &CompactRoleArg,
    selected_positive_boundary: bool,
    main_polarity: &MainPolarity,
) -> bool {
    role_arg_vars(arg).into_iter().all(|var| {
        match (
            main_polarity.positive.contains(&var),
            main_polarity.negative.contains(&var),
        ) {
            (false, false) => true,
            (true, false) => selected_positive_boundary,
            (false, true) => !selected_positive_boundary,
            (true, true) => false,
        }
    })
}

/// 下界での解決可否。main-negative な変数も、その負出現がすべて `target` と
/// 同じ交差に同伴しているなら許す。呼び出し側から入る値は交差の concrete 成分で
/// `target` 以下に絞られるので、subject が `target` 以外へ instantiate されることはない。
/// （例: `impl Debug int: our x.dsize = x.size` — x は `'x & int` で釘付け）
/// 同伴なしの負出現が一つでもあれば従来どおり拒否する（`'a + 1` の `'a` を守る）。
///
/// 見るのは subject の**トップレベル変数だけ**。con 引数の中の不変 interval 変数は
/// 構造ごと candidate との `match_bounds_pattern` が照合する領分で、ここで両極性
/// （Interval の self_var は常に bipolar）を理由に拒否すると `list int` のような
/// 入れ子 concrete subject が永遠に解決できない。
fn role_arg_lower_allowed(
    arg: &CompactRoleArg,
    target: &CompactType,
    main_polarity: &MainPolarity,
) -> bool {
    let top_level_vars = arg
        .lower
        .vars
        .iter()
        .chain(arg.upper.vars.iter())
        .map(|var| var.var)
        .collect::<FxHashSet<_>>();
    top_level_vars.into_iter().all(|var| {
        match (
            main_polarity.positive.contains(&var),
            main_polarity.negative.contains(&var),
        ) {
            (false, false) => true,
            (true, false) => true,
            (false, true) => main_polarity.negative_occurrences_pinned_to(var, target),
            (true, true) => false,
        }
    })
}

#[derive(Default)]
struct MainPolarity {
    positive: FxHashSet<TypeVar>,
    negative: FxHashSet<TypeVar>,
    negative_cooccur: FxHashMap<TypeVar, Vec<CompactType>>,
}

impl MainPolarity {
    fn collect(root: &CompactRoot) -> Self {
        let mut polarity = Self::default();
        polarity.collect_type(&root.root, true);
        for rec in &root.rec_vars {
            polarity.collect_bounds(&rec.bounds, true);
        }
        polarity
    }

    fn insert(&mut self, var: TypeVar, positive: bool) {
        if positive {
            self.positive.insert(var);
        } else {
            self.negative.insert(var);
        }
    }

    fn negative_occurrences_pinned_to(&self, var: TypeVar, target: &CompactType) -> bool {
        self.negative_cooccur.get(&var).is_some_and(|occurrences| {
            occurrences
                .iter()
                .all(|occurrence| single_concrete_type(occurrence).as_ref() == Some(target))
        })
    }

    fn collect_type(&mut self, ty: &CompactType, positive: bool) {
        for var in &ty.vars {
            self.insert(var.var, positive);
            if !positive {
                self.negative_cooccur
                    .entry(var.var)
                    .or_default()
                    .push(ty.clone());
            }
        }
        for con in &ty.cons {
            for arg in &con.args {
                self.collect_bounds(arg, positive);
            }
        }
        for fun in &ty.funs {
            self.collect_type(&fun.arg, !positive);
            self.collect_type(&fun.arg_eff, !positive);
            self.collect_type(&fun.ret_eff, positive);
            self.collect_type(&fun.ret, positive);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_type(&field.value, positive);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_type(&field.value, positive);
            }
            self.collect_type(&spread.tail, positive);
        }
        for variant in &ty.poly_variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_type(payload, positive);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in &tuple.items {
                self.collect_type(item, positive);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_type(item, positive);
            }
            self.collect_type(&row.tail, positive);
        }
    }

    fn collect_bounds(&mut self, bounds: &CompactBounds, positive: bool) {
        match bounds {
            CompactBounds::Interval {
                self_var,
                lower,
                upper,
            } => {
                self.insert(*self_var, true);
                self.insert(*self_var, false);
                self.collect_type(lower, positive);
                self.collect_type(upper, !positive);
            }
            CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
                for arg in args {
                    self.collect_bounds(arg, positive);
                }
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_bounds(arg, !positive);
                self.collect_bounds(arg_eff, !positive);
                self.collect_bounds(ret_eff, positive);
                self.collect_bounds(ret, positive);
            }
            CompactBounds::Record { fields } => {
                for field in fields {
                    self.collect_bounds(&field.value, positive);
                }
            }
            CompactBounds::PolyVariant { items } => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.collect_bounds(payload, positive);
                    }
                }
            }
        }
    }
}

fn role_arg_vars(arg: &CompactRoleArg) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    collect_type_vars(&arg.lower, &mut vars);
    collect_type_vars(&arg.upper, &mut vars);
    vars
}

fn collect_type_vars(ty: &CompactType, vars: &mut FxHashSet<TypeVar>) {
    vars.extend(ty.vars.iter().map(|var| var.var));
    for con in &ty.cons {
        for arg in &con.args {
            collect_bounds_vars(arg, vars);
        }
    }
    for fun in &ty.funs {
        collect_type_vars(&fun.arg, vars);
        collect_type_vars(&fun.arg_eff, vars);
        collect_type_vars(&fun.ret_eff, vars);
        collect_type_vars(&fun.ret, vars);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_type_vars(&field.value, vars);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_type_vars(&field.value, vars);
        }
        collect_type_vars(&spread.tail, vars);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_type_vars(payload, vars);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_type_vars(item, vars);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_type_vars(item, vars);
        }
        collect_type_vars(&row.tail, vars);
    }
}

fn collect_bounds_vars(bounds: &crate::compact::CompactBounds, vars: &mut FxHashSet<TypeVar>) {
    match bounds {
        crate::compact::CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            vars.insert(*self_var);
            collect_type_vars(lower, vars);
            collect_type_vars(upper, vars);
        }
        crate::compact::CompactBounds::Con { args, .. }
        | crate::compact::CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_bounds_vars(arg, vars);
            }
        }
        crate::compact::CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_bounds_vars(arg, vars);
            collect_bounds_vars(arg_eff, vars);
            collect_bounds_vars(ret_eff, vars);
            collect_bounds_vars(ret, vars);
        }
        crate::compact::CompactBounds::Record { fields } => {
            for field in fields {
                collect_bounds_vars(&field.value, vars);
            }
        }
        crate::compact::CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_bounds_vars(payload, vars);
                }
            }
        }
    }
}
