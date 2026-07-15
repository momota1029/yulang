use super::*;
use poly::roles::RoleConstraintArg;
use poly::types::{Neg, Pos};

#[derive(Default, Clone)]
pub(super) struct TypeSubst {
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

    pub(super) fn get(&self, var: TypeVar) -> Option<&CompactType> {
        self.vars.get(&var)
    }
}

pub(super) fn match_role_arg_candidate(
    candidate: &CompactRoleArg,
    demand: &CompactBounds,
    subst: &mut TypeSubst,
) -> bool {
    match_bounds_pattern(&candidate.bounds, demand, subst)
}

pub(super) fn match_role_candidate_inputs(
    candidate: &[CompactRoleArg],
    demand: &[CompactBounds],
    subst: &mut TypeSubst,
) -> bool {
    candidate.len() == demand.len()
        && !role_candidate_has_definite_input_head_mismatch(candidate, demand)
        && candidate
            .iter()
            .zip(demand)
            .all(|(candidate, demand)| match_role_arg_candidate(candidate, demand, subst))
}

pub(super) fn raw_role_candidate_has_definite_input_head_mismatch(
    machine: &ConstraintMachine,
    candidate: &[RoleConstraintArg],
    demand: &[CompactBounds],
) -> bool {
    // Do not follow variables or arena bounds here: both raw sides must name the same direct
    // constructor before skipping the compaction that resolves every other shape.
    candidate.iter().zip(demand).any(|(candidate, demand)| {
        let Some(candidate) = definite_raw_nominal_or_builtin_head(machine, candidate) else {
            return false;
        };
        let Some(demand) = definite_nominal_or_builtin_head(demand) else {
            return false;
        };
        candidate != demand
    })
}

pub(super) fn role_candidate_has_definite_input_head_mismatch(
    candidate: &[CompactRoleArg],
    demand: &[CompactBounds],
) -> bool {
    // Intervals and non-nominal shapes stay on the full matcher. Direct `Con` heads are the
    // narrow case where a different canonical nominal/builtin head is already a certain failure.
    candidate.iter().zip(demand).any(|(candidate, demand)| {
        let Some(candidate) = definite_nominal_or_builtin_head(&candidate.bounds) else {
            return false;
        };
        let Some(demand) = definite_nominal_or_builtin_head(demand) else {
            return false;
        };
        candidate != demand
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefiniteRoleInputHead<'a> {
    Builtin(BuiltinType),
    Nominal(&'a [String]),
}

fn definite_raw_nominal_or_builtin_head<'a>(
    machine: &'a ConstraintMachine,
    arg: &RoleConstraintArg,
) -> Option<DefiniteRoleInputHead<'a>> {
    let Pos::Con(lower_path, lower_args) = machine.types().pos(arg.lower) else {
        return None;
    };
    let Neg::Con(upper_path, upper_args) = machine.types().neg(arg.upper) else {
        return None;
    };
    let lower = canonical_nominal_or_builtin_head(lower_path, lower_args.is_empty());
    let upper = canonical_nominal_or_builtin_head(upper_path, upper_args.is_empty());
    (lower == upper).then_some(lower)
}

fn definite_nominal_or_builtin_head(bounds: &CompactBounds) -> Option<DefiniteRoleInputHead<'_>> {
    let CompactBounds::Con { path, args } = bounds else {
        return None;
    };
    Some(canonical_nominal_or_builtin_head(path, args.is_empty()))
}

fn canonical_nominal_or_builtin_head(
    path: &[String],
    args_are_empty: bool,
) -> DefiniteRoleInputHead<'_> {
    if args_are_empty && let Some(builtin) = builtin_for_path(path) {
        return DefiniteRoleInputHead::Builtin(builtin);
    }
    DefiniteRoleInputHead::Nominal(path)
}

pub(super) fn match_type_pattern(
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
    for con in compact_con_entries(&pattern.cons) {
        if !match_con_pattern(&con, demand, subst) {
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

pub(super) fn match_con_pattern(
    pattern: &CompactCon,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    if pattern.args.is_empty()
        && let Some(builtin) = builtin_for_path(&pattern.path)
    {
        return demand_has_builtin(demand, builtin);
    }
    let Some(demand_args) = demand.cons.get(&pattern.path) else {
        return false;
    };
    if pattern.args.len() != demand_args.len() {
        return false;
    }
    // The path-keyed entry has no sibling constructor to retry. An enclosing structural
    // alternative owns its own rollback snapshot, while every other failure rejects the candidate.
    pattern
        .args
        .iter()
        .zip(demand_args)
        .all(|(pattern, demand)| match_bounds_pattern(pattern, demand, subst))
}

pub(super) fn match_fun_pattern(
    pattern: &CompactFun,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.funs.iter(), |demand, subst| {
        match_type_pattern(&pattern.arg, &demand.arg, false, subst)
            && match_type_pattern(&pattern.arg_eff, &demand.arg_eff, false, subst)
            && match_type_pattern(&pattern.ret_eff, &demand.ret_eff, true, subst)
            && match_type_pattern(&pattern.ret, &demand.ret, true, subst)
    })
}

pub(super) fn match_record_pattern(
    pattern: &CompactRecord,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.records.iter(), |demand, subst| {
        match_record_fields(&pattern.fields, &demand.fields, subst)
    })
}

pub(super) fn match_record_spread_pattern(
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

pub(super) fn match_record_fields(
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

pub(super) fn match_poly_variant_pattern(
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

pub(super) fn match_tuple_pattern(
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

pub(super) fn match_row_pattern(
    pattern: &CompactRow,
    demand: &CompactType,
    subst: &mut TypeSubst,
) -> bool {
    match_alternative(subst, demand.rows.iter(), |demand, subst| {
        match_row_items(&pattern.items, &demand.items, subst)
            && match_type_pattern(&pattern.tail, &demand.tail, true, subst)
    })
}

pub(super) fn match_row_items(
    pattern: &CompactRowItemMap,
    demand: &CompactRowItemMap,
    subst: &mut TypeSubst,
) -> bool {
    if pattern.len() != demand.len() {
        return false;
    }
    for item in compact_row_item_entries(pattern) {
        let Some(demand_args) = demand.get(&item.path) else {
            return false;
        };
        if item.args.len() != demand_args.len()
            || !item
                .args
                .iter()
                .zip(demand_args)
                .all(|(pattern, demand)| match_bounds_pattern(pattern, demand, subst))
        {
            return false;
        }
    }
    true
}

pub(super) fn match_alternative<'a, T: 'a>(
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

pub(super) fn match_bounds_pattern(
    pattern: &CompactBounds,
    demand: &CompactBounds,
    subst: &mut TypeSubst,
) -> bool {
    match pattern {
        CompactBounds::Interval { lower, upper } => {
            let Some(subject_var) = interval_subject_var(lower, upper) else {
                return false;
            };
            let Some(demand_ty) = compact_type_from_bounds(demand) else {
                return false;
            };
            if interval_pattern_is_identity(subject_var, lower, upper) {
                return subst.bind(subject_var, demand_ty);
            }
            if !subst.bind(subject_var, demand_ty.clone()) {
                return false;
            }
            // `impl Add (list 'a)` の `'a` は payload 全体を受ける pattern なので、
            // demand の invariant bounds をさらに同じ変数へ分解照合しない。
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

pub(super) fn interval_pattern_is_identity(
    subject_var: TypeVar,
    lower: &CompactType,
    upper: &CompactType,
) -> bool {
    compact_type_is_plain_var(lower, subject_var) && compact_type_is_plain_var(upper, subject_var)
}

pub(super) fn interval_subject_var(lower: &CompactType, upper: &CompactType) -> Option<TypeVar> {
    common_var_in_types(lower, upper)
        .or_else(|| unique_var_in_type(lower))
        .or_else(|| unique_var_in_type(upper))
}

pub(super) fn common_var_in_types(lower: &CompactType, upper: &CompactType) -> Option<TypeVar> {
    lower
        .vars
        .iter()
        .map(|var| var.var)
        .filter(|lower_var| {
            upper
                .vars
                .iter()
                .any(|upper_var| upper_var.var == *lower_var)
        })
        .min_by_key(|var| var.0)
}

pub(super) fn unique_var_in_type(ty: &CompactType) -> Option<TypeVar> {
    let mut vars = ty.vars.iter().map(|var| var.var).collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    (vars.len() == 1).then(|| vars[0])
}

pub(super) fn compact_type_is_plain_var(ty: &CompactType, var: TypeVar) -> bool {
    ty.vars.len() == 1
        && ty.vars[0].var == var
        && !ty.never
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

pub(super) fn demand_has_builtin(demand: &CompactType, builtin: BuiltinType) -> bool {
    demand.builtins.contains(&builtin)
        || demand
            .cons
            .iter()
            .any(|(path, args)| args.is_empty() && builtin_for_path(path) == Some(builtin))
}

pub(super) fn compact_type_from_bounds(bounds: &CompactBounds) -> Option<CompactType> {
    match bounds {
        CompactBounds::Interval { lower, upper } => single_concrete_type(lower)
            .or_else(|| single_concrete_type(upper))
            .or_else(|| {
                interval_subject_var(lower, upper)
                    .map(crate::compact::CompactVar::plain)
                    .map(CompactType::from_var)
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
