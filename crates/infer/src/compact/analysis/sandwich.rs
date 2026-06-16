use super::*;

#[cfg(test)]
pub(crate) fn sandwich_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactSandwich> {
    sandwich_compact_root_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        &mut [],
        &FxHashSet::default(),
    )
}

#[cfg(test)]
pub(crate) fn sandwich_compact_root_with_roles(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
) -> Vec<CompactSandwich> {
    sandwich_compact_root_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        roles,
        &FxHashSet::default(),
    )
}

pub(super) fn sandwich_compact_root_with_roles_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<CompactSandwich> {
    let mut fresh = FreshCompactVars::new(root);
    let mut sandwiches = FxHashMap::default();
    loop {
        let verdicts = compute_sandwich_verdicts(machine, boundary, root, roles, non_generic);
        if verdicts.lift.is_empty() {
            return sorted_sandwiches(sandwiches);
        }

        let mut changed = false;
        root.root = sandwich_type(
            machine,
            boundary,
            mem::take(&mut root.root),
            &verdicts,
            &mut fresh,
            &mut changed,
            &mut sandwiches,
        );
        for rec in &mut root.rec_vars {
            rec.bounds = sandwich_bounds(
                machine,
                boundary,
                mem::replace(&mut rec.bounds, empty_interval(rec.var)),
                &verdicts,
                &mut fresh,
                &mut changed,
                &mut sandwiches,
            );
        }
        for role in &mut *roles {
            sandwich_role(
                machine,
                boundary,
                role,
                &verdicts,
                &mut fresh,
                &mut changed,
                &mut sandwiches,
            );
        }
        if !changed {
            return sorted_sandwiches(sandwiches);
        }
    }
}

pub(super) fn empty_interval(_var: TypeVar) -> CompactBounds {
    CompactBounds::Interval {
        lower: CompactType::default(),
        upper: CompactType::default(),
    }
}

#[derive(Default)]
pub(super) struct SandwichVerdicts {
    lift: FxHashMap<TypeVar, SandwichKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum SandwichVerdict {
    Single(SandwichKind),
    NoLift,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum SandwichKind {
    Con(Vec<String>, usize),
    Tuple(usize),
    Fun,
    ConcreteButNotLiftable,
}

pub(super) fn compute_sandwich_verdicts(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> SandwichVerdicts {
    let mut verdicts = FxHashMap::default();
    visit_type_for_sandwich_verdict(&root.root, &mut verdicts);
    for rec in &root.rec_vars {
        visit_bounds_for_sandwich_verdict(&rec.bounds, &mut verdicts);
    }
    for role in roles {
        visit_role_for_sandwich_verdict(role, &mut verdicts);
    }

    let rec_vars = root
        .rec_vars
        .iter()
        .map(|rec| rec.var)
        .collect::<FxHashSet<_>>();
    let mut lift = FxHashMap::default();
    for (var, verdict) in verdicts {
        if rec_vars.contains(&var)
            || !is_simplification_candidate(machine, boundary, var, non_generic)
        {
            continue;
        }
        match verdict {
            SandwichVerdict::Single(
                kind @ (SandwichKind::Con(..) | SandwichKind::Tuple(_) | SandwichKind::Fun),
            ) => {
                lift.insert(var, kind);
            }
            _ => {}
        }
    }
    SandwichVerdicts { lift }
}

pub(super) fn visit_role_for_sandwich_verdict(
    role: &CompactRoleConstraint,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    for input in &role.inputs {
        visit_role_arg_for_sandwich_verdict(input, verdicts);
    }
    for associated in &role.associated {
        visit_role_arg_for_sandwich_verdict(&associated.value, verdicts);
    }
}

pub(super) fn visit_role_arg_for_sandwich_verdict(
    arg: &CompactRoleArg,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    visit_bounds_for_sandwich_verdict(&arg.bounds, verdicts);
}

pub(super) fn visit_type_for_sandwich_verdict(
    ty: &CompactType,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    let kinds = sandwich_kinds(ty);
    for var in &ty.vars {
        record_sandwich_var_occurrence(verdicts, var.var, &kinds);
    }

    for args in ty.cons.values() {
        for arg in args {
            visit_bounds_for_sandwich_verdict(arg, verdicts);
        }
    }
    for fun in &ty.funs {
        visit_type_for_sandwich_verdict(&fun.arg, verdicts);
        visit_type_for_sandwich_verdict(&fun.arg_eff, verdicts);
        visit_type_for_sandwich_verdict(&fun.ret_eff, verdicts);
        visit_type_for_sandwich_verdict(&fun.ret, verdicts);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_for_sandwich_verdict(&field.value, verdicts);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_for_sandwich_verdict(&field.value, verdicts);
        }
        visit_type_for_sandwich_verdict(&spread.tail, verdicts);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_for_sandwich_verdict(payload, verdicts);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_for_sandwich_verdict(item, verdicts);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                visit_bounds_for_sandwich_verdict(arg, verdicts);
            }
        }
        visit_type_for_sandwich_verdict(&row.tail, verdicts);
    }
}

pub(super) fn visit_bounds_for_sandwich_verdict(
    bounds: &CompactBounds,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            visit_type_for_sandwich_verdict(lower, verdicts);
            visit_type_for_sandwich_verdict(upper, verdicts);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_for_sandwich_verdict(arg, verdicts);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_for_sandwich_verdict(arg, verdicts);
            visit_bounds_for_sandwich_verdict(arg_eff, verdicts);
            visit_bounds_for_sandwich_verdict(ret_eff, verdicts);
            visit_bounds_for_sandwich_verdict(ret, verdicts);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_for_sandwich_verdict(&field.value, verdicts);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_for_sandwich_verdict(payload, verdicts);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_for_sandwich_verdict(item, verdicts);
            }
        }
    }
}

pub(super) fn sandwich_kinds(ty: &CompactType) -> Vec<SandwichKind> {
    let mut kinds = Vec::new();
    for con in compact_con_entries(&ty.cons) {
        kinds.push(SandwichKind::Con(con.path, con.args.len()));
    }
    for tuple in &ty.tuples {
        kinds.push(SandwichKind::Tuple(tuple.items.len()));
    }
    if !ty.funs.is_empty() {
        kinds.push(SandwichKind::Fun);
    }
    if !ty.builtins.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.rows.is_empty()
    {
        kinds.push(SandwichKind::ConcreteButNotLiftable);
    }
    kinds
}

pub(super) fn record_sandwich_var_occurrence(
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
    var: TypeVar,
    kinds: &[SandwichKind],
) {
    let occurrence = if kinds.len() == 1 {
        SandwichVerdict::Single(kinds[0].clone())
    } else {
        SandwichVerdict::NoLift
    };
    let merged = match (verdicts.get(&var), &occurrence) {
        (None, _) => occurrence,
        (Some(SandwichVerdict::NoLift), _) | (_, SandwichVerdict::NoLift) => {
            SandwichVerdict::NoLift
        }
        (Some(SandwichVerdict::Single(lhs)), SandwichVerdict::Single(rhs)) => {
            if lhs == rhs {
                SandwichVerdict::Single(lhs.clone())
            } else {
                SandwichVerdict::NoLift
            }
        }
    };
    verdicts.insert(var, merged);
}

pub(super) fn sandwich_type(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut ty: CompactType,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) -> CompactType {
    ty.cons = ty
        .cons
        .into_iter()
        .map(|(path, args)| {
            (
                path,
                args.into_iter()
                    .map(|arg| {
                        sandwich_bounds(
                            machine, boundary, arg, verdicts, fresh, changed, sandwiches,
                        )
                    })
                    .collect(),
            )
        })
        .collect();
    for fun in &mut ty.funs {
        fun.arg = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.arg),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.arg_eff = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.arg_eff),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.ret_eff = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.ret_eff),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.ret = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.ret),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            field.value = sandwich_type(
                machine,
                boundary,
                mem::take(&mut field.value),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            field.value = sandwich_type(
                machine,
                boundary,
                mem::take(&mut field.value),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
        spread.tail = Box::new(sandwich_type(
            machine,
            boundary,
            *mem::take(&mut spread.tail),
            verdicts,
            fresh,
            changed,
            sandwiches,
        ));
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                *payload = sandwich_type(
                    machine,
                    boundary,
                    mem::take(payload),
                    verdicts,
                    fresh,
                    changed,
                    sandwiches,
                );
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            *item = sandwich_type(
                machine,
                boundary,
                mem::take(item),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                *arg = sandwich_bounds(
                    machine,
                    boundary,
                    mem::replace(arg, empty_interval(TypeVar(0))),
                    verdicts,
                    fresh,
                    changed,
                    sandwiches,
                );
            }
        }
        row.tail = Box::new(sandwich_type(
            machine,
            boundary,
            *mem::take(&mut row.tail),
            verdicts,
            fresh,
            changed,
            sandwiches,
        ));
    }
    ty
}

pub(super) fn sandwich_bounds(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    bounds: CompactBounds,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            if let Some((center, kind, lifted)) = try_lift_interval(&lower, &upper, verdicts, fresh)
            {
                *changed = true;
                record_sandwich(sandwiches, center, &kind);
                sandwich_bounds(
                    machine, boundary, lifted, verdicts, fresh, changed, sandwiches,
                )
            } else {
                CompactBounds::Interval {
                    lower: sandwich_type(
                        machine, boundary, lower, verdicts, fresh, changed, sandwiches,
                    ),
                    upper: sandwich_type(
                        machine, boundary, upper, verdicts, fresh, changed, sandwiches,
                    ),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| {
                    sandwich_bounds(machine, boundary, arg, verdicts, fresh, changed, sandwiches)
                })
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(sandwich_bounds(
                machine, boundary, *arg, verdicts, fresh, changed, sandwiches,
            )),
            arg_eff: Box::new(sandwich_bounds(
                machine, boundary, *arg_eff, verdicts, fresh, changed, sandwiches,
            )),
            ret_eff: Box::new(sandwich_bounds(
                machine, boundary, *ret_eff, verdicts, fresh, changed, sandwiches,
            )),
            ret: Box::new(sandwich_bounds(
                machine, boundary, *ret, verdicts, fresh, changed, sandwiches,
            )),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: sandwich_bounds(
                        machine,
                        boundary,
                        field.value,
                        verdicts,
                        fresh,
                        changed,
                        sandwiches,
                    ),
                    optional: field.optional,
                })
                .collect(),
        },
        CompactBounds::PolyVariant { items } => CompactBounds::PolyVariant {
            items: items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                sandwich_bounds(
                                    machine, boundary, payload, verdicts, fresh, changed,
                                    sandwiches,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|item| {
                    sandwich_bounds(
                        machine, boundary, item, verdicts, fresh, changed, sandwiches,
                    )
                })
                .collect(),
        },
    }
}

pub(super) fn sandwich_role(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    role: &mut CompactRoleConstraint,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) {
    for input in &mut role.inputs {
        sandwich_role_arg(
            machine, boundary, input, verdicts, fresh, changed, sandwiches,
        );
    }
    for associated in &mut role.associated {
        sandwich_role_arg(
            machine,
            boundary,
            &mut associated.value,
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
    }
}

pub(super) fn sandwich_role_arg(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    arg: &mut CompactRoleArg,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) {
    let bounds = arg.bounds.clone();
    arg.bounds = sandwich_bounds(
        machine, boundary, bounds, verdicts, fresh, changed, sandwiches,
    );
}

pub(super) fn try_lift_interval(
    lower: &CompactType,
    upper: &CompactType,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
) -> Option<(TypeVar, SandwichKind, CompactBounds)> {
    let center = common_var_in_types(lower, upper).filter(|var| verdicts.lift.contains_key(var))?;
    let kind = verdicts.lift.get(&center)?.clone();
    let lifted = match kind.clone() {
        SandwichKind::Con(path, arity) => {
            let lower_args = single_con(lower, &path, arity)?;
            let upper_args = single_con(upper, &path, arity)?;
            CompactBounds::Con {
                path,
                args: lower_args
                    .iter()
                    .zip(upper_args)
                    .map(|(lower, upper)| merge_arg_bounds(lower, upper, fresh))
                    .collect(),
            }
        }
        SandwichKind::Tuple(arity) => {
            let lower_items = single_tuple(lower, arity)?;
            let upper_items = single_tuple(upper, arity)?;
            CompactBounds::Tuple {
                items: lower_items
                    .iter()
                    .zip(upper_items)
                    .map(|(lower, upper)| interval_from_types(lower.clone(), upper.clone(), fresh))
                    .collect(),
            }
        }
        SandwichKind::Fun => {
            let lower_fun = single_fun(lower)?;
            let upper_fun = single_fun(upper)?;
            CompactBounds::Fun {
                arg: Box::new(interval_from_types(
                    upper_fun.arg.clone(),
                    lower_fun.arg.clone(),
                    fresh,
                )),
                arg_eff: Box::new(interval_from_types(
                    upper_fun.arg_eff.clone(),
                    lower_fun.arg_eff.clone(),
                    fresh,
                )),
                ret_eff: Box::new(interval_from_types(
                    lower_fun.ret_eff.clone(),
                    upper_fun.ret_eff.clone(),
                    fresh,
                )),
                ret: Box::new(interval_from_types(
                    lower_fun.ret.clone(),
                    upper_fun.ret.clone(),
                    fresh,
                )),
            }
        }
        SandwichKind::ConcreteButNotLiftable => return None,
    };
    Some((center, kind, lifted))
}

pub(super) fn record_sandwich(
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
    var: TypeVar,
    kind: &SandwichKind,
) {
    let Some(kind) = compact_sandwich_kind(kind) else {
        return;
    };
    sandwiches.insert(var, kind);
}

pub(super) fn compact_sandwich_kind(kind: &SandwichKind) -> Option<CompactSandwichKind> {
    match kind {
        SandwichKind::Con(path, arity) => Some(CompactSandwichKind::Con {
            path: path.clone(),
            arity: *arity,
        }),
        SandwichKind::Tuple(arity) => Some(CompactSandwichKind::Tuple { arity: *arity }),
        SandwichKind::Fun => Some(CompactSandwichKind::Fun),
        SandwichKind::ConcreteButNotLiftable => None,
    }
}

pub(super) fn sorted_sandwiches(
    sandwiches: FxHashMap<TypeVar, CompactSandwichKind>,
) -> Vec<CompactSandwich> {
    let mut sandwiches = sandwiches
        .into_iter()
        .map(|(var, kind)| CompactSandwich { var, kind })
        .collect::<Vec<_>>();
    sandwiches.sort_by_key(|sandwich| sandwich.var.0);
    sandwiches
}

pub(super) fn merge_arg_bounds(
    lower_arg: &CompactBounds,
    upper_arg: &CompactBounds,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    match (lower_arg, upper_arg) {
        (
            CompactBounds::Interval {
                lower: lower_lower,
                upper: lower_upper,
                ..
            },
            CompactBounds::Interval {
                lower: upper_lower,
                upper: upper_upper,
                ..
            },
        ) => interval_from_types(
            merge_compact_types(true, lower_lower.clone(), upper_lower.clone()),
            merge_compact_types(false, lower_upper.clone(), upper_upper.clone()),
            fresh,
        ),
        _ if lower_arg == upper_arg => lower_arg.clone(),
        _ => lower_arg.clone(),
    }
}

pub(super) fn interval_from_types(
    lower: CompactType,
    upper: CompactType,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    let _ = fresh;
    CompactBounds::Interval { lower, upper }
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

pub(super) fn single_con<'a>(
    ty: &'a CompactType,
    path: &[String],
    arity: usize,
) -> Option<&'a [CompactBounds]> {
    if ty.cons.len() == 1
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && let Some(args) = ty.cons.get(path)
        && args.len() == arity
    {
        Some(args)
    } else {
        None
    }
}

pub(super) fn single_tuple(ty: &CompactType, arity: usize) -> Option<&[CompactType]> {
    if ty.tuples.len() == 1
        && ty.tuples[0].items.len() == arity
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.tuples[0].items)
    } else {
        None
    }
}

pub(super) fn single_fun(ty: &CompactType) -> Option<&CompactFun> {
    if ty.funs.len() == 1
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.funs[0])
    } else {
        None
    }
}
