use super::*;

pub(super) fn apply_ancestor_simplifications(
    root: &mut GeneralizedCompactRoot,
    ancestors: &[&GeneralizedCompactRoot],
) {
    for ancestor in ancestors {
        apply_var_substitutions(root, &ancestor.substitutions);
        apply_sandwiches_to_root_and_roles(
            &mut root.compact,
            &mut root.role_predicates,
            &ancestor.sandwiches,
        );
    }
}

pub(crate) fn apply_compact_simplifications_to_root_and_roles(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    simplifications: &[CompactSimplification],
) {
    for simplification in simplifications {
        apply_var_substitutions_to_root_and_roles(root, roles, &simplification.substitutions);
        apply_sandwiches_to_root_and_roles(root, roles, &simplification.sandwiches);
    }
}

fn apply_var_substitutions(
    root: &mut GeneralizedCompactRoot,
    substitutions: &[CompactVarSubstitution],
) {
    if substitutions.is_empty() {
        return;
    }
    let map = var_substitution_map(substitutions);
    rewrite_root_vars(&mut root.compact, &map);
    rewrite_role_predicates_vars(&mut root.role_predicates, &map);
}

fn apply_var_substitutions_to_root_and_roles(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    substitutions: &[CompactVarSubstitution],
) {
    if substitutions.is_empty() {
        return;
    }
    let map = var_substitution_map(substitutions);
    rewrite_root_vars(root, &map);
    rewrite_role_predicates_vars(roles, &map);
}

fn var_substitution_map(
    substitutions: &[CompactVarSubstitution],
) -> FxHashMap<TypeVar, Option<TypeVar>> {
    substitutions
        .iter()
        .map(|substitution| (substitution.source, substitution.target))
        .collect()
}

fn rewrite_root_vars(root: &mut CompactRoot, substitutions: &FxHashMap<TypeVar, Option<TypeVar>>) {
    rewrite_type_vars(&mut root.root, substitutions);
    for rec in &mut root.rec_vars {
        if let Some(target) = resolve_rewrite_target(rec.var, substitutions) {
            rec.var = target;
        }
        rewrite_bounds_vars(&mut rec.bounds, substitutions);
    }
}

fn rewrite_role_predicates_vars(
    roles: &mut [CompactRoleConstraint],
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    for role in roles {
        rewrite_role_vars(role, substitutions);
    }
}

fn rewrite_role_vars(
    role: &mut CompactRoleConstraint,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    for input in &mut role.inputs {
        rewrite_role_arg_vars(input, substitutions);
    }
    for associated in &mut role.associated {
        rewrite_role_arg_vars(&mut associated.value, substitutions);
    }
}

fn rewrite_role_arg_vars(
    arg: &mut CompactRoleArg,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    rewrite_bounds_vars(&mut arg.bounds, substitutions);
}

fn rewrite_type_vars(ty: &mut CompactType, substitutions: &FxHashMap<TypeVar, Option<TypeVar>>) {
    let mut vars = Vec::new();
    for mut var in std::mem::take(&mut ty.vars) {
        let Some(target) = resolve_rewrite_target(var.var, substitutions) else {
            continue;
        };
        var.var = target;
        push_compact_var_with_unioned_weight(&mut vars, var);
    }
    ty.vars = vars;

    for args in ty.cons.values_mut() {
        for arg in args {
            rewrite_bounds_vars(arg, substitutions);
        }
    }
    for fun in &mut ty.funs {
        rewrite_type_vars(&mut fun.arg, substitutions);
        rewrite_type_vars(&mut fun.arg_eff, substitutions);
        rewrite_type_vars(&mut fun.ret_eff, substitutions);
        rewrite_type_vars(&mut fun.ret, substitutions);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            rewrite_type_vars(&mut field.value, substitutions);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            rewrite_type_vars(&mut field.value, substitutions);
        }
        rewrite_type_vars(&mut spread.tail, substitutions);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                rewrite_type_vars(payload, substitutions);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            rewrite_type_vars(item, substitutions);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                rewrite_bounds_vars(arg, substitutions);
            }
        }
        rewrite_type_vars(&mut row.tail, substitutions);
    }
}

fn push_compact_var_with_unioned_weight(vars: &mut Vec<CompactVar>, var: CompactVar) {
    if let Some(existing) = vars.iter_mut().find(|existing| existing.var == var.var) {
        existing.weight = existing.weight.union(&var.weight);
        existing.origin = existing.origin.merged(var.origin);
    } else {
        vars.push(var);
    }
}

fn rewrite_bounds_vars(
    bounds: &mut CompactBounds,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            rewrite_type_vars(lower, substitutions);
            rewrite_type_vars(upper, substitutions);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                rewrite_bounds_vars(arg, substitutions);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            rewrite_bounds_vars(arg, substitutions);
            rewrite_bounds_vars(arg_eff, substitutions);
            rewrite_bounds_vars(ret_eff, substitutions);
            rewrite_bounds_vars(ret, substitutions);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                rewrite_bounds_vars(&mut field.value, substitutions);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    rewrite_bounds_vars(payload, substitutions);
                }
            }
        }
    }
}

fn resolve_rewrite_target(
    source: TypeVar,
    substitutions: &FxHashMap<TypeVar, Option<TypeVar>>,
) -> Option<TypeVar> {
    let mut current = source;
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(current) {
            return Some(current);
        }
        match substitutions.get(&current).copied() {
            None => return Some(current),
            Some(None) => return None,
            Some(Some(next)) => current = next,
        }
    }
}

fn apply_sandwiches_to_root_and_roles(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    sandwiches: &[CompactSandwich],
) {
    if sandwiches.is_empty() {
        return;
    }
    let sandwiches = sandwiches
        .iter()
        .map(|sandwich| (sandwich.var, sandwich.kind.clone()))
        .collect::<FxHashMap<_, _>>();
    let mut fresh = FreshCompactVars::new(root);
    loop {
        let mut changed = false;
        root.root = apply_sandwiches_to_type(
            std::mem::take(&mut root.root),
            &sandwiches,
            &mut fresh,
            &mut changed,
        );
        for rec in &mut root.rec_vars {
            rec.bounds = apply_sandwiches_to_bounds(
                std::mem::replace(&mut rec.bounds, empty_interval(rec.var)),
                &sandwiches,
                &mut fresh,
                &mut changed,
            );
        }
        for role in &mut *roles {
            apply_sandwiches_to_role(role, &sandwiches, &mut fresh, &mut changed);
        }
        if !changed {
            return;
        }
    }
}

fn apply_sandwiches_to_role(
    role: &mut CompactRoleConstraint,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) {
    for input in &mut role.inputs {
        apply_sandwiches_to_role_arg(input, sandwiches, fresh, changed);
    }
    for associated in &mut role.associated {
        apply_sandwiches_to_role_arg(&mut associated.value, sandwiches, fresh, changed);
    }
}

fn apply_sandwiches_to_role_arg(
    arg: &mut CompactRoleArg,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) {
    arg.bounds = apply_sandwiches_to_bounds(arg.bounds.clone(), sandwiches, fresh, changed);
}

fn apply_sandwiches_to_type(
    mut ty: CompactType,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) -> CompactType {
    for args in ty.cons.values_mut() {
        for arg in args {
            *arg = apply_sandwiches_to_bounds(
                std::mem::replace(arg, empty_interval(TypeVar(0))),
                sandwiches,
                fresh,
                changed,
            );
        }
    }
    for fun in &mut ty.funs {
        fun.arg =
            apply_sandwiches_to_type(std::mem::take(&mut fun.arg), sandwiches, fresh, changed);
        fun.arg_eff =
            apply_sandwiches_to_type(std::mem::take(&mut fun.arg_eff), sandwiches, fresh, changed);
        fun.ret_eff =
            apply_sandwiches_to_type(std::mem::take(&mut fun.ret_eff), sandwiches, fresh, changed);
        fun.ret =
            apply_sandwiches_to_type(std::mem::take(&mut fun.ret), sandwiches, fresh, changed);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            field.value = apply_sandwiches_to_type(
                std::mem::take(&mut field.value),
                sandwiches,
                fresh,
                changed,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            field.value = apply_sandwiches_to_type(
                std::mem::take(&mut field.value),
                sandwiches,
                fresh,
                changed,
            );
        }
        spread.tail = Box::new(apply_sandwiches_to_type(
            *std::mem::take(&mut spread.tail),
            sandwiches,
            fresh,
            changed,
        ));
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                *payload =
                    apply_sandwiches_to_type(std::mem::take(payload), sandwiches, fresh, changed);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            *item = apply_sandwiches_to_type(std::mem::take(item), sandwiches, fresh, changed);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                *arg = apply_sandwiches_to_bounds(
                    std::mem::replace(arg, empty_interval(TypeVar(0))),
                    sandwiches,
                    fresh,
                    changed,
                );
            }
        }
        row.tail = Box::new(apply_sandwiches_to_type(
            *std::mem::take(&mut row.tail),
            sandwiches,
            fresh,
            changed,
        ));
    }
    ty
}

fn apply_sandwiches_to_bounds(
    bounds: CompactBounds,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            if let Some(lifted) = try_apply_sandwich(&lower, &upper, sandwiches, fresh) {
                *changed = true;
                apply_sandwiches_to_bounds(lifted, sandwiches, fresh, changed)
            } else {
                CompactBounds::Interval {
                    lower: apply_sandwiches_to_type(lower, sandwiches, fresh, changed),
                    upper: apply_sandwiches_to_type(upper, sandwiches, fresh, changed),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| apply_sandwiches_to_bounds(arg, sandwiches, fresh, changed))
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(apply_sandwiches_to_bounds(*arg, sandwiches, fresh, changed)),
            arg_eff: Box::new(apply_sandwiches_to_bounds(
                *arg_eff, sandwiches, fresh, changed,
            )),
            ret_eff: Box::new(apply_sandwiches_to_bounds(
                *ret_eff, sandwiches, fresh, changed,
            )),
            ret: Box::new(apply_sandwiches_to_bounds(*ret, sandwiches, fresh, changed)),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .into_iter()
                .map(|field| poly::types::RecordField {
                    name: field.name,
                    value: apply_sandwiches_to_bounds(field.value, sandwiches, fresh, changed),
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
                                apply_sandwiches_to_bounds(payload, sandwiches, fresh, changed)
                            })
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|item| apply_sandwiches_to_bounds(item, sandwiches, fresh, changed))
                .collect(),
        },
    }
}

fn try_apply_sandwich(
    lower: &CompactType,
    upper: &CompactType,
    sandwiches: &FxHashMap<TypeVar, CompactSandwichKind>,
    fresh: &mut FreshCompactVars,
) -> Option<CompactBounds> {
    let center = common_var_in_types(lower, upper).filter(|var| sandwiches.contains_key(var))?;
    match sandwiches.get(&center)? {
        CompactSandwichKind::Con { path, arity } => {
            let lower_args = single_con(lower, path, *arity)?;
            let upper_args = single_con(upper, path, *arity)?;
            Some(CompactBounds::Con {
                path: path.clone(),
                args: lower_args
                    .iter()
                    .zip(upper_args)
                    .map(|(lower, upper)| merge_arg_bounds(lower, upper, fresh))
                    .collect(),
            })
        }
        CompactSandwichKind::Tuple { arity } => {
            let lower_items = single_tuple(lower, *arity)?;
            let upper_items = single_tuple(upper, *arity)?;
            Some(CompactBounds::Tuple {
                items: lower_items
                    .iter()
                    .zip(upper_items)
                    .map(|(lower, upper)| interval_from_types(lower.clone(), upper.clone(), fresh))
                    .collect(),
            })
        }
        CompactSandwichKind::Fun => {
            let lower_fun = single_fun(lower)?;
            let upper_fun = single_fun(upper)?;
            Some(CompactBounds::Fun {
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
            })
        }
    }
}
