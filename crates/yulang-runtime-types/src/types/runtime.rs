use super::*;

pub fn contains_non_runtime_type(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    contains_non_runtime_type_with_vars(ty, &vars)
}

pub fn contains_non_runtime_effect_type(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    contains_non_runtime_type_inner(ty, true, &vars)
}

pub fn contains_non_runtime_type_with_vars(
    ty: &typed_ir::Type,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    contains_non_runtime_type_inner(ty, false, allowed_vars)
}

pub fn collect_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    collect_type_vars_inner(ty, vars, &BTreeSet::new());
}

fn collect_type_vars_inner(
    ty: &typed_ir::Type,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
    bound: &BTreeSet<typed_ir::TypeVar>,
) {
    match ty {
        typed_ir::Type::Unknown => {}
        typed_ir::Type::Var(var) => {
            if !bound.contains(var) {
                vars.insert(var.clone());
            }
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    typed_ir::TypeArg::Type(ty) => collect_type_vars_inner(ty, vars, bound),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_type_vars_inner(lower, vars, bound);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_type_vars_inner(upper, vars, bound);
                        }
                    }
                }
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars_inner(param, vars, bound);
            collect_type_vars_inner(param_effect, vars, bound);
            collect_type_vars_inner(ret_effect, vars, bound);
            collect_type_vars_inner(ret, vars, bound);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_type_vars_inner(item, vars, bound);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars_inner(&field.value, vars, bound);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_type_vars_inner(ty, vars, bound);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars_inner(payload, vars, bound);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_type_vars_inner(tail, vars, bound);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_type_vars_inner(item, vars, bound);
            }
            collect_type_vars_inner(tail, vars, bound);
        }
        typed_ir::Type::Recursive { var, body } => {
            let mut scoped_bound = bound.clone();
            scoped_bound.insert(var.clone());
            collect_type_vars_inner(body, vars, &scoped_bound);
        }
        typed_ir::Type::Never | typed_ir::Type::Any => {}
    }
}

pub(super) fn runtime_effect_row_from_items(items: Vec<typed_ir::Type>) -> typed_ir::Type {
    if items.is_empty() {
        return typed_ir::Type::Never;
    }
    typed_ir::Type::Row {
        items,
        tail: Box::new(typed_ir::Type::Never),
    }
}

pub(super) fn push_unique_effect(out: &mut Vec<typed_ir::Type>, effect: typed_ir::Type) {
    if !out.contains(&effect) {
        out.push(effect);
    }
}

pub(super) fn is_runtime_hole(ty: &typed_ir::Type) -> bool {
    core_type_is_runtime_projection_fallback(ty)
}

pub(super) fn is_runtime_floor(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Never)
}

pub(super) fn is_never_path(path: &typed_ir::Path) -> bool {
    matches!(
        path.segments.as_slice(),
        [typed_ir::Name(name)] if name == "never"
    )
}

pub(super) fn contains_non_runtime_type_inner(
    ty: &typed_ir::Type,
    effect_slot: bool,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    match ty {
        typed_ir::Type::Unknown => false,
        typed_ir::Type::Never | typed_ir::Type::Any => false,
        typed_ir::Type::Var(var) => !allowed_vars.contains(var),
        typed_ir::Type::Union(_) | typed_ir::Type::Inter(_) => true,
        typed_ir::Type::Row { .. } => !effect_slot,
        typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            typed_ir::TypeArg::Type(ty) => contains_non_runtime_type_arg(ty, allowed_vars),
            typed_ir::TypeArg::Bounds(_) => true,
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            contains_non_runtime_type_inner(param, false, allowed_vars)
                || contains_non_runtime_type_inner(param_effect, true, allowed_vars)
                || contains_non_runtime_type_inner(ret_effect, true, allowed_vars)
                || contains_non_runtime_type_inner(ret, false, allowed_vars)
        }
        typed_ir::Type::Tuple(items) => items
            .iter()
            .any(|item| contains_non_runtime_type_inner(item, false, allowed_vars)),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| contains_non_runtime_type_inner(&field.value, false, allowed_vars))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        contains_non_runtime_type_inner(ty, false, allowed_vars)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|payload| contains_non_runtime_type_inner(payload, false, allowed_vars))
            }) || variant
                .tail
                .as_deref()
                .is_some_and(|tail| contains_non_runtime_type_inner(tail, false, allowed_vars))
        }
        typed_ir::Type::Recursive { body, .. } => {
            contains_non_runtime_type_inner(body, effect_slot, allowed_vars)
        }
    }
}

fn contains_non_runtime_type_arg(
    ty: &typed_ir::Type,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    if matches_effect_type_arg_shape(ty) {
        contains_non_runtime_type_inner(ty, true, allowed_vars)
    } else {
        contains_non_runtime_type_inner(ty, false, allowed_vars)
    }
}

fn matches_effect_type_arg_shape(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Row { .. } => true,
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            !items.is_empty() && items.iter().all(matches_effect_type_arg_shape)
        }
        typed_ir::Type::Recursive { body, .. } => matches_effect_type_arg_shape(body),
        _ => false,
    }
}
