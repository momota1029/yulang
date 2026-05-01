use super::*;

pub(crate) fn contains_non_runtime_type(ty: &core_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    contains_non_runtime_type_with_vars(ty, &vars)
}

pub(crate) fn contains_non_runtime_effect_type(ty: &core_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    contains_non_runtime_type_inner(ty, true, &vars)
}

pub(crate) fn contains_non_runtime_type_with_vars(
    ty: &core_ir::Type,
    allowed_vars: &BTreeSet<core_ir::TypeVar>,
) -> bool {
    contains_non_runtime_type_inner(ty, false, allowed_vars)
}

pub(crate) fn collect_type_vars(ty: &core_ir::Type, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match ty {
        core_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        core_ir::Type::Named { args, .. } => {
            for arg in args {
                match arg {
                    core_ir::TypeArg::Type(ty) => collect_type_vars(ty, vars),
                    core_ir::TypeArg::Bounds(bounds) => {
                        if let Some(lower) = bounds.lower.as_deref() {
                            collect_type_vars(lower, vars);
                        }
                        if let Some(upper) = bounds.upper.as_deref() {
                            collect_type_vars(upper, vars);
                        }
                    }
                }
            }
        }
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars(param, vars);
            collect_type_vars(param_effect, vars);
            collect_type_vars(ret_effect, vars);
            collect_type_vars(ret, vars);
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            for item in items {
                collect_type_vars(item, vars);
            }
        }
        core_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        collect_type_vars(ty, vars);
                    }
                }
            }
        }
        core_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars(payload, vars);
                }
            }
            if let Some(tail) = variant.tail.as_deref() {
                collect_type_vars(tail, vars);
            }
        }
        core_ir::Type::Row { items, tail } => {
            for item in items {
                collect_type_vars(item, vars);
            }
            collect_type_vars(tail, vars);
        }
        core_ir::Type::Recursive { body, .. } => collect_type_vars(body, vars),
        core_ir::Type::Never | core_ir::Type::Any => {}
    }
}

pub(super) fn runtime_effect_row_from_items(items: Vec<core_ir::Type>) -> core_ir::Type {
    if items.is_empty() {
        return core_ir::Type::Never;
    }
    core_ir::Type::Row {
        items,
        tail: Box::new(core_ir::Type::Never),
    }
}

pub(super) fn push_unique_effect(out: &mut Vec<core_ir::Type>, effect: core_ir::Type) {
    if !out.contains(&effect) {
        out.push(effect);
    }
}

pub(super) fn is_runtime_hole(ty: &core_ir::Type) -> bool {
    core_type_is_runtime_projection_fallback(ty)
}

pub(super) fn is_runtime_floor(ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Never)
}

pub(super) fn is_never_path(path: &core_ir::Path) -> bool {
    matches!(
        path.segments.as_slice(),
        [core_ir::Name(name)] if name == "never"
    )
}

pub(super) fn contains_non_runtime_type_inner(
    ty: &core_ir::Type,
    effect_slot: bool,
    allowed_vars: &BTreeSet<core_ir::TypeVar>,
) -> bool {
    match ty {
        core_ir::Type::Never | core_ir::Type::Any => false,
        core_ir::Type::Var(var) => !allowed_vars.contains(var),
        core_ir::Type::Union(_) | core_ir::Type::Inter(_) => true,
        core_ir::Type::Row { .. } => !effect_slot,
        core_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            core_ir::TypeArg::Type(ty) => contains_non_runtime_type_inner(ty, false, allowed_vars),
            core_ir::TypeArg::Bounds(_) => true,
        }),
        core_ir::Type::Fun {
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
        core_ir::Type::Tuple(items) => items
            .iter()
            .any(|item| contains_non_runtime_type_inner(item, false, allowed_vars)),
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| contains_non_runtime_type_inner(&field.value, false, allowed_vars))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        contains_non_runtime_type_inner(ty, false, allowed_vars)
                    }
                })
        }
        core_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|payload| contains_non_runtime_type_inner(payload, false, allowed_vars))
            }) || variant
                .tail
                .as_deref()
                .is_some_and(|tail| contains_non_runtime_type_inner(tail, false, allowed_vars))
        }
        core_ir::Type::Recursive { body, .. } => {
            contains_non_runtime_type_inner(body, false, allowed_vars)
        }
    }
}
