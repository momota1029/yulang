use std::collections::BTreeSet;

use yulang_typed_ir as typed_ir;

use super::types::collect_core_type_vars;

pub(super) fn type_has_vars(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    !vars.is_empty()
}

pub(super) fn substitution_type_usable(ty: &typed_ir::Type, allow_never: bool) -> bool {
    !matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
    ) && (allow_never || !matches!(ty, typed_ir::Type::Never))
        && !type_has_vars(ty)
        && !type_has_unknown(ty)
}

pub(super) fn type_has_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_unknown),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_has_unknown(param)
                || type_has_unknown(param_effect)
                || type_has_unknown(ret_effect)
                || type_has_unknown(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_has_unknown),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_has_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_has_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_has_unknown))
                || variant.tail.as_deref().is_some_and(type_has_unknown)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_has_unknown) || type_has_unknown(tail)
        }
        typed_ir::Type::Recursive { body, .. } => type_has_unknown(body),
    }
}

fn type_arg_has_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_has_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_has_unknown)
                || bounds.upper.as_deref().is_some_and(type_has_unknown)
        }
    }
}

pub(super) fn type_bounds_closed(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds.lower.as_deref().is_none_or(|ty| !type_has_vars(ty))
        && bounds.upper.as_deref().is_none_or(|ty| !type_has_vars(ty))
}

pub(super) fn type_bounds_informative(bounds: &typed_ir::TypeBounds) -> bool {
    bounds.lower.as_deref().is_some_and(type_informative)
        || bounds.upper.as_deref().is_some_and(type_informative)
}

fn type_informative(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { .. } => true,
        typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record(_)
        | typed_ir::Type::Variant(_) => true,
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_informative) || type_informative(tail)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().any(type_informative)
        }
        typed_ir::Type::Recursive { body, .. } => type_informative(body),
    }
}

pub(super) fn value_type_bounds_runtime_usable(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds
            .lower
            .as_deref()
            .is_none_or(value_type_runtime_usable)
        && bounds
            .upper
            .as_deref()
            .is_none_or(value_type_runtime_usable)
}

pub(super) fn effect_type_bounds_runtime_usable(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds
            .lower
            .as_deref()
            .is_none_or(effect_type_runtime_usable)
        && bounds
            .upper
            .as_deref()
            .is_none_or(effect_type_runtime_usable)
}

fn value_type_runtime_usable(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().all(type_arg_runtime_usable),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            value_type_runtime_usable(param)
                && effect_type_runtime_usable(param_effect)
                && effect_type_runtime_usable(ret_effect)
                && value_type_runtime_usable(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().all(value_type_runtime_usable),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| value_type_runtime_usable(&field.value))
                && record
                    .spread
                    .as_ref()
                    .is_none_or(record_spread_runtime_usable)
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(value_type_runtime_usable))
                && variant
                    .tail
                    .as_deref()
                    .is_none_or(value_type_runtime_usable)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(effect_type_runtime_usable) && effect_type_runtime_usable(tail)
        }
        typed_ir::Type::Recursive { body, .. } => value_type_runtime_usable(body),
    }
}

fn effect_type_runtime_usable(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Never => true,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(effect_type_runtime_usable) && effect_type_runtime_usable(tail)
        }
        _ => value_type_runtime_usable(ty),
    }
}

fn record_spread_runtime_usable(spread: &typed_ir::RecordSpread) -> bool {
    match spread {
        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
            value_type_runtime_usable(ty)
        }
    }
}

fn type_arg_runtime_usable(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => value_type_runtime_usable(ty),
        typed_ir::TypeArg::Bounds(bounds) => value_type_bounds_runtime_usable(bounds),
    }
}

pub(super) fn bounds_primary_type(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::Type> {
    bounds
        .lower
        .as_deref()
        .and_then(primary_structural_or_concrete_type)
        .or_else(|| {
            bounds
                .upper
                .as_deref()
                .and_then(primary_structural_or_concrete_type)
        })
}

pub(super) fn primary_structural_or_concrete_type(ty: &typed_ir::Type) -> Option<&typed_ir::Type> {
    match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items
            .iter()
            .find_map(primary_structural_or_concrete_type)
            .or(Some(ty)),
        typed_ir::Type::Var(_) | typed_ir::Type::Any | typed_ir::Type::Never => None,
        _ => Some(ty),
    }
}

pub(super) fn primary_structural_or_concrete_type_not_equal<'a>(
    ty: &'a typed_ir::Type,
    expected: &typed_ir::Type,
) -> Option<&'a typed_ir::Type> {
    match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items
            .iter()
            .filter_map(primary_structural_or_concrete_type)
            .find(|item| *item != expected),
        typed_ir::Type::Var(_) | typed_ir::Type::Any | typed_ir::Type::Never => None,
        _ if ty != expected => Some(ty),
        _ => None,
    }
}
pub(super) fn core_type_has_no_vars(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    vars.is_empty()
}

pub(super) fn core_value_type_has_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(core_type_arg_has_unknown),
        typed_ir::Type::Fun { param, ret, .. } => {
            core_value_type_has_unknown(param) || core_value_type_has_unknown(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(core_value_type_has_unknown),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_value_type_has_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_value_type_has_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_value_type_has_unknown))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| core_value_type_has_unknown(tail))
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_value_type_has_unknown) || core_value_type_has_unknown(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_value_type_has_unknown(body),
    }
}

fn core_type_arg_has_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_value_type_has_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| core_value_type_has_unknown(ty))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| core_value_type_has_unknown(ty))
        }
    }
}

pub(super) fn closed_runtime_type_from_bounds(
    lower: &typed_ir::Type,
    upper: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    let lower = erase_open_vars_from_runtime_type(lower)?;
    let upper = erase_open_vars_from_runtime_type(upper)?;
    (lower == upper && core_type_has_no_vars(&lower)).then_some(lower)
}

pub(super) fn erase_open_vars_from_runtime_type(ty: &typed_ir::Type) -> Option<typed_ir::Type> {
    match ty {
        typed_ir::Type::Var(_) => None,
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Named { .. } => Some(erase_open_vars_from_type_arg_type(ty)),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Some(typed_ir::Type::Fun {
            param: Box::new(
                erase_open_vars_from_runtime_type(param).unwrap_or(typed_ir::Type::Unknown),
            ),
            param_effect: Box::new(
                erase_open_vars_from_runtime_type(param_effect).unwrap_or(typed_ir::Type::Unknown),
            ),
            ret_effect: Box::new(
                erase_open_vars_from_runtime_type(ret_effect).unwrap_or(typed_ir::Type::Unknown),
            ),
            ret: Box::new(
                erase_open_vars_from_runtime_type(ret).unwrap_or(typed_ir::Type::Unknown),
            ),
        }),
        typed_ir::Type::Tuple(items) => Some(typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| {
                    erase_open_vars_from_runtime_type(item).unwrap_or(typed_ir::Type::Unknown)
                })
                .collect(),
        )),
        typed_ir::Type::Record(record) => Some(typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: erase_open_vars_from_runtime_type(&field.value)
                        .unwrap_or(typed_ir::Type::Unknown),
                    optional: field.optional,
                })
                .collect(),
            spread: None,
        })),
        typed_ir::Type::Variant(variant) => Some(typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| {
                            erase_open_vars_from_runtime_type(payload)
                                .unwrap_or(typed_ir::Type::Unknown)
                        })
                        .collect(),
                })
                .collect(),
            tail: None,
        })),
        typed_ir::Type::Row { items, tail } => Some(typed_ir::Type::Row {
            items: items
                .iter()
                .filter_map(erase_open_vars_from_runtime_type)
                .collect(),
            tail: Box::new(
                erase_open_vars_from_runtime_type(tail).unwrap_or(typed_ir::Type::Never),
            ),
        }),
        typed_ir::Type::Union(items) => erase_open_vars_from_runtime_type_list(items, true),
        typed_ir::Type::Inter(items) => erase_open_vars_from_runtime_type_list(items, false),
        typed_ir::Type::Recursive { var, body } => {
            erase_open_vars_from_runtime_type(body).map(|body| typed_ir::Type::Recursive {
                var: var.clone(),
                body: Box::new(body),
            })
        }
    }
}

fn erase_open_vars_from_type_arg_type(ty: &typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| match arg {
                    typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(
                        erase_open_vars_from_runtime_type(ty).unwrap_or(typed_ir::Type::Unknown),
                    ),
                    typed_ir::TypeArg::Bounds(bounds) => {
                        let lower = bounds
                            .lower
                            .as_deref()
                            .and_then(erase_open_vars_from_runtime_type);
                        let upper = bounds
                            .upper
                            .as_deref()
                            .and_then(erase_open_vars_from_runtime_type);
                        match (lower, upper) {
                            (Some(lower), Some(upper)) if lower == upper => {
                                typed_ir::TypeArg::Type(lower)
                            }
                            (Some(ty), None) | (None, Some(ty)) => typed_ir::TypeArg::Type(ty),
                            (Some(lower), Some(upper)) => {
                                typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                                    lower: Some(Box::new(lower)),
                                    upper: Some(Box::new(upper)),
                                })
                            }
                            (None, None) => typed_ir::TypeArg::Type(typed_ir::Type::Unknown),
                        }
                    }
                })
                .collect(),
        },
        other => other.clone(),
    }
}

fn erase_open_vars_from_runtime_type_list(
    items: &[typed_ir::Type],
    union: bool,
) -> Option<typed_ir::Type> {
    let mut closed = items
        .iter()
        .filter_map(erase_open_vars_from_runtime_type)
        .collect::<Vec<_>>();
    closed.sort_by_key(|ty| format!("{ty:?}"));
    closed.dedup();
    match closed.len() {
        0 => None,
        1 => closed.pop(),
        _ if union => Some(typed_ir::Type::Union(closed)),
        _ => Some(typed_ir::Type::Inter(closed)),
    }
}
