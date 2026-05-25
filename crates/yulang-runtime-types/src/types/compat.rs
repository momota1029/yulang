use super::*;

pub fn type_compatible(expected: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    type_compatible_with_order(&typed_ir::PrimitiveTypeOrder::standard(), expected, actual)
}

pub fn type_compatible_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> bool {
    type_compatible_inner_with_order(primitive_order, expected, actual, 128)
}

pub fn needs_runtime_coercion(expected: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    needs_runtime_coercion_with_order(&typed_ir::PrimitiveTypeOrder::standard(), expected, actual)
}

pub fn needs_runtime_coercion_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> bool {
    expected != actual && can_widen_runtime_value_with_order(primitive_order, actual, expected)
}

#[cfg(test)]
pub(super) fn type_compatible_inner(
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
    depth: usize,
) -> bool {
    type_compatible_inner_with_order(
        &typed_ir::PrimitiveTypeOrder::standard(),
        expected,
        actual,
        depth,
    )
}

pub(super) fn type_compatible_inner_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
    depth: usize,
) -> bool {
    if expected == actual || core_type_is_never(expected) && core_type_is_never(actual) {
        return true;
    }
    if core_type_is_unit_value(expected) && core_type_is_unit_value(actual) {
        return true;
    }
    if depth == 0 {
        return false;
    }
    if core_type_is_never(actual) {
        return true;
    }
    match (expected, actual) {
        (expected, _) if core_type_is_top(expected) || core_type_is_inference_var(expected) => true,
        (_, actual) if core_type_is_top(actual) || core_type_is_inference_var(actual) => true,
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            args.iter().zip(actual_args).all(|(left, right)| {
                type_arg_compatible_with_order(primitive_order, left, right, depth - 1)
            })
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if args.is_empty() && actual_args.is_empty() => {
            primitive_order.can_widen_named_paths(actual_path, path)
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => {
            type_compatible_inner_with_order(primitive_order, param, actual_param, depth - 1)
                && effect_compatible(param_effect, actual_param_effect)
                && effect_compatible(ret_effect, actual_ret_effect)
                && type_compatible_inner_with_order(primitive_order, ret, actual_ret, depth - 1)
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            items.iter().zip(actual_items).all(|(left, right)| {
                type_compatible_inner_with_order(primitive_order, left, right, depth - 1)
            })
        }
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
            record.fields.iter().all(|field| {
                match actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                {
                    Some(actual) => type_compatible_inner_with_order(
                        primitive_order,
                        &field.value,
                        &actual.value,
                        depth - 1,
                    ),
                    None => field.optional,
                }
            })
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
            actual_variant.cases.iter().all(|actual| {
                variant
                    .cases
                    .iter()
                    .find(|case| case.name == actual.name)
                    .is_some_and(|case| {
                        variant_payloads_compatible_with_order(
                            primitive_order,
                            &case.payloads,
                            &actual.payloads,
                            depth - 1,
                        )
                    })
            })
        }
        (typed_ir::Type::Union(items), _) => items
            .iter()
            .any(|item| type_compatible_inner_with_order(primitive_order, item, actual, depth - 1)),
        (_, typed_ir::Type::Union(items)) => items.iter().any(|item| {
            type_compatible_inner_with_order(primitive_order, expected, item, depth - 1)
        }),
        (typed_ir::Type::Inter(items), _) => items
            .iter()
            .all(|item| type_compatible_inner_with_order(primitive_order, item, actual, depth - 1)),
        (_, typed_ir::Type::Inter(items)) => items.iter().all(|item| {
            type_compatible_inner_with_order(primitive_order, expected, item, depth - 1)
        }),
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) if items.len() == actual_items.len() => {
            row_items_compatible_unordered_with_order(
                primitive_order,
                items,
                actual_items,
                depth - 1,
            ) && type_compatible_inner_with_order(primitive_order, tail, actual_tail, depth - 1)
        }
        (
            typed_ir::Type::Recursive { var, body },
            typed_ir::Type::Recursive {
                var: actual_var,
                body: actual_body,
            },
        ) if var == actual_var => {
            type_compatible_inner_with_order(primitive_order, body, actual_body, depth - 1)
        }
        _ => false,
    }
}

fn core_type_is_unit_value(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Tuple(items) => items.is_empty(),
        typed_ir::Type::Named { path, args } => {
            args.is_empty()
                && path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.0 == "unit")
        }
        _ => false,
    }
}

fn row_items_compatible_unordered_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &[typed_ir::Type],
    actual: &[typed_ir::Type],
    depth: usize,
) -> bool {
    if expected.len() != actual.len() {
        return false;
    }
    let mut matched_expected = vec![false; expected.len()];
    for actual_item in actual {
        let Some(index) = expected
            .iter()
            .enumerate()
            .find_map(|(index, expected_item)| {
                (!matched_expected[index]
                    && row_item_compatible_with_order(
                        primitive_order,
                        expected_item,
                        actual_item,
                        depth,
                    ))
                .then_some(index)
            })
        else {
            return false;
        };
        matched_expected[index] = true;
    }
    true
}

fn row_item_compatible_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
    depth: usize,
) -> bool {
    type_compatible_inner_with_order(primitive_order, expected, actual, depth)
        || effect_path(expected).is_some()
            && effect_path(actual).is_some()
            && effect_compatible(expected, actual)
}

fn variant_payloads_compatible_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &[typed_ir::Type],
    actual: &[typed_ir::Type],
    depth: usize,
) -> bool {
    if expected.len() == actual.len() {
        return actual.iter().zip(expected).all(|(left, right)| {
            type_compatible_inner_with_order(primitive_order, right, left, depth)
        });
    }
    if expected.len() > 1 && actual.len() == 1 {
        return type_compatible_inner_with_order(
            primitive_order,
            &typed_ir::Type::Tuple(expected.to_vec()),
            &actual[0],
            depth,
        );
    }
    if expected.len() == 1 && actual.len() > 1 {
        return type_compatible_inner_with_order(
            primitive_order,
            &expected[0],
            &typed_ir::Type::Tuple(actual.to_vec()),
            depth,
        );
    }
    false
}

pub(super) fn can_widen_runtime_value_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
) -> bool {
    match (actual, expected) {
        (
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
            typed_ir::Type::Named {
                path: expected_path,
                args: expected_args,
            },
        ) if actual_args.is_empty() && expected_args.is_empty() => {
            primitive_order.can_widen_named_paths(actual_path, expected_path)
        }
        (typed_ir::Type::Record(_), typed_ir::Type::Named { .. })
        | (typed_ir::Type::Named { .. }, typed_ir::Type::Record(_)) => true,
        _ => false,
    }
}

pub(super) fn type_arg_compatible(
    expected: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    depth: usize,
) -> bool {
    type_arg_compatible_with_order(
        &typed_ir::PrimitiveTypeOrder::standard(),
        expected,
        actual,
        depth,
    )
}

fn type_arg_compatible_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    expected: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    depth: usize,
) -> bool {
    if type_arg_is_effect_like(expected) || type_arg_is_effect_like(actual) {
        let Some(expected) = type_arg_effect_type(expected) else {
            return false;
        };
        let Some(actual) = type_arg_effect_type(actual) else {
            return false;
        };
        return effect_compatible(expected, actual);
    }
    match (expected, actual) {
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) => {
            type_compatible_inner_with_order(primitive_order, left, right, depth)
        }
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Bounds(bounds)) => {
            bounds_admits_type_with_order(primitive_order, bounds, left, depth)
        }
        (typed_ir::TypeArg::Bounds(bounds), typed_ir::TypeArg::Type(right)) => {
            bounds_admits_type_with_order(primitive_order, bounds, right, depth)
        }
        (typed_ir::TypeArg::Bounds(left), typed_ir::TypeArg::Bounds(right)) => {
            match (&left.lower, &right.lower) {
                (Some(left), Some(right))
                    if !type_compatible_inner_with_order(primitive_order, left, right, depth) =>
                {
                    return false;
                }
                _ => {}
            }
            match (&left.upper, &right.upper) {
                (Some(left), Some(right)) => {
                    type_compatible_inner_with_order(primitive_order, left, right, depth)
                }
                _ => true,
            }
        }
    }
}

fn type_arg_is_effect_like(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_is_effect_like(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_is_effect_like)
                || bounds.upper.as_deref().is_some_and(type_is_effect_like)
        }
    }
}

fn type_arg_effect_type(arg: &typed_ir::TypeArg) -> Option<&typed_ir::Type> {
    match arg {
        typed_ir::TypeArg::Type(ty) if type_is_effect_like(ty) => Some(ty),
        typed_ir::TypeArg::Type(_) => None,
        typed_ir::TypeArg::Bounds(bounds) => bounds
            .lower
            .as_deref()
            .filter(|ty| type_is_effect_like(ty))
            .or_else(|| bounds.upper.as_deref().filter(|ty| type_is_effect_like(ty))),
    }
}

fn bounds_admits_type_with_order(
    primitive_order: &typed_ir::PrimitiveTypeOrder,
    bounds: &typed_ir::TypeBounds,
    ty: &typed_ir::Type,
    depth: usize,
) -> bool {
    bounds
        .lower
        .as_deref()
        .is_none_or(|lower| type_compatible_inner_with_order(primitive_order, lower, ty, depth))
        && bounds
            .upper
            .as_deref()
            .is_none_or(|upper| type_compatible_inner_with_order(primitive_order, upper, ty, depth))
}
