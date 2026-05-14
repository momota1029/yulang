use super::*;

pub(crate) fn type_compatible(expected: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    type_compatible_inner(expected, actual, 128)
}

pub(crate) fn needs_runtime_coercion(expected: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    expected != actual && can_widen_runtime_value(actual, expected)
}

pub(super) fn type_compatible_inner(
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
    depth: usize,
) -> bool {
    if depth == 0 {
        return true;
    }
    if expected == actual || is_never_type(expected) && is_never_type(actual) {
        return true;
    }
    if is_never_type(actual) {
        return true;
    }
    match (expected, actual) {
        (typed_ir::Type::Any, _) | (_, typed_ir::Type::Any) => true,
        (typed_ir::Type::Var(_), _) | (_, typed_ir::Type::Var(_)) => true,
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => args
            .iter()
            .zip(actual_args)
            .all(|(left, right)| type_arg_compatible(left, right, depth - 1)),
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if args.is_empty() && actual_args.is_empty() => {
            typed_ir::can_widen_named_paths(actual_path, path)
        }
        (
            typed_ir::Type::Fun { param, ret, .. },
            typed_ir::Type::Fun {
                param: actual_param,
                ret: actual_ret,
                ..
            },
        ) => {
            type_compatible_inner(param, actual_param, depth - 1)
                && type_compatible_inner(ret, actual_ret, depth - 1)
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            items
                .iter()
                .zip(actual_items)
                .all(|(left, right)| type_compatible_inner(left, right, depth - 1))
        }
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
            record.fields.iter().all(|field| {
                match actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                {
                    Some(actual) => type_compatible_inner(&field.value, &actual.value, depth - 1),
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
                        variant_payloads_compatible(&case.payloads, &actual.payloads, depth - 1)
                    })
            })
        }
        (typed_ir::Type::Union(items), _) => items
            .iter()
            .any(|item| type_compatible_inner(item, actual, depth - 1)),
        (_, typed_ir::Type::Union(items)) => items
            .iter()
            .any(|item| type_compatible_inner(expected, item, depth - 1)),
        (typed_ir::Type::Inter(items), _) => items
            .iter()
            .all(|item| type_compatible_inner(item, actual, depth - 1)),
        (_, typed_ir::Type::Inter(items)) => items
            .iter()
            .all(|item| type_compatible_inner(expected, item, depth - 1)),
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) if items.len() == actual_items.len() => {
            items
                .iter()
                .zip(actual_items)
                .all(|(left, right)| type_compatible_inner(left, right, depth - 1))
                && type_compatible_inner(tail, actual_tail, depth - 1)
        }
        (
            typed_ir::Type::Recursive { var, body },
            typed_ir::Type::Recursive {
                var: actual_var,
                body: actual_body,
            },
        ) if var == actual_var => type_compatible_inner(body, actual_body, depth - 1),
        _ => false,
    }
}

fn variant_payloads_compatible(
    expected: &[typed_ir::Type],
    actual: &[typed_ir::Type],
    depth: usize,
) -> bool {
    if expected.len() == actual.len() {
        return actual
            .iter()
            .zip(expected)
            .all(|(left, right)| type_compatible_inner(right, left, depth));
    }
    if expected.len() > 1 && actual.len() == 1 {
        return type_compatible_inner(&typed_ir::Type::Tuple(expected.to_vec()), &actual[0], depth);
    }
    if expected.len() == 1 && actual.len() > 1 {
        return type_compatible_inner(&expected[0], &typed_ir::Type::Tuple(actual.to_vec()), depth);
    }
    false
}

pub(super) fn can_widen_runtime_value(actual: &typed_ir::Type, expected: &typed_ir::Type) -> bool {
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
            typed_ir::can_widen_named_paths(actual_path, expected_path)
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
    match (expected, actual) {
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) => {
            type_compatible_inner(left, right, depth)
        }
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Bounds(bounds)) => {
            bounds_admits_type(bounds, left, depth)
        }
        (typed_ir::TypeArg::Bounds(bounds), typed_ir::TypeArg::Type(right)) => {
            bounds_admits_type(bounds, right, depth)
        }
        (typed_ir::TypeArg::Bounds(left), typed_ir::TypeArg::Bounds(right)) => {
            match (&left.lower, &right.lower) {
                (Some(left), Some(right)) if !type_compatible_inner(left, right, depth) => {
                    return false;
                }
                _ => {}
            }
            match (&left.upper, &right.upper) {
                (Some(left), Some(right)) => type_compatible_inner(left, right, depth),
                _ => true,
            }
        }
    }
}

pub(super) fn bounds_admits_type(
    bounds: &typed_ir::TypeBounds,
    ty: &typed_ir::Type,
    depth: usize,
) -> bool {
    bounds
        .lower
        .as_deref()
        .is_none_or(|lower| type_compatible_inner(lower, ty, depth))
        && bounds
            .upper
            .as_deref()
            .is_none_or(|upper| type_compatible_inner(upper, ty, depth))
}

pub(super) fn is_never_type(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Never)
        || matches!(
            ty,
            typed_ir::Type::Named { path, args }
                if args.is_empty()
                    && matches!(path.segments.as_slice(), [typed_ir::Name(name)] if name == "never")
        )
}
