use super::*;

pub(crate) fn boundary_expr(actual: &Type, expected: &Type, expr: Expr) -> Expr {
    boundary_expr_with_hygiene(
        actual,
        expected,
        expr,
        hygiene::function_adapter_hygiene(actual, expected),
    )
}

pub(crate) fn boundary_expr_with_hygiene(
    actual: &Type,
    expected: &Type,
    expr: Expr,
    function_hygiene: mono::FunctionAdapterHygiene,
) -> Expr {
    if equivalent_boundary_types(actual, expected) {
        return expr;
    }
    if let (
        Type::Thunk {
            effect: source_effect,
            value: source_value,
        },
        Type::Thunk {
            effect: target_effect,
            value: target_value,
        },
    ) = (actual, expected)
    {
        let forced = Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: source_effect.as_ref().clone(),
                value: source_value.as_ref().clone(),
            },
            target: ComputationType {
                effect: source_effect.as_ref().clone(),
                value: source_value.as_ref().clone(),
            },
            thunk: Box::new(expr),
        });
        let body = if equivalent_boundary_types(source_value, target_value) {
            forced
        } else {
            boundary_expr(source_value, target_value, forced)
        };
        return Expr::new(ExprKind::MakeThunk {
            source: ComputationType {
                effect: target_effect.as_ref().clone(),
                value: target_value.as_ref().clone(),
            },
            target: EffectiveThunkType {
                effect: target_effect.as_ref().clone(),
                value: target_value.as_ref().clone(),
            },
            body: Box::new(body),
        });
    }
    if let Type::Thunk { effect, value } = expected
        && equivalent_boundary_types(actual, value)
    {
        return Expr::new(ExprKind::MakeThunk {
            source: ComputationType {
                effect: effect.as_ref().clone(),
                value: actual.clone(),
            },
            target: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            body: Box::new(expr),
        });
    }
    if let Type::Thunk { effect, value } = actual
        && matches!(value.as_ref(), Type::Never)
    {
        let forced = Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            target: ComputationType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            thunk: Box::new(expr),
        });
        return boundary_expr(value, expected, forced);
    }
    if let Type::Thunk { effect, value } = actual
        && equivalent_boundary_types(value, expected)
    {
        return Expr::new(ExprKind::ForceThunk {
            source: EffectiveThunkType {
                effect: effect.as_ref().clone(),
                value: value.as_ref().clone(),
            },
            target: ComputationType {
                effect: effect.as_ref().clone(),
                value: expected.clone(),
            },
            thunk: Box::new(expr),
        });
    }
    if function_boundary_types(actual, expected) {
        return Expr::new(ExprKind::FunctionAdapter {
            source: actual.clone(),
            target: expected.clone(),
            function: Box::new(expr),
            hygiene: function_hygiene,
        });
    }
    Expr::new(ExprKind::Coerce {
        source: actual.clone(),
        target: expected.clone(),
        expr: Box::new(expr),
    })
}

pub(crate) fn wrap_raw_thunk_computation(actual: Option<&Type>, expr: Expr) -> Expr {
    let Some(Type::Thunk { effect, value }) = actual else {
        return expr;
    };
    Expr::new(ExprKind::MakeThunk {
        source: ComputationType {
            effect: effect.as_ref().clone(),
            value: value.as_ref().clone(),
        },
        target: EffectiveThunkType {
            effect: effect.as_ref().clone(),
            value: value.as_ref().clone(),
        },
        body: Box::new(expr),
    })
}

pub(crate) fn force_expr_if_thunk(actual: Option<&Type>, expr: Expr) -> Expr {
    let Some(actual @ Type::Thunk { value, .. }) = actual else {
        return expr;
    };
    boundary_expr(actual, value, expr)
}

pub(crate) fn implicit_force_type(
    plan: &solve::ExprTypePlan,
    expr: poly_expr::ExprId,
) -> Option<&Type> {
    let actual = plan.actual_type_of(expr)?;
    if let Some(boundary) = plan.boundary(expr)
        && matches!(boundary.actual, Type::Thunk { .. })
        && !matches!(boundary.expected, Type::Thunk { .. })
    {
        return None;
    }
    Some(actual)
}

pub(crate) fn discards_unit_boundary(plan: &solve::ExprTypePlan, expr: poly_expr::ExprId) -> bool {
    plan.boundary(expr)
        .is_some_and(|boundary| equivalent_boundary_types(boundary.expected, &Type::unit()))
}

pub(crate) fn wrap_stack_handler_marker(signature: &Type, body: Expr) -> Expr {
    let Some(path) = stack_handler_marker_path(signature) else {
        return body;
    };
    // The frame belongs to the handler invocation, not to partially applied function values.
    // Curried handlers therefore carry the marker around the innermost body.
    wrap_stack_handler_marker_body(path, body)
}

pub(crate) fn wrap_stack_handler_marker_body(path: Vec<String>, body: Expr) -> Expr {
    match body.kind {
        ExprKind::Lambda(param, lambda_body) => Expr::new(ExprKind::Lambda(
            param,
            Box::new(wrap_stack_handler_marker_body(path, *lambda_body)),
        )),
        ExprKind::Catch { body, arms } => Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::MarkerFrame { path, body })),
            arms,
        }),
        ExprKind::MakeThunk {
            source,
            target,
            body,
        } => Expr::new(ExprKind::MakeThunk {
            source,
            target,
            body: Box::new(wrap_stack_handler_marker_body(path, *body)),
        }),
        other => Expr::new(ExprKind::MarkerFrame {
            path,
            body: Box::new(Expr::new(other)),
        }),
    }
}

pub(crate) fn stack_handler_marker_path(signature: &Type) -> Option<Vec<String>> {
    let Type::Fun { arg, .. } = signature else {
        return None;
    };
    thunk_effect_marker_path(arg)
}

pub(crate) fn thunk_effect_marker_path(ty: &Type) -> Option<Vec<String>> {
    match ty {
        Type::Thunk { effect, .. } => effect_marker_path(effect),
        Type::Stack { inner, .. } => thunk_effect_marker_path(inner),
        _ => None,
    }
}

pub(crate) fn effect_marker_path(effect: &Type) -> Option<Vec<String>> {
    match effect {
        Type::EffectRow(items) => items.iter().find_map(effect_marker_path),
        Type::Con { path, .. } if !path.is_empty() => Some(path.clone()),
        Type::Stack { inner, .. } => effect_marker_path(inner),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            effect_marker_path(left).or_else(|| effect_marker_path(right))
        }
        _ => None,
    }
}

pub(crate) fn is_field_projection_method(arena: &poly_expr::Arena, def: poly_expr::DefId) -> bool {
    arena.field_projections.contains(&def)
}

pub(crate) fn method_instance_expected_type(
    plan: &solve::ExprTypePlan,
    base: poly_expr::ExprId,
    select: poly_expr::ExprId,
) -> Option<Type> {
    let receiver = method_receiver_type(plan, base)?;
    let result = plan
        .boundary(select)
        .map(|boundary| boundary.expected.clone())
        .or_else(|| plan.actual_type_of(select).cloned())?;
    Some(types::pure_function_type(receiver, result))
}

pub(crate) fn method_receiver_type(
    plan: &solve::ExprTypePlan,
    base: poly_expr::ExprId,
) -> Option<Type> {
    plan.boundary(base)
        .map(|boundary| boundary.expected.clone())
        .or_else(|| plan.actual_type_of(base).cloned())
}

pub(crate) fn var_instance_type(
    plan: &solve::ExprTypePlan,
    expr: poly_expr::ExprId,
) -> Option<&Type> {
    plan.boundary(expr)
        .map(|boundary| boundary.expected)
        .or_else(|| plan.actual_type_of(expr))
}
pub(crate) fn function_boundary_types(actual: &Type, expected: &Type) -> bool {
    matches!((actual, expected), (Type::Fun { .. }, Type::Fun { .. }))
}

pub(crate) fn equivalent_boundary_types(actual: &Type, expected: &Type) -> bool {
    if actual == expected || actual.is_pure_effect() && expected.is_pure_effect() {
        return true;
    }
    match (actual, expected) {
        (Type::EffectRow(items), expected) if items.len() == 1 => {
            equivalent_boundary_types(&items[0], expected)
        }
        (actual, Type::EffectRow(items)) if items.len() == 1 => {
            equivalent_boundary_types(actual, &items[0])
        }
        (actual, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            equivalent_boundary_types(actual, value)
        }
        (Type::Thunk { effect, value }, expected) if effect.is_pure_effect() => {
            equivalent_boundary_types(value, expected)
        }
        (
            Type::Con {
                path: actual_path,
                args: actual_args,
            },
            Type::Con {
                path: expected_path,
                args: expected_args,
            },
        ) => {
            actual_path == expected_path
                && actual_args.len() == expected_args.len()
                && actual_args
                    .iter()
                    .zip(expected_args)
                    .all(|(actual, expected)| equivalent_boundary_types(actual, expected))
        }
        (
            Type::Fun {
                arg: actual_arg,
                arg_effect: actual_arg_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
            Type::Fun {
                arg: expected_arg,
                arg_effect: expected_arg_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            },
        ) => {
            equivalent_boundary_types(actual_arg, expected_arg)
                && equivalent_effect_boundary_types(actual_arg_effect, expected_arg_effect)
                && equivalent_effect_boundary_types(actual_ret_effect, expected_ret_effect)
                && equivalent_boundary_types(actual_ret, expected_ret)
        }
        (Type::Tuple(actual_items), Type::Tuple(expected_items)) => {
            actual_items.len() == expected_items.len()
                && actual_items
                    .iter()
                    .zip(expected_items)
                    .all(|(actual, expected)| equivalent_boundary_types(actual, expected))
        }
        (Type::Record(actual_fields), Type::Record(expected_fields)) => {
            expected_fields.iter().all(|expected| {
                record_field_type(actual_fields, &expected.name)
                    .map_or(expected.optional, |actual| {
                        equivalent_boundary_types(&actual.value, &expected.value)
                    })
            })
        }
        (Type::PolyVariant(actual_variants), Type::PolyVariant(expected_variants)) => {
            actual_variants.iter().all(|actual| {
                expected_variants
                    .iter()
                    .find(|expected| {
                        expected.name == actual.name
                            && expected.payloads.len() == actual.payloads.len()
                    })
                    .is_some_and(|expected| {
                        actual
                            .payloads
                            .iter()
                            .zip(&expected.payloads)
                            .all(|(actual, expected)| equivalent_boundary_types(actual, expected))
                    })
            })
        }
        (actual, Type::Union(left, right)) => {
            equivalent_boundary_types(actual, left) || equivalent_boundary_types(actual, right)
        }
        (Type::Union(left, right), expected) => {
            equivalent_boundary_types(left, expected) && equivalent_boundary_types(right, expected)
        }
        (actual, Type::Intersection(left, right)) => {
            equivalent_boundary_types(actual, left) && equivalent_boundary_types(actual, right)
        }
        (Type::Intersection(left, right), expected) => {
            equivalent_boundary_types(left, expected) || equivalent_boundary_types(right, expected)
        }
        (Type::EffectRow(actual_items), Type::EffectRow(expected_items)) => {
            equivalent_effect_row_boundary_types(actual_items, expected_items)
        }
        (
            Type::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
            Type::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
        ) => {
            equivalent_effect_boundary_types(actual_effect, expected_effect)
                && equivalent_boundary_types(actual_value, expected_value)
        }
        _ => false,
    }
}

pub(crate) fn equivalent_effect_row_boundary_types(
    actual_items: &[Type],
    expected_items: &[Type],
) -> bool {
    if actual_items.len() != expected_items.len() {
        return false;
    }
    let mut used = vec![false; expected_items.len()];
    actual_items.iter().all(|actual| {
        let Some(index) = expected_items
            .iter()
            .enumerate()
            .find_map(|(index, expected)| {
                (!used[index] && equivalent_effect_item_boundary_types(actual, expected))
                    .then_some(index)
            })
        else {
            return false;
        };
        used[index] = true;
        true
    })
}

pub(crate) fn equivalent_effect_item_boundary_types(actual: &Type, expected: &Type) -> bool {
    match (actual, expected) {
        (
            Type::Con {
                path: actual_path,
                args: actual_args,
            },
            Type::Con {
                path: expected_path,
                args: expected_args,
            },
        ) if actual_path == expected_path && actual_args.len() == expected_args.len() => {
            actual_args
                .iter()
                .zip(expected_args)
                .all(|(actual, expected)| equivalent_boundary_types(actual, expected))
        }
        _ => equivalent_boundary_types(actual, expected),
    }
}

pub(crate) fn equivalent_effect_boundary_types(actual: &Type, expected: &Type) -> bool {
    if equivalent_boundary_types(actual, expected) {
        return true;
    }
    match (actual, expected) {
        (Type::EffectRow(items), expected) if items.len() == 1 => {
            equivalent_boundary_types(&items[0], expected)
        }
        (actual, Type::EffectRow(items)) if items.len() == 1 => {
            equivalent_boundary_types(actual, &items[0])
        }
        _ => false,
    }
}

pub(crate) fn record_field_type<'a>(
    fields: &'a [mono::TypeField],
    name: &str,
) -> Option<&'a mono::TypeField> {
    fields.iter().find(|field| field.name == name)
}
