use super::*;

pub(super) fn core_type(ty: &RuntimeType) -> &core_ir::Type {
    match ty {
        RuntimeType::Core(ty) => ty,
        RuntimeType::Thunk { value, .. } => core_type(value),
        RuntimeType::Fun { .. } => &core_ir::Type::Any,
    }
}

pub(super) fn core_function_as_hir_type(ty: &RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        }) => RuntimeType::fun(
            effected_core_as_hir_type(param, param_effect),
            effected_core_as_hir_type(ret, ret_effect),
        ),
        other => other.clone(),
    }
}

pub(super) fn function_result_type(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        RuntimeType::Core(core_ir::Type::Fun {
            ret_effect, ret, ..
        }) => Some(effected_core_as_hir_type(ret, ret_effect)),
        _ => None,
    }
}

pub(super) fn function_param_type(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some(effected_core_as_hir_type(param, param_effect)),
        _ => None,
    }
}

pub(super) fn effected_core_as_hir_type(
    value: &core_ir::Type,
    effect: &core_ir::Type,
) -> RuntimeType {
    let value = RuntimeType::core(value.clone());
    let effect = project_runtime_effect(effect);
    if should_thunk_effect(&effect) {
        RuntimeType::thunk(effect, value)
    } else {
        value
    }
}

pub(super) fn hir_type_compatible(expected: &RuntimeType, actual: &RuntimeType) -> bool {
    match (expected, actual) {
        (RuntimeType::Core(expected), RuntimeType::Core(actual)) => {
            type_compatible(expected, actual)
        }
        (
            RuntimeType::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => {
            hir_type_compatible(expected_param, actual_param)
                && hir_type_compatible(expected_ret, actual_ret)
        }
        (
            RuntimeType::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => {
            type_compatible(expected_effect, actual_effect)
                && hir_type_compatible(expected_value, actual_value)
        }
        (RuntimeType::Thunk { value, .. }, actual) => hir_type_compatible(value, actual),
        _ => false,
    }
}

pub(super) fn bind_thunk_for_expected(expr: Expr, expected: &RuntimeType) -> Expr {
    let RuntimeType::Thunk { value, .. } = &expr.ty else {
        return expr;
    };
    if matches!(expected, RuntimeType::Thunk { .. }) || !hir_type_compatible(expected, value) {
        return expr;
    }
    Expr {
        ty: expected.clone(),
        kind: ExprKind::BindHere {
            expr: Box::new(expr),
        },
    }
}

pub(super) fn applied_head_path(expr: &Expr) -> Option<core_ir::Path> {
    match &expr.kind {
        ExprKind::Var(path) => Some(path.clone()),
        ExprKind::Apply { callee, .. } => applied_head_path(callee),
        ExprKind::BindHere { expr } => applied_head_path(expr),
        _ => None,
    }
}

pub(super) fn hir_type_produces_value(ty: &RuntimeType, expected_value: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Thunk { value, .. } => hir_type_compatible(expected_value, value),
        other => hir_type_compatible(expected_value, other),
    }
}

pub(super) fn refine_expected_expr_type(
    expected: &RuntimeType,
    actual: &RuntimeType,
) -> RuntimeType {
    if let RuntimeType::Thunk { value, .. } = expected
        && !matches!(actual, RuntimeType::Thunk { .. })
        && hir_type_compatible(value, actual)
    {
        return actual.clone();
    }
    expected.clone()
}

pub(super) fn refine_type_from_tail(current: RuntimeType, tail: &RuntimeType) -> RuntimeType {
    if hir_type_is_core_never(tail) {
        return current;
    }
    if !hir_type_has_vars(tail)
        && !hir_type_compatible(&current, tail)
        && !hir_type_compatible(tail, &current)
    {
        tail.clone()
    } else {
        current
    }
}

pub(super) fn refine_lambda_type_from_body(
    lambda_ty: &RuntimeType,
    body: &Expr,
) -> Option<RuntimeType> {
    let RuntimeType::Fun { param, ret } = lambda_ty else {
        return None;
    };
    if hir_type_is_core_never(&body.ty) {
        return None;
    }
    if !hir_type_has_vars(&body.ty)
        && !hir_type_compatible(ret, &body.ty)
        && !hir_type_compatible(&body.ty, ret)
    {
        Some(RuntimeType::fun(param.as_ref().clone(), body.ty.clone()))
    } else {
        None
    }
}

pub(super) fn flatten_nested_thunk_body(
    effect: core_ir::Type,
    value: RuntimeType,
    body: Expr,
) -> (core_ir::Type, RuntimeType, Expr) {
    let RuntimeType::Thunk {
        effect: inner_effect,
        value: inner_value,
    } = &body.ty
    else {
        return (effect, value, body);
    };
    let effect = merge_refined_effects(effect, inner_effect.clone());
    let value = inner_value.as_ref().clone();
    let body = Expr {
        ty: value.clone(),
        kind: ExprKind::BindHere {
            expr: Box::new(body),
        },
    };
    (effect, value, body)
}

fn merge_refined_effects(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    match (left, right) {
        (
            core_ir::Type::Row {
                mut items,
                tail: left_tail,
            },
            core_ir::Type::Row {
                items: right_items,
                tail: right_tail,
            },
        ) if matches!(
            (left_tail.as_ref(), right_tail.as_ref()),
            (core_ir::Type::Never, core_ir::Type::Never)
        ) =>
        {
            for item in right_items {
                if !items.contains(&item) {
                    items.push(item);
                }
            }
            effect_row(items, core_ir::Type::Never)
        }
        (left, right) => core_ir::Type::Union(vec![left, right]),
    }
}

pub(super) fn hir_type_is_core_never(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Core(core_ir::Type::Never))
}

pub(super) fn core_type_vars(ty: &core_ir::Type) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars
}

pub(super) fn all_type_vars(ty: &core_ir::Type) -> BTreeSet<core_ir::TypeVar> {
    core_type_vars(ty)
}

pub(super) fn occurs_in(var: &core_ir::TypeVar, ty: &core_ir::Type) -> bool {
    core_type_vars(ty).contains(var)
}

pub(super) fn choose_refined_substitution(
    existing: core_ir::Type,
    candidate: core_ir::Type,
) -> core_ir::Type {
    if existing == candidate {
        return existing;
    }
    if matches!(existing, core_ir::Type::Never) && !matches!(candidate, core_ir::Type::Never) {
        return candidate;
    }
    if matches!(candidate, core_ir::Type::Never) {
        return existing;
    }
    if type_compatible(&existing, &candidate) || type_compatible(&candidate, &existing) {
        choose_core_type(existing, candidate, TypeChoice::Substitution)
    } else {
        existing
    }
}

pub(super) fn pattern_type(pattern: &Pattern) -> Option<RuntimeType> {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => Some(ty.clone()),
    }
}

pub(super) fn tuple_item_type(ty: &RuntimeType, index: usize) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Core(core_ir::Type::Tuple(items)) => {
            items.get(index).cloned().map(RuntimeType::core)
        }
        _ => None,
    }
}

pub(super) fn record_field_type(ty: &RuntimeType, name: &core_ir::Name) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Core(core_ir::Type::Record(record)) => record
            .fields
            .iter()
            .find(|field| field.name == *name)
            .map(|field| RuntimeType::core(field.value.clone())),
        _ => None,
    }
}

pub(super) fn is_data_constructor_path(path: &core_ir::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|name| matches!(name.0.as_str(), "nil" | "just"))
}
