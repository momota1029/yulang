use super::*;

pub(super) fn simplify_rewritten_expr(expr: Expr) -> Expr {
    match expr.kind {
        ExprKind::BindHere { expr: inner } if !matches!(inner.ty, RuntimeType::Thunk { .. }) => {
            *inner
        }
        kind => Expr { ty: expr.ty, kind },
    }
}

pub(super) fn apply_result_type(callee_ty: &RuntimeType) -> Option<RuntimeType> {
    match callee_ty {
        RuntimeType::Fun { ret, .. } => Some((**ret).clone()),
        _ => None,
    }
}

pub(super) fn variant_payload_expected(
    tag: &core_ir::Name,
    ty: &RuntimeType,
) -> Option<RuntimeType> {
    let RuntimeType::Core(ty) = ty else {
        return None;
    };
    match ty {
        core_ir::Type::Named { path, args }
            if type_path_last_is(path, "opt") && tag.0 == "just" =>
        {
            args.first().and_then(|arg| match arg {
                core_ir::TypeArg::Type(ty) => Some(RuntimeType::core(ty.clone())),
                core_ir::TypeArg::Bounds(bounds) => {
                    choose_hir_bounds_type(bounds, BoundsChoice::TirEvidence)
                }
            })
        }
        core_ir::Type::Variant(variant) => variant
            .cases
            .iter()
            .find(|case| case.name == *tag)
            .and_then(|case| match case.payloads.as_slice() {
                [payload] => Some(RuntimeType::core(payload.clone())),
                [] => None,
                payloads => Some(RuntimeType::core(core_ir::Type::Tuple(payloads.to_vec()))),
            }),
        _ => None,
    }
}

pub(super) fn specialize_constructor_apply(callee: &mut Expr, arg: &Expr) -> Option<RuntimeType> {
    let ExprKind::Var(path) = &callee.kind else {
        return None;
    };
    if path.segments.last().is_none_or(|name| name.0 != "just") {
        return None;
    }
    let mut type_path = path.clone();
    type_path.segments.pop();
    if !type_path_last_is(&type_path, "opt") {
        return None;
    }
    let ret = RuntimeType::core(core_ir::Type::Named {
        path: type_path,
        args: vec![core_ir::TypeArg::Type(core_value_type(&arg.ty))],
    });
    callee.ty = RuntimeType::fun(arg.ty.clone(), ret.clone());
    Some(ret)
}

pub(super) fn specialize_primitive_apply(callee: &mut Expr, arg: &Expr) -> Option<RuntimeType> {
    let ExprKind::PrimitiveOp(op) = callee.kind else {
        return None;
    };
    let ret = match op {
        core_ir::PrimitiveOp::ListSingleton => {
            RuntimeType::core(list_core_type(core_value_type(&arg.ty)))
        }
        core_ir::PrimitiveOp::ListMerge => {
            let item = list_item_type(&core_value_type(&arg.ty))?;
            let list = RuntimeType::core(list_core_type(item));
            RuntimeType::fun(list.clone(), list)
        }
        _ => return None,
    };
    callee.ty = RuntimeType::fun(arg.ty.clone(), ret.clone());
    Some(ret)
}

pub(super) fn list_core_type(item: core_ir::Type) -> core_ir::Type {
    core_ir::Type::Named {
        path: core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("list".to_string()),
                core_ir::Name("list".to_string()),
            ],
        },
        args: vec![core_ir::TypeArg::Type(item)],
    }
}

pub(super) fn function_param(ty: &RuntimeType) -> Option<&RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param),
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
        }) => {
            let value = RuntimeType::core(param.as_ref().clone());
            if should_thunk_effect(&project_runtime_effect(param_effect)) {
                Some(RuntimeType::thunk(
                    project_runtime_effect(param_effect),
                    value,
                ))
            } else {
                Some(value)
            }
        }
        _ => None,
    }
}

pub(super) fn refine_lambda_type_from_body(
    lambda_ty: &RuntimeType,
    body: &Expr,
) -> Option<RuntimeType> {
    let body_ty = &body.ty;
    if matches!(body_ty, RuntimeType::Core(core_ir::Type::Never)) {
        return None;
    }
    let RuntimeType::Fun { param, ret } = lambda_ty else {
        return None;
    };
    match ret.as_ref() {
        RuntimeType::Thunk { value, .. }
            if !matches!(body_ty, RuntimeType::Thunk { .. })
                && hir_type_compatible(value, body_ty)
                && lambda_body_consumes_ret_effect(body, ret) =>
        {
            Some(RuntimeType::fun(param.as_ref().clone(), body_ty.clone()))
        }
        expected if hir_type_has_vars(expected) && !hir_type_has_vars(body_ty) => {
            Some(RuntimeType::fun(param.as_ref().clone(), body_ty.clone()))
        }
        _ => None,
    }
}

fn lambda_body_consumes_ret_effect(body: &Expr, ret: &RuntimeType) -> bool {
    let RuntimeType::Thunk { effect, .. } = ret else {
        return true;
    };
    let effect = project_runtime_effect(effect);
    if effect_is_empty(&effect) {
        return true;
    }
    let expected_paths = effect_paths(&effect);
    if expected_paths.is_empty() {
        return false;
    }
    let Some(consumes) = pure_handler_consumes(body) else {
        return false;
    };
    expected_paths.iter().all(|expected| {
        consumes
            .iter()
            .any(|consume| effect_paths_match(consume, expected))
    })
}

fn pure_handler_consumes(expr: &Expr) -> Option<Vec<core_ir::Path>> {
    match &expr.kind {
        ExprKind::Handle { handler, .. }
            if handler.residual_after.as_ref().is_some_and(effect_is_empty) =>
        {
            Some(handler.consumes.clone())
        }
        ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => pure_handler_consumes(body),
        ExprKind::Block {
            tail: Some(tail), ..
        } => pure_handler_consumes(tail),
        ExprKind::Block { stmts, tail: None } => {
            let Some(Stmt::Expr(expr)) = stmts.last() else {
                return None;
            };
            pure_handler_consumes(expr)
        }
        _ => None,
    }
}

pub(super) fn force_arg_for_param(arg: Expr, param: &RuntimeType) -> Expr {
    let RuntimeType::Thunk { value, .. } = &arg.ty else {
        return arg;
    };
    if matches!(param, RuntimeType::Thunk { .. }) {
        return arg;
    }
    let value = value.as_ref().clone();
    if !hir_type_compatible(param, &value) {
        return arg;
    }
    Expr {
        ty: value,
        kind: ExprKind::BindHere {
            expr: Box::new(arg),
        },
    }
}

pub(super) fn bind_here_inner_expected(
    inner_ty: &RuntimeType,
    expected_value: Option<&RuntimeType>,
) -> Option<RuntimeType> {
    let expected_value = expected_value?;
    if matches!(expected_value, RuntimeType::Thunk { .. }) {
        return None;
    }
    let RuntimeType::Thunk { effect, .. } = inner_ty else {
        return None;
    };
    Some(RuntimeType::thunk(effect.clone(), expected_value.clone()))
}

pub(super) fn apply_result_expected(callee_ret: RuntimeType, fallback: RuntimeType) -> RuntimeType {
    if hir_type_is_hole(&fallback) {
        return callee_ret;
    }
    if let RuntimeType::Thunk { value, .. } = &fallback
        && !matches!(callee_ret, RuntimeType::Thunk { .. })
        && hir_type_compatible(value, &callee_ret)
    {
        return callee_ret;
    }
    if is_function_like(&callee_ret) && !is_function_like(&fallback) {
        return callee_ret;
    }
    if hir_type_has_vars(&callee_ret) && !hir_type_has_vars(&fallback) {
        return fallback;
    }
    callee_ret
}

pub(super) fn is_function_like(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Fun { .. } | RuntimeType::Core(core_ir::Type::Fun { .. })
    )
}

pub(super) fn rewrite_child_expected(
    evidence: Option<RuntimeType>,
    parent: Option<&RuntimeType>,
    fallback: &RuntimeType,
) -> RuntimeType {
    match (evidence, parent) {
        (Some(evidence), Some(parent))
            if matches!(parent, RuntimeType::Thunk { .. })
                && !matches!(evidence, RuntimeType::Thunk { .. })
                && matches!(fallback, RuntimeType::Thunk { .. }) =>
        {
            parent.clone()
        }
        (Some(evidence), Some(parent)) if hir_type_has_vars(&evidence) => parent.clone(),
        (Some(evidence), _) => evidence,
        (None, Some(parent)) => parent.clone(),
        (None, None) => fallback.clone(),
    }
}

pub(super) fn bounds_hir_type(bounds: &core_ir::TypeBounds) -> Option<RuntimeType> {
    choose_hir_bounds_type(bounds, BoundsChoice::MonomorphicExpected)
}

pub(super) fn infer_role_requirement_substitutions(
    requirements: &[core_ir::RoleRequirement],
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    for requirement in requirements {
        let inputs = requirement
            .args
            .iter()
            .filter_map(|arg| match arg {
                core_ir::RoleRequirementArg::Input(bounds) => {
                    substituted_requirement_bound(bounds, substitutions)
                }
                core_ir::RoleRequirementArg::Associated { .. } => None,
            })
            .collect::<Vec<_>>();

        for arg in &requirement.args {
            let core_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(resolved) = resolve_associated_requirement(requirement, name, &inputs) else {
                continue;
            };
            let Some(template) = substituted_requirement_bound(bounds, substitutions) else {
                continue;
            };
            infer_type_substitutions(&template, &resolved, params, substitutions);
        }
    }
}

pub(super) fn infer_direct_associated_requirement_substitutions(
    requirements: &[core_ir::RoleRequirement],
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    for requirement in requirements {
        let inputs = requirement
            .args
            .iter()
            .filter_map(|arg| match arg {
                core_ir::RoleRequirementArg::Input(bounds) => {
                    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
                }
                core_ir::RoleRequirementArg::Associated { .. } => None,
            })
            .collect::<Vec<_>>();
        for arg in &requirement.args {
            let core_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(var) = same_var_bounds(bounds) else {
                continue;
            };
            if !params.is_empty() && !params.contains(var) {
                continue;
            }
            let Some(resolved) = resolve_associated_requirement(requirement, name, &inputs) else {
                continue;
            };
            if !matches!(resolved, core_ir::Type::Any) {
                substitutions.entry(var.clone()).or_insert(resolved);
            }
        }
    }
}

fn same_var_bounds(bounds: &core_ir::TypeBounds) -> Option<&core_ir::TypeVar> {
    match (bounds.lower.as_deref(), bounds.upper.as_deref()) {
        (Some(core_ir::Type::Var(lower)), Some(core_ir::Type::Var(upper))) if lower == upper => {
            Some(lower)
        }
        _ => None,
    }
}

pub(super) fn substituted_requirement_bound(
    bounds: &core_ir::TypeBounds,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Option<core_ir::Type> {
    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
        .map(|ty| substitute_type(&ty, substitutions))
}

pub(super) fn resolve_associated_requirement(
    requirement: &core_ir::RoleRequirement,
    name: &core_ir::Name,
    inputs: &[core_ir::Type],
) -> Option<core_ir::Type> {
    let role = requirement.role.segments.last()?;
    match (role.0.as_str(), name.0.as_str(), inputs) {
        ("Fold", "item", [container]) => fold_item_type(container),
        ("Index", "value", [container, key]) => index_value_type(container, key),
        _ => None,
    }
}

pub(super) fn fold_item_type(ty: &core_ir::Type) -> Option<core_ir::Type> {
    list_item_type(ty).or_else(|| range_item_type(ty))
}

pub(super) fn list_item_type(ty: &core_ir::Type) -> Option<core_ir::Type> {
    match ty {
        core_ir::Type::Named { path, args } if type_path_last_is(path, "list") => {
            args.first().and_then(|arg| match arg {
                core_ir::TypeArg::Type(ty) => Some(normalize_mono_type(ty)),
                core_ir::TypeArg::Bounds(bounds) => {
                    choose_bounds_type(bounds, BoundsChoice::TirEvidence)
                        .map(|ty| normalize_mono_type(&ty))
                }
            })
        }
        _ => None,
    }
}

pub(super) fn range_item_type(ty: &core_ir::Type) -> Option<core_ir::Type> {
    match ty {
        core_ir::Type::Named { path, args }
            if type_path_last_is(path, "range") && args.is_empty() =>
        {
            Some(core_ir::Type::Named {
                path: core_ir::Path::from_name(core_ir::Name("int".to_string())),
                args: Vec::new(),
            })
        }
        _ => None,
    }
}

pub(super) fn index_value_type(
    container: &core_ir::Type,
    key: &core_ir::Type,
) -> Option<core_ir::Type> {
    match (container, key) {
        (
            core_ir::Type::Named { path, .. },
            core_ir::Type::Named {
                path: key_path,
                args,
            },
        ) if type_path_last_is(path, "str")
            && (type_path_last_is(key_path, "int") || type_path_last_is(key_path, "range"))
            && args.is_empty() =>
        {
            Some(container.clone())
        }
        (core_ir::Type::Named { path, .. }, core_ir::Type::Named { path: key_path, .. })
            if type_path_last_is(path, "list") && type_path_last_is(key_path, "int") =>
        {
            list_item_type(container)
        }
        (core_ir::Type::Named { path, .. }, core_ir::Type::Named { path: key_path, .. })
            if type_path_last_is(path, "list") && type_path_last_is(key_path, "range") =>
        {
            Some(container.clone())
        }
        _ => None,
    }
}

pub(super) fn applied_head(expr: &Expr) -> Option<(core_ir::Path, usize)> {
    match &expr.kind {
        ExprKind::Var(path) | ExprKind::EffectOp(path) => Some((path.clone(), 0)),
        ExprKind::Apply { callee, .. } => {
            let (path, count) = applied_head(callee)?;
            Some((path, count + 1))
        }
        _ => None,
    }
}

pub(super) fn applied_arg_types(expr: &Expr) -> Vec<RuntimeType> {
    let mut args = Vec::new();
    collect_applied_arg_types(expr, &mut args);
    args
}

fn collect_applied_arg_types(expr: &Expr, args: &mut Vec<RuntimeType>) {
    if let ExprKind::Apply { callee, arg, .. } = &expr.kind {
        collect_applied_arg_types(callee, args);
        args.push(arg.ty.clone());
    }
}

pub(super) fn unapplied_hir_type(ty: &RuntimeType, applied_args: usize) -> Option<&RuntimeType> {
    let mut ty = ty;
    for _ in 0..applied_args {
        let RuntimeType::Fun { ret, .. } = ty else {
            return None;
        };
        ty = ret;
    }
    Some(ty)
}

pub(super) fn unapplied_core_type(
    ty: &core_ir::Type,
    applied_args: usize,
) -> Option<&core_ir::Type> {
    let mut ty = ty;
    for _ in 0..applied_args {
        let core_ir::Type::Fun { ret, .. } = ty else {
            return None;
        };
        ty = ret;
    }
    Some(ty)
}

pub(super) fn effected_function_core_type(param: &RuntimeType, ret: &RuntimeType) -> core_ir::Type {
    let (param, param_effect) = effected_core_type(param);
    let (ret, ret_effect) = effected_core_type(ret);
    core_ir::Type::Fun {
        param: Box::new(param),
        param_effect: Box::new(param_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

pub(super) fn effected_core_type(ty: &RuntimeType) -> (core_ir::Type, core_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (core_value_type(value), effect.clone()),
        other => (core_value_type(other), core_ir::Type::Never),
    }
}

pub(super) fn core_value_type(ty: &RuntimeType) -> core_ir::Type {
    match ty {
        RuntimeType::Core(ty) => ty.clone(),
        RuntimeType::Fun { param, ret } => effected_function_core_type(param, ret),
        RuntimeType::Thunk { value, .. } => core_value_type(value),
    }
}

pub(super) fn infer_hir_type_substitutions(
    template: &RuntimeType,
    actual: &RuntimeType,
    params: &[core_ir::TypeVar],
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    infer_hir_type_substitutions_inner(template, actual, params, substitutions, false);
}

pub(super) fn infer_hir_call_type_substitutions(
    template: &RuntimeType,
    actual: &RuntimeType,
    params: &[core_ir::TypeVar],
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    infer_hir_type_substitutions_inner(template, actual, params, substitutions, true);
}

pub(super) fn infer_hir_type_substitutions_inner(
    template: &RuntimeType,
    actual: &RuntimeType,
    params: &[core_ir::TypeVar],
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
    prefer_non_never_effects: bool,
) {
    match (template, actual) {
        (RuntimeType::Fun { .. }, RuntimeType::Core(core_ir::Type::Fun { .. })) => {
            let actual = core_function_as_hir_type(actual);
            infer_hir_type_substitutions_inner(
                template,
                &actual,
                params,
                substitutions,
                prefer_non_never_effects,
            );
        }
        (RuntimeType::Core(core_ir::Type::Fun { .. }), RuntimeType::Fun { .. }) => {
            let template = core_function_as_hir_type(template);
            infer_hir_type_substitutions_inner(
                &template,
                actual,
                params,
                substitutions,
                prefer_non_never_effects,
            );
        }
        (RuntimeType::Core(template), RuntimeType::Core(actual)) => {
            infer_type_substitutions(
                template,
                actual,
                &params.iter().cloned().collect(),
                substitutions,
            );
        }
        (
            RuntimeType::Fun {
                param: template_param,
                ret: template_ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => {
            infer_hir_type_substitutions_inner(
                template_param,
                actual_param,
                params,
                substitutions,
                prefer_non_never_effects,
            );
            infer_hir_type_substitutions_inner(
                template_ret,
                actual_ret,
                params,
                substitutions,
                prefer_non_never_effects,
            );
        }
        (
            RuntimeType::Thunk {
                effect: template_effect,
                value: template_value,
            },
            RuntimeType::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => {
            let params = params.iter().cloned().collect();
            if prefer_non_never_effects {
                infer_effectful_type_substitutions(
                    template_effect,
                    actual_effect,
                    &params,
                    substitutions,
                );
            } else {
                infer_type_substitutions(template_effect, actual_effect, &params, substitutions);
            }
            infer_hir_type_substitutions_inner(
                template_value,
                actual_value,
                &params.iter().cloned().collect::<Vec<_>>(),
                substitutions,
                prefer_non_never_effects,
            );
        }
        (RuntimeType::Thunk { value, .. }, actual) => {
            infer_hir_type_substitutions_inner(
                value,
                actual,
                params,
                substitutions,
                prefer_non_never_effects,
            );
        }
        (template, RuntimeType::Thunk { value, .. }) => {
            infer_hir_type_substitutions_inner(
                template,
                value,
                params,
                substitutions,
                prefer_non_never_effects,
            );
        }
        _ => {}
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

pub(super) fn effected_core_as_hir_type(
    value: &core_ir::Type,
    effect: &core_ir::Type,
) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value.clone()));
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
