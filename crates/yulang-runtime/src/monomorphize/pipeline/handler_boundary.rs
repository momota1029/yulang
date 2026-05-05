use super::*;
use crate::types::{project_runtime_type_with_vars, runtime_core_type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerBindingInfo {
    pub(super) consumes: Vec<core_ir::Path>,
    pub(super) principal_input_effect: Option<core_ir::Type>,
    pub(super) principal_output_effect: Option<core_ir::Type>,
    pub(super) residual_before_known: bool,
    pub(super) residual_after_known: bool,
    pub(super) pure: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerCallBoundary {
    pub(super) consumes: Vec<core_ir::Path>,
    pub(super) input_effect: Option<core_ir::Type>,
    pub(super) output_effect: Option<core_ir::Type>,
    pub(super) consumes_input_effect: bool,
    pub(super) preserves_output_effect: bool,
    pub(super) pure: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerAdapterPlan {
    pub(super) consumes: Vec<core_ir::Path>,
    pub(super) residual_before: Option<core_ir::Type>,
    pub(super) residual_after: Option<core_ir::Type>,
    pub(super) return_wrapper_effect: Option<core_ir::Type>,
}

pub(super) fn handler_binding_info(binding: &Binding) -> Option<HandlerBindingInfo> {
    let mut info = expr_handler_info(&binding.body)?;
    if info.consumes.is_empty()
        && let Some(effect) = local_ref_run_effect_path(&binding.name)
    {
        info.consumes.push(effect);
    }
    if let Some((input_effect, output_effect)) = principal_handler_effects(&binding.scheme.body) {
        info.principal_input_effect = Some(input_effect);
        info.principal_output_effect = Some(output_effect);
    }
    Some(info)
}

pub(super) fn handler_call_boundary(
    info: &HandlerBindingInfo,
    args: &[&Expr],
    result_ty: &RuntimeType,
) -> HandlerCallBoundary {
    let input_effect = args.iter().find_map(|arg| runtime_thunk_effect(&arg.ty));
    let output_effect = runtime_thunk_effect(result_ty);
    let structural_input_consumes = info
        .principal_input_effect
        .as_ref()
        .is_some_and(|effect| effect_contains_any(effect, &info.consumes));
    let curried_handler_input_consumes =
        input_effect.is_none() && args.len() > 1 && !info.consumes.is_empty();
    HandlerCallBoundary {
        consumes: info.consumes.clone(),
        consumes_input_effect: input_effect
            .as_ref()
            .is_some_and(|effect| effect_contains_any(effect, &info.consumes))
            || structural_input_consumes
            || curried_handler_input_consumes,
        preserves_output_effect: output_effect
            .as_ref()
            .is_some_and(|effect| !effect_is_empty(effect)),
        input_effect,
        output_effect,
        pure: info.pure,
    }
}

pub(super) fn handler_adapter_plan(
    info: &HandlerBindingInfo,
    boundary: &HandlerCallBoundary,
) -> HandlerAdapterPlan {
    let mut residual_before = handler_residual_before(info, boundary);
    let mut residual_after = residual_before
        .as_ref()
        .map(|effect| remove_consumed_effects(effect, &info.consumes));
    let mut return_wrapper_effect =
        handler_return_wrapper_effect(info, boundary, residual_after.as_ref());
    if boundary.consumes_input_effect
        && boundary.preserves_output_effect
        && let Some(output_effect) = boundary
            .output_effect
            .as_ref()
            .filter(|effect| !effect_is_empty(effect))
    {
        residual_before = Some(effect_row_from_paths(info.consumes.clone()));
        residual_after = Some(core_ir::Type::Never);
        return_wrapper_effect = Some(output_effect.clone());
    }
    HandlerAdapterPlan {
        consumes: info.consumes.clone(),
        residual_before,
        residual_after,
        return_wrapper_effect,
    }
}

pub(super) fn substitute_handler_adapter_plan(
    plan: &HandlerAdapterPlan,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> HandlerAdapterPlan {
    HandlerAdapterPlan {
        consumes: plan.consumes.clone(),
        residual_before: plan
            .residual_before
            .as_ref()
            .map(|effect| normalize_effect(substitute_type(effect, substitutions))),
        residual_after: plan
            .residual_after
            .as_ref()
            .map(|effect| normalize_effect(substitute_type(effect, substitutions))),
        return_wrapper_effect: plan
            .return_wrapper_effect
            .as_ref()
            .map(|effect| normalize_effect(substitute_type(effect, substitutions))),
    }
}

pub(super) fn apply_handler_adapter_plan_to_binding(
    mut binding: Binding,
    plan: &HandlerAdapterPlan,
) -> Binding {
    let mut next_effect_id = next_effect_id_after_expr(&binding.body);
    binding.body = apply_handler_adapter_plan_to_expr(binding.body, plan, &mut next_effect_id);
    binding.scheme.body =
        project_runtime_type_with_vars(&runtime_core_type(&binding.body.ty), &BTreeSet::new());
    binding
}

fn runtime_thunk_effect(ty: &RuntimeType) -> Option<core_ir::Type> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(effect.clone()),
        RuntimeType::Core(_) | RuntimeType::Fun { .. } => None,
    }
}

fn local_ref_run_effect_path(target: &core_ir::Path) -> Option<core_ir::Path> {
    let [namespace, name] = target.segments.as_slice() else {
        return None;
    };
    (name.0 == "run" && namespace.0.starts_with('&')).then(|| core_ir::Path {
        segments: vec![namespace.clone()],
    })
}

fn handler_residual_before(
    info: &HandlerBindingInfo,
    boundary: &HandlerCallBoundary,
) -> Option<core_ir::Type> {
    let structural = info
        .principal_input_effect
        .as_ref()
        .filter(|effect| effect_contains_any(effect, &info.consumes))
        .cloned()
        .or_else(|| {
            (!info.consumes.is_empty()).then(|| effect_row_from_paths(info.consumes.clone()))
        });
    merge_effects(structural, boundary.input_effect.clone())
}

fn handler_return_wrapper_effect(
    info: &HandlerBindingInfo,
    boundary: &HandlerCallBoundary,
    residual_after: Option<&core_ir::Type>,
) -> Option<core_ir::Type> {
    if boundary.consumes_input_effect && boundary.output_effect.is_none() {
        let residual = residual_after
            .cloned()
            .filter(|effect| !effect_is_empty(effect));
        if residual.is_some() {
            return residual;
        }
    }
    if !boundary.pure || boundary.output_effect.is_some() {
        return None;
    }
    if std::env::var_os("YULANG_SUBST_SPECIALIZE_HANDLER_RETURN").is_none() {
        return None;
    }
    info.consumes
        .first()
        .cloned()
        .map(|path| core_ir::Type::Named {
            path,
            args: Vec::new(),
        })
}

fn merge_effects(
    left: Option<core_ir::Type>,
    right: Option<core_ir::Type>,
) -> Option<core_ir::Type> {
    match (left, right) {
        (Some(left), Some(right)) => Some(merge_effect_rows(left, right)),
        (Some(effect), None) | (None, Some(effect)) => Some(effect),
        (None, None) => None,
    }
}

fn merge_effect_rows(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    let (mut items, left_tail) = effect_row_parts(left);
    let (right_items, right_tail) = effect_row_parts(right);
    for item in right_items {
        push_unique_effect_item(&mut items, item);
    }
    let tail = merge_effect_tails(left_tail, right_tail);
    effect_row(items, tail)
}

fn effect_row_parts(effect: core_ir::Type) -> (Vec<core_ir::Type>, core_ir::Type) {
    match effect {
        core_ir::Type::Row { items, tail } => (items, *tail),
        other => (vec![other], core_ir::Type::Never),
    }
}

fn merge_effect_tails(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    core_ir::Type::Union(vec![left, right])
}

fn push_unique_effect_item(items: &mut Vec<core_ir::Type>, item: core_ir::Type) {
    if effect_is_empty(&item) || items.iter().any(|existing| existing == &item) {
        return;
    }
    items.push(item);
}

fn effect_row(items: Vec<core_ir::Type>, tail: core_ir::Type) -> core_ir::Type {
    let items = items
        .into_iter()
        .filter(|item| !effect_is_empty(item) && item != &tail)
        .collect::<Vec<_>>();
    if items.is_empty() {
        return tail;
    }
    core_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

fn effect_row_from_paths(paths: Vec<core_ir::Path>) -> core_ir::Type {
    effect_row(
        paths
            .into_iter()
            .map(|path| core_ir::Type::Named {
                path,
                args: Vec::new(),
            })
            .collect(),
        core_ir::Type::Never,
    )
}

fn remove_consumed_effects(effect: &core_ir::Type, consumed: &[core_ir::Path]) -> core_ir::Type {
    match effect {
        core_ir::Type::Named { path, .. }
            if consumed
                .iter()
                .any(|consumed| effect_paths_match(consumed, path)) =>
        {
            core_ir::Type::Never
        }
        core_ir::Type::Row { items, tail } => {
            let items = items
                .iter()
                .map(|item| remove_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect();
            let tail = remove_consumed_effects(tail, consumed);
            effect_row(items, tail)
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => effect_row(
            items
                .iter()
                .map(|item| remove_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect(),
            core_ir::Type::Never,
        ),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(remove_consumed_effects(body, consumed)),
        },
        other => other.clone(),
    }
}

fn normalize_effect(effect: core_ir::Type) -> core_ir::Type {
    match effect {
        core_ir::Type::Row { items, tail } => {
            let items = items
                .into_iter()
                .map(normalize_effect)
                .filter(|item| !effect_is_empty(item))
                .collect();
            effect_row(items, normalize_effect(*tail))
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => effect_row(
            items
                .into_iter()
                .map(normalize_effect)
                .filter(|item| !effect_is_empty(item))
                .collect(),
            core_ir::Type::Never,
        ),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var,
            body: Box::new(normalize_effect(*body)),
        },
        other => other,
    }
}

fn apply_handler_adapter_plan_to_expr(
    expr: Expr,
    plan: &HandlerAdapterPlan,
    next_effect_id: &mut usize,
) -> Expr {
    let Expr { ty, kind } = expr;
    match kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let body = rewrite_first_handle(*body, plan);
            let body = wrap_first_handler_returns(body, plan, next_effect_id);
            let ty = update_lambda_runtime_type(ty, &body.ty);
            Expr::typed(
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(body),
                },
                ty,
            )
        }
        other => {
            let expr = Expr::typed(other, ty);
            let expr = rewrite_first_handle(expr, plan);
            wrap_first_handler_returns(expr, plan, next_effect_id)
        }
    }
}

fn update_lambda_runtime_type(ty: RuntimeType, body_ty: &RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Fun { param, .. } => RuntimeType::fun(*param, body_ty.clone()),
        other => other,
    }
}

fn rewrite_first_handle(expr: Expr, plan: &HandlerAdapterPlan) -> Expr {
    let Expr { ty, kind } = expr;
    match kind {
        ExprKind::Handle {
            body,
            arms,
            evidence,
            mut handler,
        } => {
            handler.consumes = plan.consumes.clone();
            if plan.residual_before.is_some() {
                handler.residual_before = plan.residual_before.clone();
            }
            if plan.residual_after.is_some() {
                handler.residual_after = plan.residual_after.clone();
            }
            let body = ensure_consuming_handle_body_thunk(*body, plan);
            Expr::typed(
                ExprKind::Handle {
                    body: Box::new(body),
                    arms,
                    evidence,
                    handler,
                },
                ty,
            )
        }
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => Expr::typed(
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body: Box::new(rewrite_first_handle(*body, plan)),
            },
            ty,
        ),
        ExprKind::BindHere { expr } => Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(rewrite_first_handle(*expr, plan)),
            },
            ty,
        ),
        ExprKind::LocalPushId { id, body } => Expr::typed(
            ExprKind::LocalPushId {
                id,
                body: Box::new(rewrite_first_handle(*body, plan)),
            },
            ty,
        ),
        ExprKind::AddId { id, allowed, thunk } => Expr::typed(
            ExprKind::AddId {
                id,
                allowed,
                thunk: Box::new(rewrite_first_handle(*thunk, plan)),
            },
            ty,
        ),
        other => Expr::typed(other, ty),
    }
}

fn ensure_consuming_handle_body_thunk(body: Expr, plan: &HandlerAdapterPlan) -> Expr {
    if plan.consumes.is_empty() || matches!(body.ty, RuntimeType::Thunk { .. }) {
        return body;
    }
    let effect = plan
        .residual_before
        .clone()
        .filter(|effect| !effect_is_empty(effect))
        .unwrap_or_else(|| effect_row_from_paths(plan.consumes.clone()));
    let value = body.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(body),
        },
        RuntimeType::thunk(effect, value),
    )
}

fn wrap_first_handler_returns(
    body: Expr,
    plan: &HandlerAdapterPlan,
    next_effect_id: &mut usize,
) -> Expr {
    let Some(effect) = plan.return_wrapper_effect.clone() else {
        return body;
    };
    if effect_is_empty(&effect) {
        return body;
    }
    wrap_first_handle_returns_with_effect(body, effect, next_effect_id)
}

fn wrap_first_handle_returns_with_effect(
    expr: Expr,
    effect: core_ir::Type,
    next_effect_id: &mut usize,
) -> Expr {
    let Expr { ty, kind } = expr;
    match kind {
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let arms = arms
                .into_iter()
                .map(|arm| HandleArm {
                    body: wrap_value_in_thunk(arm.body, &effect),
                    ..arm
                })
                .collect::<Vec<_>>();
            let value = ty;
            let thunk_ty = RuntimeType::thunk(effect, value);
            Expr::typed(
                ExprKind::Handle {
                    body,
                    arms,
                    evidence,
                    handler,
                },
                thunk_ty,
            )
        }
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let body = wrap_first_handle_returns_with_effect(*body, effect, next_effect_id);
            let ty = update_lambda_runtime_type(ty, &body.ty);
            Expr::typed(
                ExprKind::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(body),
                },
                ty,
            )
        }
        ExprKind::BindHere { expr } => {
            let expr = wrap_first_handle_returns_with_effect(*expr, effect, next_effect_id);
            let ty = match &expr.ty {
                RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
                _ => ty,
            };
            Expr::typed(
                ExprKind::BindHere {
                    expr: Box::new(expr),
                },
                ty,
            )
        }
        ExprKind::LocalPushId { id, body } => {
            let body = wrap_first_handle_returns_with_effect(*body, effect, next_effect_id);
            let ty = body.ty.clone();
            Expr::typed(
                ExprKind::LocalPushId {
                    id,
                    body: Box::new(body),
                },
                ty,
            )
        }
        ExprKind::AddId { id, allowed, thunk } => {
            let thunk = wrap_first_handle_returns_with_effect(*thunk, effect, next_effect_id);
            let ty = thunk.ty.clone();
            Expr::typed(
                ExprKind::AddId {
                    id,
                    allowed,
                    thunk: Box::new(thunk),
                },
                ty,
            )
        }
        other => {
            let expr = Expr::typed(other, ty);
            wrap_handler_return(expr, &effect, next_effect_id)
        }
    }
}

fn wrap_value_in_thunk(body: Expr, effect: &core_ir::Type) -> Expr {
    if let RuntimeType::Thunk {
        effect: existing,
        value: _,
    } = &body.ty
        && existing == effect
    {
        return body;
    }
    let value = body.ty.clone();
    let thunk_ty = RuntimeType::thunk(effect.clone(), value.clone());
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value,
            expr: Box::new(body),
        },
        thunk_ty,
    )
}

fn wrap_handler_return(body: Expr, effect: &core_ir::Type, next_effect_id: &mut usize) -> Expr {
    if matches!(body.kind, ExprKind::LocalPushId { .. }) || !matches!(body.ty, RuntimeType::Core(_))
    {
        return body;
    }
    let value_ty = body.ty.clone();
    let thunk_ty = RuntimeType::thunk(effect.clone(), value_ty.clone());
    let thunk = Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value_ty.clone(),
            expr: Box::new(body),
        },
        thunk_ty.clone(),
    );
    let add_id = Expr::typed(
        ExprKind::AddId {
            id: crate::ir::EffectIdRef::Peek,
            allowed: effect.clone(),
            thunk: Box::new(thunk),
        },
        thunk_ty,
    );
    let forced = Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(add_id),
        },
        value_ty.clone(),
    );
    let id = crate::ir::EffectIdVar(*next_effect_id);
    *next_effect_id += 1;
    Expr::typed(
        ExprKind::LocalPushId {
            id,
            body: Box::new(forced),
        },
        value_ty,
    )
}

fn next_effect_id_after_expr(expr: &Expr) -> usize {
    max_effect_id_expr(expr).map_or(0, |id| id + 1)
}

fn max_effect_id_expr(expr: &Expr) -> Option<usize> {
    let mut max = None;
    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => update_max(&mut max, max_effect_id_expr(body)),
        ExprKind::Apply { callee, arg, .. } => {
            update_max(&mut max, max_effect_id_expr(callee));
            update_max(&mut max, max_effect_id_expr(arg));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            update_max(&mut max, max_effect_id_expr(cond));
            update_max(&mut max, max_effect_id_expr(then_branch));
            update_max(&mut max, max_effect_id_expr(else_branch));
        }
        ExprKind::Tuple(items) => {
            for item in items {
                update_max(&mut max, max_effect_id_expr(item));
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                update_max(&mut max, max_effect_id_expr(&field.value));
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        update_max(&mut max, max_effect_id_expr(expr));
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                update_max(&mut max, max_effect_id_expr(value));
            }
        }
        ExprKind::Select { base, .. } => update_max(&mut max, max_effect_id_expr(base)),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            update_max(&mut max, max_effect_id_expr(scrutinee));
            for arm in arms {
                update_max(&mut max, max_effect_id_pattern(&arm.pattern));
                if let Some(guard) = &arm.guard {
                    update_max(&mut max, max_effect_id_expr(guard));
                }
                update_max(&mut max, max_effect_id_expr(&arm.body));
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                update_max(&mut max, max_effect_id_stmt(stmt));
            }
            if let Some(tail) = tail {
                update_max(&mut max, max_effect_id_expr(tail));
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            update_max(&mut max, max_effect_id_expr(body));
            for arm in arms {
                update_max(&mut max, max_effect_id_pattern(&arm.payload));
                if let Some(guard) = &arm.guard {
                    update_max(&mut max, max_effect_id_expr(guard));
                }
                update_max(&mut max, max_effect_id_expr(&arm.body));
            }
        }
        ExprKind::AddId { id, thunk, .. } => {
            update_max(&mut max, max_effect_id_ref(*id));
            update_max(&mut max, max_effect_id_expr(thunk));
        }
        ExprKind::FindId { id } => update_max(&mut max, max_effect_id_ref(*id)),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId => {}
    }
    max
}

fn max_effect_id_stmt(stmt: &Stmt) -> Option<usize> {
    match stmt {
        Stmt::Let { pattern, value } => {
            max_effect_id_pattern(pattern).max(max_effect_id_expr(value))
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => max_effect_id_expr(expr),
    }
}

fn max_effect_id_pattern(pattern: &Pattern) -> Option<usize> {
    match pattern {
        Pattern::Tuple { items, .. } => items.iter().filter_map(max_effect_id_pattern).max(),
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => prefix
            .iter()
            .chain(suffix)
            .filter_map(max_effect_id_pattern)
            .chain(
                spread
                    .iter()
                    .filter_map(|pattern| max_effect_id_pattern(pattern)),
            )
            .max(),
        Pattern::Record { fields, spread, .. } => {
            let mut max = None;
            for field in fields {
                update_max(&mut max, max_effect_id_pattern(&field.pattern));
                if let Some(default) = &field.default {
                    update_max(&mut max, max_effect_id_expr(default));
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        update_max(&mut max, max_effect_id_pattern(pattern));
                    }
                }
            }
            max
        }
        Pattern::Variant { value, .. } => value.as_deref().and_then(max_effect_id_pattern),
        Pattern::Or { left, right, .. } => {
            max_effect_id_pattern(left).max(max_effect_id_pattern(right))
        }
        Pattern::As { pattern, .. } => max_effect_id_pattern(pattern),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => None,
    }
}

fn max_effect_id_ref(id: crate::ir::EffectIdRef) -> Option<usize> {
    match id {
        crate::ir::EffectIdRef::Var(id) => Some(id.0),
        crate::ir::EffectIdRef::Peek => None,
    }
}

fn update_max(max: &mut Option<usize>, candidate: Option<usize>) {
    if let Some(candidate) = candidate {
        *max = Some(max.map_or(candidate, |max| max.max(candidate)));
    }
}

fn effect_contains_any(effect: &core_ir::Type, targets: &[core_ir::Path]) -> bool {
    if matches!(effect, core_ir::Type::Any) && !targets.is_empty() {
        return true;
    }
    let paths = effect_paths(effect);
    paths.iter().any(|path| {
        targets
            .iter()
            .any(|target| effect_paths_match(path, target))
    })
}

fn expr_handler_info(expr: &Expr) -> Option<HandlerBindingInfo> {
    match &expr.kind {
        ExprKind::Handle {
            body,
            arms,
            handler,
            ..
        } => Some(HandlerBindingInfo {
            consumes: handler.consumes.clone(),
            principal_input_effect: None,
            principal_output_effect: None,
            residual_before_known: handler.residual_before.is_some(),
            residual_after_known: handler.residual_after.is_some(),
            pure: handler.residual_after.as_ref().is_some_and(effect_is_empty),
        })
        .or_else(|| expr_handler_info(body))
        .or_else(|| arms.iter().find_map(handle_arm_handler_info)),
        ExprKind::Apply { callee, arg, .. } => {
            expr_handler_info(callee).or_else(|| expr_handler_info(arg))
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_handler_info(body),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => expr_handler_info(cond)
            .or_else(|| expr_handler_info(then_branch))
            .or_else(|| expr_handler_info(else_branch)),
        ExprKind::Tuple(items) => items.iter().find_map(expr_handler_info),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| expr_handler_info(&field.value))
            .or_else(|| {
                spread.as_ref().and_then(|spread| match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        expr_handler_info(expr)
                    }
                })
            }),
        ExprKind::Variant { value, .. } => {
            value.as_ref().and_then(|value| expr_handler_info(value))
        }
        ExprKind::Select { base, .. } => expr_handler_info(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => expr_handler_info(scrutinee).or_else(|| arms.iter().find_map(match_arm_handler_info)),
        ExprKind::Block { stmts, tail } => stmts
            .iter()
            .find_map(stmt_handler_info)
            .or_else(|| tail.as_ref().and_then(|tail| expr_handler_info(tail))),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => None,
    }
}

fn principal_handler_effects(ty: &core_ir::Type) -> Option<(core_ir::Type, core_ir::Type)> {
    match ty {
        core_ir::Type::Fun {
            param_effect,
            ret_effect,
            ..
        } => Some((param_effect.as_ref().clone(), ret_effect.as_ref().clone())),
        core_ir::Type::Recursive { body, .. } => principal_handler_effects(body),
        core_ir::Type::Inter(items) | core_ir::Type::Union(items) => {
            items.iter().find_map(principal_handler_effects)
        }
        _ => None,
    }
}

fn handle_arm_handler_info(arm: &HandleArm) -> Option<HandlerBindingInfo> {
    arm.guard
        .as_ref()
        .and_then(expr_handler_info)
        .or_else(|| expr_handler_info(&arm.body))
}

fn match_arm_handler_info(arm: &MatchArm) -> Option<HandlerBindingInfo> {
    arm.guard
        .as_ref()
        .and_then(expr_handler_info)
        .or_else(|| expr_handler_info(&arm.body))
}

fn stmt_handler_info(stmt: &Stmt) -> Option<HandlerBindingInfo> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_handler_info(value)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handler_binding_detection_is_structural() {
        let mut binding = test_binding(fun(named("unit"), named("unit")));

        assert!(handler_binding_info(&binding).is_none());

        binding.body = Expr::typed(
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(named("unit")),
                        )),
                        arms: vec![HandleArm {
                            effect: path_segments(&["std", "effect"]),
                            payload: Pattern::Wildcard {
                                ty: RuntimeType::core(named("unit")),
                            },
                            resume: None,
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Unit),
                                RuntimeType::core(named("unit")),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: named("unit"),
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: Vec::new(),
                            residual_before: None,
                            residual_after: None,
                        },
                    },
                    RuntimeType::core(named("unit")),
                )),
            },
            RuntimeType::fun(
                RuntimeType::core(named("unit")),
                RuntimeType::core(named("unit")),
            ),
        );

        let info = handler_binding_info(&binding).expect("handler info");
        assert_eq!(info.consumes, Vec::<core_ir::Path>::new());
        assert_eq!(info.principal_input_effect, Some(core_ir::Type::Never));
        assert_eq!(info.principal_output_effect, Some(core_ir::Type::Never));
        assert!(!info.residual_before_known);
        assert!(!info.residual_after_known);
        assert!(!info.pure);
    }

    #[test]
    fn handler_call_boundary_reports_consumed_and_preserved_effects() {
        let consumes = path_segments(&["std", "flow", "sub"]);
        let outer = path_segments(&["std", "junction", "junction"]);
        let info = HandlerBindingInfo {
            consumes: vec![consumes.clone()],
            principal_input_effect: None,
            principal_output_effect: None,
            residual_before_known: true,
            residual_after_known: true,
            pure: true,
        };
        let arg = Expr::typed(
            ExprKind::Var(path("x")),
            RuntimeType::thunk(
                effect_row(vec![effect(consumes), effect(outer.clone())]),
                RuntimeType::core(named("int")),
            ),
        );
        let result_ty = RuntimeType::thunk(effect(outer), RuntimeType::core(named("int")));

        let boundary = handler_call_boundary(&info, &[&arg], &result_ty);

        assert!(boundary.consumes_input_effect);
        assert!(boundary.preserves_output_effect);
        assert!(boundary.pure);
    }

    #[test]
    fn handler_adapter_plan_combines_structural_and_call_site_effects() {
        let consumes = path_segments(&["std", "flow", "sub"]);
        let outer = path_segments(&["std", "junction", "junction"]);
        let info = HandlerBindingInfo {
            consumes: vec![consumes.clone()],
            principal_input_effect: Some(effect(consumes.clone())),
            principal_output_effect: Some(core_ir::Type::Never),
            residual_before_known: true,
            residual_after_known: true,
            pure: true,
        };
        let boundary = HandlerCallBoundary {
            consumes: vec![consumes.clone()],
            input_effect: Some(effect(outer.clone())),
            output_effect: None,
            consumes_input_effect: false,
            preserves_output_effect: false,
            pure: true,
        };

        let plan = handler_adapter_plan(&info, &boundary);

        assert_eq!(
            plan.residual_before,
            Some(effect_row(vec![
                effect(consumes.clone()),
                effect(outer.clone())
            ]))
        );
        assert_eq!(plan.residual_after, Some(effect_row(vec![effect(outer)])));
        assert_eq!(plan.return_wrapper_effect, None);
    }

    fn test_binding(scheme_body: core_ir::Type) -> Binding {
        Binding {
            name: path_segments(&["std", "prelude", "&impl#0", "method"]),
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: scheme_body.clone(),
            },
            body: Expr::typed(ExprKind::Var(path("body")), RuntimeType::core(scheme_body)),
        }
    }

    fn fun(param: core_ir::Type, ret: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn effect(path: core_ir::Path) -> core_ir::Type {
        core_ir::Type::Named {
            path,
            args: Vec::new(),
        }
    }

    fn effect_row(items: Vec<core_ir::Type>) -> core_ir::Type {
        core_ir::Type::Row {
            items,
            tail: Box::new(core_ir::Type::Never),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }

    fn path_segments(segments: &[&str]) -> core_ir::Path {
        core_ir::Path {
            segments: segments
                .iter()
                .map(|segment| core_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
