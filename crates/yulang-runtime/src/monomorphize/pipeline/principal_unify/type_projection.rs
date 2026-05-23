use super::super::type_projection_metrics::{self, TypeProjectionFallbackReason};
use super::*;

pub(super) fn principal_rewrite_type_from_kind(
    fallback: RuntimeType,
    kind: &ExprKind,
) -> RuntimeType {
    match kind {
        ExprKind::Tuple(items) => RuntimeType::core(typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| runtime_core_type(&item.ty))
                .collect(),
        )),
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } if then_branch.ty == else_branch.ty => then_branch.ty.clone(),
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } => {
            type_projection_metrics::record(TypeProjectionFallbackReason::IfBranchMismatch);
            choose_projected_if_result(fallback, &then_branch.ty, &else_branch.ty)
        }
        ExprKind::Match { arms, .. } => choose_projected_match_result(fallback, arms),
        ExprKind::Block { stmts, tail } => {
            choose_projected_block_result(fallback, stmts, tail.as_deref())
        }
        ExprKind::Apply { callee, .. } => match principal_rewrite_apply_type(&callee.ty) {
            Some(ty) => choose_projected_apply_result(fallback, ty),
            None => {
                type_projection_metrics::record(
                    TypeProjectionFallbackReason::ApplyCalleeNotFunction,
                );
                fallback
            }
        },
        ExprKind::Lambda { body, .. } => update_lambda_return_type(fallback, &body.ty),
        ExprKind::BindHere { expr } => match &expr.ty {
            RuntimeType::Thunk { value, .. } => {
                choose_projected_force_result(fallback, value.as_ref().clone())
            }
            _ => {
                type_projection_metrics::record(TypeProjectionFallbackReason::BindHereNotThunk);
                fallback
            }
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
            ..
        } => choose_projected_thunk_result(effect.clone(), value.clone(), &expr.ty),
        ExprKind::LocalPushId { body, .. } => body.ty.clone(),
        ExprKind::AddId { thunk, .. } => thunk.ty.clone(),
        ExprKind::Coerce { to, .. } => RuntimeType::core(to.clone()),
        _ => fallback,
    }
}

pub(super) fn principal_rewrite_apply_type(callee: &RuntimeType) -> Option<RuntimeType> {
    match callee {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) => Some(runtime_type_from_core_value_and_effect(
            ret.as_ref().clone(),
            ret_effect.as_ref().clone(),
        )),
        RuntimeType::Thunk { value, .. } => principal_rewrite_apply_type(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn choose_projected_apply_result(existing: RuntimeType, projected: RuntimeType) -> RuntimeType {
    if runtime_type_contains_unknown(&projected) && !runtime_type_contains_unknown(&existing) {
        type_projection_metrics::record(TypeProjectionFallbackReason::ApplyProjectedUnknown);
        existing
    } else {
        projected
    }
}

fn choose_projected_force_result(existing: RuntimeType, projected: RuntimeType) -> RuntimeType {
    if runtime_type_contains_unknown(&projected) && !runtime_type_contains_unknown(&existing) {
        type_projection_metrics::record(TypeProjectionFallbackReason::BindHereProjectedUnknown);
        existing
    } else {
        projected
    }
}

fn choose_projected_if_result(
    fallback: RuntimeType,
    then_ty: &RuntimeType,
    else_ty: &RuntimeType,
) -> RuntimeType {
    let (fallback_value, fallback_effect) = runtime_value_and_effect(&fallback);
    let (then_value, then_effect) = runtime_value_and_effect(then_ty);
    let (else_value, else_effect) = runtime_value_and_effect(else_ty);
    let value = if then_value == else_value
        && !core_type_contains_unknown(&then_value)
        && !core_type_has_vars(&then_value)
    {
        then_value
    } else {
        fallback_value
    };
    let effect = merge_effects(merge_effects(fallback_effect, then_effect), else_effect);
    runtime_type_from_core_value_and_effect(value, effect)
}

fn choose_projected_match_result(fallback: RuntimeType, arms: &[MatchArm]) -> RuntimeType {
    if arms.is_empty() {
        type_projection_metrics::record(TypeProjectionFallbackReason::MatchNoArms);
        return fallback;
    }
    let (fallback_value, fallback_effect) = runtime_value_and_effect(&fallback);
    let mut effect = fallback_effect;
    let mut projected_value = None::<typed_ir::Type>;
    let mut conflict = false;
    for arm in arms {
        let (value, arm_effect) = runtime_value_and_effect(&arm.body.ty);
        effect = merge_effects(effect, arm_effect);
        if !match_arm_value_type_usable(&value) {
            continue;
        }
        let value = match projected_match_arm_value(&fallback_value, value) {
            Some(value) => value,
            None => continue,
        };
        match &projected_value {
            Some(existing) => {
                if let Some(merged) = merge_projected_value_type_precision(existing, &value) {
                    projected_value = Some(merged);
                } else {
                    conflict = true;
                }
            }
            None => projected_value = Some(value),
        }
    }
    let value = if !conflict {
        projected_value.unwrap_or(fallback_value)
    } else {
        fallback_value
    };
    runtime_type_from_core_value_and_effect(value, effect)
}

fn projected_match_arm_value(
    fallback_value: &typed_ir::Type,
    arm_value: typed_ir::Type,
) -> Option<typed_ir::Type> {
    if let Some(merged) = merge_projected_value_type_precision(fallback_value, &arm_value) {
        return Some(merged);
    }
    if core_type_contains_unknown(fallback_value) || core_type_has_vars(fallback_value) {
        None
    } else {
        Some(arm_value)
    }
}

fn match_arm_value_type_usable(value: &typed_ir::Type) -> bool {
    !matches!(
        value,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Never
    ) && !core_type_contains_unknown(value)
        && !core_type_has_vars(value)
}

fn choose_projected_block_result(
    fallback: RuntimeType,
    stmts: &[Stmt],
    tail: Option<&Expr>,
) -> RuntimeType {
    let (fallback_value, fallback_effect) = runtime_value_and_effect(&fallback);
    let mut effect = fallback_effect;
    for stmt in stmts {
        effect = merge_effects(effect, projected_stmt_effect(stmt));
    }
    let value = if let Some(tail) = tail {
        let (tail_value, tail_effect) = runtime_value_and_effect(&tail.ty);
        effect = merge_effects(effect, tail_effect);
        if !core_type_contains_unknown(&tail_value) && !core_type_has_vars(&tail_value) {
            tail_value
        } else {
            fallback_value
        }
    } else {
        fallback_value
    };
    runtime_type_from_core_value_and_effect(value, effect)
}

fn projected_stmt_effect(stmt: &Stmt) -> typed_ir::Type {
    let expr = match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => value,
    };
    let (_value, effect) = runtime_value_and_effect(&expr.ty);
    effect
}

fn choose_projected_thunk_result(
    effect: typed_ir::Type,
    value: RuntimeType,
    body_ty: &RuntimeType,
) -> RuntimeType {
    let (body_value, body_effect) = runtime_value_and_effect(body_ty);
    let effect = merge_effects(effect, body_effect);
    let value = if runtime_type_contains_unknown(&value) || runtime_type_has_vars(&value) {
        RuntimeType::core(body_value)
    } else {
        value
    };
    RuntimeType::thunk(effect, value)
}

fn update_lambda_return_type(ty: RuntimeType, body_ty: &RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            *param,
            choose_rewritten_lambda_return(*ret, body_ty.clone()),
        ),
        other => other,
    }
}

fn choose_rewritten_lambda_return(existing: RuntimeType, rewritten: RuntimeType) -> RuntimeType {
    if runtime_type_contains_unknown(&rewritten) && !runtime_type_contains_unknown(&existing) {
        type_projection_metrics::record(TypeProjectionFallbackReason::LambdaProjectedUnknown);
        existing
    } else if runtime_type_is_unit_value(&rewritten) && !runtime_type_is_unit_value(&existing) {
        type_projection_metrics::record(TypeProjectionFallbackReason::LambdaProjectedUnit);
        existing
    } else {
        rewritten
    }
}

fn runtime_type_is_unit_value(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Core(typed_ir::Type::Tuple(items)) if items.is_empty())
}
