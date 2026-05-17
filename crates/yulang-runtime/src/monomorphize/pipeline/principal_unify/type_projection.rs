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
        ExprKind::If { .. } => {
            type_projection_metrics::record(TypeProjectionFallbackReason::IfBranchMismatch);
            fallback
        }
        ExprKind::Match { arms, .. } => match arms.first() {
            Some(arm) => arm.body.ty.clone(),
            None => {
                type_projection_metrics::record(TypeProjectionFallbackReason::MatchNoArms);
                fallback
            }
        },
        ExprKind::Block {
            tail: Some(tail), ..
        } => tail.ty.clone(),
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
        ExprKind::Thunk { effect, value, .. } => RuntimeType::thunk(effect.clone(), value.clone()),
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
