use super::*;

pub(super) fn handle_effect_for_arms(
    arms: &[HandleArm],
    residual_before: Option<core_ir::Type>,
    handled: core_ir::Type,
) -> HandleEffect {
    let arm_effects = arms
        .iter()
        .filter_map(|arm| {
            merge_effects(
                arm.guard.as_ref().and_then(expr_forced_effect),
                expr_forced_effect(&arm.body),
            )
        })
        .reduce(merge_effect_rows);
    let residual_before = merge_effects(residual_before, arm_effects);
    let consumes = effect_paths(&handled);
    let residual_before = residual_before.map(|effect| project_runtime_effect(&effect));
    let residual_after = residual_before
        .as_ref()
        .map(|effect| subtract_handled_effects(effect, &consumes));
    HandleEffect {
        consumes,
        residual_before,
        residual_after,
    }
}

pub(super) fn handler_consumes_from_body_type(ty: &RuntimeType) -> core_ir::Type {
    match ty {
        RuntimeType::Thunk { effect, .. } => project_runtime_effect(effect),
        _ => core_ir::Type::Never,
    }
}

pub(super) fn handler_body_residual(
    effect: &core_ir::Type,
    handled: &core_ir::Type,
) -> core_ir::Type {
    let total = project_runtime_effect(effect);
    if effect_is_unknown(&total) {
        return core_ir::Type::Never;
    }
    subtract_handled_effects(&total, &effect_paths(handled))
}

pub(super) fn effect_is_unknown(effect: &core_ir::Type) -> bool {
    matches!(effect, core_ir::Type::Any | core_ir::Type::Var(_))
}

pub(super) fn expr_forced_effect(expr: &Expr) -> Option<core_ir::Type> {
    match &expr.kind {
        ExprKind::BindHere { expr } => thunk_effect(&expr.ty),
        ExprKind::Lambda { .. }
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Var(_) => None,
        ExprKind::Apply { callee, arg, .. } => {
            let parts = function_parts(&callee.ty).ok();
            let apply_effect = parts.as_ref().and_then(|parts| thunk_effect(&parts.ret));
            let arg_effect = parts
                .as_ref()
                .and_then(|parts| {
                    (!matches!(parts.param, RuntimeType::Thunk { .. }))
                        .then(|| expr_forced_effect(arg))
                })
                .flatten();
            merge_effects(
                merge_effects(expr_forced_effect(callee), arg_effect),
                apply_effect,
            )
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => merge_effects(
            expr_forced_effect(cond),
            merge_effects(
                expr_forced_effect(then_branch),
                expr_forced_effect(else_branch),
            ),
        ),
        ExprKind::Tuple(items) => items
            .iter()
            .filter_map(expr_forced_effect)
            .reduce(merge_effect_rows),
        ExprKind::Record { fields, spread } => {
            let fields = fields
                .iter()
                .filter_map(|field| expr_forced_effect(&field.value))
                .reduce(merge_effect_rows);
            let spread = match spread {
                Some(RecordSpreadExpr::Head(expr)) | Some(RecordSpreadExpr::Tail(expr)) => {
                    expr_forced_effect(expr)
                }
                None => None,
            };
            merge_effects(fields, spread)
        }
        ExprKind::Variant { value, .. } => value.as_deref().and_then(expr_forced_effect),
        ExprKind::Select { base, .. } => expr_forced_effect(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let arms = arms
                .iter()
                .filter_map(|arm| {
                    merge_effects(
                        arm.guard.as_ref().and_then(expr_forced_effect),
                        expr_forced_effect(&arm.body),
                    )
                })
                .reduce(merge_effect_rows);
            merge_effects(expr_forced_effect(scrutinee), arms)
        }
        ExprKind::Block { stmts, tail } => {
            let stmts = stmts
                .iter()
                .filter_map(stmt_forced_effect)
                .reduce(merge_effect_rows);
            merge_effects(stmts, tail.as_deref().and_then(expr_forced_effect))
        }
        ExprKind::Handle { handler, .. } => handler.residual_after.clone(),
        ExprKind::Thunk { .. } => None,
        ExprKind::LocalPushId { body, .. } => expr_forced_effect(body),
        ExprKind::PeekId | ExprKind::FindId { .. } => None,
        ExprKind::AddId { thunk, .. } => expr_forced_effect(thunk),
        ExprKind::Coerce { expr, .. } | ExprKind::Pack { expr, .. } => expr_forced_effect(expr),
    }
}

pub(super) fn stmt_forced_effect(stmt: &Stmt) -> Option<core_ir::Type> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_forced_effect(value)
        }
    }
}

pub(super) fn merge_effects(
    left: Option<core_ir::Type>,
    right: Option<core_ir::Type>,
) -> Option<core_ir::Type> {
    match (left, right) {
        (Some(left), Some(right)) => Some(merge_effect_rows(left, right)),
        (Some(effect), None) | (None, Some(effect)) => Some(effect),
        (None, None) => None,
    }
}

pub(super) fn merge_effect_rows(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    merge_effect_values(left, right)
}

pub(super) fn merge_effect_values(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) {
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
            core_ir::Type::Row {
                items,
                tail: Box::new(core_ir::Type::Never),
            }
        }
        (left, right) if left == right => left,
        (left, right) => core_ir::Type::Union(vec![left, right]),
    }
}

pub(super) fn subtract_handled_effects(
    residual: &core_ir::Type,
    consumes: &[core_ir::Path],
) -> core_ir::Type {
    match residual {
        core_ir::Type::Row { items, tail } => core_ir::Type::Row {
            items: items
                .iter()
                .filter(|item| {
                    let Some(path) = effect_path(item) else {
                        return true;
                    };
                    !consumes
                        .iter()
                        .any(|consume| effect_paths_match(consume, &path))
                })
                .cloned()
                .collect(),
            tail: tail.clone(),
        },
        core_ir::Type::Named { path, .. }
            if consumes
                .iter()
                .any(|consume| effect_paths_match(consume, path)) =>
        {
            core_ir::Type::Never
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => effect_row_from_items(
            items
                .iter()
                .map(|item| subtract_handled_effects(item, consumes))
                .filter(|item| !effect_is_empty(item))
                .collect(),
        ),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(subtract_handled_effects(body, consumes)),
        },
        other => other.clone(),
    }
}
