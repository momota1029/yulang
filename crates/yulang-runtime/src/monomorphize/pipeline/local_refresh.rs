use super::type_projection_metrics::{self, TypeProjectionFallbackReason};
use super::*;
use crate::HandleEffect;
use crate::types::{runtime_core_type, runtime_type_contains_unknown};

pub(super) fn refresh_local_expr_types(expr: Expr) -> Expr {
    let mut locals = HashMap::new();
    refresh_expr_local_types(expr, &mut locals)
}

pub(super) fn project_runtime_expr_types(expr: Expr) -> Expr {
    project_expr_runtime_types(expr)
}

fn refresh_expr_local_types(expr: Expr, locals: &mut HashMap<typed_ir::Path, RuntimeType>) -> Expr {
    let mut ty = expr.ty;
    let kind = match expr.kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let previous = hir_function_param_type(&ty).map(|param_ty| {
                let path = typed_ir::Path::from_name(param.clone());
                (path.clone(), locals.insert(path, param_ty))
            });
            let body = Box::new(refresh_expr_local_types(*body, locals));
            if let Some((path, previous)) = previous {
                restore_local(locals, path, previous);
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            }
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(refresh_expr_local_types(*callee, locals)),
            arg: Box::new(refresh_expr_local_types(*arg, locals)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(refresh_expr_local_types(*cond, locals)),
            then_branch: Box::new(refresh_expr_local_types(*then_branch, locals)),
            else_branch: Box::new(refresh_expr_local_types(*else_branch, locals)),
            evidence,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| refresh_expr_local_types(item, locals))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: refresh_expr_local_types(field.value, locals),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(refresh_expr_local_types(*expr, locals)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(refresh_expr_local_types(*expr, locals)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(refresh_expr_local_types(*value, locals))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(refresh_expr_local_types(*base, locals)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(refresh_expr_local_types(*scrutinee, locals)),
            arms: arms
                .into_iter()
                .map(|arm| {
                    let pattern = refresh_pattern_default_local_types(arm.pattern, locals);
                    let saved = locals.clone();
                    push_pattern_local_types(&pattern, locals);
                    let guard = arm
                        .guard
                        .map(|guard| refresh_expr_local_types(guard, locals));
                    let body = refresh_expr_local_types(arm.body, locals);
                    *locals = saved;
                    MatchArm {
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => {
            let saved = locals.clone();
            let stmts = stmts
                .into_iter()
                .map(|stmt| refresh_stmt_local_types(stmt, locals))
                .collect();
            let tail = tail.map(|tail| Box::new(refresh_expr_local_types(*tail, locals)));
            *locals = saved;
            ExprKind::Block { stmts, tail }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(refresh_expr_local_types(*body, locals)),
            arms: arms
                .into_iter()
                .map(|arm| {
                    let payload = refresh_pattern_default_local_types(arm.payload, locals);
                    let saved = locals.clone();
                    push_pattern_local_types(&payload, locals);
                    if let Some(resume) = &arm.resume {
                        locals.insert(
                            typed_ir::Path::from_name(resume.name.clone()),
                            resume.ty.clone(),
                        );
                    }
                    let guard = arm
                        .guard
                        .map(|guard| refresh_expr_local_types(guard, locals));
                    let body = refresh_expr_local_types(arm.body, locals);
                    *locals = saved;
                    HandleArm {
                        effect: arm.effect,
                        payload,
                        resume: arm.resume,
                        guard,
                        body,
                    }
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value,
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(refresh_expr_local_types(*body, locals)),
        },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(refresh_expr_local_types(*thunk, locals)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
        ExprKind::Var(path) => {
            if let Some(local_ty) = locals.get(&path) {
                ty = local_ty.clone();
            }
            ExprKind::Var(path)
        }
        ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit),
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
    };
    Expr { ty, kind }
}

fn project_expr_runtime_types(expr: Expr) -> Expr {
    let ty = substitute_hir_type(expr.ty, &BTreeMap::new());
    let kind = match expr.kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(project_expr_runtime_types(*body)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(project_expr_runtime_types(*callee)),
            arg: Box::new(project_expr_runtime_types(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(project_expr_runtime_types(*cond)),
            then_branch: Box::new(project_expr_runtime_types(*then_branch)),
            else_branch: Box::new(project_expr_runtime_types(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => {
            ExprKind::Tuple(items.into_iter().map(project_expr_runtime_types).collect())
        }
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: project_expr_runtime_types(field.value),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(project_expr_runtime_types(*expr)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(project_expr_runtime_types(*expr)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(project_expr_runtime_types(*value))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(project_expr_runtime_types(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(project_expr_runtime_types(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: project_pattern_runtime_types(arm.pattern),
                    guard: arm.guard.map(project_expr_runtime_types),
                    body: project_expr_runtime_types(arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts.into_iter().map(project_stmt_runtime_types).collect(),
            tail: tail.map(|tail| Box::new(project_expr_runtime_types(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let body = project_handle_body_runtime_types(*body, &handler);
            ExprKind::Handle {
                body: Box::new(body),
                arms: arms
                    .into_iter()
                    .map(|arm| HandleArm {
                        effect: arm.effect,
                        payload: project_pattern_runtime_types(arm.payload),
                        resume: arm.resume.map(project_resume_runtime_types),
                        guard: arm.guard.map(project_expr_runtime_types),
                        body: project_expr_runtime_types(arm.body),
                    })
                    .collect(),
                evidence,
                handler,
            }
        }
        ExprKind::BindHere { expr } => {
            let expr = project_expr_runtime_types(*expr);
            if !matches!(expr.ty, RuntimeType::Thunk { .. }) {
                return expr;
            }
            ExprKind::BindHere {
                expr: Box::new(expr),
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect: project_core_runtime_effect(effect),
            value: substitute_hir_type(value, &BTreeMap::new()),
            expr: Box::new(project_expr_runtime_types(*expr)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(project_expr_runtime_types(*body)),
        },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed: project_core_runtime_effect(allowed),
            active,
            thunk: Box::new(project_expr_runtime_types(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from: project_core_runtime_type(from),
            to: project_core_runtime_type(to),
            expr: Box::new(project_expr_runtime_types(*expr)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(project_expr_runtime_types(*expr)),
        },
        ExprKind::Var(path) => ExprKind::Var(path),
        ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit),
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
    };
    let ty = project_expr_runtime_type_from_kind(ty, &kind);
    Expr { ty, kind }
}

fn project_stmt_runtime_types(stmt: Stmt) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern: project_pattern_runtime_types(pattern),
            value: project_expr_runtime_types(value),
        },
        Stmt::Expr(expr) => Stmt::Expr(project_expr_runtime_types(expr)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: project_expr_runtime_types(body),
        },
    }
}

fn project_handle_body_runtime_types(body: Expr, handler: &HandleEffect) -> Expr {
    let body = project_expr_runtime_types(body);
    if handler.consumes.is_empty() || matches!(body.ty, RuntimeType::Thunk { .. }) {
        return body;
    }
    let effect = handler
        .residual_before
        .clone()
        .filter(|effect| !effect_is_empty(effect))
        .unwrap_or_else(|| typed_ir::Type::Row {
            items: handler
                .consumes
                .iter()
                .cloned()
                .map(|path| typed_ir::Type::Named {
                    path,
                    args: Vec::new(),
                })
                .collect(),
            tail: Box::new(typed_ir::Type::Never),
        });
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

fn project_resume_runtime_types(resume: ResumeBinding) -> ResumeBinding {
    ResumeBinding {
        name: resume.name,
        ty: substitute_hir_type(resume.ty, &BTreeMap::new()),
    }
}

fn project_expr_runtime_type_from_kind(fallback: RuntimeType, kind: &ExprKind) -> RuntimeType {
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
        ExprKind::Apply { callee, .. } => {
            match project_apply_runtime_type_from_callee(&callee.ty) {
                Some(ty) => choose_projected_apply_result(fallback, ty),
                None => {
                    type_projection_metrics::record(
                        TypeProjectionFallbackReason::ApplyCalleeNotFunction,
                    );
                    fallback
                }
            }
        }
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

fn project_apply_runtime_type_from_callee(callee: &RuntimeType) -> Option<RuntimeType> {
    match callee {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) => Some(local_runtime_type_from_core_value_and_effect(
            ret.as_ref().clone(),
            ret_effect.as_ref().clone(),
        )),
        RuntimeType::Thunk { value, .. } => project_apply_runtime_type_from_callee(value),
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
            choose_projected_lambda_return(*ret, body_ty.clone()),
        ),
        other => other,
    }
}

fn choose_projected_lambda_return(existing: RuntimeType, projected: RuntimeType) -> RuntimeType {
    if runtime_type_contains_unknown(&projected) && !runtime_type_contains_unknown(&existing) {
        type_projection_metrics::record(TypeProjectionFallbackReason::LambdaProjectedUnknown);
        existing
    } else if runtime_type_is_unit_value(&projected) && !runtime_type_is_unit_value(&existing) {
        type_projection_metrics::record(TypeProjectionFallbackReason::LambdaProjectedUnit);
        existing
    } else {
        projected
    }
}

fn runtime_type_is_unit_value(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Core(typed_ir::Type::Tuple(items)) if items.is_empty())
}

fn local_runtime_type_from_core_value_and_effect(
    value: typed_ir::Type,
    effect: typed_ir::Type,
) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value));
    if effect_is_empty(&effect) {
        value
    } else {
        RuntimeType::thunk(effect, value)
    }
}

fn project_pattern_runtime_types(pattern: Pattern) -> Pattern {
    match pattern {
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(project_pattern_runtime_types)
                .collect(),
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(project_pattern_runtime_types)
                .collect(),
            spread: spread.map(|spread| Box::new(project_pattern_runtime_types(*spread))),
            suffix: suffix
                .into_iter()
                .map(project_pattern_runtime_types)
                .collect(),
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordPatternField {
                    name: field.name,
                    pattern: project_pattern_runtime_types(field.pattern),
                    default: field.default.map(project_expr_runtime_types),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadPattern::Head(pattern) => {
                    RecordSpreadPattern::Head(Box::new(project_pattern_runtime_types(*pattern)))
                }
                RecordSpreadPattern::Tail(pattern) => {
                    RecordSpreadPattern::Tail(Box::new(project_pattern_runtime_types(*pattern)))
                }
            }),
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::Variant { tag, value, ty } => {
            let value = value.map(|value| Box::new(project_pattern_runtime_types(*value)));
            let ty = substitute_hir_type(ty, &BTreeMap::new());
            let ty = variant_pattern_runtime_type(&tag, value.as_deref(), ty);
            Pattern::Variant { tag, value, ty }
        }
        Pattern::Lit { lit, ty } => Pattern::Lit {
            lit,
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::Bind { name, ty } => Pattern::Bind {
            name,
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::Wildcard { ty } => Pattern::Wildcard {
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(project_pattern_runtime_types(*left)),
            right: Box::new(project_pattern_runtime_types(*right)),
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(project_pattern_runtime_types(*pattern)),
            name,
            ty: substitute_hir_type(ty, &BTreeMap::new()),
        },
    }
}

fn project_core_runtime_type(ty: typed_ir::Type) -> typed_ir::Type {
    project_runtime_type_with_vars(&ty, &BTreeSet::new())
}

fn project_core_runtime_effect(ty: typed_ir::Type) -> typed_ir::Type {
    project_runtime_effect(&ty)
}

fn refresh_stmt_local_types(stmt: Stmt, locals: &mut HashMap<typed_ir::Path, RuntimeType>) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => {
            let value = refresh_expr_local_types(value, locals);
            let pattern = refresh_pattern_default_local_types(pattern, locals);
            let pattern = refresh_pattern_value_local_types(pattern, &value.ty);
            push_pattern_local_types(&pattern, locals);
            Stmt::Let { pattern, value }
        }
        Stmt::Expr(expr) => Stmt::Expr(refresh_expr_local_types(expr, locals)),
        Stmt::Module { def, body } => {
            let body = refresh_expr_local_types(body, locals);
            locals.insert(def.clone(), body.ty.clone());
            Stmt::Module { def, body }
        }
    }
}

pub(super) fn refresh_pattern_value_local_types(
    pattern: Pattern,
    value_ty: &RuntimeType,
) -> Pattern {
    if !runtime_type_local_binding_usable(value_ty) {
        return pattern;
    }
    match pattern {
        Pattern::Bind { name, .. } => Pattern::Bind {
            name,
            ty: value_ty.clone(),
        },
        Pattern::Wildcard { .. } => Pattern::Wildcard {
            ty: value_ty.clone(),
        },
        Pattern::As { pattern, name, .. } => Pattern::As {
            pattern: Box::new(refresh_pattern_value_local_types(*pattern, value_ty)),
            name,
            ty: value_ty.clone(),
        },
        Pattern::Tuple { items, .. } => match value_ty {
            RuntimeType::Core(typed_ir::Type::Tuple(value_items))
                if items.len() == value_items.len() =>
            {
                Pattern::Tuple {
                    items: items
                        .into_iter()
                        .zip(value_items)
                        .map(|(item, value_item)| {
                            refresh_pattern_value_local_types(
                                item,
                                &RuntimeType::core(value_item.clone()),
                            )
                        })
                        .collect(),
                    ty: value_ty.clone(),
                }
            }
            _ => Pattern::Tuple {
                items,
                ty: value_ty.clone(),
            },
        },
        Pattern::Record { fields, spread, .. } => match value_ty {
            RuntimeType::Core(typed_ir::Type::Record(record)) => Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| {
                        let Some(value_field) =
                            record.fields.iter().find(|value| value.name == field.name)
                        else {
                            return field;
                        };
                        RecordPatternField {
                            name: field.name,
                            pattern: refresh_pattern_value_local_types(
                                field.pattern,
                                &RuntimeType::core(value_field.value.clone()),
                            ),
                            default: field.default,
                        }
                    })
                    .collect(),
                spread,
                ty: value_ty.clone(),
            },
            _ => Pattern::Record {
                fields,
                spread,
                ty: value_ty.clone(),
            },
        },
        Pattern::Variant { tag, value, .. } => {
            let payload_ty = variant_payload_runtime_type(value_ty, &tag);
            Pattern::Variant {
                tag,
                value: value.map(|inner| match payload_ty {
                    Some(ty) => Box::new(refresh_pattern_value_local_types(*inner, &ty)),
                    None => inner,
                }),
                ty: value_ty.clone(),
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            let item_ty = list_item_runtime_type(value_ty);
            Pattern::List {
                prefix: prefix
                    .into_iter()
                    .map(|item| match &item_ty {
                        Some(ty) => refresh_pattern_value_local_types(item, ty),
                        None => item,
                    })
                    .collect(),
                spread: spread
                    .map(|inner| Box::new(refresh_pattern_value_local_types(*inner, value_ty))),
                suffix: suffix
                    .into_iter()
                    .map(|item| match &item_ty {
                        Some(ty) => refresh_pattern_value_local_types(item, ty),
                        None => item,
                    })
                    .collect(),
                ty: value_ty.clone(),
            }
        }
        Pattern::Lit { lit, .. } => Pattern::Lit {
            lit,
            ty: value_ty.clone(),
        },
        Pattern::Or { left, right, .. } => Pattern::Or {
            left: Box::new(refresh_pattern_value_local_types(*left, value_ty)),
            right: Box::new(refresh_pattern_value_local_types(*right, value_ty)),
            ty: value_ty.clone(),
        },
    }
}

/// Extract the payload type that `tag` carries inside `value_ty`. Returns
/// `None` when `value_ty` is not a variant or no case matches `tag`, so
/// callers can fall back to leaving the inner pattern's type untouched.
fn variant_payload_runtime_type(
    value_ty: &RuntimeType,
    tag: &typed_ir::Name,
) -> Option<RuntimeType> {
    let RuntimeType::Core(typed_ir::Type::Variant(variant)) = value_ty else {
        return None;
    };
    let case = variant.cases.iter().find(|case| &case.name == tag)?;
    // Pattern::Variant carries `Option<Box<Pattern>>`, so we only look at
    // the first payload slot; multi-payload variants are not representable
    // here.
    case.payloads
        .first()
        .map(|ty| RuntimeType::core(ty.clone()))
}

/// Extract the element type from a `std::list::list<T>`-shaped runtime
/// type. Used when refreshing list pattern items.
fn list_item_runtime_type(value_ty: &RuntimeType) -> Option<RuntimeType> {
    let RuntimeType::Core(typed_ir::Type::Named { args, .. }) = value_ty else {
        return None;
    };
    let arg = args.first()?;
    match arg {
        typed_ir::TypeArg::Type(ty) => Some(RuntimeType::core(ty.clone())),
        typed_ir::TypeArg::Bounds(bounds) => bounds
            .lower
            .as_deref()
            .or(bounds.upper.as_deref())
            .map(|ty| RuntimeType::core(ty.clone())),
    }
}

fn runtime_type_local_binding_usable(ty: &RuntimeType) -> bool {
    !matches!(ty, RuntimeType::Core(typed_ir::Type::Any))
        && !hir_type_has_vars(ty)
        && !runtime_type_has_any(ty)
}

fn runtime_type_has_any(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_has_any(ty),
        RuntimeType::Fun { param, ret } => runtime_type_has_any(param) || runtime_type_has_any(ret),
        RuntimeType::Thunk { effect, value } => {
            core_type_has_any(effect) || runtime_type_has_any(value)
        }
    }
}

fn core_type_has_any(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Any => true,
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(core_type_arg_has_any),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_has_any(param)
                || core_type_has_any(param_effect)
                || core_type_has_any(ret_effect)
                || core_type_has_any(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items)
        | typed_ir::Type::Row { items, .. } => items.iter().any(core_type_has_any),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_has_any(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_has_any(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_has_any))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| core_type_has_any(tail))
        }
        typed_ir::Type::Recursive { body, .. } => core_type_has_any(body),
    }
}

fn core_type_arg_has_any(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_has_any(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(core_type_has_any)
                || bounds.upper.as_deref().is_some_and(core_type_has_any)
        }
    }
}

fn refresh_pattern_default_local_types(
    pattern: Pattern,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> Pattern {
    match pattern {
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| refresh_pattern_default_local_types(item, locals))
                .collect(),
            ty,
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(|item| refresh_pattern_default_local_types(item, locals))
                .collect(),
            spread: spread
                .map(|spread| Box::new(refresh_pattern_default_local_types(*spread, locals))),
            suffix: suffix
                .into_iter()
                .map(|item| refresh_pattern_default_local_types(item, locals))
                .collect(),
            ty,
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordPatternField {
                    name: field.name,
                    pattern: refresh_pattern_default_local_types(field.pattern, locals),
                    default: field
                        .default
                        .map(|default| refresh_expr_local_types(default, locals)),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadPattern::Head(pattern) => RecordSpreadPattern::Head(Box::new(
                    refresh_pattern_default_local_types(*pattern, locals),
                )),
                RecordSpreadPattern::Tail(pattern) => RecordSpreadPattern::Tail(Box::new(
                    refresh_pattern_default_local_types(*pattern, locals),
                )),
            }),
            ty,
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(refresh_pattern_default_local_types(*value, locals))),
            ty,
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(refresh_pattern_default_local_types(*left, locals)),
            right: Box::new(refresh_pattern_default_local_types(*right, locals)),
            ty,
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(refresh_pattern_default_local_types(*pattern, locals)),
            name,
            ty,
        },
        Pattern::Wildcard { ty } => Pattern::Wildcard { ty },
        Pattern::Bind { name, ty } => Pattern::Bind { name, ty },
        Pattern::Lit { lit, ty } => Pattern::Lit { lit, ty },
    }
}

fn push_pattern_local_types(pattern: &Pattern, locals: &mut HashMap<typed_ir::Path, RuntimeType>) {
    match pattern {
        Pattern::Bind { name, ty } => {
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone());
        }
        Pattern::As { pattern, name, ty } => {
            push_pattern_local_types(pattern, locals);
            locals.insert(typed_ir::Path::from_name(name.clone()), ty.clone());
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                push_pattern_local_types(item, locals);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                push_pattern_local_types(item, locals);
            }
            if let Some(spread) = spread {
                push_pattern_local_types(spread, locals);
            }
            for item in suffix {
                push_pattern_local_types(item, locals);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                push_pattern_local_types(&field.pattern, locals);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        push_pattern_local_types(pattern, locals);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                push_pattern_local_types(value, locals);
            }
        }
        Pattern::Or { left, right, .. } => {
            push_pattern_local_types(left, locals);
            push_pattern_local_types(right, locals);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn restore_local(
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    path: typed_ir::Path,
    previous: Option<RuntimeType>,
) {
    match previous {
        Some(ty) => {
            locals.insert(path, ty);
        }
        None => {
            locals.remove(&path);
        }
    }
}

fn hir_function_param_type(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some(effected_core_as_hir_type(param, param_effect)),
        _ => None,
    }
}

fn effected_core_as_hir_type(value: &typed_ir::Type, effect: &typed_ir::Type) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value.clone()));
    let effect = project_runtime_effect(effect);
    if should_thunk_effect(&effect) {
        RuntimeType::thunk(effect, value)
    } else {
        value
    }
}

fn variant_pattern_runtime_type(
    tag: &typed_ir::Name,
    value: Option<&Pattern>,
    fallback: RuntimeType,
) -> RuntimeType {
    if matches!(fallback, RuntimeType::Core(typed_ir::Type::Named { .. })) {
        return fallback;
    }
    RuntimeType::core(typed_ir::Type::Variant(typed_ir::VariantType {
        cases: vec![typed_ir::VariantCase {
            name: tag.clone(),
            payloads: value
                .iter()
                .map(|value| runtime_core_type(&pattern_type(value)))
                .collect(),
        }],
        tail: None,
    }))
}
