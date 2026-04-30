use super::*;

pub(super) fn value_hir_type(ty: &RuntimeType) -> &RuntimeType {
    match ty {
        RuntimeType::Thunk { value, .. } => value,
        other => other,
    }
}

pub(super) fn value_core_type(ty: &RuntimeType) -> &core_ir::Type {
    core_type(value_hir_type(ty))
}

pub(super) fn force_value_expr(expr: Expr) -> (Expr, RuntimeType) {
    let value_ty = value_hir_type(&expr.ty).clone();
    let expr = bind_here_if_thunk(expr, value_ty.clone());
    (expr, value_ty)
}

pub(super) fn force_core_value_expr(expr: Expr) -> (Expr, core_ir::Type) {
    let (expr, ty) = force_value_expr(expr);
    let ty = core_type(&ty).clone();
    (expr, ty)
}

pub(super) fn prepare_expr_for_expected(
    expr: Expr,
    expected: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<Expr> {
    match expected {
        RuntimeType::Thunk { effect, value } => match &expr.ty {
            RuntimeType::Thunk { .. } => {
                require_apply_arg_compatible(expected, &expr.ty, source)?;
                Ok(expr)
            }
            _ => {
                require_same_hir_type(value, &expr.ty, source)?;
                let value = more_informative_hir_type(value, &expr.ty);
                let ty = RuntimeType::thunk(effect.clone(), value.clone());
                Ok(Expr::typed(
                    ExprKind::Thunk {
                        effect: effect.clone(),
                        value,
                        expr: Box::new(expr),
                    },
                    ty,
                ))
            }
        },
        RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))
            if matches!(expr.ty, RuntimeType::Thunk { .. }) =>
        {
            Ok(expr)
        }
        _ => {
            let (expr, actual) = force_value_expr(expr);
            require_same_hir_type(expected, &actual, source)?;
            Ok(expr)
        }
    }
}

pub(super) fn finalize_effectful_expr(
    expr: Expr,
    expected: Option<&RuntimeType>,
    source: TypeSource,
) -> RuntimeResult<Expr> {
    let expr = attach_forced_effect(expr);
    match expected {
        Some(expected) => prepare_expr_for_expected(expr, expected, source),
        None => Ok(expr),
    }
}

pub(super) fn finalize_handler_expr(
    expr: Expr,
    expected: Option<&RuntimeType>,
    source: TypeSource,
) -> RuntimeResult<Expr> {
    let expr = attach_forced_effect(expr);
    match (expected, &expr.ty) {
        (
            Some(RuntimeType::Thunk {
                value: expected_value,
                ..
            }),
            actual,
        ) if hir_type_compatible(expected_value, actual) => {
            require_same_hir_type(expected_value, actual, source)?;
            Ok(expr)
        }
        (Some(expected), _) => prepare_expr_for_expected(expr, expected, source),
        (None, _) => Ok(expr),
    }
}

pub(super) fn attach_forced_effect(expr: Expr) -> Expr {
    match expr_forced_effect(&expr) {
        Some(effect) => {
            let effect = project_runtime_effect(&effect);
            if should_thunk_effect(&effect) {
                attach_expr_effect(expr, effect)
            } else {
                expr
            }
        }
        _ => expr,
    }
}

pub(super) fn attach_expr_effect(expr: Expr, effect: core_ir::Type) -> Expr {
    match expr.ty.clone() {
        RuntimeType::Thunk {
            effect: existing,
            value,
        } => {
            let effect = project_runtime_effect(&merge_effect_rows(effect, existing));
            let ty = RuntimeType::thunk(effect.clone(), (*value).clone());
            let kind = match expr.kind {
                ExprKind::Thunk {
                    value, expr: inner, ..
                } => ExprKind::Thunk {
                    effect,
                    value,
                    expr: inner,
                },
                other => other,
            };
            Expr { ty, kind }
        }
        value => Expr::typed(
            ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(expr),
            },
            RuntimeType::thunk(effect, value),
        ),
    }
}

pub(super) fn effect_operation_effect(
    path: &core_ir::Path,
    arg_ty: &core_ir::Type,
) -> Option<core_ir::Type> {
    path.segments.last()?;
    let effect_path = core_ir::Path {
        segments: path
            .segments
            .iter()
            .take(path.segments.len().saturating_sub(1))
            .cloned()
            .collect(),
    };
    if effect_path.segments.is_empty() {
        return None;
    }
    let args = (!matches!(arg_ty, core_ir::Type::Any) && arg_ty != &unit_type())
        .then(|| vec![core_ir::TypeArg::Type(arg_ty.clone())])
        .unwrap_or_default();
    Some(core_ir::Type::Row {
        items: vec![core_ir::Type::Named {
            path: effect_path,
            args,
        }],
        tail: Box::new(core_ir::Type::Never),
    })
}

pub(super) fn add_id_to_created_thunks(expr: Expr) -> Expr {
    let ty = expr.ty;
    let kind = match expr.kind {
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let inner = add_id_to_created_thunks(*expr);
            let thunk = Expr::typed(
                ExprKind::Thunk {
                    effect: effect.clone(),
                    value,
                    expr: Box::new(inner),
                },
                ty,
            );
            return add_id_with_peek_if_needed(thunk, effect);
        }
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(add_id_to_created_thunks(*callee)),
            arg: Box::new(add_id_to_created_thunks(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(add_id_to_created_thunks(*cond)),
            then_branch: Box::new(add_id_to_created_thunks(*then_branch)),
            else_branch: Box::new(add_id_to_created_thunks(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => {
            ExprKind::Tuple(items.into_iter().map(add_id_to_created_thunks).collect())
        }
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: add_id_to_created_thunks(field.value),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(add_id_to_created_thunks(*expr)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(add_id_to_created_thunks(*expr)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(add_id_to_created_thunks(*value))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(add_id_to_created_thunks(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(add_id_to_created_thunks(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    guard: arm.guard.map(add_id_to_created_thunks),
                    body: add_id_to_created_thunks(arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| match stmt {
                    Stmt::Let { pattern, value } => Stmt::Let {
                        pattern,
                        value: add_id_to_created_thunks(value),
                    },
                    Stmt::Expr(expr) => Stmt::Expr(add_id_to_created_thunks(expr)),
                    Stmt::Module { def, body } => Stmt::Module {
                        def,
                        body: add_id_to_created_thunks(body),
                    },
                })
                .collect(),
            tail: tail.map(|tail| Box::new(add_id_to_created_thunks(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(add_id_to_created_thunks(*body)),
            arms: arms
                .into_iter()
                .map(|arm| HandleArm {
                    effect: arm.effect,
                    payload: arm.payload,
                    resume: arm.resume,
                    guard: arm.guard.map(add_id_to_created_thunks),
                    body: add_id_to_created_thunks(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(add_id_to_created_thunks(*expr)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(add_id_to_created_thunks(*body)),
        },
        ExprKind::FindId { id } => ExprKind::FindId { id },
        ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
            id,
            allowed,
            thunk: Box::new(add_id_to_created_thunks(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(add_id_to_created_thunks(*expr)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(add_id_to_created_thunks(*expr)),
        },
        kind @ (ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId) => kind,
    };
    Expr { ty, kind }
}

pub(super) fn add_id_with_peek_if_needed(thunk: Expr, allowed: core_ir::Type) -> Expr {
    let allowed = project_runtime_effect(&allowed);
    if !should_thunk_effect(&allowed) {
        return thunk;
    }
    Expr::typed(
        ExprKind::AddId {
            id: EffectIdRef::Peek,
            allowed,
            thunk: Box::new(thunk.clone()),
        },
        thunk.ty,
    )
}

pub(super) fn contains_peek_add_id(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::AddId {
            id: EffectIdRef::Peek,
            ..
        } => true,
        ExprKind::Lambda { .. } => false,
        ExprKind::Apply { callee, arg, .. } => {
            contains_peek_add_id(callee) || contains_peek_add_id(arg)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            contains_peek_add_id(cond)
                || contains_peek_add_id(then_branch)
                || contains_peek_add_id(else_branch)
        }
        ExprKind::Tuple(items) => items.iter().any(contains_peek_add_id),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| contains_peek_add_id(&field.value))
                || spread.as_ref().is_some_and(|spread| match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        contains_peek_add_id(expr)
                    }
                })
        }
        ExprKind::Variant { value, .. } => value.as_deref().is_some_and(contains_peek_add_id),
        ExprKind::Select { base, .. } => contains_peek_add_id(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            contains_peek_add_id(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(contains_peek_add_id)
                        || contains_peek_add_id(&arm.body)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                Stmt::Let { value, .. } | Stmt::Expr(value) => contains_peek_add_id(value),
                Stmt::Module { body, .. } => contains_peek_add_id(body),
            }) || tail.as_deref().is_some_and(contains_peek_add_id)
        }
        ExprKind::Handle { body, arms, .. } => {
            contains_peek_add_id(body)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(contains_peek_add_id)
                        || contains_peek_add_id(&arm.body)
                })
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => contains_peek_add_id(expr),
        ExprKind::LocalPushId { body, .. } => contains_peek_add_id(body),
        ExprKind::AddId { thunk, .. } => contains_peek_add_id(thunk),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}
