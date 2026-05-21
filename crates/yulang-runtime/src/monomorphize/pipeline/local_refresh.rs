use super::type_projection_metrics::{self, TypeProjectionFallbackReason};
use super::*;
use crate::HandleEffect;
use crate::types::{core_type_contains_unknown, runtime_core_type, runtime_type_contains_unknown};

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
        } => {
            let result_context = if core_type_contains_unknown(&evidence.result)
                && !runtime_type_contains_unknown(&ty)
            {
                runtime_core_type(&ty)
            } else {
                evidence.result
            };
            ExprKind::Match {
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
                        let body = refresh_join_body_result_type(body, &result_context);
                        *locals = saved;
                        MatchArm {
                            pattern,
                            guard,
                            body,
                        }
                    })
                    .collect(),
                evidence: JoinEvidence {
                    result: result_context,
                },
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = locals.clone();
            let stmts = stmts
                .into_iter()
                .map(|stmt| refresh_stmt_local_types(stmt, locals))
                .collect();
            let tail = tail.map(|tail| {
                let tail = refresh_expr_local_types(*tail, locals);
                Box::new(refresh_block_tail_result_type(tail, &ty))
            });
            *locals = saved;
            ExprKind::Block { stmts, tail }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let result_context = if core_type_contains_unknown(&evidence.result)
                && !runtime_type_contains_unknown(&ty)
            {
                runtime_core_type(&ty)
            } else {
                evidence.result
            };
            let body = refresh_expr_local_types(*body, locals);
            let default_payload_context = default_handle_payload_runtime_type(&body.ty);
            ExprKind::Handle {
                body: Box::new(body),
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        let is_default_arm = arm.effect == typed_ir::Path::default();
                        let payload = refresh_pattern_default_local_types(arm.payload, locals);
                        let payload = if is_default_arm {
                            match default_payload_context.clone().or_else(|| {
                                infer_default_handle_payload_runtime_type(
                                    &payload,
                                    &arm.body.ty,
                                    &result_context,
                                )
                            }) {
                                Some(payload_ty) => {
                                    refresh_pattern_value_local_types(payload, &payload_ty)
                                }
                                None => payload,
                            }
                        } else {
                            payload
                        };
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
                        let body = refresh_join_body_result_type(body, &result_context);
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
                evidence: JoinEvidence {
                    result: result_context,
                },
                handler,
            }
        }
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
    let mut ty = substitute_hir_type(expr.ty, &BTreeMap::new());
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
        } => {
            let callee = project_expr_runtime_types(*callee);
            let arg = project_expr_runtime_types(*arg);
            let arg = match project_apply_param_runtime_type_from_callee(&callee.ty)
                .filter(|ty| !runtime_type_contains_unknown(ty))
            {
                Some(param_ty) => refresh_unknown_expr_runtime_type(arg, &param_ty),
                None => arg,
            };
            let callee = refresh_applied_callee_runtime_type(callee, &arg.ty);
            if let Some(apply_ty) = project_apply_runtime_type_from_callee(&callee.ty)
                .filter(|ty| !runtime_type_contains_unknown(ty))
                && apply_ty != ty
            {
                ty = apply_ty;
            }
            ExprKind::Apply {
                callee: Box::new(refresh_applied_callee_result_runtime_type(callee, &ty)),
                arg: Box::new(arg),
                evidence,
                instantiation,
            }
        }
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
        } => {
            let result_context = if core_type_contains_unknown(&evidence.result)
                && !runtime_type_contains_unknown(&ty)
            {
                runtime_core_type(&ty)
            } else {
                evidence.result
            };
            ExprKind::Match {
                scrutinee: Box::new(project_expr_runtime_types(*scrutinee)),
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        let body = project_expr_runtime_types(arm.body);
                        MatchArm {
                            pattern: project_pattern_runtime_types(arm.pattern),
                            guard: arm.guard.map(project_expr_runtime_types),
                            body: refresh_join_body_result_type(body, &result_context),
                        }
                    })
                    .collect(),
                evidence: JoinEvidence {
                    result: result_context,
                },
            }
        }
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts.into_iter().map(project_stmt_runtime_types).collect(),
            tail: tail.map(|tail| {
                let tail = project_expr_runtime_types(*tail);
                Box::new(refresh_block_tail_result_type(tail, &ty))
            }),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let body = project_handle_body_runtime_types(*body, &handler);
            let handled_body_ty = body.ty.clone();
            let result_context = if core_type_contains_unknown(&evidence.result)
                && !runtime_type_contains_unknown(&ty)
            {
                runtime_core_type(&ty)
            } else {
                evidence.result
            };
            ExprKind::Handle {
                body: Box::new(body),
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        let guard = arm.guard.map(project_expr_runtime_types);
                        let body = project_expr_runtime_types(arm.body);
                        let body = refresh_join_body_result_type(body, &result_context);
                        HandleArm {
                            effect: arm.effect,
                            payload: project_pattern_runtime_types(arm.payload),
                            resume: arm.resume.map(|resume| {
                                project_resume_runtime_types_for_arm(
                                    resume,
                                    guard.as_ref(),
                                    &body,
                                    &handled_body_ty,
                                )
                            }),
                            guard,
                            body,
                        }
                    })
                    .collect(),
                evidence: JoinEvidence {
                    result: result_context,
                },
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
        ExprKind::Coerce { from, to, expr } => {
            let expr = project_expr_runtime_types(*expr);
            let from = project_core_runtime_type(from);
            let from =
                if core_type_contains_unknown(&from) && !runtime_type_contains_unknown(&expr.ty) {
                    runtime_core_type(&expr.ty)
                } else {
                    from
                };
            ExprKind::Coerce {
                from,
                to: project_core_runtime_type(to),
                expr: Box::new(expr),
            }
        }
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

fn project_resume_runtime_types_for_arm(
    resume: ResumeBinding,
    guard: Option<&Expr>,
    body: &Expr,
    handled_body_ty: &RuntimeType,
) -> ResumeBinding {
    let mut resume = project_resume_runtime_types(resume);
    let RuntimeType::Fun { param, ret } = &mut resume.ty else {
        return resume;
    };
    if !runtime_type_contains_unknown(param) && !runtime_type_contains_unknown(ret) {
        return resume;
    }
    let path = typed_ir::Path::from_name(resume.name.clone());
    let resume_is_used =
        guard.is_some_and(|guard| expr_refs_path(guard, &path)) || expr_refs_path(body, &path);
    if runtime_type_contains_unknown(param) {
        if let Some(arg_ty) = guard
            .and_then(|guard| resume_call_arg_type(guard, &path))
            .or_else(|| resume_call_arg_type(body, &path))
            .filter(|ty| !runtime_type_contains_unknown(ty))
        {
            *param = Box::new(arg_ty);
        } else if !resume_is_used {
            *param = Box::new(RuntimeType::core(typed_ir::Type::Never));
        }
    }
    if runtime_type_contains_unknown(ret) {
        if let Some(ret_ty) = guard
            .and_then(|guard| resume_call_result_type(guard, &path))
            .or_else(|| resume_call_result_type(body, &path))
            .filter(|ty| !runtime_type_contains_unknown(ty))
        {
            *ret = Box::new(ret_ty);
        } else if !runtime_type_contains_unknown(handled_body_ty) {
            *ret = Box::new(handled_body_ty.clone());
        } else if !resume_is_used {
            *ret = Box::new(RuntimeType::core(typed_ir::Type::Never));
        }
    }
    let ret_ty = ret.as_ref().clone();
    resume.ty = RuntimeType::fun(param.as_ref().clone(), ret_ty);
    resume
}

fn resume_call_arg_type(expr: &Expr, resume: &typed_ir::Path) -> Option<RuntimeType> {
    match &expr.kind {
        ExprKind::Apply { callee, arg, .. } if expr_is_path(callee, resume) => Some(arg.ty.clone()),
        ExprKind::Apply { callee, arg, .. } => {
            resume_call_arg_type(callee, resume).or_else(|| resume_call_arg_type(arg, resume))
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Pack { expr: body, .. } => resume_call_arg_type(body, resume),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => resume_call_arg_type(cond, resume)
            .or_else(|| resume_call_arg_type(then_branch, resume))
            .or_else(|| resume_call_arg_type(else_branch, resume)),
        ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| resume_call_arg_type(item, resume)),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| resume_call_arg_type(&field.value, resume))
            .or_else(|| match spread {
                Some(RecordSpreadExpr::Head(expr)) | Some(RecordSpreadExpr::Tail(expr)) => {
                    resume_call_arg_type(expr, resume)
                }
                None => None,
            }),
        ExprKind::Variant { value, .. } => value
            .as_deref()
            .and_then(|value| resume_call_arg_type(value, resume)),
        ExprKind::Select { base, .. } => resume_call_arg_type(base, resume),
        ExprKind::Match {
            scrutinee, arms, ..
        } => resume_call_arg_type(scrutinee, resume).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| resume_call_arg_type(guard, resume))
                    .or_else(|| resume_call_arg_type(&arm.body, resume))
            })
        }),
        ExprKind::Block { stmts, tail } => stmts
            .iter()
            .find_map(|stmt| resume_call_arg_type_from_stmt(stmt, resume))
            .or_else(|| {
                tail.as_deref()
                    .and_then(|tail| resume_call_arg_type(tail, resume))
            }),
        ExprKind::Handle { body, arms, .. } => resume_call_arg_type(body, resume).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| resume_call_arg_type(guard, resume))
                    .or_else(|| resume_call_arg_type(&arm.body, resume))
            })
        }),
        ExprKind::Thunk { expr, .. } => resume_call_arg_type(expr, resume),
        ExprKind::LocalPushId { body, .. } | ExprKind::AddId { thunk: body, .. } => {
            resume_call_arg_type(body, resume)
        }
        ExprKind::Coerce { expr, .. } => resume_call_arg_type(expr, resume),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => None,
    }
}

fn resume_call_arg_type_from_stmt(stmt: &Stmt, resume: &typed_ir::Path) -> Option<RuntimeType> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            resume_call_arg_type(value, resume)
        }
    }
}

fn resume_call_result_type(expr: &Expr, resume: &typed_ir::Path) -> Option<RuntimeType> {
    match &expr.kind {
        ExprKind::Apply { callee, arg, .. } if expr_is_path(callee, resume) => {
            Some(expr.ty.clone())
        }
        ExprKind::Apply { callee, arg, .. } => {
            resume_call_result_type(callee, resume).or_else(|| resume_call_result_type(arg, resume))
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Pack { expr: body, .. } => resume_call_result_type(body, resume),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => resume_call_result_type(cond, resume)
            .or_else(|| resume_call_result_type(then_branch, resume))
            .or_else(|| resume_call_result_type(else_branch, resume)),
        ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| resume_call_result_type(item, resume)),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| resume_call_result_type(&field.value, resume))
            .or_else(|| match spread {
                Some(RecordSpreadExpr::Head(expr)) | Some(RecordSpreadExpr::Tail(expr)) => {
                    resume_call_result_type(expr, resume)
                }
                None => None,
            }),
        ExprKind::Variant { value, .. } => value
            .as_deref()
            .and_then(|value| resume_call_result_type(value, resume)),
        ExprKind::Select { base, .. } => resume_call_result_type(base, resume),
        ExprKind::Match {
            scrutinee, arms, ..
        } => resume_call_result_type(scrutinee, resume).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| resume_call_result_type(guard, resume))
                    .or_else(|| resume_call_result_type(&arm.body, resume))
            })
        }),
        ExprKind::Block { stmts, tail } => stmts
            .iter()
            .find_map(|stmt| resume_call_result_type_from_stmt(stmt, resume))
            .or_else(|| {
                tail.as_deref()
                    .and_then(|tail| resume_call_result_type(tail, resume))
            }),
        ExprKind::Handle { body, arms, .. } => {
            resume_call_result_type(body, resume).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| resume_call_result_type(guard, resume))
                        .or_else(|| resume_call_result_type(&arm.body, resume))
                })
            })
        }
        ExprKind::Thunk { expr, .. } => resume_call_result_type(expr, resume),
        ExprKind::LocalPushId { body, .. } | ExprKind::AddId { thunk: body, .. } => {
            resume_call_result_type(body, resume)
        }
        ExprKind::Coerce { expr, .. } => resume_call_result_type(expr, resume),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => None,
    }
}

fn resume_call_result_type_from_stmt(stmt: &Stmt, resume: &typed_ir::Path) -> Option<RuntimeType> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            resume_call_result_type(value, resume)
        }
    }
}

fn expr_refs_path(expr: &Expr, path: &typed_ir::Path) -> bool {
    expr_is_path(expr, path)
        || match &expr.kind {
            ExprKind::Lambda { body, .. }
            | ExprKind::BindHere { expr: body }
            | ExprKind::Pack { expr: body, .. }
            | ExprKind::Thunk { expr: body, .. }
            | ExprKind::LocalPushId { body, .. }
            | ExprKind::AddId { thunk: body, .. }
            | ExprKind::Coerce { expr: body, .. } => expr_refs_path(body, path),
            ExprKind::Apply { callee, arg, .. } => {
                expr_refs_path(callee, path) || expr_refs_path(arg, path)
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                expr_refs_path(cond, path)
                    || expr_refs_path(then_branch, path)
                    || expr_refs_path(else_branch, path)
            }
            ExprKind::Tuple(items) => items.iter().any(|item| expr_refs_path(item, path)),
            ExprKind::Record { fields, spread } => {
                fields
                    .iter()
                    .any(|field| expr_refs_path(&field.value, path))
                    || match spread {
                        Some(RecordSpreadExpr::Head(expr)) | Some(RecordSpreadExpr::Tail(expr)) => {
                            expr_refs_path(expr, path)
                        }
                        None => false,
                    }
            }
            ExprKind::Variant { value, .. } => value
                .as_deref()
                .is_some_and(|value| expr_refs_path(value, path)),
            ExprKind::Select { base, .. } => expr_refs_path(base, path),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                expr_refs_path(scrutinee, path)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| expr_refs_path(guard, path))
                            || expr_refs_path(&arm.body, path)
                    })
            }
            ExprKind::Block { stmts, tail } => {
                stmts.iter().any(|stmt| stmt_refs_path(stmt, path))
                    || tail
                        .as_deref()
                        .is_some_and(|tail| expr_refs_path(tail, path))
            }
            ExprKind::Handle { body, arms, .. } => {
                expr_refs_path(body, path)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .is_some_and(|guard| expr_refs_path(guard, path))
                            || expr_refs_path(&arm.body, path)
                    })
            }
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => false,
        }
}

fn stmt_refs_path(stmt: &Stmt, path: &typed_ir::Path) -> bool {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_refs_path(value, path)
        }
    }
}

fn expr_is_path(expr: &Expr, path: &typed_ir::Path) -> bool {
    matches!(&expr.kind, ExprKind::Var(candidate) if candidate == path)
}

fn expr_local_var_runtime_type(expr: &Expr, path: &typed_ir::Path) -> Option<RuntimeType> {
    if expr_is_path(expr, path) && !runtime_type_contains_unknown(&expr.ty) {
        return Some(expr.ty.clone());
    }
    match &expr.kind {
        ExprKind::Lambda { param, body, .. } => {
            if typed_ir::Path::from_name(param.clone()) == *path {
                None
            } else {
                expr_local_var_runtime_type(body, path)
            }
        }
        ExprKind::Apply { callee, arg, .. } => expr_local_var_runtime_type(callee, path)
            .or_else(|| expr_local_var_runtime_type(arg, path)),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => expr_local_var_runtime_type(cond, path)
            .or_else(|| expr_local_var_runtime_type(then_branch, path))
            .or_else(|| expr_local_var_runtime_type(else_branch, path)),
        ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| expr_local_var_runtime_type(item, path)),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| expr_local_var_runtime_type(&field.value, path))
            .or_else(|| match spread {
                Some(RecordSpreadExpr::Head(expr)) | Some(RecordSpreadExpr::Tail(expr)) => {
                    expr_local_var_runtime_type(expr, path)
                }
                None => None,
            }),
        ExprKind::Variant { value, .. } => value
            .as_deref()
            .and_then(|value| expr_local_var_runtime_type(value, path)),
        ExprKind::Select { base, .. } => expr_local_var_runtime_type(base, path),
        ExprKind::Match {
            scrutinee, arms, ..
        } => expr_local_var_runtime_type(scrutinee, path).or_else(|| {
            arms.iter().find_map(|arm| {
                if pattern_binds_path(&arm.pattern, path) {
                    None
                } else {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| expr_local_var_runtime_type(guard, path))
                        .or_else(|| expr_local_var_runtime_type(&arm.body, path))
                }
            })
        }),
        ExprKind::Block { stmts, tail } => {
            let mut shadowed = false;
            for stmt in stmts {
                if let Some(ty) = stmt_local_var_runtime_type(stmt, path) {
                    return Some(ty);
                }
                if stmt_binds_path(stmt, path) {
                    shadowed = true;
                    break;
                }
            }
            if shadowed {
                None
            } else {
                tail.as_deref()
                    .and_then(|tail| expr_local_var_runtime_type(tail, path))
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            expr_local_var_runtime_type(body, path).or_else(|| {
                arms.iter().find_map(|arm| {
                    let resume_shadows = arm.resume.as_ref().is_some_and(|resume| {
                        typed_ir::Path::from_name(resume.name.clone()) == *path
                    });
                    if pattern_binds_path(&arm.payload, path) || resume_shadows {
                        None
                    } else {
                        arm.guard
                            .as_ref()
                            .and_then(|guard| expr_local_var_runtime_type(guard, path))
                            .or_else(|| expr_local_var_runtime_type(&arm.body, path))
                    }
                })
            })
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Pack { expr, .. }
        | ExprKind::Coerce { expr, .. } => expr_local_var_runtime_type(expr, path),
        ExprKind::LocalPushId { body, .. } | ExprKind::AddId { thunk: body, .. } => {
            expr_local_var_runtime_type(body, path)
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => None,
    }
}

fn stmt_local_var_runtime_type(stmt: &Stmt, path: &typed_ir::Path) -> Option<RuntimeType> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_local_var_runtime_type(value, path)
        }
    }
}

fn stmt_binds_path(stmt: &Stmt, path: &typed_ir::Path) -> bool {
    match stmt {
        Stmt::Let { pattern, .. } => pattern_binds_path(pattern, path),
        Stmt::Module { def, .. } => def == path,
        Stmt::Expr(_) => false,
    }
}

fn pattern_binds_path(pattern: &Pattern, path: &typed_ir::Path) -> bool {
    match pattern {
        Pattern::Bind { name, .. } => typed_ir::Path::from_name(name.clone()) == *path,
        Pattern::As { pattern, name, .. } => {
            typed_ir::Path::from_name(name.clone()) == *path || pattern_binds_path(pattern, path)
        }
        Pattern::Tuple { items, .. } => items.iter().any(|item| pattern_binds_path(item, path)),
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            prefix.iter().any(|item| pattern_binds_path(item, path))
                || spread
                    .as_deref()
                    .is_some_and(|item| pattern_binds_path(item, path))
                || suffix.iter().any(|item| pattern_binds_path(item, path))
        }
        Pattern::Record { fields, spread, .. } => {
            fields
                .iter()
                .any(|field| pattern_binds_path(&field.pattern, path))
                || spread.as_ref().is_some_and(|spread| match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        pattern_binds_path(pattern, path)
                    }
                })
        }
        Pattern::Variant { value, .. } => value
            .as_deref()
            .is_some_and(|value| pattern_binds_path(value, path)),
        Pattern::Or { left, right, .. } => {
            pattern_binds_path(left, path) || pattern_binds_path(right, path)
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => false,
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
        ExprKind::Lambda { param, body, .. } => update_lambda_runtime_type(fallback, param, body),
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
        ExprKind::Variant { tag, value } => {
            variant_expr_runtime_type(tag, value.as_deref(), fallback)
        }
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

fn project_apply_param_runtime_type_from_callee(callee: &RuntimeType) -> Option<RuntimeType> {
    match callee {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some(local_runtime_type_from_core_value_and_effect(
            param.as_ref().clone(),
            param_effect.as_ref().clone(),
        )),
        RuntimeType::Thunk { value, .. } => project_apply_param_runtime_type_from_callee(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn refresh_unknown_expr_runtime_type(mut expr: Expr, expected: &RuntimeType) -> Expr {
    if !matches!(expr.kind, ExprKind::Thunk { .. }) && runtime_type_contains_unknown(&expr.ty) {
        expr.ty = expected.clone();
    }
    expr
}

fn refresh_applied_callee_runtime_type(mut callee: Expr, arg_ty: &RuntimeType) -> Expr {
    if runtime_type_contains_unknown(arg_ty) {
        return callee;
    }
    match &mut callee.ty {
        RuntimeType::Fun { param, .. } if runtime_type_contains_unknown(param) => {
            *param = Box::new(arg_ty.clone());
        }
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) if core_type_contains_unknown(param) || core_type_contains_unknown(param_effect) => {
            let (arg_value, arg_effect) = runtime_value_and_effect_type(arg_ty);
            if !core_type_contains_open_runtime_slot(&arg_value)
                && !core_type_contains_open_runtime_slot(&arg_effect)
            {
                *param = Box::new(arg_value);
                *param_effect = Box::new(arg_effect);
            }
        }
        _ => {}
    }
    callee
}

fn refresh_applied_callee_result_runtime_type(mut callee: Expr, result_ty: &RuntimeType) -> Expr {
    if runtime_type_contains_unknown(result_ty) {
        return callee;
    }
    match &mut callee.ty {
        RuntimeType::Fun { ret, .. } if runtime_type_contains_unknown(ret) => {
            *ret = Box::new(result_ty.clone());
        }
        RuntimeType::Core(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) if core_type_contains_unknown(ret) || core_type_contains_unknown(ret_effect) => {
            let (result_value, result_effect) = runtime_value_and_effect_type(result_ty);
            if !core_type_contains_open_runtime_slot(&result_value)
                && !core_type_contains_open_runtime_slot(&result_effect)
            {
                *ret = Box::new(result_value);
                *ret_effect = Box::new(result_effect);
            }
        }
        _ => {}
    }
    callee
}

fn runtime_value_and_effect_type(ty: &RuntimeType) -> (typed_ir::Type, typed_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_core_type(value), effect.clone()),
        other => (runtime_core_type(other), typed_ir::Type::Never),
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

fn update_lambda_runtime_type(
    ty: RuntimeType,
    param_name: &typed_ir::Name,
    body: &Expr,
) -> RuntimeType {
    match ty {
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            choose_projected_lambda_param(
                *param,
                expr_local_var_runtime_type(body, &typed_ir::Path::from_name(param_name.clone())),
            ),
            choose_projected_lambda_return(*ret, body.ty.clone()),
        ),
        other => other,
    }
}

fn choose_projected_lambda_param(
    existing: RuntimeType,
    projected: Option<RuntimeType>,
) -> RuntimeType {
    let Some(projected) = projected else {
        return existing;
    };
    if runtime_type_contains_unknown(&existing) && !runtime_type_contains_unknown(&projected) {
        projected
    } else {
        existing
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
            locals.insert(def.clone(), body.ty.clone());
            let body = refresh_expr_local_types(body, locals);
            locals.insert(def.clone(), body.ty.clone());
            Stmt::Module { def, body }
        }
    }
}

fn refresh_join_body_result_type(mut body: Expr, result_ty: &typed_ir::Type) -> Expr {
    if !matches!(body.kind, ExprKind::Thunk { .. })
        && runtime_type_contains_unknown(&body.ty)
        && !core_type_contains_open_runtime_slot(result_ty)
    {
        body.ty = RuntimeType::core(result_ty.clone());
    }
    body
}

fn refresh_block_tail_result_type(tail: Expr, block_ty: &RuntimeType) -> Expr {
    if runtime_type_contains_unknown(block_ty) {
        tail
    } else {
        refresh_unknown_expr_runtime_type(tail, block_ty)
    }
}

fn default_handle_payload_runtime_type(handled_body_ty: &RuntimeType) -> Option<RuntimeType> {
    let payload_ty = match handled_body_ty {
        RuntimeType::Thunk { value, .. } => value.as_ref(),
        other => other,
    };
    (!runtime_type_contains_unknown(payload_ty)).then(|| payload_ty.clone())
}

fn infer_default_handle_payload_runtime_type(
    payload: &Pattern,
    body_ty: &RuntimeType,
    result_ty: &typed_ir::Type,
) -> Option<RuntimeType> {
    if !pattern_accepts_single_value(payload) {
        return None;
    }
    let RuntimeType::Core(body_ty) = body_ty else {
        return None;
    };
    let mut inferred = None;
    collect_single_unknown_replacement(body_ty, result_ty, &mut inferred)?;
    inferred.map(RuntimeType::core)
}

fn pattern_accepts_single_value(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Bind { .. } | Pattern::Wildcard { .. } => true,
        Pattern::As { pattern, .. } => pattern_accepts_single_value(pattern),
        _ => false,
    }
}

fn collect_single_unknown_replacement(
    template: &typed_ir::Type,
    context: &typed_ir::Type,
    inferred: &mut Option<typed_ir::Type>,
) -> Option<()> {
    match (template, context) {
        (typed_ir::Type::Unknown, context) => record_inferred_type(context, inferred),
        (
            typed_ir::Type::Named {
                path: template_path,
                args: template_args,
            },
            typed_ir::Type::Named { path, args },
        ) if template_path == path && template_args.len() == args.len() => {
            for (template_arg, context_arg) in template_args.iter().zip(args) {
                collect_single_unknown_replacement_from_arg(template_arg, context_arg, inferred)?;
            }
            Some(())
        }
        (typed_ir::Type::Tuple(template_items), typed_ir::Type::Tuple(context_items))
            if template_items.len() == context_items.len() =>
        {
            for (template_item, context_item) in template_items.iter().zip(context_items) {
                collect_single_unknown_replacement(template_item, context_item, inferred)?;
            }
            Some(())
        }
        (
            typed_ir::Type::Fun {
                param: template_param,
                param_effect: template_param_effect,
                ret_effect: template_ret_effect,
                ret: template_ret,
            },
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
        ) => {
            collect_single_unknown_replacement(template_param, param, inferred)?;
            collect_single_unknown_replacement(template_param_effect, param_effect, inferred)?;
            collect_single_unknown_replacement(template_ret_effect, ret_effect, inferred)?;
            collect_single_unknown_replacement(template_ret, ret, inferred)
        }
        (typed_ir::Type::Record(template_record), typed_ir::Type::Record(context_record)) => {
            for template_field in &template_record.fields {
                let context_field = context_record
                    .fields
                    .iter()
                    .find(|field| field.name == template_field.name)?;
                collect_single_unknown_replacement(
                    &template_field.value,
                    &context_field.value,
                    inferred,
                )?;
            }
            match (&template_record.spread, &context_record.spread) {
                (
                    Some(typed_ir::RecordSpread::Head(template_spread)),
                    Some(typed_ir::RecordSpread::Head(context_spread)),
                )
                | (
                    Some(typed_ir::RecordSpread::Tail(template_spread)),
                    Some(typed_ir::RecordSpread::Tail(context_spread)),
                ) => collect_single_unknown_replacement(template_spread, context_spread, inferred),
                (None, _) => Some(()),
                (Some(_), None) => None,
                _ => None,
            }
        }
        (typed_ir::Type::Variant(template_variant), typed_ir::Type::Variant(context_variant)) => {
            for template_case in &template_variant.cases {
                let context_case = context_variant
                    .cases
                    .iter()
                    .find(|case| case.name == template_case.name)?;
                if template_case.payloads.len() != context_case.payloads.len() {
                    return None;
                }
                for (template_payload, context_payload) in
                    template_case.payloads.iter().zip(&context_case.payloads)
                {
                    collect_single_unknown_replacement(
                        template_payload,
                        context_payload,
                        inferred,
                    )?;
                }
            }
            match (&template_variant.tail, &context_variant.tail) {
                (Some(template_tail), Some(context_tail)) => {
                    collect_single_unknown_replacement(template_tail, context_tail, inferred)
                }
                (None, _) => Some(()),
                (Some(_), None) => None,
            }
        }
        (
            typed_ir::Type::Row {
                items: template_items,
                tail: template_tail,
            },
            typed_ir::Type::Row { items, tail },
        ) if template_items.len() == items.len() => {
            for (template_item, item) in template_items.iter().zip(items) {
                collect_single_unknown_replacement(template_item, item, inferred)?;
            }
            collect_single_unknown_replacement(template_tail, tail, inferred)
        }
        (typed_ir::Type::Union(template_items), typed_ir::Type::Union(context_items))
        | (typed_ir::Type::Inter(template_items), typed_ir::Type::Inter(context_items))
            if template_items.len() == context_items.len() =>
        {
            for (template_item, context_item) in template_items.iter().zip(context_items) {
                collect_single_unknown_replacement(template_item, context_item, inferred)?;
            }
            Some(())
        }
        (
            typed_ir::Type::Recursive {
                var: template_var,
                body: template_body,
            },
            typed_ir::Type::Recursive { var, body },
        ) if template_var == var => {
            collect_single_unknown_replacement(template_body, body, inferred)
        }
        _ if template == context => Some(()),
        _ => None,
    }
}

fn collect_single_unknown_replacement_from_arg(
    template: &typed_ir::TypeArg,
    context: &typed_ir::TypeArg,
    inferred: &mut Option<typed_ir::Type>,
) -> Option<()> {
    match (template, context) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(context)) => {
            collect_single_unknown_replacement(template, context, inferred)
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(context)) => {
            collect_single_unknown_replacement_from_bounds(template, context, inferred)
        }
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(context)) => {
            let context = closed_type_from_type_arg_bounds(context)?;
            collect_single_unknown_replacement(template, context, inferred)
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(context)) => {
            let template = closed_type_from_type_arg_bounds(template)?;
            collect_single_unknown_replacement(template, context, inferred)
        }
    }
}

fn collect_single_unknown_replacement_from_bounds(
    template: &typed_ir::TypeBounds,
    context: &typed_ir::TypeBounds,
    inferred: &mut Option<typed_ir::Type>,
) -> Option<()> {
    match (&template.lower, &context.lower) {
        (Some(template), Some(context)) => {
            collect_single_unknown_replacement(template, context, inferred)?
        }
        (None, _) => {}
        (Some(_), None) => return None,
    }
    match (&template.upper, &context.upper) {
        (Some(template), Some(context)) => {
            collect_single_unknown_replacement(template, context, inferred)
        }
        (None, _) => Some(()),
        (Some(_), None) => None,
    }
}

fn closed_type_from_type_arg_bounds(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::Type> {
    match (&bounds.lower, &bounds.upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        (Some(lower), None) if !core_type_contains_open_runtime_slot(lower) => Some(lower),
        (None, Some(upper)) if !core_type_contains_open_runtime_slot(upper) => Some(upper),
        _ => None,
    }
}

fn record_inferred_type(
    context: &typed_ir::Type,
    inferred: &mut Option<typed_ir::Type>,
) -> Option<()> {
    if core_type_contains_open_runtime_slot(context) {
        return None;
    }
    match inferred {
        Some(existing) if existing == context => Some(()),
        Some(_) => None,
        None => {
            *inferred = Some(context.clone());
            Some(())
        }
    }
}

fn core_type_contains_open_runtime_slot(ty: &typed_ir::Type) -> bool {
    core_type_contains_unknown(ty) || core_type_has_vars(ty)
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

fn variant_expr_runtime_type(
    tag: &typed_ir::Name,
    value: Option<&Expr>,
    fallback: RuntimeType,
) -> RuntimeType {
    if matches!(fallback, RuntimeType::Core(typed_ir::Type::Named { .. }))
        || !runtime_type_contains_unknown(&fallback)
    {
        return fallback;
    }
    RuntimeType::core(typed_ir::Type::Variant(typed_ir::VariantType {
        cases: vec![typed_ir::VariantCase {
            name: tag.clone(),
            payloads: value
                .iter()
                .map(|value| runtime_core_type(&value.ty))
                .collect(),
        }],
        tail: None,
    }))
}
