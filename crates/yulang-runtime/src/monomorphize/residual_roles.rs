use super::*;

pub(super) fn resolve_residual_role_method_calls(mut module: Module) -> Module {
    let mut monomorphizer = Monomorphizer::new(&module);
    for _ in 0..32 {
        let mut changed = false;

        let original_root_exprs = std::mem::take(&mut module.root_exprs);
        let root_exprs = original_root_exprs
            .iter()
            .cloned()
            .map(|expr| rewrite_expr(&mut monomorphizer, expr))
            .collect::<Vec<_>>();
        if root_exprs != original_root_exprs {
            changed = true;
        }
        module.root_exprs = root_exprs;

        for binding in &mut module.bindings {
            if !binding.type_params.is_empty() && !is_specialized_path(&binding.name) {
                continue;
            }
            let rewritten = rewrite_expr(&mut monomorphizer, binding.body.clone());
            if rewritten != binding.body {
                binding.body = rewritten;
                changed = true;
            }
        }

        let specialized = std::mem::take(&mut monomorphizer.specialized);
        if !specialized.is_empty() {
            module.bindings.extend(specialized);
            changed = true;
        }

        if !changed {
            break;
        }
    }
    module
}

fn rewrite_expr(monomorphizer: &mut Monomorphizer, expr: Expr) -> Expr {
    let Expr { mut ty, kind } = expr;
    let kind = match kind {
        ExprKind::Var(path) => {
            if let Some(local_ty) = monomorphizer.locals.get(&path).cloned() {
                ty = local_ty;
            }
            ExprKind::Var(path)
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            mut instantiation,
        } => {
            let mut callee = rewrite_expr(monomorphizer, *callee);
            let mut arg = rewrite_expr(monomorphizer, *arg);
            let result_ty = apply_result_type(&callee.ty).unwrap_or_else(|| ty.clone());
            if monomorphizer.resolve_role_callee_from_call(&mut callee, &arg.ty, &result_ty) {
                instantiation = None;
            }
            if let Some(ret) = apply_result_type(&callee.ty) {
                ty = ret;
            }
            if let Some(param) = function_param_type(&callee.ty) {
                arg = force_arg_for_param(arg, &param);
            }
            ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence,
                instantiation,
            }
        }
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let local = core_ir::Path::from_name(param.clone());
            let previous = function_param_type(&ty)
                .map(|param_ty| monomorphizer.locals.insert(local.clone(), param_ty));
            let body = rewrite_expr(monomorphizer, *body);
            restore_local_type(&mut monomorphizer.locals, local, previous);
            if let Some(refined) = refine_lambda_type_from_body(&ty, &body) {
                ty = refined;
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body: Box::new(body),
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(rewrite_expr(monomorphizer, *cond)),
            then_branch: Box::new(rewrite_expr(monomorphizer, *then_branch)),
            else_branch: Box::new(rewrite_expr(monomorphizer, *else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| rewrite_expr(monomorphizer, item))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: rewrite_expr(monomorphizer, field.value),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(rewrite_expr(monomorphizer, *expr)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(rewrite_expr(monomorphizer, *expr)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(rewrite_expr(monomorphizer, *value))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(rewrite_expr(monomorphizer, *base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(rewrite_expr(monomorphizer, *scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    guard: arm.guard.map(|guard| rewrite_expr(monomorphizer, guard)),
                    body: rewrite_expr(monomorphizer, arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => {
            let stmts = stmts
                .into_iter()
                .map(|stmt| rewrite_stmt(monomorphizer, stmt))
                .collect();
            let tail = tail.map(|tail| Box::new(rewrite_expr(monomorphizer, *tail)));
            if let Some(tail) = tail.as_deref() {
                ty = refine_block_type_from_tail(ty, &tail.ty);
            }
            ExprKind::Block { stmts, tail }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(rewrite_expr(monomorphizer, *body)),
            arms: arms
                .into_iter()
                .map(|arm| HandleArm {
                    effect: arm.effect,
                    payload: arm.payload,
                    resume: arm.resume,
                    guard: arm.guard.map(|guard| rewrite_expr(monomorphizer, guard)),
                    body: rewrite_expr(monomorphizer, arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(rewrite_expr(monomorphizer, *expr)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let expr = rewrite_expr(monomorphizer, *expr);
            let (effect, body_ty, expr) = flatten_nested_thunk_body(effect, expr);
            let value = refine_thunk_value_from_body(value, &body_ty);
            ty = RuntimeType::thunk(effect.clone(), value.clone());
            ExprKind::Thunk {
                effect,
                value,
                expr: Box::new(expr),
            }
        }
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(rewrite_expr(monomorphizer, *body)),
        },
        ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
            id,
            allowed,
            thunk: Box::new(rewrite_expr(monomorphizer, *thunk)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(rewrite_expr(monomorphizer, *expr)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(rewrite_expr(monomorphizer, *expr)),
        },
        kind @ (ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. }) => kind,
    };
    Expr { ty, kind }
}

fn rewrite_stmt(monomorphizer: &mut Monomorphizer, stmt: Stmt) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: rewrite_expr(monomorphizer, value),
        },
        Stmt::Expr(expr) => Stmt::Expr(rewrite_expr(monomorphizer, expr)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: rewrite_expr(monomorphizer, body),
        },
    }
}
