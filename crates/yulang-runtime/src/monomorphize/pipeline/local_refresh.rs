use super::*;

pub(super) fn refresh_local_expr_types(expr: Expr) -> Expr {
    let mut locals = HashMap::new();
    refresh_expr_local_types(expr, &mut locals)
}

fn refresh_expr_local_types(expr: Expr, locals: &mut HashMap<core_ir::Path, RuntimeType>) -> Expr {
    let mut ty = expr.ty;
    let kind = match expr.kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let previous = hir_function_param_type(&ty).map(|param_ty| {
                let path = core_ir::Path::from_name(param.clone());
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
                            core_ir::Path::from_name(resume.name.clone()),
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
        ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
            id,
            allowed,
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

fn refresh_stmt_local_types(stmt: Stmt, locals: &mut HashMap<core_ir::Path, RuntimeType>) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => {
            let value = refresh_expr_local_types(value, locals);
            let pattern = refresh_pattern_default_local_types(pattern, locals);
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

fn refresh_pattern_default_local_types(
    pattern: Pattern,
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
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

fn push_pattern_local_types(pattern: &Pattern, locals: &mut HashMap<core_ir::Path, RuntimeType>) {
    match pattern {
        Pattern::Bind { name, ty } => {
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
        }
        Pattern::As { pattern, name, ty } => {
            push_pattern_local_types(pattern, locals);
            locals.insert(core_ir::Path::from_name(name.clone()), ty.clone());
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
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    path: core_ir::Path,
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
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some(effected_core_as_hir_type(param, param_effect)),
        _ => None,
    }
}

fn effected_core_as_hir_type(value: &core_ir::Type, effect: &core_ir::Type) -> RuntimeType {
    let value = normalize_hir_function_type(RuntimeType::core(value.clone()));
    let effect = project_runtime_effect(effect);
    if should_thunk_effect(&effect) {
        RuntimeType::thunk(effect, value)
    } else {
        value
    }
}
