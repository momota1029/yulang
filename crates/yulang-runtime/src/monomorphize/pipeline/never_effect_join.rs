use super::*;
use crate::types::core_type_contains_unknown;

pub(super) fn normalize_never_effect_join_arms(
    module: &mut Module,
    never_effect_ops: &HashSet<typed_ir::Path>,
) {
    if never_effect_ops.is_empty() {
        return;
    }
    module.root_exprs = module
        .root_exprs
        .drain(..)
        .map(|expr| normalize_expr(expr, never_effect_ops))
        .collect();
    for binding in &mut module.bindings {
        binding.body = normalize_expr(binding.body.clone(), never_effect_ops);
    }
}

pub(super) fn collect_never_effect_ops(module: &Module) -> HashSet<typed_ir::Path> {
    let mut out = HashSet::new();
    for expr in &module.root_exprs {
        collect_expr(expr, &mut out);
    }
    for binding in &module.bindings {
        collect_expr(&binding.body, &mut out);
    }
    out
}

fn normalize_expr(expr: Expr, never_effect_ops: &HashSet<typed_ir::Path>) -> Expr {
    let Expr { ty, kind } = expr;
    match kind {
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
                body: Box::new(normalize_expr(*body, never_effect_ops)),
            },
            ty,
        ),
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => Expr::typed(
            ExprKind::Apply {
                callee: Box::new(normalize_expr(*callee, never_effect_ops)),
                arg: Box::new(normalize_expr(*arg, never_effect_ops)),
                evidence,
                instantiation,
            },
            ty,
        ),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => normalize_if(
            ty,
            *cond,
            *then_branch,
            *else_branch,
            evidence,
            never_effect_ops,
        ),
        ExprKind::Tuple(items) => Expr::typed(
            ExprKind::Tuple(
                items
                    .into_iter()
                    .map(|item| normalize_expr(item, never_effect_ops))
                    .collect(),
            ),
            ty,
        ),
        ExprKind::Record { fields, spread } => Expr::typed(
            ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordExprField {
                        name: field.name,
                        value: normalize_expr(field.value, never_effect_ops),
                    })
                    .collect(),
                spread: spread.map(|spread| match spread {
                    RecordSpreadExpr::Head(expr) => {
                        RecordSpreadExpr::Head(Box::new(normalize_expr(*expr, never_effect_ops)))
                    }
                    RecordSpreadExpr::Tail(expr) => {
                        RecordSpreadExpr::Tail(Box::new(normalize_expr(*expr, never_effect_ops)))
                    }
                }),
            },
            ty,
        ),
        ExprKind::Variant { tag, value } => Expr::typed(
            ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(normalize_expr(*value, never_effect_ops))),
            },
            ty,
        ),
        ExprKind::Select { base, field } => Expr::typed(
            ExprKind::Select {
                base: Box::new(normalize_expr(*base, never_effect_ops)),
                field,
            },
            ty,
        ),
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => normalize_match(ty, *scrutinee, arms, evidence, never_effect_ops),
        ExprKind::Block { stmts, tail } => normalize_block(ty, stmts, tail, never_effect_ops),
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => normalize_handle(ty, *body, arms, evidence, handler, never_effect_ops),
        ExprKind::BindHere { expr } => {
            let inner = normalize_expr(*expr, never_effect_ops);
            let bind_ty = bind_here_result_type(&inner);
            Expr::typed(
                ExprKind::BindHere {
                    expr: Box::new(inner),
                },
                bind_ty,
            )
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => Expr::typed(
            ExprKind::Thunk {
                effect,
                value,
                expr: Box::new(normalize_expr(*expr, never_effect_ops)),
            },
            ty,
        ),
        ExprKind::LocalPushId { id, body } => Expr::typed(
            ExprKind::LocalPushId {
                id,
                body: Box::new(normalize_expr(*body, never_effect_ops)),
            },
            ty,
        ),
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => Expr::typed(
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk: Box::new(normalize_expr(*thunk, never_effect_ops)),
            },
            ty,
        ),
        ExprKind::Coerce { from, to, expr } => Expr::typed(
            ExprKind::Coerce {
                from,
                to,
                expr: Box::new(normalize_expr(*expr, never_effect_ops)),
            },
            ty,
        ),
        ExprKind::Pack { var, expr } => Expr::typed(
            ExprKind::Pack {
                var,
                expr: Box::new(normalize_expr(*expr, never_effect_ops)),
            },
            ty,
        ),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => Expr::typed(kind, ty),
    }
}

fn normalize_if(
    ty: RuntimeType,
    cond: Expr,
    then_branch: Expr,
    else_branch: Expr,
    evidence: Option<JoinEvidence>,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> Expr {
    let result = evidence
        .as_ref()
        .and_then(|evidence| final_join_result_type(&ty, &evidence.result));
    let expected = result
        .as_ref()
        .map(|result| RuntimeType::core(result.clone()));
    let then_branch = normalize_join_branch(then_branch, expected.as_ref(), never_effect_ops);
    let else_branch = normalize_join_branch(else_branch, expected.as_ref(), never_effect_ops);
    Expr::typed(
        ExprKind::If {
            cond: Box::new(normalize_expr(cond, never_effect_ops)),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
            evidence,
        },
        result.map(RuntimeType::core).unwrap_or(ty),
    )
}

fn normalize_match(
    ty: RuntimeType,
    scrutinee: Expr,
    arms: Vec<MatchArm>,
    evidence: JoinEvidence,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> Expr {
    let result = final_join_result_type(&ty, &evidence.result);
    let expected = result
        .as_ref()
        .map(|result| RuntimeType::core(result.clone()));
    let arms = arms
        .into_iter()
        .map(|arm| MatchArm {
            pattern: normalize_pattern(arm.pattern, never_effect_ops),
            guard: arm
                .guard
                .map(|guard| normalize_expr(guard, never_effect_ops)),
            body: normalize_join_branch(arm.body, expected.as_ref(), never_effect_ops),
        })
        .collect();
    Expr::typed(
        ExprKind::Match {
            scrutinee: Box::new(normalize_expr(scrutinee, never_effect_ops)),
            arms,
            evidence,
        },
        result.map(RuntimeType::core).unwrap_or(ty),
    )
}

fn normalize_handle(
    ty: RuntimeType,
    body: Expr,
    arms: Vec<HandleArm>,
    evidence: JoinEvidence,
    handler: HandleEffect,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> Expr {
    let result = final_join_result_type(&ty, &evidence.result);
    let expected = result
        .as_ref()
        .map(|result| RuntimeType::core(result.clone()));
    let arms = arms
        .into_iter()
        .map(|arm| HandleArm {
            effect: arm.effect,
            payload: normalize_pattern(arm.payload, never_effect_ops),
            resume: arm.resume,
            guard: arm
                .guard
                .map(|guard| normalize_expr(guard, never_effect_ops)),
            body: normalize_join_branch(arm.body, expected.as_ref(), never_effect_ops),
        })
        .collect();
    Expr::typed(
        ExprKind::Handle {
            body: Box::new(normalize_expr(body, never_effect_ops)),
            arms,
            evidence,
            handler,
        },
        result.map(RuntimeType::core).unwrap_or(ty),
    )
}

fn normalize_block(
    ty: RuntimeType,
    stmts: Vec<Stmt>,
    tail: Option<Box<Expr>>,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> Expr {
    let stmts = stmts
        .into_iter()
        .map(|stmt| normalize_stmt(stmt, never_effect_ops))
        .collect::<Vec<_>>();
    let tail = tail.map(|tail| Box::new(normalize_expr(*tail, never_effect_ops)));
    let block_ty = tail.as_ref().map(|tail| tail.ty.clone()).unwrap_or(ty);
    Expr::typed(ExprKind::Block { stmts, tail }, block_ty)
}

fn normalize_stmt(stmt: Stmt, never_effect_ops: &HashSet<typed_ir::Path>) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern: normalize_pattern(pattern, never_effect_ops),
            value: normalize_expr(value, never_effect_ops),
        },
        Stmt::Expr(expr) => Stmt::Expr(normalize_expr(expr, never_effect_ops)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: normalize_expr(body, never_effect_ops),
        },
    }
}

fn normalize_pattern(pattern: Pattern, never_effect_ops: &HashSet<typed_ir::Path>) -> Pattern {
    match pattern {
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| normalize_pattern(item, never_effect_ops))
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
                .map(|item| normalize_pattern(item, never_effect_ops))
                .collect(),
            spread: spread.map(|spread| Box::new(normalize_pattern(*spread, never_effect_ops))),
            suffix: suffix
                .into_iter()
                .map(|item| normalize_pattern(item, never_effect_ops))
                .collect(),
            ty,
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordPatternField {
                    name: field.name,
                    pattern: normalize_pattern(field.pattern, never_effect_ops),
                    default: field
                        .default
                        .map(|default| normalize_expr(default, never_effect_ops)),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadPattern::Head(pattern) => RecordSpreadPattern::Head(Box::new(
                    normalize_pattern(*pattern, never_effect_ops),
                )),
                RecordSpreadPattern::Tail(pattern) => RecordSpreadPattern::Tail(Box::new(
                    normalize_pattern(*pattern, never_effect_ops),
                )),
            }),
            ty,
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(normalize_pattern(*value, never_effect_ops))),
            ty,
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(normalize_pattern(*left, never_effect_ops)),
            right: Box::new(normalize_pattern(*right, never_effect_ops)),
            ty,
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(normalize_pattern(*pattern, never_effect_ops)),
            name,
            ty,
        },
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => pattern,
    }
}

fn normalize_join_branch(
    expr: Expr,
    expected: Option<&RuntimeType>,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> Expr {
    let expr = normalize_expr(expr, never_effect_ops);
    match expected {
        Some(expected) => adapt_never_effect_expr_to_type(expr, expected, never_effect_ops),
        None => expr,
    }
}

fn final_join_result_type(
    expr_ty: &RuntimeType,
    evidence_result: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if closed_slot_type_usable(evidence_result, true)
        && !core_type_contains_unknown(evidence_result)
    {
        return Some(evidence_result.clone());
    }
    let expr_result = runtime_core_type(expr_ty);
    (closed_slot_type_usable(&expr_result, true) && !core_type_contains_unknown(&expr_result))
        .then_some(expr_result)
}

fn bind_here_result_type(expr: &Expr) -> RuntimeType {
    match &expr.ty {
        RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
        _ => expr.ty.clone(),
    }
}

fn adapt_never_effect_expr_to_type(
    expr: Expr,
    expected: &RuntimeType,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> Expr {
    let Expr { ty, kind } = expr;
    match kind {
        ExprKind::BindHere { expr: inner } => {
            let inner = adapt_never_effect_expr_to_type(*inner, expected, never_effect_ops);
            let bind_ty = match &inner.ty {
                RuntimeType::Thunk { .. }
                    if expr_is_never_effect_op_apply_for_paths(&inner, never_effect_ops) =>
                {
                    expected.clone()
                }
                _ => bind_here_result_type(&inner),
            };
            Expr::typed(
                ExprKind::BindHere {
                    expr: Box::new(inner),
                },
                bind_ty,
            )
        }
        ExprKind::Apply {
            mut callee,
            arg,
            mut evidence,
            instantiation,
        } => {
            let is_never_effect = matches!(
                callee.kind,
                ExprKind::EffectOp(ref path) if never_effect_ops.contains(path)
            );
            let ty = match (is_never_effect, ty) {
                (true, RuntimeType::Thunk { effect, .. }) => {
                    let result_ty = RuntimeType::thunk(effect, expected.clone());
                    callee.ty =
                        runtime_function_type_with_forced_return(callee.ty, result_ty.clone());
                    if let Some(evidence) = &mut evidence {
                        evidence.result = typed_ir::TypeBounds::exact(runtime_core_type(expected));
                    }
                    result_ty
                }
                (_, ty) => ty,
            };
            Expr::typed(
                ExprKind::Apply {
                    callee,
                    arg,
                    evidence,
                    instantiation,
                },
                ty,
            )
        }
        ExprKind::Block { stmts, tail } => {
            let tail = tail.map(|tail| {
                Box::new(adapt_never_effect_expr_to_type(
                    *tail,
                    expected,
                    never_effect_ops,
                ))
            });
            let ty = tail.as_ref().map(|tail| tail.ty.clone()).unwrap_or(ty);
            Expr::typed(ExprKind::Block { stmts, tail }, ty)
        }
        ExprKind::Coerce { from, to, expr } => Expr::typed(
            ExprKind::Coerce {
                from,
                to,
                expr: Box::new(adapt_never_effect_expr_to_type(
                    *expr,
                    expected,
                    never_effect_ops,
                )),
            },
            ty,
        ),
        ExprKind::Pack { var, expr } => Expr::typed(
            ExprKind::Pack {
                var,
                expr: Box::new(adapt_never_effect_expr_to_type(
                    *expr,
                    expected,
                    never_effect_ops,
                )),
            },
            ty,
        ),
        ExprKind::LocalPushId { id, body } => Expr::typed(
            ExprKind::LocalPushId {
                id,
                body: Box::new(adapt_never_effect_expr_to_type(
                    *body,
                    expected,
                    never_effect_ops,
                )),
            },
            ty,
        ),
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => Expr::typed(
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk: Box::new(adapt_never_effect_expr_to_type(
                    *thunk,
                    expected,
                    never_effect_ops,
                )),
            },
            ty,
        ),
        kind => Expr::typed(kind, ty),
    }
}

fn expr_is_never_effect_op_apply_for_paths(
    expr: &Expr,
    never_effect_ops: &HashSet<typed_ir::Path>,
) -> bool {
    let ExprKind::Apply { callee, .. } = &expr.kind else {
        return false;
    };
    matches!(
        &callee.kind,
        ExprKind::EffectOp(path) if never_effect_ops.contains(path)
    )
}

fn runtime_function_type_with_forced_return(ty: RuntimeType, ret_ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Fun { param, .. } => RuntimeType::fun(*param, ret_ty),
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => {
            let (ret, ret_effect) = runtime_value_and_effect(&ret_ty);
            RuntimeType::core(typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            })
        }
        other => other,
    }
}

fn runtime_value_and_effect(ty: &RuntimeType) -> (typed_ir::Type, typed_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_core_type(value), effect.clone()),
        other => (runtime_core_type(other), typed_ir::Type::Never),
    }
}

fn collect_expr(expr: &Expr, out: &mut HashSet<typed_ir::Path>) {
    match &expr.kind {
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            ..
        } => {
            if evidence
                .as_ref()
                .is_some_and(apply_evidence_result_is_never)
                && let ExprKind::EffectOp(path) = &callee.kind
            {
                out.insert(path.clone());
            }
            collect_expr(callee, out);
            collect_expr(arg, out);
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. } => collect_expr(body, out),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr(cond, out);
            collect_expr(then_branch, out);
            collect_expr(else_branch, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr(item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr(expr, out)
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr(value, out);
            }
        }
        ExprKind::Select { base, .. } => collect_expr(base, out),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr(guard, out);
                }
                collect_expr(&arm.body, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt(stmt, out);
            }
            if let Some(tail) = tail {
                collect_expr(tail, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr(guard, out);
                }
                collect_expr(&arm.body, out);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_stmt(stmt: &Stmt, out: &mut HashSet<typed_ir::Path>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr(value, out);
        }
    }
}
