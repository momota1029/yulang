use super::*;

pub(super) fn pattern_type(pattern: &Pattern) -> RuntimeType {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty.clone(),
    }
}

pub(super) fn collect_expr_vars(expr: &Expr, vars: &mut HashSet<core_ir::Path>) {
    match &expr.kind {
        ExprKind::Var(path) => {
            vars.insert(path.clone());
        }
        ExprKind::Lambda { body, .. } => collect_expr_vars(body, vars),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_vars(callee, vars);
            collect_expr_vars(arg, vars);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_vars(cond, vars);
            collect_expr_vars(then_branch, vars);
            collect_expr_vars(else_branch, vars);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_vars(item, vars);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_vars(&field.value, vars);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_vars(expr, vars);
                    }
                }
            }
        }
        ExprKind::Variant {
            value: Some(value), ..
        } => collect_expr_vars(value, vars),
        ExprKind::Select { base, .. } => collect_expr_vars(base, vars),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_vars(scrutinee, vars);
            for arm in arms {
                collect_pattern_default_vars(&arm.pattern, vars);
                if let Some(guard) = &arm.guard {
                    collect_expr_vars(guard, vars);
                }
                collect_expr_vars(&arm.body, vars);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_vars(tail, vars);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_vars(body, vars);
            for arm in arms {
                collect_pattern_default_vars(&arm.payload, vars);
                if let Some(guard) = &arm.guard {
                    collect_expr_vars(guard, vars);
                }
                collect_expr_vars(&arm.body, vars);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => collect_expr_vars(expr, vars),
        ExprKind::LocalPushId { body, .. } => collect_expr_vars(body, vars),
        ExprKind::AddId { thunk, .. } => collect_expr_vars(thunk, vars),
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_stmt_vars(stmt: &Stmt, vars: &mut HashSet<core_ir::Path>) {
    match stmt {
        Stmt::Let { pattern, value } => {
            collect_pattern_default_vars(pattern, vars);
            collect_expr_vars(value, vars);
        }
        Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_vars(value, vars);
        }
    }
}

fn collect_pattern_default_vars(pattern: &Pattern, vars: &mut HashSet<core_ir::Path>) {
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_default_vars(item, vars);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_default_vars(item, vars);
            }
            if let Some(spread) = spread {
                collect_pattern_default_vars(spread, vars);
            }
            for item in suffix {
                collect_pattern_default_vars(item, vars);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                if let Some(default) = &field.default {
                    collect_expr_vars(default, vars);
                }
                collect_pattern_default_vars(&field.pattern, vars);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_default_vars(pattern, vars);
                    }
                }
            }
        }
        Pattern::Variant {
            value: Some(value), ..
        } => collect_pattern_default_vars(value, vars),
        Pattern::Or { left, right, .. } => {
            collect_pattern_default_vars(left, vars);
            collect_pattern_default_vars(right, vars);
        }
        Pattern::As { pattern, .. } => collect_pattern_default_vars(pattern, vars),
        Pattern::Wildcard { .. }
        | Pattern::Bind { .. }
        | Pattern::Lit { .. }
        | Pattern::Variant { value: None, .. } => {}
    }
}
