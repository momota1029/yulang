use super::*;

pub(super) fn remove_dead_lambda_lets(stmts: Vec<Stmt>, tail: Option<&Expr>) -> Vec<Stmt> {
    let mut used = HashSet::new();
    if let Some(tail) = tail {
        collect_expr_vars(tail, &mut used);
    }
    let mut kept = Vec::with_capacity(stmts.len());
    for stmt in stmts.into_iter().rev() {
        match stmt {
            Stmt::Let { pattern, value } => {
                let bound = single_bind_pattern_name(&pattern);
                if matches!(value.kind, ExprKind::Lambda { .. })
                    && bound.as_ref().is_some_and(|name| !used.contains(name))
                {
                    continue;
                }
                remove_pattern_binds(&pattern, &mut used);
                collect_expr_vars(&value, &mut used);
                kept.push(Stmt::Let { pattern, value });
            }
            Stmt::Expr(expr) => {
                collect_expr_vars(&expr, &mut used);
                kept.push(Stmt::Expr(expr));
            }
            Stmt::Module { def, body } => {
                used.remove(&def);
                collect_expr_vars(&body, &mut used);
                kept.push(Stmt::Module { def, body });
            }
        }
    }
    kept.reverse();
    kept
}

pub(super) fn single_bind_pattern_name(pattern: &Pattern) -> Option<core_ir::Path> {
    match pattern {
        Pattern::Bind { name, .. } => Some(core_ir::Path::from_name(name.clone())),
        Pattern::As { name, .. } => Some(core_ir::Path::from_name(name.clone())),
        _ => None,
    }
}

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

pub(super) fn push_stmt_locals(locals: &mut HashMap<core_ir::Path, RuntimeType>, stmt: &Stmt) {
    if let Stmt::Let { pattern, .. } = stmt {
        for (path, ty) in pattern_bindings(pattern) {
            locals.insert(path, ty);
        }
    }
}

pub(super) fn pattern_bindings(pattern: &Pattern) -> Vec<(core_ir::Path, RuntimeType)> {
    let mut bindings = Vec::new();
    collect_pattern_bindings(pattern, &mut bindings);
    bindings
}

pub(super) fn collect_pattern_bindings(
    pattern: &Pattern,
    bindings: &mut Vec<(core_ir::Path, RuntimeType)>,
) {
    match pattern {
        Pattern::Bind { name, ty } => {
            bindings.push((core_ir::Path::from_name(name.clone()), ty.clone()));
        }
        Pattern::As { pattern, name, ty } => {
            collect_pattern_bindings(pattern, bindings);
            bindings.push((core_ir::Path::from_name(name.clone()), ty.clone()));
        }
        Pattern::Tuple { items, .. } | Pattern::List { prefix: items, .. } => {
            for item in items {
                collect_pattern_bindings(item, bindings);
            }
            if let Pattern::List { spread, suffix, .. } = pattern {
                if let Some(spread) = spread {
                    collect_pattern_bindings(spread, bindings);
                }
                for item in suffix {
                    collect_pattern_bindings(item, bindings);
                }
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_bindings(&field.pattern, bindings);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_bindings(pattern, bindings);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_bindings(value, bindings);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_bindings(left, bindings);
            collect_pattern_bindings(right, bindings);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

pub(super) fn push_local_types(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    bindings: &[(core_ir::Path, RuntimeType)],
) -> Vec<(core_ir::Path, Option<RuntimeType>)> {
    bindings
        .iter()
        .map(|(path, ty)| (path.clone(), locals.insert(path.clone(), ty.clone())))
        .collect()
}

pub(super) fn pop_local_types(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    previous: Vec<(core_ir::Path, Option<RuntimeType>)>,
) {
    for (path, ty) in previous.into_iter().rev() {
        restore_local_type(locals, path, Some(ty));
    }
}

pub(super) fn restore_local_type(
    locals: &mut HashMap<core_ir::Path, RuntimeType>,
    path: core_ir::Path,
    previous: Option<Option<RuntimeType>>,
) {
    match previous {
        Some(Some(ty)) => {
            locals.insert(path, ty);
        }
        Some(None) => {
            locals.remove(&path);
        }
        None => {}
    }
}

pub(super) fn remove_pattern_binds(pattern: &Pattern, used: &mut HashSet<core_ir::Path>) {
    match pattern {
        Pattern::Bind { name, .. } | Pattern::As { name, .. } => {
            used.remove(&core_ir::Path::from_name(name.clone()));
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                remove_pattern_binds(item, used);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                remove_pattern_binds(item, used);
            }
            if let Some(spread) = spread {
                remove_pattern_binds(spread, used);
            }
            for item in suffix {
                remove_pattern_binds(item, used);
            }
        }
        Pattern::Record { fields, .. } => {
            for field in fields {
                remove_pattern_binds(&field.pattern, used);
            }
        }
        Pattern::Variant {
            value: Some(value), ..
        } => remove_pattern_binds(value, used),
        Pattern::Or { left, right, .. } => {
            remove_pattern_binds(left, used);
            remove_pattern_binds(right, used);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } | Pattern::Variant { value: None, .. } => {}
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

pub(super) fn collect_stmt_vars(stmt: &Stmt, vars: &mut HashSet<core_ir::Path>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_vars(value, vars);
        }
    }
}
