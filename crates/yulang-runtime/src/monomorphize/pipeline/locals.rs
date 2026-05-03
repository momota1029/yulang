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
    let mut bound = HashSet::new();
    collect_expr_free_vars(expr, &mut bound, vars);
}

fn collect_expr_free_vars(
    expr: &Expr,
    bound: &mut HashSet<core_ir::Path>,
    vars: &mut HashSet<core_ir::Path>,
) {
    match &expr.kind {
        ExprKind::Var(path) => {
            if !bound.contains(path) {
                vars.insert(path.clone());
            }
        }
        ExprKind::Lambda { param, body, .. } => {
            with_bound_path(bound, core_ir::Path::from_name(param.clone()), |bound| {
                collect_expr_free_vars(body, bound, vars);
            });
        }
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_free_vars(callee, bound, vars);
            collect_expr_free_vars(arg, bound, vars);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_free_vars(cond, bound, vars);
            collect_expr_free_vars(then_branch, bound, vars);
            collect_expr_free_vars(else_branch, bound, vars);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_free_vars(item, bound, vars);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_free_vars(&field.value, bound, vars);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_expr_free_vars(expr, bound, vars);
                    }
                }
            }
        }
        ExprKind::Variant {
            value: Some(value), ..
        } => collect_expr_free_vars(value, bound, vars),
        ExprKind::Select { base, .. } => collect_expr_free_vars(base, bound, vars),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_free_vars(scrutinee, bound, vars);
            for arm in arms {
                collect_pattern_default_free_vars(&arm.pattern, bound, vars);
                with_bound_pattern(bound, &arm.pattern, |bound| {
                    if let Some(guard) = &arm.guard {
                        collect_expr_free_vars(guard, bound, vars);
                    }
                    collect_expr_free_vars(&arm.body, bound, vars);
                });
            }
        }
        ExprKind::Block { stmts, tail } => {
            collect_block_free_vars(stmts, tail.as_deref(), bound, vars);
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_free_vars(body, bound, vars);
            for arm in arms {
                collect_pattern_default_free_vars(&arm.payload, bound, vars);
                with_bound_pattern(bound, &arm.payload, |bound| {
                    if let Some(guard) = &arm.guard {
                        collect_expr_free_vars(guard, bound, vars);
                    }
                    if let Some(resume) = &arm.resume {
                        with_bound_path(
                            bound,
                            core_ir::Path::from_name(resume.name.clone()),
                            |bound| {
                                collect_expr_free_vars(&arm.body, bound, vars);
                            },
                        );
                    } else {
                        collect_expr_free_vars(&arm.body, bound, vars);
                    }
                });
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => collect_expr_free_vars(expr, bound, vars),
        ExprKind::LocalPushId { body, .. } => collect_expr_free_vars(body, bound, vars),
        ExprKind::AddId { thunk, .. } => collect_expr_free_vars(thunk, bound, vars),
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Variant { value: None, .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_block_free_vars(
    stmts: &[Stmt],
    tail: Option<&Expr>,
    bound: &mut HashSet<core_ir::Path>,
    vars: &mut HashSet<core_ir::Path>,
) {
    let checkpoint = bound.clone();
    for stmt in stmts {
        collect_stmt_free_vars(stmt, bound, vars);
    }
    if let Some(tail) = tail {
        collect_expr_free_vars(tail, bound, vars);
    }
    *bound = checkpoint;
}

fn collect_stmt_free_vars(
    stmt: &Stmt,
    bound: &mut HashSet<core_ir::Path>,
    vars: &mut HashSet<core_ir::Path>,
) {
    match stmt {
        Stmt::Let { pattern, value } => {
            collect_pattern_default_free_vars(pattern, bound, vars);
            collect_expr_free_vars(value, bound, vars);
            bind_pattern_paths(bound, pattern);
        }
        Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_free_vars(value, bound, vars);
        }
    }
    if let Stmt::Module { def, .. } = stmt {
        bound.insert(def.clone());
    }
}

fn with_bound_path(
    bound: &mut HashSet<core_ir::Path>,
    path: core_ir::Path,
    f: impl FnOnce(&mut HashSet<core_ir::Path>),
) {
    let inserted = bound.insert(path.clone());
    f(bound);
    if inserted {
        bound.remove(&path);
    }
}

fn with_bound_pattern(
    bound: &mut HashSet<core_ir::Path>,
    pattern: &Pattern,
    f: impl FnOnce(&mut HashSet<core_ir::Path>),
) {
    let checkpoint = bound.clone();
    bind_pattern_paths(bound, pattern);
    f(bound);
    *bound = checkpoint;
}

fn bind_pattern_paths(bound: &mut HashSet<core_ir::Path>, pattern: &Pattern) {
    match pattern {
        Pattern::Bind { name, .. } => {
            bound.insert(core_ir::Path::from_name(name.clone()));
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                bind_pattern_paths(bound, item);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                bind_pattern_paths(bound, item);
            }
            if let Some(spread) = spread {
                bind_pattern_paths(bound, spread);
            }
            for item in suffix {
                bind_pattern_paths(bound, item);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                bind_pattern_paths(bound, &field.pattern);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        bind_pattern_paths(bound, pattern);
                    }
                }
            }
        }
        Pattern::Variant {
            value: Some(value), ..
        } => bind_pattern_paths(bound, value),
        Pattern::Or { left, right, .. } => {
            bind_pattern_paths(bound, left);
            bind_pattern_paths(bound, right);
        }
        Pattern::As { pattern, name, .. } => {
            bind_pattern_paths(bound, pattern);
            bound.insert(core_ir::Path::from_name(name.clone()));
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } | Pattern::Variant { value: None, .. } => {}
    }
}

fn collect_pattern_default_free_vars(
    pattern: &Pattern,
    bound: &mut HashSet<core_ir::Path>,
    vars: &mut HashSet<core_ir::Path>,
) {
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_default_free_vars(item, bound, vars);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_default_free_vars(item, bound, vars);
            }
            if let Some(spread) = spread {
                collect_pattern_default_free_vars(spread, bound, vars);
            }
            for item in suffix {
                collect_pattern_default_free_vars(item, bound, vars);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                if let Some(default) = &field.default {
                    collect_expr_free_vars(default, bound, vars);
                }
                collect_pattern_default_free_vars(&field.pattern, bound, vars);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_default_free_vars(pattern, bound, vars);
                    }
                }
            }
        }
        Pattern::Variant {
            value: Some(value), ..
        } => collect_pattern_default_free_vars(value, bound, vars),
        Pattern::Or { left, right, .. } => {
            collect_pattern_default_free_vars(left, bound, vars);
            collect_pattern_default_free_vars(right, bound, vars);
        }
        Pattern::As { pattern, .. } => collect_pattern_default_free_vars(pattern, bound, vars),
        Pattern::Wildcard { .. }
        | Pattern::Bind { .. }
        | Pattern::Lit { .. }
        | Pattern::Variant { value: None, .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collect_expr_vars_ignores_handle_resume_in_arm_body() {
        let resume = core_ir::Name("resume".to_string());
        let resume_path = core_ir::Path::from_name(resume.clone());
        let unit = RuntimeType::Core(core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("unit".to_string())),
            args: Vec::new(),
        });
        let expr = Expr::typed(
            ExprKind::Handle {
                body: Box::new(Expr::typed(ExprKind::Lit(core_ir::Lit::Unit), unit.clone())),
                arms: vec![HandleArm {
                    effect: core_ir::Path::from_name(core_ir::Name("eff".to_string())),
                    payload: Pattern::Wildcard { ty: unit.clone() },
                    resume: Some(ResumeBinding {
                        name: resume,
                        ty: unit.clone(),
                    }),
                    guard: None,
                    body: Expr::typed(ExprKind::Var(resume_path.clone()), unit.clone()),
                }],
                evidence: crate::ir::JoinEvidence {
                    result: core_ir::Type::Never,
                },
                handler: crate::ir::HandleEffect {
                    consumes: Vec::new(),
                    residual_before: None,
                    residual_after: None,
                },
            },
            unit,
        );

        let mut vars = HashSet::new();
        collect_expr_vars(&expr, &mut vars);

        assert!(
            !vars.contains(&resume_path),
            "resume binding should not be treated as a top-level reference: {vars:?}",
        );
    }
}
