use super::*;

/// Normalize typed metadata after monomorphization so it obeys the same
/// concrete runtime contract as the surrounding `Expr.ty` slots. The
/// monomorphize substitute pass only rewrites variables that appear in
/// the binding scheme's quantified list, so inference vars that live
/// solely inside evidence `TypeBounds` can survive untouched.
///
/// This pass is not a source-level type inference step. It lowers
/// monomorphized metadata to the minimal concrete shape consumed by
/// validate/runtime: Apply evidence mirrors callee/arg/result slots,
/// join evidence mirrors the enclosing result, and principal inference
/// traces that runtime never reads are dropped.
pub(super) fn normalize_monomorphized_metadata(mut module: Module) -> Module {
    let binding_types = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.body.ty.clone()))
        .collect::<HashMap<_, _>>();
    for binding in &mut module.bindings {
        refresh_global_var_types(&mut binding.body, &binding_types, &mut BTreeSet::new());
        binding.body = project_runtime_expr_types(take_expr(&mut binding.body));
    }
    for root in &mut module.root_exprs {
        refresh_global_var_types(root, &binding_types, &mut BTreeSet::new());
        *root = project_runtime_expr_types(take_expr(root));
    }
    for binding in &mut module.bindings {
        refresh_expr(&mut binding.body);
    }
    for root in &mut module.root_exprs {
        refresh_expr(root);
    }
    module
}

fn take_expr(expr: &mut Expr) -> Expr {
    std::mem::replace(
        expr,
        Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), RuntimeType::Unknown),
    )
}

fn refresh_global_var_types(
    expr: &mut Expr,
    binding_types: &HashMap<typed_ir::Path, RuntimeType>,
    shadowed: &mut BTreeSet<typed_ir::Name>,
) {
    match &mut expr.kind {
        ExprKind::Var(path) => {
            if !path_is_shadowed(path, shadowed)
                && let Some(ty) = binding_types.get(path)
            {
                expr.ty = ty.clone();
            }
        }
        ExprKind::Lambda { param, body, .. } => {
            let inserted = shadowed.insert(param.clone());
            refresh_global_var_types(body, binding_types, shadowed);
            if inserted {
                shadowed.remove(param);
            }
        }
        ExprKind::Apply { callee, arg, .. } => {
            refresh_global_var_types(callee, binding_types, shadowed);
            refresh_global_var_types(arg, binding_types, shadowed);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            refresh_global_var_types(cond, binding_types, shadowed);
            refresh_global_var_types(then_branch, binding_types, shadowed);
            refresh_global_var_types(else_branch, binding_types, shadowed);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                refresh_global_var_types(item, binding_types, shadowed);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                refresh_global_var_types(&mut field.value, binding_types, shadowed);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        refresh_global_var_types(expr, binding_types, shadowed);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                refresh_global_var_types(value, binding_types, shadowed);
            }
        }
        ExprKind::Select { base, .. } => refresh_global_var_types(base, binding_types, shadowed),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            refresh_global_var_types(scrutinee, binding_types, shadowed);
            for arm in arms {
                let saved = shadowed.clone();
                collect_pattern_bind_names(&arm.pattern, shadowed);
                if let Some(guard) = &mut arm.guard {
                    refresh_global_var_types(guard, binding_types, shadowed);
                }
                refresh_global_var_types(&mut arm.body, binding_types, shadowed);
                *shadowed = saved;
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = shadowed.clone();
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pattern, value } => {
                        refresh_global_var_types(value, binding_types, shadowed);
                        collect_pattern_bind_names(pattern, shadowed);
                    }
                    Stmt::Expr(expr) => refresh_global_var_types(expr, binding_types, shadowed),
                    Stmt::Module { def, body } => {
                        refresh_global_var_types(body, binding_types, shadowed);
                        if let [name] = def.segments.as_slice() {
                            shadowed.insert(name.clone());
                        }
                    }
                }
            }
            if let Some(tail) = tail {
                refresh_global_var_types(tail, binding_types, shadowed);
            }
            *shadowed = saved;
        }
        ExprKind::Handle { body, arms, .. } => {
            refresh_global_var_types(body, binding_types, shadowed);
            for arm in arms {
                let saved = shadowed.clone();
                collect_pattern_bind_names(&arm.payload, shadowed);
                if let Some(resume) = &arm.resume {
                    shadowed.insert(resume.name.clone());
                }
                if let Some(guard) = &mut arm.guard {
                    refresh_global_var_types(guard, binding_types, shadowed);
                }
                refresh_global_var_types(&mut arm.body, binding_types, shadowed);
                *shadowed = saved;
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => refresh_global_var_types(expr, binding_types, shadowed),
        ExprKind::LocalPushId { body, .. } => {
            refresh_global_var_types(body, binding_types, shadowed)
        }
        ExprKind::AddId { thunk, .. } => refresh_global_var_types(thunk, binding_types, shadowed),
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_pattern_bind_names(pattern: &Pattern, names: &mut BTreeSet<typed_ir::Name>) {
    match pattern {
        Pattern::Bind { name, .. } => {
            names.insert(name.clone());
        }
        Pattern::As { pattern, name, .. } => {
            collect_pattern_bind_names(pattern, names);
            names.insert(name.clone());
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_bind_names(item, names);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_bind_names(item, names);
            }
            if let Some(spread) = spread {
                collect_pattern_bind_names(spread, names);
            }
            for item in suffix {
                collect_pattern_bind_names(item, names);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_bind_names(&field.pattern, names);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_bind_names(pattern, names);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_bind_names(value, names);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_bind_names(left, names);
            collect_pattern_bind_names(right, names);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn path_is_shadowed(path: &typed_ir::Path, shadowed: &BTreeSet<typed_ir::Name>) -> bool {
    path.segments
        .as_slice()
        .first()
        .is_some_and(|name| path.segments.len() == 1 && shadowed.contains(name))
}

fn refresh_expr(expr: &mut Expr) {
    match &mut expr.kind {
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            refresh_expr(callee);
            refresh_expr(arg);
            if let Some(evidence) = evidence {
                let callee_ty = runtime_core_type(&callee.ty);
                let arg_ty = runtime_core_type(&arg.ty);
                let result_ty = runtime_core_type(&expr.ty);
                evidence.callee = typed_ir::TypeBounds::exact(callee_ty.clone());
                evidence.expected_callee = None;
                evidence.arg = typed_ir::TypeBounds::exact(arg_ty);
                evidence.expected_arg = None;
                evidence.result = typed_ir::TypeBounds::exact(result_ty);
                evidence.principal_callee = Some(callee_ty);
                evidence.substitutions = Vec::new();
                evidence.substitution_candidates = Vec::new();
                evidence.principal_elaboration = None;
            }
            // `instantiation` only describes the principal substitution
            // chosen at inference time. The arguments here are already
            // monomorphic Types, but their inner TypeVar payloads can be
            // stale; replace them with the resolved callee type so the
            // residual walker sees no var.
            if let Some(instantiation) = instantiation {
                let arg_ty = runtime_core_type(&arg.ty);
                instantiation.args = instantiation
                    .args
                    .iter()
                    .map(|substitution| crate::ir::TypeSubstitution {
                        var: substitution.var.clone(),
                        ty: arg_ty.clone(),
                    })
                    .collect();
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            refresh_expr(cond);
            refresh_expr(then_branch);
            refresh_expr(else_branch);
            if let Some(evidence) = evidence {
                evidence.result = runtime_core_type(&expr.ty);
            }
        }
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            refresh_expr(scrutinee);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    refresh_expr(guard);
                }
                refresh_expr(&mut arm.body);
            }
            evidence.result = runtime_core_type(&expr.ty);
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler: _,
        } => {
            refresh_expr(body);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    refresh_expr(guard);
                }
                refresh_expr(&mut arm.body);
            }
            evidence.result = runtime_core_type(&expr.ty);
        }
        ExprKind::Lambda { body, .. } => refresh_expr(body),
        ExprKind::Tuple(items) => {
            for item in items {
                refresh_expr(item);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                refresh_expr(&mut field.value);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        refresh_expr(expr);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                refresh_expr(value);
            }
        }
        ExprKind::Select { base, .. } => refresh_expr(base),
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                refresh_stmt(stmt);
            }
            if let Some(tail) = tail {
                refresh_expr(tail);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => refresh_expr(expr),
        ExprKind::LocalPushId { body, .. } => refresh_expr(body),
        ExprKind::AddId { thunk, .. } => refresh_expr(thunk),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn refresh_stmt(stmt: &mut Stmt) {
    match stmt {
        Stmt::Let { value, .. } => refresh_expr(value),
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => refresh_expr(expr),
    }
}
