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
    for binding in &mut module.bindings {
        refresh_expr(&mut binding.body);
    }
    for root in &mut module.root_exprs {
        refresh_expr(root);
    }
    module
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
