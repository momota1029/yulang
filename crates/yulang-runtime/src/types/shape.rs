use super::*;

pub(crate) fn core_types_compatible(expected: &typed_ir::Type, actual: &typed_ir::Type) -> bool {
    if type_compatible(expected, actual) || (effect_is_empty(expected) && effect_is_empty(actual)) {
        return true;
    }
    match (expected, actual) {
        (
            typed_ir::Type::Fun {
                param: expected_param,
                ret: expected_ret,
                ..
            },
            typed_ir::Type::Fun {
                param: actual_param,
                ret: actual_ret,
                ..
            },
        ) => {
            core_types_compatible(expected_param, actual_param)
                && core_types_compatible(expected_ret, actual_ret)
        }
        _ => false,
    }
}

pub(crate) fn is_qualified_runtime_path(path: &typed_ir::Path) -> bool {
    path.segments.len() > 1
        || path
            .segments
            .first()
            .is_some_and(|segment| segment.0.contains("::"))
}

pub(crate) fn thunk_effect(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(effect.clone()),
        _ => None,
    }
}

pub(crate) fn is_nullary_constructor_path_for_type(
    path: &typed_ir::Path,
    ty: &RuntimeType,
) -> bool {
    let RuntimeType::Value(typed_ir::Type::Named {
        path: type_path, ..
    }) = ty
    else {
        return false;
    };
    path.segments.len() == type_path.segments.len() + 1
        && path
            .segments
            .iter()
            .zip(&type_path.segments)
            .all(|(left, right)| left == right)
}

pub(crate) fn hir_type_has_vars(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Value(ty) => core_type_has_vars(ty),
        RuntimeType::Fun { param, ret } => hir_type_has_vars(param) || hir_type_has_vars(ret),
        RuntimeType::Thunk { effect, value } => {
            core_type_has_vars(effect) || hir_type_has_vars(value)
        }
    }
}

pub(crate) fn core_type_has_vars(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    !vars.is_empty()
}

pub(crate) fn collect_expr_type_vars(expr: &Expr, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    collect_hir_type_vars(&expr.ty, vars);
    match &expr.kind {
        ExprKind::Lambda { body, .. } => collect_expr_type_vars(body, vars),
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            collect_expr_type_vars(callee, vars);
            collect_expr_type_vars(arg, vars);
            if let Some(evidence) = evidence {
                collect_apply_evidence_type_vars(evidence, vars);
            }
            if let Some(instantiation) = instantiation {
                collect_type_instantiation_type_vars(instantiation, vars);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            collect_expr_type_vars(cond, vars);
            collect_expr_type_vars(then_branch, vars);
            collect_expr_type_vars(else_branch, vars);
            if let Some(evidence) = evidence {
                collect_join_evidence_type_vars(evidence, vars);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_type_vars(item, vars);
            }
        }
        ExprKind::Record { fields, spread } => {
            for RecordExprField { value, .. } in fields {
                collect_expr_type_vars(value, vars);
            }
            collect_record_spread_expr_type_vars(spread, vars);
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_type_vars(value, vars);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_type_vars(base, vars),
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            collect_expr_type_vars(scrutinee, vars);
            for arm in arms {
                collect_match_arm_type_vars(arm, vars);
            }
            collect_join_evidence_type_vars(evidence, vars);
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_type_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_type_vars(tail, vars);
            }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            collect_expr_type_vars(body, vars);
            for arm in arms {
                collect_pattern_type_vars(&arm.payload, vars);
                if let Some(ResumeBinding { ty, .. }) = &arm.resume {
                    collect_hir_type_vars(ty, vars);
                }
                if let Some(guard) = &arm.guard {
                    collect_expr_type_vars(guard, vars);
                }
                collect_expr_type_vars(&arm.body, vars);
            }
            collect_join_evidence_type_vars(evidence, vars);
            collect_handle_effect_type_vars(handler, vars);
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => collect_expr_type_vars(expr, vars),
        ExprKind::LocalPushId { body, .. } => collect_expr_type_vars(body, vars),
        ExprKind::AddId { allowed, thunk, .. } => {
            collect_type_vars(allowed, vars);
            collect_expr_type_vars(thunk, vars);
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Var(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
    if let ExprKind::Thunk { effect, value, .. } = &expr.kind {
        collect_type_vars(effect, vars);
        collect_hir_type_vars(value, vars);
    }
    if let ExprKind::Coerce { from, to, .. } = &expr.kind {
        collect_type_vars(from, vars);
        collect_type_vars(to, vars);
    }
}

fn collect_apply_evidence_type_vars(
    evidence: &typed_ir::ApplyEvidence,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    collect_type_bounds_type_vars(&evidence.callee, vars);
    if let Some(expected) = &evidence.expected_callee {
        collect_type_bounds_type_vars(expected, vars);
    }
    collect_type_bounds_type_vars(&evidence.arg, vars);
    if let Some(expected) = &evidence.expected_arg {
        collect_type_bounds_type_vars(expected, vars);
    }
    collect_type_bounds_type_vars(&evidence.result, vars);
    if let Some(principal) = &evidence.principal_callee {
        collect_type_vars(principal, vars);
    }
    for substitution in &evidence.substitutions {
        collect_type_vars(&substitution.ty, vars);
    }
    if let Some(plan) = &evidence.principal_elaboration {
        collect_type_vars(&plan.principal_callee, vars);
        for substitution in &plan.substitutions {
            collect_type_vars(&substitution.ty, vars);
        }
    }
}

fn collect_type_bounds_type_vars(
    bounds: &typed_ir::TypeBounds,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_type_vars(upper, vars);
    }
}

fn collect_type_instantiation_type_vars(
    instantiation: &crate::ir::TypeInstantiation,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    for substitution in &instantiation.args {
        collect_type_vars(&substitution.ty, vars);
    }
}

fn collect_join_evidence_type_vars(
    evidence: &JoinEvidence,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    collect_type_vars(&evidence.result, vars);
}

fn collect_handle_effect_type_vars(
    handler: &crate::ir::HandleEffect,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(residual) = &handler.residual_before {
        collect_type_vars(residual, vars);
    }
    if let Some(residual) = &handler.residual_after {
        collect_type_vars(residual, vars);
    }
}

pub(crate) fn collect_stmt_type_vars(stmt: &Stmt, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match stmt {
        Stmt::Let { pattern, value } => {
            collect_pattern_type_vars(pattern, vars);
            collect_expr_type_vars(value, vars);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => collect_expr_type_vars(expr, vars),
    }
}

pub(crate) fn collect_pattern_type_vars(pattern: &Pattern, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => collect_hir_type_vars(ty, vars),
    }
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_type_vars(item, vars);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_type_vars(item, vars);
            }
            if let Some(spread) = spread {
                collect_pattern_type_vars(spread, vars);
            }
            for item in suffix {
                collect_pattern_type_vars(item, vars);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for RecordPatternField {
                pattern, default, ..
            } in fields
            {
                collect_pattern_type_vars(pattern, vars);
                if let Some(default) = default {
                    collect_expr_type_vars(default, vars);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_type_vars(pattern, vars);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_type_vars(value, vars);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_type_vars(left, vars);
            collect_pattern_type_vars(right, vars);
        }
        Pattern::As { pattern, .. } => collect_pattern_type_vars(pattern, vars),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
}

pub(crate) fn collect_hir_type_vars(ty: &RuntimeType, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        RuntimeType::Unknown => {}
        RuntimeType::Value(ty) => collect_type_vars(ty, vars),
        RuntimeType::Fun { param, ret } => {
            collect_hir_type_vars(param, vars);
            collect_hir_type_vars(ret, vars);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_type_vars(effect, vars);
            collect_hir_type_vars(value, vars);
        }
    }
}

fn collect_match_arm_type_vars(arm: &MatchArm, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    collect_pattern_type_vars(&arm.pattern, vars);
    if let Some(guard) = &arm.guard {
        collect_expr_type_vars(guard, vars);
    }
    collect_expr_type_vars(&arm.body, vars);
}

fn collect_record_spread_expr_type_vars(
    spread: &Option<RecordSpreadExpr>,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    if let Some(spread) = spread {
        match spread {
            RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                collect_expr_type_vars(expr, vars);
            }
        }
    }
}
