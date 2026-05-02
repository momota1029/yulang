use super::*;

pub(crate) fn core_types_compatible(expected: &core_ir::Type, actual: &core_ir::Type) -> bool {
    if type_compatible(expected, actual) || (effect_is_empty(expected) && effect_is_empty(actual)) {
        return true;
    }
    match (expected, actual) {
        (
            core_ir::Type::Fun {
                param: expected_param,
                ret: expected_ret,
                ..
            },
            core_ir::Type::Fun {
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

pub(crate) fn is_qualified_runtime_path(path: &core_ir::Path) -> bool {
    path.segments.len() > 1
        || path
            .segments
            .first()
            .is_some_and(|segment| segment.0.contains("::"))
}

pub(crate) fn thunk_effect(ty: &RuntimeType) -> Option<core_ir::Type> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(effect.clone()),
        _ => None,
    }
}

pub(crate) fn is_nullary_constructor_path_for_type(path: &core_ir::Path, ty: &RuntimeType) -> bool {
    let RuntimeType::Core(core_ir::Type::Named {
        path: type_path, ..
    }) = ty
    else {
        return false;
    };
    path.segments.len() == type_path.segments.len() + 1
        && path.segments.last().is_some_and(|name| name.0 == "nil")
        && path
            .segments
            .iter()
            .zip(&type_path.segments)
            .all(|(left, right)| left == right)
}

pub(crate) fn hir_type_has_vars(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Core(ty) => core_type_has_vars(ty),
        RuntimeType::Fun { param, ret } => hir_type_has_vars(param) || hir_type_has_vars(ret),
        RuntimeType::Thunk { effect, value } => {
            core_type_has_vars(effect) || hir_type_has_vars(value)
        }
    }
}

pub(crate) fn core_type_has_vars(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Var(_) => true,
        core_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            core_ir::TypeArg::Type(ty) => core_type_has_vars(ty),
            core_ir::TypeArg::Bounds(bounds) => {
                bounds.lower.as_deref().is_some_and(core_type_has_vars)
                    || bounds.upper.as_deref().is_some_and(core_type_has_vars)
            }
        }),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_has_vars(param)
                || core_type_has_vars(param_effect)
                || core_type_has_vars(ret_effect)
                || core_type_has_vars(ret)
        }
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(core_type_has_vars)
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_has_vars(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        core_type_has_vars(ty)
                    }
                })
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .any(core_type_has_vars)
                || variant.tail.as_deref().is_some_and(core_type_has_vars)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_has_vars) || core_type_has_vars(tail)
        }
        core_ir::Type::Recursive { body, .. } => core_type_has_vars(body),
        core_ir::Type::Never | core_ir::Type::Any => false,
    }
}

pub(crate) fn collect_expr_type_vars(expr: &Expr, vars: &mut BTreeSet<core_ir::TypeVar>) {
    collect_hir_type_vars(&expr.ty, vars);
    match &expr.kind {
        ExprKind::Lambda { body, .. } => collect_expr_type_vars(body, vars),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_type_vars(callee, vars);
            collect_expr_type_vars(arg, vars);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_type_vars(cond, vars);
            collect_expr_type_vars(then_branch, vars);
            collect_expr_type_vars(else_branch, vars);
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
            scrutinee, arms, ..
        } => {
            collect_expr_type_vars(scrutinee, vars);
            for arm in arms {
                collect_match_arm_type_vars(arm, vars);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_type_vars(stmt, vars);
            }
            if let Some(tail) = tail {
                collect_expr_type_vars(tail, vars);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
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
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => collect_expr_type_vars(expr, vars),
        ExprKind::LocalPushId { body, .. } => collect_expr_type_vars(body, vars),
        ExprKind::AddId { thunk, .. } => collect_expr_type_vars(thunk, vars),
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

pub(crate) fn collect_stmt_type_vars(stmt: &Stmt, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match stmt {
        Stmt::Let { pattern, value } => {
            collect_pattern_type_vars(pattern, vars);
            collect_expr_type_vars(value, vars);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => collect_expr_type_vars(expr, vars),
    }
}

pub(crate) fn collect_pattern_type_vars(pattern: &Pattern, vars: &mut BTreeSet<core_ir::TypeVar>) {
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

pub(crate) fn collect_hir_type_vars(ty: &RuntimeType, vars: &mut BTreeSet<core_ir::TypeVar>) {
    match ty {
        RuntimeType::Core(ty) => collect_type_vars(ty, vars),
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

fn collect_match_arm_type_vars(arm: &MatchArm, vars: &mut BTreeSet<core_ir::TypeVar>) {
    collect_pattern_type_vars(&arm.pattern, vars);
    if let Some(guard) = &arm.guard {
        collect_expr_type_vars(guard, vars);
    }
    collect_expr_type_vars(&arm.body, vars);
}

fn collect_record_spread_expr_type_vars(
    spread: &Option<RecordSpreadExpr>,
    vars: &mut BTreeSet<core_ir::TypeVar>,
) {
    if let Some(spread) = spread {
        match spread {
            RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                collect_expr_type_vars(expr, vars);
            }
        }
    }
}
