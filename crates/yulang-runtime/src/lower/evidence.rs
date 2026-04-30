use super::*;

pub(super) fn infer_handle_payload_type(
    pattern: &core_ir::Pattern,
    guard: Option<&core_ir::Expr>,
    body: &core_ir::Expr,
    result_ty: &core_ir::Type,
) -> Option<core_ir::Type> {
    let name = single_bound_name(pattern)?;
    guard
        .and_then(|guard| infer_local_expected_type(&name, guard, &bool_type()))
        .or_else(|| infer_local_expected_type(&name, body, result_ty))
}

pub(super) fn single_bound_name(pattern: &core_ir::Pattern) -> Option<core_ir::Name> {
    match pattern {
        core_ir::Pattern::Bind(name) => Some(name.clone()),
        core_ir::Pattern::As { name, .. } => Some(name.clone()),
        _ => None,
    }
}

pub(super) fn infer_local_expected_type(
    name: &core_ir::Name,
    expr: &core_ir::Expr,
    expected: &core_ir::Type,
) -> Option<core_ir::Type> {
    match expr {
        core_ir::Expr::Var(path) if path.segments.as_slice() == std::slice::from_ref(name) => {
            Some(expected.clone())
        }
        core_ir::Expr::Coerce { expr } | core_ir::Expr::Pack { expr, .. } => {
            infer_local_expected_type(name, expr, expected)
        }
        core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => infer_local_expected_type(name, cond, &bool_type())
            .or_else(|| infer_local_expected_type(name, then_branch, expected))
            .or_else(|| infer_local_expected_type(name, else_branch, expected)),
        core_ir::Expr::Match { arms, .. } => arms.iter().find_map(|arm| {
            arm.guard
                .as_ref()
                .and_then(|guard| infer_local_expected_type(name, guard, &bool_type()))
                .or_else(|| infer_local_expected_type(name, &arm.body, expected))
        }),
        core_ir::Expr::Block { tail, .. } => tail
            .as_deref()
            .and_then(|tail| infer_local_expected_type(name, tail, expected)),
        core_ir::Expr::Handle { arms, .. } => arms.iter().find_map(|arm| {
            arm.guard
                .as_ref()
                .and_then(|guard| infer_local_expected_type(name, guard, &bool_type()))
                .or_else(|| infer_local_expected_type(name, &arm.body, expected))
        }),
        _ => None,
    }
}

pub(super) fn infer_resume_param_type(
    resume: &core_ir::Name,
    guard: Option<&core_ir::Expr>,
    body: &core_ir::Expr,
) -> Option<core_ir::Type> {
    guard
        .and_then(|guard| infer_resume_param_type_from_expr(resume, guard))
        .or_else(|| infer_resume_param_type_from_expr(resume, body))
}

pub(super) fn infer_resume_param_type_from_expr(
    resume: &core_ir::Name,
    expr: &core_ir::Expr,
) -> Option<core_ir::Type> {
    match expr {
        core_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            if is_resume_call(resume, callee) {
                return evidence
                    .as_ref()
                    .and_then(|evidence| runtime_bounds_type(&evidence.arg))
                    .or_else(|| literal_expr_type(arg));
            }
            infer_resume_param_type_from_expr(resume, callee)
                .or_else(|| infer_resume_param_type_from_expr(resume, arg))
        }
        core_ir::Expr::Lambda { body, .. }
        | core_ir::Expr::Coerce { expr: body }
        | core_ir::Expr::Pack { expr: body, .. } => infer_resume_param_type_from_expr(resume, body),
        core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => infer_resume_param_type_from_expr(resume, cond)
            .or_else(|| infer_resume_param_type_from_expr(resume, then_branch))
            .or_else(|| infer_resume_param_type_from_expr(resume, else_branch)),
        core_ir::Expr::Tuple(items) => items
            .iter()
            .find_map(|item| infer_resume_param_type_from_expr(resume, item)),
        core_ir::Expr::Record { fields, spread } => fields
            .iter()
            .find_map(|field| infer_resume_param_type_from_expr(resume, &field.value))
            .or_else(|| match spread {
                Some(core_ir::RecordSpreadExpr::Head(expr))
                | Some(core_ir::RecordSpreadExpr::Tail(expr)) => {
                    infer_resume_param_type_from_expr(resume, expr)
                }
                None => None,
            }),
        core_ir::Expr::Variant { value, .. } => value
            .as_deref()
            .and_then(|value| infer_resume_param_type_from_expr(resume, value)),
        core_ir::Expr::Select { base, .. } => infer_resume_param_type_from_expr(resume, base),
        core_ir::Expr::Match {
            scrutinee, arms, ..
        } => infer_resume_param_type_from_expr(resume, scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| infer_resume_param_type_from_expr(resume, guard))
                    .or_else(|| infer_resume_param_type_from_expr(resume, &arm.body))
            })
        }),
        core_ir::Expr::Block { stmts, tail } => stmts
            .iter()
            .find_map(|stmt| infer_resume_param_type_from_stmt(resume, stmt))
            .or_else(|| {
                tail.as_deref()
                    .and_then(|tail| infer_resume_param_type_from_expr(resume, tail))
            }),
        core_ir::Expr::Handle { body, arms, .. } => infer_resume_param_type_from_expr(resume, body)
            .or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| infer_resume_param_type_from_expr(resume, guard))
                        .or_else(|| infer_resume_param_type_from_expr(resume, &arm.body))
                })
            }),
        core_ir::Expr::Var(_) | core_ir::Expr::PrimitiveOp(_) | core_ir::Expr::Lit(_) => None,
    }
}

pub(super) fn infer_resume_param_type_from_stmt(
    resume: &core_ir::Name,
    stmt: &core_ir::Stmt,
) -> Option<core_ir::Type> {
    match stmt {
        core_ir::Stmt::Let { value, .. } | core_ir::Stmt::Expr(value) => {
            infer_resume_param_type_from_expr(resume, value)
        }
        core_ir::Stmt::Module { body, .. } => infer_resume_param_type_from_expr(resume, body),
    }
}

pub(super) fn is_resume_call(resume: &core_ir::Name, callee: &core_ir::Expr) -> bool {
    match callee {
        core_ir::Expr::Var(path) => path.segments.as_slice() == std::slice::from_ref(resume),
        core_ir::Expr::Coerce { expr } | core_ir::Expr::Pack { expr, .. } => {
            is_resume_call(resume, expr)
        }
        _ => false,
    }
}

pub(super) fn literal_expr_type(expr: &core_ir::Expr) -> Option<core_ir::Type> {
    match expr {
        core_ir::Expr::Lit(lit) => Some(lit_type(lit)),
        core_ir::Expr::Coerce { expr } | core_ir::Expr::Pack { expr, .. } => {
            literal_expr_type(expr)
        }
        _ => None,
    }
}
