use super::*;
use yulang_runtime_types::types::core_type_contains_unknown;

pub(super) fn infer_handle_payload_type(
    primitive_paths: &RuntimePrimitivePathTable,
    pattern: &typed_ir::Pattern,
    guard: Option<&typed_ir::Expr>,
    body: &typed_ir::Expr,
    result_ty: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    infer_handle_payload_pattern_type(primitive_paths, pattern, guard, body, result_ty)
}

fn infer_handle_payload_pattern_type(
    primitive_paths: &RuntimePrimitivePathTable,
    pattern: &typed_ir::Pattern,
    guard: Option<&typed_ir::Expr>,
    body: &typed_ir::Expr,
    result_ty: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    match pattern {
        typed_ir::Pattern::Bind(name) => guard
            .and_then(|guard| {
                infer_local_expected_type(
                    primitive_paths,
                    name,
                    guard,
                    &primitive_paths.bool_type(),
                )
            })
            .or_else(|| infer_local_expected_type(primitive_paths, name, body, result_ty)),
        typed_ir::Pattern::As { pattern, name } => guard
            .and_then(|guard| {
                infer_local_expected_type(
                    primitive_paths,
                    name,
                    guard,
                    &primitive_paths.bool_type(),
                )
            })
            .or_else(|| infer_local_expected_type(primitive_paths, name, body, result_ty))
            .or_else(|| {
                infer_handle_payload_pattern_type(primitive_paths, pattern, guard, body, result_ty)
            }),
        typed_ir::Pattern::Tuple(items) => Some(typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| {
                    infer_handle_payload_pattern_type(primitive_paths, item, guard, body, result_ty)
                        .unwrap_or(typed_ir::Type::Unknown)
                })
                .collect(),
        )),
        _ => None,
    }
}

pub(super) fn single_bound_name(pattern: &typed_ir::Pattern) -> Option<typed_ir::Name> {
    match pattern {
        typed_ir::Pattern::Bind(name) => Some(name.clone()),
        typed_ir::Pattern::As { name, .. } => Some(name.clone()),
        _ => None,
    }
}

pub(super) fn infer_local_expected_type(
    primitive_paths: &RuntimePrimitivePathTable,
    name: &typed_ir::Name,
    expr: &typed_ir::Expr,
    expected: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    match expr {
        typed_ir::Expr::Var(path) if path.segments.as_slice() == std::slice::from_ref(name) => {
            Some(expected.clone())
        }
        typed_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            let arg_expected = evidence
                .as_ref()
                .and_then(|evidence| {
                    evidence
                        .expected_arg
                        .as_ref()
                        .and_then(runtime_bounds_type)
                        .or_else(|| runtime_bounds_type(&evidence.arg))
                })
                .unwrap_or(typed_ir::Type::Unknown);
            infer_local_expected_type(primitive_paths, name, arg, &arg_expected).or_else(|| {
                let callee_expected = typed_ir::Type::Fun {
                    param: Box::new(arg_expected),
                    param_effect: Box::new(typed_ir::Type::Any),
                    ret_effect: Box::new(typed_ir::Type::Any),
                    ret: Box::new(expected.clone()),
                };
                infer_local_expected_type(primitive_paths, name, callee, &callee_expected)
            })
        }
        typed_ir::Expr::Coerce { expr, .. } | typed_ir::Expr::Pack { expr, .. } => {
            infer_local_expected_type(primitive_paths, name, expr, expected)
        }
        typed_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => infer_local_expected_type(primitive_paths, name, cond, &primitive_paths.bool_type())
            .or_else(|| infer_local_expected_type(primitive_paths, name, then_branch, expected))
            .or_else(|| infer_local_expected_type(primitive_paths, name, else_branch, expected)),
        typed_ir::Expr::Match { arms, .. } => arms.iter().find_map(|arm| {
            arm.guard
                .as_ref()
                .and_then(|guard| {
                    infer_local_expected_type(
                        primitive_paths,
                        name,
                        guard,
                        &primitive_paths.bool_type(),
                    )
                })
                .or_else(|| infer_local_expected_type(primitive_paths, name, &arm.body, expected))
        }),
        typed_ir::Expr::Block { stmts, tail } => stmts
            .iter()
            .find_map(|stmt| infer_local_expected_type_from_stmt(primitive_paths, name, stmt))
            .or_else(|| {
                tail.as_deref().and_then(|tail| {
                    infer_local_expected_type(primitive_paths, name, tail, expected)
                })
            }),
        typed_ir::Expr::Handle { arms, .. } => arms.iter().find_map(|arm| {
            arm.guard
                .as_ref()
                .and_then(|guard| {
                    infer_local_expected_type(
                        primitive_paths,
                        name,
                        guard,
                        &primitive_paths.bool_type(),
                    )
                })
                .or_else(|| infer_local_expected_type(primitive_paths, name, &arm.body, expected))
        }),
        _ => None,
    }
}

fn infer_local_expected_type_from_stmt(
    primitive_paths: &RuntimePrimitivePathTable,
    name: &typed_ir::Name,
    stmt: &typed_ir::Stmt,
) -> Option<typed_ir::Type> {
    match stmt {
        typed_ir::Stmt::Let { value, .. } | typed_ir::Stmt::Expr(value) => {
            infer_local_expected_type(primitive_paths, name, value, &typed_ir::Type::Unknown)
        }
        typed_ir::Stmt::Module { body, .. } => {
            infer_local_expected_type(primitive_paths, name, body, &typed_ir::Type::Unknown)
        }
    }
}

pub(super) fn infer_resume_param_type(
    primitive_paths: &RuntimePrimitivePathTable,
    resume: &typed_ir::Name,
    guard: Option<&typed_ir::Expr>,
    body: &typed_ir::Expr,
    locals: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<typed_ir::Type> {
    guard
        .and_then(|guard| infer_resume_param_type_from_expr(primitive_paths, resume, guard, locals))
        .or_else(|| infer_resume_param_type_from_expr(primitive_paths, resume, body, locals))
}

pub(super) fn infer_resume_param_type_from_expr(
    primitive_paths: &RuntimePrimitivePathTable,
    resume: &typed_ir::Name,
    expr: &typed_ir::Expr,
    locals: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<typed_ir::Type> {
    match expr {
        typed_ir::Expr::Apply {
            callee,
            arg,
            evidence,
        } => {
            if is_resume_call(resume, callee) {
                return evidence
                    .as_ref()
                    .and_then(|evidence| runtime_bounds_type(&evidence.arg))
                    .or_else(|| local_expr_type(arg, locals))
                    .or_else(|| literal_expr_type(primitive_paths, arg));
            }
            infer_resume_param_type_from_expr(primitive_paths, resume, callee, locals)
                .or_else(|| infer_resume_param_type_from_expr(primitive_paths, resume, arg, locals))
        }
        typed_ir::Expr::Lambda { body, .. }
        | typed_ir::Expr::Coerce { expr: body, .. }
        | typed_ir::Expr::BindHere { expr: body }
        | typed_ir::Expr::Pack { expr: body, .. } => {
            infer_resume_param_type_from_expr(primitive_paths, resume, body, locals)
        }
        typed_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => infer_resume_param_type_from_expr(primitive_paths, resume, cond, locals)
            .or_else(|| {
                infer_resume_param_type_from_expr(primitive_paths, resume, then_branch, locals)
            })
            .or_else(|| {
                infer_resume_param_type_from_expr(primitive_paths, resume, else_branch, locals)
            }),
        typed_ir::Expr::Tuple(items) => items.iter().find_map(|item| {
            infer_resume_param_type_from_expr(primitive_paths, resume, item, locals)
        }),
        typed_ir::Expr::Record { fields, spread } => fields
            .iter()
            .find_map(|field| {
                infer_resume_param_type_from_expr(primitive_paths, resume, &field.value, locals)
            })
            .or_else(|| match spread {
                Some(typed_ir::RecordSpreadExpr::Head(expr))
                | Some(typed_ir::RecordSpreadExpr::Tail(expr)) => {
                    infer_resume_param_type_from_expr(primitive_paths, resume, expr, locals)
                }
                None => None,
            }),
        typed_ir::Expr::Variant { value, .. } => value.as_deref().and_then(|value| {
            infer_resume_param_type_from_expr(primitive_paths, resume, value, locals)
        }),
        typed_ir::Expr::Select { base, .. } => {
            infer_resume_param_type_from_expr(primitive_paths, resume, base, locals)
        }
        typed_ir::Expr::Match {
            scrutinee, arms, ..
        } => infer_resume_param_type_from_expr(primitive_paths, resume, scrutinee, locals).or_else(
            || {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| {
                            infer_resume_param_type_from_expr(
                                primitive_paths,
                                resume,
                                guard,
                                locals,
                            )
                        })
                        .or_else(|| {
                            infer_resume_param_type_from_expr(
                                primitive_paths,
                                resume,
                                &arm.body,
                                locals,
                            )
                        })
                })
            },
        ),
        typed_ir::Expr::Block { stmts, tail } => stmts
            .iter()
            .find_map(|stmt| {
                infer_resume_param_type_from_stmt(primitive_paths, resume, stmt, locals)
            })
            .or_else(|| {
                tail.as_deref().and_then(|tail| {
                    infer_resume_param_type_from_expr(primitive_paths, resume, tail, locals)
                })
            }),
        typed_ir::Expr::Handle { body, arms, .. } => {
            infer_resume_param_type_from_expr(primitive_paths, resume, body, locals).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| {
                            infer_resume_param_type_from_expr(
                                primitive_paths,
                                resume,
                                guard,
                                locals,
                            )
                        })
                        .or_else(|| {
                            infer_resume_param_type_from_expr(
                                primitive_paths,
                                resume,
                                &arm.body,
                                locals,
                            )
                        })
                })
            })
        }
        typed_ir::Expr::Var(_) | typed_ir::Expr::PrimitiveOp(_) | typed_ir::Expr::Lit(_) => None,
    }
}

pub(super) fn infer_resume_param_type_from_stmt(
    primitive_paths: &RuntimePrimitivePathTable,
    resume: &typed_ir::Name,
    stmt: &typed_ir::Stmt,
    locals: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<typed_ir::Type> {
    match stmt {
        typed_ir::Stmt::Let { value, .. } | typed_ir::Stmt::Expr(value) => {
            infer_resume_param_type_from_expr(primitive_paths, resume, value, locals)
        }
        typed_ir::Stmt::Module { body, .. } => {
            infer_resume_param_type_from_expr(primitive_paths, resume, body, locals)
        }
    }
}

pub(super) fn is_resume_call(resume: &typed_ir::Name, callee: &typed_ir::Expr) -> bool {
    match callee {
        typed_ir::Expr::Var(path) => path.segments.as_slice() == std::slice::from_ref(resume),
        typed_ir::Expr::Coerce { expr, .. } | typed_ir::Expr::Pack { expr, .. } => {
            is_resume_call(resume, expr)
        }
        _ => false,
    }
}

pub(super) fn literal_expr_type(
    primitive_paths: &RuntimePrimitivePathTable,
    expr: &typed_ir::Expr,
) -> Option<typed_ir::Type> {
    match expr {
        typed_ir::Expr::Lit(lit) => Some(primitive_paths.lit_type(lit)),
        typed_ir::Expr::Coerce { expr, .. } | typed_ir::Expr::Pack { expr, .. } => {
            literal_expr_type(primitive_paths, expr)
        }
        _ => None,
    }
}

fn local_expr_type(
    expr: &typed_ir::Expr,
    locals: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<typed_ir::Type> {
    match expr {
        typed_ir::Expr::Var(path) => locals.get(path).and_then(runtime_type_value_core),
        typed_ir::Expr::Coerce { expr, .. } | typed_ir::Expr::Pack { expr, .. } => {
            local_expr_type(expr, locals)
        }
        _ => None,
    }
}

fn runtime_type_value_core(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Value(ty) if !core_type_contains_unknown(ty) => Some(ty.clone()),
        RuntimeType::Thunk { value, .. } => runtime_type_value_core(value),
        RuntimeType::Fun { .. } | RuntimeType::Unknown | RuntimeType::Value(_) => None,
    }
}
