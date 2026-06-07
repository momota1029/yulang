//! Local variable type refresh after materialization.
//!
//! Materialization can specialize a lambda parameter from a plain value into a
//! thunk.  Local references inside the body must then see the specialized
//! parameter type, and value-only sites such as select/coerce operands must
//! force it explicitly.

use std::collections::HashMap;

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, FinalizedPattern as Pattern,
    FinalizedRecordSpreadExpr, FinalizedRecordSpreadPattern, FinalizedStmt, RuntimeType,
};
use yulang_typed_ir as typed_ir;

use super::materialize::force_core_value_expr;
use super::pattern_types::{
    choose_pattern_ty, record_field_runtime_type, tuple_component_runtime_types,
    variant_payload_runtime_type,
};

pub(crate) fn refresh_local_expr_types(expr: Expr) -> Expr {
    let mut locals = HashMap::new();
    refresh_expr_local_types(expr, &mut locals)
}

fn refresh_expr_local_types(expr: Expr, locals: &mut HashMap<typed_ir::Path, RuntimeType>) -> Expr {
    let mut ty = expr.ty;
    let kind = match expr.kind {
        ExprKind::Var(path) => {
            if let Some(local_ty) = locals.get(&path) {
                ty = local_ty.clone();
            }
            ExprKind::Var(path)
        }
        ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit),
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let path = super::path_from_name(&param);
            let previous = runtime_function_param(&ty).map(|param_ty| {
                let previous = locals.insert(path.clone(), param_ty);
                (path.clone(), previous)
            });
            let body = Box::new(refresh_expr_local_types(*body, locals));
            if let Some((path, previous)) = previous {
                restore_local(locals, path, previous);
            }
            ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            }
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(refresh_expr_local_types(*callee, locals)),
            arg: Box::new(refresh_expr_local_types(*arg, locals)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(refresh_expr_local_types(*cond, locals)),
            then_branch: Box::new(refresh_expr_local_types(*then_branch, locals)),
            else_branch: Box::new(refresh_expr_local_types(*else_branch, locals)),
            evidence,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| refresh_expr_local_types(item, locals))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::FinalizedRecordExprField {
                    name: field.name,
                    value: refresh_expr_local_types(field.value, locals),
                })
                .collect(),
            spread: spread.map(|spread| refresh_record_spread_expr_local_types(spread, locals)),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(refresh_expr_local_types(*value, locals))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(refresh_core_value_expr_local_types(*base, locals)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            let scrutinee = refresh_expr_local_types(*scrutinee, locals);
            let scrutinee_ty = scrutinee.ty.clone();
            ExprKind::Match {
                scrutinee: Box::new(scrutinee),
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        let mut arm_locals = locals.clone();
                        refresh_pattern_local_types(
                            &arm.pattern,
                            Some(&scrutinee_ty),
                            &mut arm_locals,
                        );
                        yulang_runtime_ir::FinalizedMatchArm {
                            pattern: arm.pattern,
                            guard: arm
                                .guard
                                .map(|guard| refresh_expr_local_types(guard, &mut arm_locals)),
                            body: refresh_expr_local_types(arm.body, &mut arm_locals),
                        }
                    })
                    .collect(),
                evidence,
            }
        }
        ExprKind::Block { stmts, tail } => {
            let saved = locals.clone();
            let stmts = stmts
                .into_iter()
                .map(|stmt| refresh_stmt_local_types(stmt, locals))
                .collect();
            let tail = tail.map(|tail| Box::new(refresh_expr_local_types(*tail, locals)));
            *locals = saved;
            ExprKind::Block { stmts, tail }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(refresh_expr_local_types(*body, locals)),
            arms: arms
                .into_iter()
                .map(|arm| {
                    let mut arm_locals = locals.clone();
                    refresh_pattern_local_types(&arm.payload, None, &mut arm_locals);
                    if let Some(resume) = &arm.resume {
                        arm_locals.insert(super::path_from_name(&resume.name), resume.ty.clone());
                    }
                    yulang_runtime_ir::FinalizedHandleArm {
                        effect: arm.effect,
                        payload: arm.payload,
                        resume: arm.resume,
                        guard: arm
                            .guard
                            .map(|guard| refresh_expr_local_types(guard, &mut arm_locals)),
                        body: refresh_expr_local_types(arm.body, &mut arm_locals),
                    }
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value,
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(refresh_expr_local_types(*body, locals)),
        },
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(refresh_expr_local_types(*thunk, locals)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(refresh_core_value_expr_local_types(*expr, locals)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(refresh_expr_local_types(*expr, locals)),
        },
    };
    Expr::typed(kind, ty)
}

fn refresh_stmt_local_types(
    stmt: FinalizedStmt,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> FinalizedStmt {
    match stmt {
        FinalizedStmt::Let { pattern, value } => {
            let value = refresh_expr_local_types(value, locals);
            refresh_pattern_local_types(&pattern, Some(&value.ty), locals);
            FinalizedStmt::Let { pattern, value }
        }
        FinalizedStmt::Expr(expr) => FinalizedStmt::Expr(refresh_expr_local_types(expr, locals)),
        FinalizedStmt::Module { def, body } => FinalizedStmt::Module {
            def,
            body: refresh_expr_local_types(body, locals),
        },
    }
}

fn refresh_record_spread_expr_local_types(
    spread: FinalizedRecordSpreadExpr,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> FinalizedRecordSpreadExpr {
    match spread {
        FinalizedRecordSpreadExpr::Head(expr) => FinalizedRecordSpreadExpr::Head(Box::new(
            refresh_core_value_expr_local_types(*expr, locals),
        )),
        FinalizedRecordSpreadExpr::Tail(expr) => FinalizedRecordSpreadExpr::Tail(Box::new(
            refresh_core_value_expr_local_types(*expr, locals),
        )),
    }
}

fn refresh_pattern_local_types(
    pattern: &Pattern,
    scrutinee_ty: Option<&RuntimeType>,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) {
    match pattern {
        Pattern::Bind { name, ty } => {
            locals.insert(
                super::path_from_name(name),
                choose_pattern_ty(ty, scrutinee_ty),
            );
        }
        Pattern::Tuple { items, ty } => {
            let component_tys = tuple_component_runtime_types(scrutinee_ty, ty, items.len());
            for (item, comp) in items.iter().zip(component_tys.iter()) {
                refresh_pattern_local_types(item, comp.as_ref(), locals);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                refresh_pattern_local_types(item, None, locals);
            }
            if let Some(spread) = spread {
                refresh_pattern_local_types(spread, None, locals);
            }
            for item in suffix {
                refresh_pattern_local_types(item, None, locals);
            }
        }
        Pattern::Record { fields, spread, ty } => {
            for field in fields {
                let field_ty = record_field_runtime_type(scrutinee_ty, ty, &field.name);
                refresh_pattern_local_types(&field.pattern, field_ty.as_ref(), locals);
            }
            if let Some(spread) = spread {
                match spread {
                    FinalizedRecordSpreadPattern::Head(pattern)
                    | FinalizedRecordSpreadPattern::Tail(pattern) => {
                        refresh_pattern_local_types(pattern, None, locals);
                    }
                }
            }
        }
        Pattern::Variant { tag, value, ty } => {
            if let Some(value) = value {
                let payload_ty = variant_payload_runtime_type(scrutinee_ty, ty, tag);
                refresh_pattern_local_types(value, payload_ty.as_ref(), locals);
            }
        }
        Pattern::Or { left, right, .. } => {
            refresh_pattern_local_types(left, scrutinee_ty, locals);
            refresh_pattern_local_types(right, scrutinee_ty, locals);
        }
        Pattern::As { pattern, name, ty } => {
            let chosen = choose_pattern_ty(ty, scrutinee_ty);
            refresh_pattern_local_types(pattern, Some(&chosen), locals);
            locals.insert(super::path_from_name(name), chosen);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn runtime_function_param(ty: &RuntimeType) -> Option<RuntimeType> {
    let RuntimeType::Fun { param, .. } = ty else {
        return None;
    };
    Some((**param).clone())
}

fn restore_local(
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
    path: typed_ir::Path,
    previous: Option<RuntimeType>,
) {
    match previous {
        Some(previous) => {
            locals.insert(path, previous);
        }
        None => {
            locals.remove(&path);
        }
    }
}

fn refresh_core_value_expr_local_types(
    expr: Expr,
    locals: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> Expr {
    force_core_value_expr(refresh_expr_local_types(expr, locals))
}
