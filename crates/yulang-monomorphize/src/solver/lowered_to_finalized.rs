//! Convert lowered runtime IR into the finalized-runtime shape.
//!
//! This is a structural conversion used before monomorphization starts. The
//! solver owns specialization; this module only lifts lowered core-value types
//! into runtime types.

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, FinalizedModule as Module, LoweredExpr,
    LoweredExprKind, LoweredModule, LoweredPattern, LoweredRecordSpreadExpr,
    LoweredRecordSpreadPattern, LoweredStmt, RuntimeType,
};

use crate::graph::runtime_type_from_core_value;

/// Effect ops carry their declared signature `Fun(Value(t), Value(unit))` and
/// the call-site effect row is tracked separately in evidence/payload, so we
/// strip Thunk wraps from the op's own Expr.ty. Handlers receive payloads
/// eagerly; wrapping the op's param/ret in Thunk would force every effect call
/// through `force_apply_arg`, which can leak inner effects past the handler's
/// continuation scope.
fn strip_effect_op_thunk_wrap(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Thunk { value, .. } => strip_effect_op_thunk_wrap(*value),
        RuntimeType::Fun { param, ret } => RuntimeType::Fun {
            param: Box::new(strip_effect_op_thunk_wrap(*param)),
            ret: Box::new(strip_effect_op_thunk_wrap(*ret)),
        },
        RuntimeType::Value(_) | RuntimeType::Unknown => ty,
    }
}

pub(crate) fn from_lowered_module(module: LoweredModule) -> Module {
    yulang_runtime_ir::Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(|binding| yulang_runtime_ir::Binding {
                name: binding.name,
                type_params: binding.type_params,
                scheme: binding.scheme,
                body: from_lowered_expr(binding.body),
            })
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(from_lowered_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn from_lowered_expr(expr: LoweredExpr) -> Expr {
    let raw_ty = runtime_type_from_core_value(expr.ty);
    let ty = if matches!(expr.kind, LoweredExprKind::EffectOp(_)) {
        strip_effect_op_thunk_wrap(raw_ty)
    } else {
        raw_ty
    };
    let kind = match expr.kind {
        LoweredExprKind::Var(path) => ExprKind::Var(path),
        LoweredExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        LoweredExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        LoweredExprKind::Lit(lit) => ExprKind::Lit(lit),
        LoweredExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(from_lowered_expr(*body)),
        },
        LoweredExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(from_lowered_expr(*callee)),
            arg: Box::new(from_lowered_expr(*arg)),
            evidence,
            instantiation,
        },
        LoweredExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(from_lowered_expr(*cond)),
            then_branch: Box::new(from_lowered_expr(*then_branch)),
            else_branch: Box::new(from_lowered_expr(*else_branch)),
            evidence,
        },
        LoweredExprKind::Tuple(items) => {
            ExprKind::Tuple(items.into_iter().map(from_lowered_expr).collect())
        }
        LoweredExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordExprField {
                    name: field.name,
                    value: from_lowered_expr(field.value),
                })
                .collect(),
            spread: spread.map(from_lowered_record_spread_expr),
        },
        LoweredExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(from_lowered_expr(*value))),
        },
        LoweredExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(from_lowered_expr(*base)),
            field,
        },
        LoweredExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(from_lowered_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::MatchArm {
                    pattern: from_lowered_pattern(arm.pattern),
                    guard: arm.guard.map(from_lowered_expr),
                    body: from_lowered_expr(arm.body),
                })
                .collect(),
            evidence,
        },
        LoweredExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts.into_iter().map(from_lowered_stmt).collect(),
            tail: tail.map(|tail| Box::new(from_lowered_expr(*tail))),
        },
        LoweredExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(from_lowered_expr(*body)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::HandleArm {
                    effect: arm.effect,
                    payload: from_lowered_pattern(arm.payload),
                    resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
                        name: resume.name,
                        ty: runtime_type_from_core_value(resume.ty),
                    }),
                    guard: arm.guard.map(from_lowered_expr),
                    body: from_lowered_expr(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        LoweredExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(from_lowered_expr(*expr)),
        },
        LoweredExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value: runtime_type_from_core_value(value),
            expr: Box::new(from_lowered_expr(*expr)),
        },
        LoweredExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(from_lowered_expr(*body)),
        },
        LoweredExprKind::PeekId => ExprKind::PeekId,
        LoweredExprKind::FindId { id } => ExprKind::FindId { id },
        LoweredExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(from_lowered_expr(*thunk)),
        },
        LoweredExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(from_lowered_expr(*expr)),
        },
        LoweredExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(from_lowered_expr(*expr)),
        },
    };
    Expr::typed(kind, ty)
}

fn from_lowered_stmt(stmt: LoweredStmt) -> yulang_runtime_ir::FinalizedStmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: from_lowered_pattern(pattern),
            value: from_lowered_expr(value),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(from_lowered_expr(expr))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: from_lowered_expr(body),
        },
    }
}

fn from_lowered_pattern(pattern: LoweredPattern) -> yulang_runtime_ir::FinalizedPattern {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty } => yulang_runtime_ir::Pattern::Wildcard {
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Bind { name, ty } => yulang_runtime_ir::Pattern::Bind {
            name,
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Lit { lit, ty } => yulang_runtime_ir::Pattern::Lit {
            lit,
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Tuple { items, ty } => yulang_runtime_ir::Pattern::Tuple {
            items: items.into_iter().map(from_lowered_pattern).collect(),
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => yulang_runtime_ir::Pattern::List {
            prefix: prefix.into_iter().map(from_lowered_pattern).collect(),
            spread: spread.map(|spread| Box::new(from_lowered_pattern(*spread))),
            suffix: suffix.into_iter().map(from_lowered_pattern).collect(),
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Record { fields, spread, ty } => {
            yulang_runtime_ir::Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| yulang_runtime_ir::RecordPatternField {
                        name: field.name,
                        pattern: from_lowered_pattern(field.pattern),
                        default: field.default.map(from_lowered_expr),
                    })
                    .collect(),
                spread: spread.map(from_lowered_record_spread_pattern),
                ty: runtime_type_from_core_value(ty),
            }
        }
        yulang_runtime_ir::Pattern::Variant { tag, value, ty } => {
            yulang_runtime_ir::Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(from_lowered_pattern(*value))),
                ty: runtime_type_from_core_value(ty),
            }
        }
        yulang_runtime_ir::Pattern::Or { left, right, ty } => yulang_runtime_ir::Pattern::Or {
            left: Box::new(from_lowered_pattern(*left)),
            right: Box::new(from_lowered_pattern(*right)),
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => yulang_runtime_ir::Pattern::As {
            pattern: Box::new(from_lowered_pattern(*pattern)),
            name,
            ty: runtime_type_from_core_value(ty),
        },
    }
}

fn from_lowered_record_spread_expr(
    spread: LoweredRecordSpreadExpr,
) -> yulang_runtime_ir::FinalizedRecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(from_lowered_expr(*expr)))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(from_lowered_expr(*expr)))
        }
    }
}

fn from_lowered_record_spread_pattern(
    spread: LoweredRecordSpreadPattern,
) -> yulang_runtime_ir::FinalizedRecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(from_lowered_pattern(*pattern)))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(from_lowered_pattern(*pattern)))
        }
    }
}
