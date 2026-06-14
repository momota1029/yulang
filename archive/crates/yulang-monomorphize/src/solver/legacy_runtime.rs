//! Convert finalized runtime IR back to the legacy runtime type surface.
//!
//! The finalized IR is the main output of monomorphization. This conversion is
//! kept as an adapter for legacy VM/runtime entry points.

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, FinalizedModule as Module,
};
use yulang_typed_ir as typed_ir;

pub(crate) fn from_finalized_module(module: Module) -> yulang_runtime_types::Module {
    yulang_runtime_ir::Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(|binding| yulang_runtime_ir::Binding {
                name: binding.name,
                type_params: binding.type_params,
                scheme: binding.scheme,
                body: from_finalized_expr(binding.body),
            })
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(from_finalized_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn from_finalized_expr(expr: Expr) -> yulang_runtime_types::Expr {
    let ty = from_finalized_type(expr.ty);
    let kind = match expr.kind {
        ExprKind::Var(path) => yulang_runtime_ir::ExprKind::Var(path),
        ExprKind::EffectOp(path) => yulang_runtime_ir::ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => yulang_runtime_ir::ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => yulang_runtime_ir::ExprKind::Lit(lit),
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => yulang_runtime_ir::ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(from_finalized_expr(*body)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => yulang_runtime_ir::ExprKind::Apply {
            callee: Box::new(from_finalized_expr(*callee)),
            arg: Box::new(from_finalized_expr(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => yulang_runtime_ir::ExprKind::If {
            cond: Box::new(from_finalized_expr(*cond)),
            then_branch: Box::new(from_finalized_expr(*then_branch)),
            else_branch: Box::new(from_finalized_expr(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => {
            yulang_runtime_ir::ExprKind::Tuple(items.into_iter().map(from_finalized_expr).collect())
        }
        ExprKind::Record { fields, spread } => yulang_runtime_ir::ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordExprField {
                    name: field.name,
                    value: from_finalized_expr(field.value),
                })
                .collect(),
            spread: spread.map(from_finalized_record_spread_expr),
        },
        ExprKind::Variant { tag, value } => yulang_runtime_ir::ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(from_finalized_expr(*value))),
        },
        ExprKind::Select { base, field } => yulang_runtime_ir::ExprKind::Select {
            base: Box::new(from_finalized_expr(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => yulang_runtime_ir::ExprKind::Match {
            scrutinee: Box::new(from_finalized_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::MatchArm {
                    pattern: from_finalized_pattern(arm.pattern),
                    guard: arm.guard.map(from_finalized_expr),
                    body: from_finalized_expr(arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => yulang_runtime_ir::ExprKind::Block {
            stmts: stmts.into_iter().map(from_finalized_stmt).collect(),
            tail: tail.map(|tail| Box::new(from_finalized_expr(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => yulang_runtime_ir::ExprKind::Handle {
            body: Box::new(from_finalized_expr(*body)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::HandleArm {
                    effect: arm.effect,
                    payload: from_finalized_pattern(arm.payload),
                    resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
                        name: resume.name,
                        ty: from_finalized_type(resume.ty),
                    }),
                    guard: arm.guard.map(from_finalized_expr),
                    body: from_finalized_expr(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => {
            let mut expr = from_finalized_expr(*expr);
            if !matches!(expr.ty, yulang_runtime_types::Type::Thunk { .. }) {
                let value = expr.ty.clone();
                expr.ty = yulang_runtime_types::Type::thunk(typed_ir::Type::Unknown, value);
            }
            yulang_runtime_ir::ExprKind::BindHere {
                expr: Box::new(expr),
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let value = from_finalized_type(value);
            let kind = yulang_runtime_ir::ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(from_finalized_expr(*expr)),
            };
            return yulang_runtime_ir::Expr::typed(
                kind,
                yulang_runtime_types::Type::thunk(effect, value),
            );
        }
        ExprKind::LocalPushId { id, body } => yulang_runtime_ir::ExprKind::LocalPushId {
            id,
            body: Box::new(from_finalized_expr(*body)),
        },
        ExprKind::PeekId => yulang_runtime_ir::ExprKind::PeekId,
        ExprKind::FindId { id } => yulang_runtime_ir::ExprKind::FindId { id },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => yulang_runtime_ir::ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(from_finalized_expr(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => yulang_runtime_ir::ExprKind::Coerce {
            from,
            to,
            expr: Box::new(from_finalized_expr(*expr)),
        },
        ExprKind::Pack { var, expr } => yulang_runtime_ir::ExprKind::Pack {
            var,
            expr: Box::new(from_finalized_expr(*expr)),
        },
    };
    yulang_runtime_ir::Expr::typed(kind, ty)
}

fn from_finalized_stmt(stmt: yulang_runtime_ir::FinalizedStmt) -> yulang_runtime_types::Stmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: from_finalized_pattern(pattern),
            value: from_finalized_expr(value),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(from_finalized_expr(expr))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: from_finalized_expr(body),
        },
    }
}

fn from_finalized_pattern(
    pattern: yulang_runtime_ir::FinalizedPattern,
) -> yulang_runtime_types::Pattern {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty } => yulang_runtime_ir::Pattern::Wildcard {
            ty: from_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Bind { name, ty } => yulang_runtime_ir::Pattern::Bind {
            name,
            ty: from_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Lit { lit, ty } => yulang_runtime_ir::Pattern::Lit {
            lit,
            ty: from_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Tuple { items, ty } => yulang_runtime_ir::Pattern::Tuple {
            items: items.into_iter().map(from_finalized_pattern).collect(),
            ty: from_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => yulang_runtime_ir::Pattern::List {
            prefix: prefix.into_iter().map(from_finalized_pattern).collect(),
            spread: spread.map(|spread| Box::new(from_finalized_pattern(*spread))),
            suffix: suffix.into_iter().map(from_finalized_pattern).collect(),
            ty: from_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Record { fields, spread, ty } => {
            yulang_runtime_ir::Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| yulang_runtime_ir::RecordPatternField {
                        name: field.name,
                        pattern: from_finalized_pattern(field.pattern),
                        default: field.default.map(from_finalized_expr),
                    })
                    .collect(),
                spread: spread.map(from_finalized_record_spread_pattern),
                ty: from_finalized_type(ty),
            }
        }
        yulang_runtime_ir::Pattern::Variant { tag, value, ty } => {
            yulang_runtime_ir::Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(from_finalized_pattern(*value))),
                ty: from_finalized_type(ty),
            }
        }
        yulang_runtime_ir::Pattern::Or { left, right, ty } => yulang_runtime_ir::Pattern::Or {
            left: Box::new(from_finalized_pattern(*left)),
            right: Box::new(from_finalized_pattern(*right)),
            ty: from_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => yulang_runtime_ir::Pattern::As {
            pattern: Box::new(from_finalized_pattern(*pattern)),
            name,
            ty: from_finalized_type(ty),
        },
    }
}

fn from_finalized_record_spread_expr(
    spread: yulang_runtime_ir::FinalizedRecordSpreadExpr,
) -> yulang_runtime_types::RecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(from_finalized_expr(*expr)))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(from_finalized_expr(*expr)))
        }
    }
}

fn from_finalized_record_spread_pattern(
    spread: yulang_runtime_ir::FinalizedRecordSpreadPattern,
) -> yulang_runtime_types::RecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(from_finalized_pattern(*pattern)))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(from_finalized_pattern(*pattern)))
        }
    }
}

fn from_finalized_type(ty: yulang_runtime_ir::RuntimeType) -> yulang_runtime_types::Type {
    match ty {
        yulang_runtime_ir::RuntimeType::Unknown => yulang_runtime_types::Type::Unknown,
        yulang_runtime_ir::RuntimeType::Value(ty) => yulang_runtime_types::Type::Value(ty),
        yulang_runtime_ir::RuntimeType::Fun { param, ret } => yulang_runtime_types::Type::Fun {
            param: Box::new(from_finalized_type(*param)),
            ret: Box::new(from_finalized_type(*ret)),
        },
        yulang_runtime_ir::RuntimeType::Thunk { effect, value } => {
            yulang_runtime_types::Type::Thunk {
                effect,
                value: Box::new(from_finalized_type(*value)),
            }
        }
    }
}
