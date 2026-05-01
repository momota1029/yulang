use yulang_core_ir as core_ir;

use crate::ir::{EffectIdRef, EffectIdVar, Expr, ExprKind, HandleEffect, Module, Stmt};
use crate::types::{effect_path, effect_paths};

pub fn format_hygiene_module(module: &Module) -> String {
    let mut out = String::new();
    for binding in &module.bindings {
        out.push_str(&format_path(&binding.name));
        out.push('\n');
        format_hygiene_expr_into(&binding.body, 1, &mut out);
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        out.push_str("<root ");
        out.push_str(&index.to_string());
        out.push_str(">\n");
        format_hygiene_expr_into(expr, 1, &mut out);
    }
    out
}

pub fn format_hygiene_expr(expr: &Expr) -> String {
    let mut out = String::new();
    format_hygiene_expr_into(expr, 0, &mut out);
    out
}

fn format_hygiene_expr_into(expr: &Expr, indent: usize, out: &mut String) {
    match &expr.kind {
        ExprKind::LocalPushId { id, body } => {
            line(
                indent,
                out,
                &format!("local_push_id {}", format_id_var(*id)),
            );
            format_hygiene_expr_into(body, indent + 1, out);
        }
        ExprKind::AddId { id, allowed, thunk } => {
            line(
                indent,
                out,
                &format!("add_id[{}, {}]", format_id_ref(*id), format_effect(allowed)),
            );
            format_hygiene_expr_into(thunk, indent + 1, out);
        }
        ExprKind::FindId { id } => {
            line(indent, out, &format!("find_id {}", format_id_ref(*id)));
        }
        ExprKind::PeekId => line(indent, out, "peek_id"),
        ExprKind::Handle {
            body,
            arms,
            handler,
            ..
        } => {
            line(indent, out, &format_handle(handler));
            format_hygiene_expr_into(body, indent + 1, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    line(indent + 1, out, "guard");
                    format_hygiene_expr_into(guard, indent + 2, out);
                }
                line(indent + 1, out, "arm");
                format_hygiene_expr_into(&arm.body, indent + 2, out);
            }
        }
        ExprKind::BindHere { expr } => {
            line(indent, out, "bind_here");
            format_hygiene_expr_into(expr, indent + 1, out);
        }
        ExprKind::Thunk { effect, expr, .. } => {
            line(indent, out, &format!("thunk[{}]", format_effect(effect)));
            format_hygiene_expr_into(expr, indent + 1, out);
        }
        ExprKind::Lambda { body, .. } => {
            line(indent, out, "lambda");
            format_hygiene_expr_into(body, indent + 1, out);
        }
        ExprKind::Apply { callee, arg, .. } => {
            line(indent, out, "apply");
            format_hygiene_expr_into(callee, indent + 1, out);
            format_hygiene_expr_into(arg, indent + 1, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            line(indent, out, "if");
            format_hygiene_expr_into(cond, indent + 1, out);
            format_hygiene_expr_into(then_branch, indent + 1, out);
            format_hygiene_expr_into(else_branch, indent + 1, out);
        }
        ExprKind::Tuple(items) => {
            line(indent, out, "tuple");
            for item in items {
                format_hygiene_expr_into(item, indent + 1, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            line(indent, out, "record");
            for field in fields {
                format_hygiene_expr_into(&field.value, indent + 1, out);
            }
            if let Some(spread) = spread {
                match spread {
                    crate::ir::RecordSpreadExpr::Head(expr)
                    | crate::ir::RecordSpreadExpr::Tail(expr) => {
                        format_hygiene_expr_into(expr, indent + 1, out);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            line(indent, out, "variant");
            if let Some(value) = value {
                format_hygiene_expr_into(value, indent + 1, out);
            }
        }
        ExprKind::Select { base, .. } => {
            line(indent, out, "select");
            format_hygiene_expr_into(base, indent + 1, out);
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            line(indent, out, "match");
            format_hygiene_expr_into(scrutinee, indent + 1, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    line(indent + 1, out, "guard");
                    format_hygiene_expr_into(guard, indent + 2, out);
                }
                line(indent + 1, out, "arm");
                format_hygiene_expr_into(&arm.body, indent + 2, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            line(indent, out, "block");
            for stmt in stmts {
                format_hygiene_stmt_into(stmt, indent + 1, out);
            }
            if let Some(tail) = tail {
                format_hygiene_expr_into(tail, indent + 1, out);
            }
        }
        ExprKind::Coerce { expr, .. } | ExprKind::Pack { expr, .. } => {
            format_hygiene_expr_into(expr, indent, out);
        }
        ExprKind::Var(_) | ExprKind::EffectOp(_) | ExprKind::PrimitiveOp(_) | ExprKind::Lit(_) => {}
    }
}

fn format_hygiene_stmt_into(stmt: &Stmt, indent: usize, out: &mut String) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            format_hygiene_expr_into(value, indent, out);
        }
    }
}

fn format_handle(handler: &HandleEffect) -> String {
    let consumes = handler
        .consumes
        .iter()
        .map(format_path)
        .collect::<Vec<_>>()
        .join(", ");
    let before = handler
        .residual_before
        .as_ref()
        .map(format_effect)
        .unwrap_or_else(|| "_".to_string());
    let after = handler
        .residual_after
        .as_ref()
        .map(format_effect)
        .unwrap_or_else(|| "_".to_string());
    format!("handle consumes=[{consumes}] residual={before}->{after}")
}

fn line(indent: usize, out: &mut String, text: &str) {
    for _ in 0..indent {
        out.push_str("  ");
    }
    out.push_str(text);
    out.push('\n');
}

fn format_id_var(id: EffectIdVar) -> String {
    format!("ae{}", id.0)
}

fn format_id_ref(id: EffectIdRef) -> String {
    match id {
        EffectIdRef::Var(id) => format_id_var(id),
        EffectIdRef::Peek => "peek".to_string(),
    }
}

fn format_effect(effect: &core_ir::Type) -> String {
    let paths = effect_paths(effect);
    if !paths.is_empty() {
        return paths.iter().map(format_path).collect::<Vec<_>>().join("; ");
    }
    effect_path(effect)
        .map(|path| format_path(&path))
        .unwrap_or_else(|| format!("{effect:?}"))
}

fn format_path(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Expr, ExprKind, Type as RuntimeType};

    fn named_type(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn row(name: &str) -> core_ir::Type {
        core_ir::Type::Row {
            items: vec![named_type(name)],
            tail: Box::new(core_ir::Type::Never),
        }
    }

    #[test]
    fn shows_local_push_and_add_id_scope() {
        let int = RuntimeType::core(named_type("int"));
        let effect = row("io");
        let thunk = Expr::typed(
            ExprKind::Thunk {
                effect: effect.clone(),
                value: int.clone(),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                    int,
                )),
            },
            RuntimeType::thunk(effect.clone(), RuntimeType::core(named_type("int"))),
        );
        let expr = Expr::typed(
            ExprKind::LocalPushId {
                id: EffectIdVar(0),
                body: Box::new(Expr::typed(
                    ExprKind::AddId {
                        id: EffectIdRef::Peek,
                        allowed: effect,
                        thunk: Box::new(thunk),
                    },
                    RuntimeType::thunk(row("io"), RuntimeType::core(named_type("int"))),
                )),
            },
            RuntimeType::thunk(row("io"), RuntimeType::core(named_type("int"))),
        );

        let text = format_hygiene_expr(&expr);

        assert!(text.contains("local_push_id ae0"));
        assert!(text.contains("add_id[peek, io]"));
        assert!(text.contains("thunk[io]"));
    }

    #[test]
    fn shows_handler_effect_summary_and_find_id() {
        let unit = RuntimeType::core(named_type("unit"));
        let effect_path = core_ir::Path::from_name(core_ir::Name("io".to_string()));
        let expr = Expr::typed(
            ExprKind::Handle {
                body: Box::new(Expr::typed(
                    ExprKind::FindId {
                        id: EffectIdRef::Var(EffectIdVar(1)),
                    },
                    RuntimeType::core(named_type("__effect_id")),
                )),
                arms: Vec::new(),
                evidence: crate::ir::JoinEvidence {
                    result: named_type("unit"),
                },
                handler: HandleEffect {
                    consumes: vec![effect_path],
                    residual_before: Some(row("io")),
                    residual_after: Some(core_ir::Type::Never),
                },
            },
            unit,
        );

        let text = format_hygiene_expr(&expr);

        assert!(text.contains("handle consumes=[io] residual=io->"));
        assert!(text.contains("find_id ae1"));
    }
}
