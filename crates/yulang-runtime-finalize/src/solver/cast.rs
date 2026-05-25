//! Semantic cast handling.
//!
//! Cast edges come from `role Cast<...>` impls. This module:
//!   - builds the cast lattice (`type_cast_order`, `semantic_cast_edges`)
//!   - searches for a chain of casts between two concrete types
//!     (`semantic_cast_path`)
//!   - normalizes a finalized module's `Coerce` nodes by collapsing identities
//!     and expanding multi-step paths (`normalize_semantic_cast_coercions`
//!     and friends)
//!
//! No subtype constraint solving lives here — see `apply_spine` for that.

use std::collections::VecDeque;

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, FinalizedModule as Module,
    FinalizedType as RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::graph::TypeCastOrder;

pub(crate) fn normalize_semantic_cast_coercions(module: &mut Module) {
    let role_impls = module.role_impls.clone();
    for binding in &mut module.bindings {
        binding.body = normalize_semantic_cast_expr(binding.body.clone(), &role_impls);
    }
    for expr in &mut module.root_exprs {
        *expr = normalize_semantic_cast_expr(expr.clone(), &role_impls);
    }
}

fn normalize_semantic_cast_expr(expr: Expr, role_impls: &[typed_ir::RoleImplGraphNode]) -> Expr {
    let ty = expr.ty.clone();
    let kind = match expr.kind {
        ExprKind::Var(path) => ExprKind::Var(path),
        ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit),
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(normalize_semantic_cast_expr(*body, role_impls)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(normalize_semantic_cast_expr(*callee, role_impls)),
            arg: Box::new(normalize_semantic_cast_expr(*arg, role_impls)),
            evidence,
            instantiation,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| normalize_semantic_cast_expr(item, role_impls))
                .collect(),
        ),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(normalize_semantic_cast_expr(*cond, role_impls)),
            then_branch: Box::new(normalize_semantic_cast_expr(*then_branch, role_impls)),
            else_branch: Box::new(normalize_semantic_cast_expr(*else_branch, role_impls)),
            evidence,
        },
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::FinalizedRecordExprField {
                    name: field.name,
                    value: normalize_semantic_cast_expr(field.value, role_impls),
                })
                .collect(),
            spread: spread.map(|spread| normalize_semantic_cast_record_spread(spread, role_impls)),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(normalize_semantic_cast_expr(*value, role_impls))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(normalize_semantic_cast_expr(*base, role_impls)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(normalize_semantic_cast_expr(*scrutinee, role_impls)),
            arms: arms
                .into_iter()
                .map(|arm| normalize_semantic_cast_match_arm(arm, role_impls))
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| normalize_semantic_cast_stmt(stmt, role_impls))
                .collect(),
            tail: tail.map(|tail| Box::new(normalize_semantic_cast_expr(*tail, role_impls))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(normalize_semantic_cast_expr(*body, role_impls)),
            arms: arms
                .into_iter()
                .map(|arm| normalize_semantic_cast_handle_arm(arm, role_impls))
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(normalize_semantic_cast_expr(*expr, role_impls)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value,
            expr: Box::new(normalize_semantic_cast_expr(*expr, role_impls)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(normalize_semantic_cast_expr(*body, role_impls)),
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
            thunk: Box::new(normalize_semantic_cast_expr(*thunk, role_impls)),
        },
        ExprKind::Coerce { from, to, expr } => {
            let expr = normalize_semantic_cast_expr(*expr, role_impls);
            let actual = precise_coerce_actual_type(&expr, &from);
            if actual == to {
                return expr;
            }
            if let Some(steps) = semantic_cast_path(role_impls, &actual, &to) {
                return apply_semantic_cast_path(expr, steps);
            }
            ExprKind::Coerce {
                from: actual,
                to,
                expr: Box::new(expr),
            }
        }
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(normalize_semantic_cast_expr(*expr, role_impls)),
        },
    };
    Expr::typed(kind, ty)
}

fn normalize_semantic_cast_stmt(
    stmt: yulang_runtime_ir::FinalizedStmt,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::FinalizedStmt {
    match stmt {
        yulang_runtime_ir::FinalizedStmt::Let { pattern, value } => {
            yulang_runtime_ir::FinalizedStmt::Let {
                pattern: normalize_semantic_cast_pattern(pattern, role_impls),
                value: normalize_semantic_cast_expr(value, role_impls),
            }
        }
        yulang_runtime_ir::FinalizedStmt::Expr(expr) => {
            yulang_runtime_ir::FinalizedStmt::Expr(normalize_semantic_cast_expr(expr, role_impls))
        }
        yulang_runtime_ir::FinalizedStmt::Module { def, body } => {
            yulang_runtime_ir::FinalizedStmt::Module {
                def,
                body: normalize_semantic_cast_expr(body, role_impls),
            }
        }
    }
}

fn normalize_semantic_cast_match_arm(
    arm: yulang_runtime_ir::FinalizedMatchArm,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::FinalizedMatchArm {
    yulang_runtime_ir::FinalizedMatchArm {
        pattern: normalize_semantic_cast_pattern(arm.pattern, role_impls),
        guard: arm
            .guard
            .map(|guard| normalize_semantic_cast_expr(guard, role_impls)),
        body: normalize_semantic_cast_expr(arm.body, role_impls),
    }
}

fn normalize_semantic_cast_handle_arm(
    arm: yulang_runtime_ir::FinalizedHandleArm,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::FinalizedHandleArm {
    yulang_runtime_ir::FinalizedHandleArm {
        effect: arm.effect,
        payload: normalize_semantic_cast_pattern(arm.payload, role_impls),
        resume: arm.resume,
        guard: arm
            .guard
            .map(|guard| normalize_semantic_cast_expr(guard, role_impls)),
        body: normalize_semantic_cast_expr(arm.body, role_impls),
    }
}

fn normalize_semantic_cast_pattern(
    pattern: yulang_runtime_ir::FinalizedPattern,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::FinalizedPattern {
    use yulang_runtime_ir::FinalizedPattern as Pattern;

    match pattern {
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| normalize_semantic_cast_pattern(item, role_impls))
                .collect(),
            ty,
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(|item| normalize_semantic_cast_pattern(item, role_impls))
                .collect(),
            spread: spread
                .map(|spread| Box::new(normalize_semantic_cast_pattern(*spread, role_impls))),
            suffix: suffix
                .into_iter()
                .map(|item| normalize_semantic_cast_pattern(item, role_impls))
                .collect(),
            ty,
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::FinalizedRecordPatternField {
                    name: field.name,
                    pattern: normalize_semantic_cast_pattern(field.pattern, role_impls),
                    default: field
                        .default
                        .map(|expr| normalize_semantic_cast_expr(expr, role_impls)),
                })
                .collect(),
            spread: spread
                .map(|spread| normalize_semantic_cast_record_pattern_spread(spread, role_impls)),
            ty,
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(normalize_semantic_cast_pattern(*value, role_impls))),
            ty,
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(normalize_semantic_cast_pattern(*left, role_impls)),
            right: Box::new(normalize_semantic_cast_pattern(*right, role_impls)),
            ty,
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(normalize_semantic_cast_pattern(*pattern, role_impls)),
            name,
            ty,
        },
        Pattern::Wildcard { ty } => Pattern::Wildcard { ty },
        Pattern::Bind { name, ty } => Pattern::Bind { name, ty },
        Pattern::Lit { lit, ty } => Pattern::Lit { lit, ty },
    }
}

fn normalize_semantic_cast_record_spread(
    spread: yulang_runtime_ir::FinalizedRecordSpreadExpr,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::FinalizedRecordSpreadExpr {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(Box::new(
                normalize_semantic_cast_expr(*expr, role_impls),
            ))
        }
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(Box::new(
                normalize_semantic_cast_expr(*expr, role_impls),
            ))
        }
    }
}

fn normalize_semantic_cast_record_pattern_spread(
    spread: yulang_runtime_ir::FinalizedRecordSpreadPattern,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::FinalizedRecordSpreadPattern {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::FinalizedRecordSpreadPattern::Head(Box::new(
                normalize_semantic_cast_pattern(*pattern, role_impls),
            ))
        }
        yulang_runtime_ir::FinalizedRecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::FinalizedRecordSpreadPattern::Tail(Box::new(
                normalize_semantic_cast_pattern(*pattern, role_impls),
            ))
        }
    }
}

#[derive(Clone)]
struct SemanticCastStep {
    method: typed_ir::Path,
    from: typed_ir::Type,
    to: typed_ir::Type,
}

fn apply_semantic_cast_path(expr: Expr, steps: Vec<SemanticCastStep>) -> Expr {
    steps.into_iter().fold(expr, |value, step| {
        let callee_ty = RuntimeType::fun(
            RuntimeType::value(step.from.clone()),
            RuntimeType::value(step.to.clone()),
        );
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(step.method), callee_ty)),
                arg: Box::new(value),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::value(step.to),
        )
    })
}

fn semantic_cast_path(
    role_impls: &[typed_ir::RoleImplGraphNode],
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
) -> Option<Vec<SemanticCastStep>> {
    if !semantic_cast_target_needs_apply(expected)
        || primitive_runtime_coercion_covers(actual, expected)
        || semantic_cast_endpoint_is_open(actual)
        || semantic_cast_endpoint_is_open(expected)
        || same_core_type(actual, expected)
    {
        return None;
    }
    let edges = semantic_cast_edges(role_impls);
    let mut seen = Vec::new();
    let mut queue = VecDeque::from([(actual.clone(), Vec::new())]);
    while let Some((current, path)) = queue.pop_front() {
        if seen.iter().any(|seen| same_core_type(seen, &current)) {
            continue;
        }
        seen.push(current.clone());
        for edge in &edges {
            if !same_core_type(&edge.from, &current) {
                continue;
            }
            let mut next_path = path.clone();
            next_path.push(edge.clone());
            if same_core_type(&edge.to, expected) {
                return Some(next_path);
            }
            queue.push_back((edge.to.clone(), next_path));
        }
    }
    None
}

fn semantic_cast_edges(role_impls: &[typed_ir::RoleImplGraphNode]) -> Vec<SemanticCastStep> {
    role_impls
        .iter()
        .filter(|role_impl| {
            role_impl
                .role
                .segments
                .last()
                .is_some_and(|name| name.0 == "Cast")
        })
        .filter_map(|role_impl| {
            let from = role_impl
                .inputs
                .first()
                .and_then(super::apply_spine::type_from_bounds)?;
            let to = role_impl
                .associated_types
                .iter()
                .find(|associated| associated.name.0 == "to")
                .and_then(|associated| super::apply_spine::type_from_bounds(&associated.value))?;
            let method = role_impl
                .members
                .iter()
                .find(|member| member.name.0 == "cast")
                .map(|member| member.value.clone())?;
            Some(SemanticCastStep { method, from, to })
        })
        .collect()
}

pub(crate) fn type_cast_order(role_impls: &[typed_ir::RoleImplGraphNode]) -> TypeCastOrder {
    TypeCastOrder::from_edges(
        semantic_cast_edges(role_impls)
            .into_iter()
            .map(|step| (step.from, step.to))
            .collect(),
    )
}

fn precise_coerce_actual_type(expr: &Expr, fallback: &typed_ir::Type) -> typed_ir::Type {
    let actual = super::runtime_type_to_core(expr.ty.clone());
    if semantic_cast_endpoint_is_open(&actual) {
        fallback.clone()
    } else {
        actual
    }
}

fn semantic_cast_endpoint_is_open(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Any | typed_ir::Type::Unknown | typed_ir::Type::Var(_)
    ) || !super::core_type_is_closed(ty)
}

fn semantic_cast_target_needs_apply(ty: &typed_ir::Type) -> bool {
    is_bare_named_type(ty, "float")
}

fn primitive_runtime_coercion_covers(actual: &typed_ir::Type, expected: &typed_ir::Type) -> bool {
    is_bare_named_type(actual, "int") && is_bare_named_type(expected, "float")
}

fn is_bare_named_type(ty: &typed_ir::Type, name: &str) -> bool {
    matches!(
        ty,
        typed_ir::Type::Named { path, args }
            if args.is_empty()
                && path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.0 == name)
    )
}

fn same_core_type(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    super::role::core_subtype_match_score(left, right).is_some()
        && super::role::core_subtype_match_score(right, left).is_some()
}
