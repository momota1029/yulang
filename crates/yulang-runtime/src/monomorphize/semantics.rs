use std::collections::HashMap;

use yulang_typed_ir as typed_ir;

use crate::ir::{Expr, ExprKind, Module, Stmt};
use crate::types::effect_paths;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct DemandSemantics {
    handler_bindings: HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
}

impl DemandSemantics {
    pub(super) fn from_module(module: &Module) -> Self {
        let handler_bindings = module
            .bindings
            .iter()
            .filter_map(|binding| {
                expr_handler_consumes(&binding.body)
                    .map(|consumes| (binding.name.clone(), consumes))
            })
            .collect();
        Self { handler_bindings }
    }

    pub(super) fn is_effect_polymorphic_higher_order_target(
        &self,
        _target: &typed_ir::Path,
    ) -> bool {
        false
    }
}

pub(super) fn pure_handler_bindings(
    module: &Module,
) -> HashMap<typed_ir::Path, Vec<typed_ir::Path>> {
    module
        .bindings
        .iter()
        .filter_map(|binding| {
            expr_pure_handler_consumes(&binding.body)
                .map(|consumes| (binding.name.clone(), consumes))
        })
        .collect()
}

pub(super) fn consumed_effects_for_target(
    _semantics: &DemandSemantics,
    pure_handlers: &HashMap<typed_ir::Path, Vec<typed_ir::Path>>,
    target: &typed_ir::Path,
) -> Vec<typed_ir::Path> {
    pure_handlers.get(target).cloned().unwrap_or_default()
}

pub(super) fn known_consumed_effects_for_target(
    semantics: &DemandSemantics,
    target: &typed_ir::Path,
) -> Vec<typed_ir::Path> {
    semantics
        .handler_bindings
        .get(target)
        .cloned()
        .unwrap_or_default()
}

fn expr_handler_consumes(expr: &Expr) -> Option<Vec<typed_ir::Path>> {
    match &expr.kind {
        ExprKind::Handle { handler, .. } => Some(handler.consumes.clone()),
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_handler_consumes(body),
        ExprKind::Block {
            tail: Some(tail), ..
        } => expr_handler_consumes(tail),
        ExprKind::Block { stmts, tail: None } => match stmts.last() {
            Some(Stmt::Expr(expr)) => expr_handler_consumes(expr),
            _ => None,
        },
        _ => None,
    }
}

fn expr_pure_handler_consumes(expr: &Expr) -> Option<Vec<typed_ir::Path>> {
    match &expr.kind {
        ExprKind::Handle { handler, .. }
            if handler
                .residual_after
                .as_ref()
                .is_some_and(core_effect_is_empty) =>
        {
            Some(handler.consumes.clone())
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_pure_handler_consumes(body),
        ExprKind::Block {
            tail: Some(tail), ..
        } => expr_pure_handler_consumes(tail),
        ExprKind::Block { stmts, tail: None } => match stmts.last() {
            Some(Stmt::Expr(expr)) => expr_pure_handler_consumes(expr),
            _ => None,
        },
        _ => None,
    }
}

fn core_effect_is_empty(effect: &typed_ir::Type) -> bool {
    matches!(effect, typed_ir::Type::Never)
        || matches!(
            effect,
            typed_ir::Type::Row { items, tail }
                if items.is_empty() && matches!(tail.as_ref(), typed_ir::Type::Never)
        )
        || effect_paths(effect).is_empty()
}
