use yulang_runtime_ir::Type as RuntimeType;
use yulang_typed_ir as typed_ir;

use crate::types::{LowerSubstitutions, materialize_core_type, runtime_type_is_closed};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EffectLane {
    ret_effect: typed_ir::Type,
}

impl EffectLane {
    pub(crate) fn from_return_effect(ret_effect: typed_ir::Type) -> Self {
        Self { ret_effect }
    }

    pub(crate) fn solve(&self, substitutions: &LowerSubstitutions) -> EffectSolution {
        let closed_effect = materialize_core_type(self.ret_effect.clone(), substitutions);
        let is_closed = runtime_type_is_closed(&RuntimeType::Core(closed_effect.clone()));
        EffectSolution {
            closed_effect,
            is_closed,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EffectSolution {
    pub(crate) closed_effect: typed_ir::Type,
    pub(crate) is_closed: bool,
}

pub(crate) fn handler_output_type(
    body_ty: &RuntimeType,
    handler: &yulang_runtime_ir::HandleEffect,
) -> RuntimeType {
    let value = runtime_value_type(body_ty);
    let effect = handler
        .residual_after
        .as_ref()
        .map(project_runtime_effect)
        .unwrap_or(typed_ir::Type::Never);
    if should_thunk_effect(&effect) {
        RuntimeType::Thunk {
            effect,
            value: Box::new(value),
        }
    } else {
        value
    }
}

pub(crate) fn materialize_handle_effect(
    handler: yulang_runtime_ir::HandleEffect,
    substitutions: &LowerSubstitutions,
) -> yulang_runtime_ir::HandleEffect {
    yulang_runtime_ir::HandleEffect {
        consumes: handler.consumes,
        residual_before: handler
            .residual_before
            .map(|effect| project_runtime_effect(&materialize_core_type(effect, substitutions))),
        residual_after: handler
            .residual_after
            .map(|effect| project_runtime_effect(&materialize_core_type(effect, substitutions))),
    }
}

pub(crate) fn close_handle_effect(
    residual_before: typed_ir::Type,
    consumes: &[typed_ir::Path],
    arm_effects: Option<typed_ir::Type>,
) -> yulang_runtime_ir::HandleEffect {
    let residual_before = project_runtime_effect(&residual_before);
    let residual_after = subtract_handled_effects(&residual_before, consumes);
    let residual_after = merge_effects(Some(residual_after), arm_effects)
        .map(|effect| project_runtime_effect(&effect))
        .unwrap_or(typed_ir::Type::Never);
    yulang_runtime_ir::HandleEffect {
        consumes: consumes.to_vec(),
        residual_before: Some(residual_before),
        residual_after: Some(residual_after),
    }
}

pub(crate) fn expr_forced_effect(expr: &yulang_runtime_ir::Expr) -> Option<typed_ir::Type> {
    use yulang_runtime_ir::ExprKind;

    match &expr.kind {
        ExprKind::BindHere { expr } => thunk_effect(&expr.ty),
        ExprKind::Apply { callee, arg, .. } => {
            let apply_effect =
                runtime_function_result(&callee.ty).and_then(|ret| thunk_effect(&ret));
            let arg_effect = runtime_function_param(&callee.ty)
                .filter(|param| !matches!(param, RuntimeType::Thunk { .. }))
                .and_then(|_| expr_forced_effect(arg));
            merge_effects(
                merge_effects(expr_forced_effect(callee), arg_effect),
                apply_effect,
            )
        }
        ExprKind::Tuple(items) => items
            .iter()
            .filter_map(expr_forced_effect)
            .reduce(merge_effect_rows),
        ExprKind::Block { stmts, tail } => {
            let stmts = stmts
                .iter()
                .filter_map(stmt_forced_effect)
                .reduce(merge_effect_rows);
            merge_effects(stmts, tail.as_deref().and_then(expr_forced_effect))
        }
        ExprKind::Handle { handler, .. } => handler.residual_after.clone(),
        ExprKind::LocalPushId { body, .. } => expr_forced_effect(body),
        ExprKind::AddId { thunk, .. } => expr_forced_effect(thunk),
        ExprKind::Coerce { expr, .. } | ExprKind::Pack { expr, .. } => expr_forced_effect(expr),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::Lambda { .. }
        | ExprKind::Thunk { .. }
        | ExprKind::If { .. }
        | ExprKind::Record { .. }
        | ExprKind::Variant { .. }
        | ExprKind::Select { .. }
        | ExprKind::Match { .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => None,
    }
}

pub(crate) fn thunk_effect(ty: &RuntimeType) -> Option<typed_ir::Type> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(project_runtime_effect(effect)),
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Fun { .. } => None,
    }
}

pub(crate) fn runtime_value_type(ty: &RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
        ty => ty.clone(),
    }
}

pub(crate) fn should_thunk_effect(effect: &typed_ir::Type) -> bool {
    !effect_is_empty(effect)
        && !matches!(
            effect,
            typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
        )
}

pub(crate) fn effect_is_empty(effect: &typed_ir::Type) -> bool {
    match effect {
        typed_ir::Type::Never => true,
        typed_ir::Type::Row { items, tail } => items.is_empty() && effect_is_empty(tail),
        typed_ir::Type::Recursive { body, .. } => effect_is_empty(body),
        _ => false,
    }
}

pub(crate) fn project_runtime_effect(effect: &typed_ir::Type) -> typed_ir::Type {
    match effect {
        typed_ir::Type::Unknown | typed_ir::Type::Var(_) => typed_ir::Type::Never,
        typed_ir::Type::Never => typed_ir::Type::Never,
        typed_ir::Type::Any => typed_ir::Type::Any,
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args.iter().filter_map(project_effect_type_arg).collect(),
        },
        typed_ir::Type::Row { items, tail } => {
            let mut projected = Vec::new();
            for item in items {
                push_unique_effect(&mut projected, project_runtime_effect(item));
            }
            match project_runtime_effect(tail) {
                effect if effect_is_empty(&effect) => {}
                typed_ir::Type::Row { items, .. } => {
                    for item in items {
                        push_unique_effect(&mut projected, item);
                    }
                }
                effect => push_unique_effect(&mut projected, effect),
            }
            effect_row_from_items(projected)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            effect_row_from_items(items.iter().map(project_runtime_effect).collect())
        }
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(project_runtime_effect(body)),
        },
        other => other.clone(),
    }
}

pub(crate) fn merge_effects(
    left: Option<typed_ir::Type>,
    right: Option<typed_ir::Type>,
) -> Option<typed_ir::Type> {
    match (left, right) {
        (Some(left), Some(right)) => Some(merge_effect_rows(left, right)),
        (Some(effect), None) | (None, Some(effect)) => Some(effect),
        (None, None) => None,
    }
}

pub(crate) fn merge_effect_rows(left: typed_ir::Type, right: typed_ir::Type) -> typed_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) {
        return left;
    }
    match (left, right) {
        (
            typed_ir::Type::Row {
                mut items,
                tail: left_tail,
            },
            typed_ir::Type::Row {
                items: right_items,
                tail: right_tail,
            },
        ) if matches!(
            (left_tail.as_ref(), right_tail.as_ref()),
            (typed_ir::Type::Never, typed_ir::Type::Never)
        ) =>
        {
            for item in right_items {
                push_unique_effect(&mut items, item);
            }
            effect_row_from_items(items)
        }
        (left, right) if left == right => left,
        (left, right) => effect_row_from_items(vec![left, right]),
    }
}

pub(crate) fn subtract_handled_effects(
    residual: &typed_ir::Type,
    consumes: &[typed_ir::Path],
) -> typed_ir::Type {
    match residual {
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .filter(|item| {
                    let Some(path) = effect_path(item) else {
                        return true;
                    };
                    !consumes
                        .iter()
                        .any(|consume| effect_paths_match(consume, &path))
                })
                .cloned()
                .collect(),
            tail: tail.clone(),
        },
        typed_ir::Type::Named { path, .. }
            if consumes
                .iter()
                .any(|consume| effect_paths_match(consume, path)) =>
        {
            typed_ir::Type::Never
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => effect_row_from_items(
            items
                .iter()
                .map(|item| subtract_handled_effects(item, consumes))
                .filter(|item| !effect_is_empty(item))
                .collect(),
        ),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(subtract_handled_effects(body, consumes)),
        },
        other => other.clone(),
    }
}

pub(crate) fn effect_path(effect: &typed_ir::Type) -> Option<typed_ir::Path> {
    match effect {
        typed_ir::Type::Named { path, .. } => Some(path.clone()),
        _ => None,
    }
}

pub(crate) fn effect_paths_match(left: &typed_ir::Path, right: &typed_ir::Path) -> bool {
    left == right
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

pub(crate) fn effect_row_from_items(items: Vec<typed_ir::Type>) -> typed_ir::Type {
    let mut unique = Vec::new();
    for item in items {
        push_unique_effect(&mut unique, item);
    }
    if unique.is_empty() {
        typed_ir::Type::Never
    } else {
        typed_ir::Type::Row {
            items: unique,
            tail: Box::new(typed_ir::Type::Never),
        }
    }
}

fn stmt_forced_effect(stmt: &yulang_runtime_ir::Stmt) -> Option<typed_ir::Type> {
    match stmt {
        yulang_runtime_ir::Stmt::Let { value, .. }
        | yulang_runtime_ir::Stmt::Expr(value)
        | yulang_runtime_ir::Stmt::Module { body: value, .. } => expr_forced_effect(value),
    }
}

fn runtime_function_param(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun { param, .. }) => {
            Some(RuntimeType::Core(param.as_ref().clone()))
        }
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Thunk { .. } => None,
    }
}

fn runtime_function_result(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun {
            ret, ret_effect, ..
        }) => {
            let effect = project_runtime_effect(ret_effect);
            let value = RuntimeType::Core(ret.as_ref().clone());
            if should_thunk_effect(&effect) {
                Some(RuntimeType::Thunk {
                    effect,
                    value: Box::new(value),
                })
            } else {
                Some(value)
            }
        }
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Thunk { .. } => None,
    }
}

fn project_effect_type_arg(arg: &typed_ir::TypeArg) -> Option<typed_ir::TypeArg> {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            let ty = project_runtime_effect(ty);
            (!matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Var(_)))
                .then_some(typed_ir::TypeArg::Type(ty))
        }
        typed_ir::TypeArg::Bounds(bounds) => {
            let lower = bounds
                .lower
                .as_deref()
                .map(project_runtime_effect)
                .filter(|ty| !matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Var(_)));
            lower.map(typed_ir::TypeArg::Type)
        }
    }
}

fn push_unique_effect(out: &mut Vec<typed_ir::Type>, effect: typed_ir::Type) {
    if effect_is_empty(&effect) {
        return;
    }
    match effect {
        typed_ir::Type::Row { items, .. } => {
            for item in items {
                push_unique_effect(out, item);
            }
        }
        effect => {
            if !out.contains(&effect) {
                out.push(effect);
            }
        }
    }
}

fn qualified_prefix_effect_paths_match(parent: &typed_ir::Path, child: &typed_ir::Path) -> bool {
    effect_path_can_match_child_prefix(parent)
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}

fn effect_path_can_match_child_prefix(path: &typed_ir::Path) -> bool {
    path.segments.len() > 1
        || path.segments.first().is_some_and(|name| {
            name.0.starts_with('#') || name.0.starts_with('&') && name.0.contains('#')
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn effect_lane_closes_return_effect_from_substitution() {
        let lane =
            EffectLane::from_return_effect(typed_ir::Type::Var(typed_ir::TypeVar("e".into())));
        let substitutions =
            LowerSubstitutions::from_type_substitutions(&[typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("e".into()),
                ty: typed_ir::Type::Never,
            }])
            .unwrap();

        let solution = lane.solve(&substitutions);

        assert_eq!(solution.closed_effect, typed_ir::Type::Never);
        assert!(solution.is_closed);
    }

    #[test]
    fn effect_lane_keeps_open_return_effect_visible() {
        let lane =
            EffectLane::from_return_effect(typed_ir::Type::Var(typed_ir::TypeVar("e".into())));
        let solution = lane.solve(&LowerSubstitutions::default());

        assert_eq!(
            solution.closed_effect,
            typed_ir::Type::Var(typed_ir::TypeVar("e".into()))
        );
        assert!(!solution.is_closed);
    }

    #[test]
    fn subtract_handled_effect_removes_matching_row_item() {
        let residual = effect_row(&["io", "log"]);

        let after = subtract_handled_effects(&residual, &[path(&["io"])]);

        assert_eq!(after, effect_row(&["log"]));
    }

    #[test]
    fn handler_output_is_value_when_all_body_effects_are_consumed() {
        let body_ty = RuntimeType::Thunk {
            effect: effect_row(&["io"]),
            value: Box::new(RuntimeType::Core(int_type())),
        };
        let handler = close_handle_effect(effect_row(&["io"]), &[path(&["io"])], None);

        let output = handler_output_type(&body_ty, &handler);

        assert_eq!(output, RuntimeType::Core(int_type()));
    }

    #[test]
    fn handler_output_keeps_residual_effect_as_thunk() {
        let body_ty = RuntimeType::Thunk {
            effect: effect_row(&["io", "log"]),
            value: Box::new(RuntimeType::Core(int_type())),
        };
        let handler = close_handle_effect(effect_row(&["io", "log"]), &[path(&["io"])], None);

        let output = handler_output_type(&body_ty, &handler);

        assert_eq!(
            output,
            RuntimeType::Thunk {
                effect: effect_row(&["log"]),
                value: Box::new(RuntimeType::Core(int_type())),
            }
        );
    }

    fn effect_row(names: &[&str]) -> typed_ir::Type {
        effect_row_from_items(
            names
                .iter()
                .map(|name| typed_ir::Type::Named {
                    path: path(&[name]),
                    args: Vec::new(),
                })
                .collect(),
        )
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "int", "Int"]),
            args: Vec::new(),
        }
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
