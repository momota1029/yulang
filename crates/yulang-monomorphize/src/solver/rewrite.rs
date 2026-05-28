//! Emitting monomorphic bindings and rewriting call sites.
//!
//! After the graph solver produces `RootGraphSolution`s, this module:
//!   - canonicalizes aliases so identical solutions reuse one binding
//!     (`canonicalize_aliases`)
//!   - emits new monomorphic `Binding`s into the module, going through the
//!     finalize instance cache (`append_monomorphic_bindings`,
//!     `solution_instance_key`, `alias_path`)
//!   - walks every root expression and binding body to replace polymorphic
//!     `Var` / apply-spine call sites with the new mono aliases
//!     (`rewrite_root_exprs`, `rewrite_binding_exprs`, `rewrite_root_expr`)
//!   - performs the apply-spine specific surgery: stripping evidence on the
//!     spine, refreshing `RuntimeType`s top-down (`rewrite_simple_apply`,
//!     `replace_apply_spine_binding`, `refresh_apply_spine_runtime_types`).

use std::collections::{HashMap, HashSet};

use yulang_runtime_ir::{
    FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
    FinalizedModule as Module, RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::{
    CachedMonomorphizeInstance, MonomorphizeDiagnostic, MonomorphizeInstanceCache,
    MonomorphizeInstanceKey, MonomorphizeResult, RootGraphSolution,
    graph::runtime_type_from_core_value_and_effect, output::RootGraphRoot,
};

use super::materialize;

pub(crate) fn canonicalize_aliases(solutions: &mut [RootGraphSolution]) {
    let mut aliases = HashMap::new();
    let mut next_alias = 0;
    for solution in solutions {
        let key = solution_instance_key(solution);
        let alias = aliases.entry(key).or_insert_with(|| {
            let alias = alias_path(&solution.binding, next_alias);
            next_alias += 1;
            alias
        });
        solution.alias = alias.clone();
    }
}

pub(crate) fn append_monomorphic_bindings(
    module: &mut Module,
    solutions: &[RootGraphSolution],
    cache: &mut MonomorphizeInstanceCache,
) -> MonomorphizeResult<Vec<typed_ir::Path>> {
    let bindings = module
        .bindings
        .iter()
        .enumerate()
        .map(|(index, binding)| (binding.name.clone(), index))
        .collect::<HashMap<_, _>>();
    let mut emitted_aliases = module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let mut emitted = Vec::new();
    for solution in solutions {
        if !emitted_aliases.insert(solution.alias.clone()) {
            continue;
        }
        let key = solution_instance_key(solution);
        if let Some(cached) = cache.get(&key) {
            emitted.push(cached.binding_with_alias(solution.alias.clone()));
            continue;
        }
        let binding = bindings
            .get(&solution.binding)
            .and_then(|index| module.bindings.get(*index))
            .ok_or_else(|| MonomorphizeDiagnostic::MissingBinding {
                binding: solution.binding.clone(),
            })?;
        let scheme_body = super::runtime_type_to_core(solution.callee_type.clone());
        let scheme = typed_ir::Scheme {
            requirements: Vec::new(),
            body: scheme_body,
        };
        let body = materialize::materialize_expr_with_expected(
            binding.body.clone(),
            &solution.type_substitutions,
            Some(&solution.callee_type),
        );
        let mut body = body;
        // Self-targeting instantiations come from the generic body and are
        // stale inside the emitted monomorphic alias.
        clear_binding_instantiations(&mut body, &solution.binding);
        let body = super::local_types::refresh_local_expr_types(body);
        cache.insert(CachedMonomorphizeInstance {
            key,
            scheme: scheme.clone(),
            body: body.clone(),
            callee_type: solution.callee_type.clone(),
            result_type: solution.result_type.clone(),
        });
        emitted.push(Binding {
            name: solution.alias.clone(),
            type_params: Vec::new(),
            scheme,
            body,
        });
    }
    let aliases = emitted
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<Vec<_>>();
    module.bindings.extend(emitted);
    Ok(aliases)
}

pub(crate) fn rewrite_root_exprs(
    module: &mut Module,
    solutions: &[RootGraphSolution],
) -> MonomorphizeResult<()> {
    let mut solutions_by_root = HashMap::<usize, Vec<&RootGraphSolution>>::new();
    for solution in solutions {
        let RootGraphRoot::Expr(root_index) = solution.root else {
            continue;
        };
        solutions_by_root
            .entry(root_index)
            .or_default()
            .push(solution);
    }
    for (root_index, root_solutions) in solutions_by_root {
        let Some(expr) = module.root_exprs.get_mut(root_index) else {
            continue;
        };
        let mut cursor = 0;
        rewrite_root_expr(expr, &root_solutions, &mut cursor)?;
    }
    Ok(())
}

pub(crate) fn rewrite_binding_exprs(
    module: &mut Module,
    solutions: &[RootGraphSolution],
) -> MonomorphizeResult<()> {
    let mut solutions_by_binding = HashMap::<typed_ir::Path, Vec<&RootGraphSolution>>::new();
    for solution in solutions {
        let RootGraphRoot::Binding(binding) = &solution.root else {
            continue;
        };
        solutions_by_binding
            .entry(binding.clone())
            .or_default()
            .push(solution);
    }
    for binding in &mut module.bindings {
        let Some(binding_solutions) = solutions_by_binding.remove(&binding.name) else {
            continue;
        };
        let mut cursor = 0;
        rewrite_root_expr(&mut binding.body, &binding_solutions, &mut cursor)?;
    }
    Ok(())
}

fn rewrite_root_expr(
    expr: &mut Expr,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> MonomorphizeResult<()> {
    if rewrite_polymorphic_var(expr, solutions, cursor) {
        return Ok(());
    }
    if matches!(expr.kind, ExprKind::Apply { .. }) && apply_spine_binding(expr).is_some() {
        rewrite_apply_spine_args(expr, solutions, cursor)?;
        rewrite_simple_apply(expr, solutions, cursor)?;
        return Ok(());
    }
    yulang_runtime_ir::walk::walk_children_try_mut(expr, |child| {
        rewrite_root_expr(child, solutions, cursor)
    })
}

fn rewrite_polymorphic_var(
    expr: &mut Expr,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> bool {
    let ExprKind::Var(path) = &mut expr.kind else {
        return false;
    };
    let Some(solution) = solutions.get(*cursor) else {
        return false;
    };
    if solution.binding != *path {
        return false;
    }
    *path = solution.alias.clone();
    expr.ty = solution.result_type.clone();
    *cursor += 1;
    true
}

fn rewrite_apply_spine_args(
    expr: &mut Expr,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> MonomorphizeResult<()> {
    let ExprKind::Apply { callee, arg, .. } = &mut expr.kind else {
        return Ok(());
    };
    rewrite_apply_spine_args(callee, solutions, cursor)?;
    rewrite_root_expr(arg, solutions, cursor)
}

fn rewrite_simple_apply(
    expr: &mut Expr,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> MonomorphizeResult<bool> {
    if !matches!(expr.kind, ExprKind::Apply { .. }) {
        return Ok(false);
    };
    let Some(binding_path) = apply_spine_binding(expr) else {
        return Ok(false);
    };
    let Some(solution) = solutions.get(*cursor) else {
        return Ok(false);
    };
    if solution.binding != *binding_path {
        return Ok(false);
    }
    replace_apply_spine_binding(expr, &solution.alias, &solution.callee_type);
    materialize::materialize_expr_in_place(expr, &solution.type_substitutions);
    clear_apply_spine_instantiations(expr, &solution.binding);
    refresh_apply_spine_runtime_types(expr, solution.callee_type.clone());
    expr.ty = solution.result_type.clone();
    *cursor += 1;
    Ok(true)
}

fn refresh_apply_spine_runtime_types(expr: &mut Expr, callee_type: RuntimeType) -> RuntimeType {
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            let callee_type = refresh_apply_spine_runtime_types(callee, callee_type);
            if let Some(param) = super::runtime_function_param(&callee_type) {
                super::narrow_runtime_type_in_place(&mut arg.ty, &param);
            }
            if let Some(ret) = runtime_function_ret(&callee_type) {
                expr.ty = ret.clone();
                ret
            } else {
                expr.ty.clone()
            }
        }
        ExprKind::Var(_) => {
            expr.ty = callee_type.clone();
            callee_type
        }
        _ => expr.ty.clone(),
    }
}

fn runtime_function_ret(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { ret, .. } => Some((**ret).clone()),
        RuntimeType::Value(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) => Some(runtime_type_from_core_value_and_effect(
            ret.as_ref().clone(),
            ret_effect.as_ref().clone(),
        )),
        RuntimeType::Unknown | RuntimeType::Value(_) | RuntimeType::Thunk { .. } => None,
    }
}

pub(crate) fn apply_spine_binding(expr: &Expr) -> Option<&typed_ir::Path> {
    let mut current = expr;
    while let ExprKind::Apply { callee, .. } = &current.kind {
        current = callee;
    }
    let ExprKind::Var(path) = &current.kind else {
        return None;
    };
    Some(path)
}

pub(crate) fn replace_apply_spine_binding(
    expr: &mut Expr,
    alias: &typed_ir::Path,
    callee_type: &RuntimeType,
) {
    match &mut expr.kind {
        ExprKind::Apply { callee, .. } => replace_apply_spine_binding(callee, alias, callee_type),
        ExprKind::Var(path) => {
            *path = alias.clone();
            expr.ty = callee_type.clone();
        }
        _ => {}
    }
}

fn clear_apply_spine_instantiations(expr: &mut Expr, binding: &typed_ir::Path) {
    if let ExprKind::Apply {
        callee,
        instantiation,
        ..
    } = &mut expr.kind
    {
        if instantiation
            .as_ref()
            .is_some_and(|instantiation| instantiation.target == *binding)
        {
            *instantiation = None;
        }
        clear_apply_spine_instantiations(callee, binding);
    }
}

fn clear_binding_instantiations(expr: &mut Expr, binding: &typed_ir::Path) {
    if let ExprKind::Apply { instantiation, .. } = &mut expr.kind
        && instantiation
            .as_ref()
            .is_some_and(|instantiation| instantiation.target == *binding)
    {
        *instantiation = None;
    }
    yulang_runtime_ir::walk::walk_children_mut(expr, |child| {
        clear_binding_instantiations(child, binding);
    });
}

fn solution_instance_key(solution: &RootGraphSolution) -> MonomorphizeInstanceKey {
    MonomorphizeInstanceKey {
        binding: solution.binding.clone(),
        substitutions: solution.type_substitutions.clone(),
        callee_type: solution.callee_type.clone(),
    }
}

pub(crate) fn alias_path(original: &typed_ir::Path, index: usize) -> typed_ir::Path {
    let mut segments = original.segments.clone();
    segments.push(typed_ir::Name(format!("mono{index}")));
    typed_ir::Path::new(segments)
}

#[cfg(test)]
mod tests {
    use super::*;

    use yulang_runtime_ir::{TypeInstantiation, TypeSubstitution};

    #[test]
    fn clear_binding_instantiations_removes_only_self_targeted_instantiations() {
        let binding = path("dispatch");
        let other = path("other");
        let mut expr = apply(
            apply(var("dispatch"), tuple(), Some(instantiation(other.clone()))),
            apply(
                var("dispatch"),
                tuple(),
                Some(instantiation(binding.clone())),
            ),
            Some(instantiation(binding.clone())),
        );

        clear_binding_instantiations(&mut expr, &binding);

        let ExprKind::Apply {
            callee,
            arg,
            instantiation,
            ..
        } = &expr.kind
        else {
            panic!("expected outer apply");
        };
        assert!(instantiation.is_none());

        let ExprKind::Apply {
            instantiation: other_instantiation,
            ..
        } = &callee.kind
        else {
            panic!("expected callee apply");
        };
        assert_eq!(
            other_instantiation
                .as_ref()
                .map(|instantiation| &instantiation.target),
            Some(&other)
        );

        let ExprKind::Apply {
            instantiation: self_instantiation,
            ..
        } = &arg.kind
        else {
            panic!("expected arg apply");
        };
        assert!(self_instantiation.is_none());
    }

    fn apply(callee: Expr, arg: Expr, instantiation: Option<TypeInstantiation>) -> Expr {
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: None,
                instantiation,
            },
            RuntimeType::Unknown,
        )
    }

    fn var(name: &str) -> Expr {
        Expr::typed(ExprKind::Var(path(name)), RuntimeType::Unknown)
    }

    fn tuple() -> Expr {
        Expr::typed(
            ExprKind::Tuple(Vec::new()),
            RuntimeType::Value(typed_ir::Type::Tuple(Vec::new())),
        )
    }

    fn instantiation(target: typed_ir::Path) -> TypeInstantiation {
        TypeInstantiation {
            target,
            args: vec![TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: typed_ir::Type::Any,
            }],
        }
    }

    fn path(name: &str) -> typed_ir::Path {
        typed_ir::Path::new(vec![typed_ir::Name(name.into())])
    }
}
