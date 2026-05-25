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

use yulang_runtime_ir::{Binding, Expr, ExprKind, Module, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{
    CachedFinalizeInstance, FinalizeDiagnostic, FinalizeInstanceCache, FinalizeInstanceKey,
    FinalizeResult, RootGraphSolution, graph::runtime_type_from_core_value_and_effect,
    output::RootGraphRoot,
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
    cache: &mut FinalizeInstanceCache,
) -> FinalizeResult<Vec<typed_ir::Path>> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.clone()))
        .collect::<HashMap<_, _>>();
    let mut emitted_aliases = module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let emitted = solutions
        .iter()
        .filter(|solution| emitted_aliases.insert(solution.alias.clone()))
        .map(|solution| {
            let key = solution_instance_key(solution);
            if let Some(cached) = cache.get(&key) {
                return Ok(cached.binding_with_alias(solution.alias.clone()));
            }
            let binding = bindings.get(&solution.binding).ok_or_else(|| {
                FinalizeDiagnostic::MissingBinding {
                    binding: solution.binding.clone(),
                }
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
            cache.insert(CachedFinalizeInstance {
                key,
                scheme: scheme.clone(),
                body: body.clone(),
                callee_type: solution.callee_type.clone(),
                result_type: solution.result_type.clone(),
            });
            Ok(Binding {
                name: solution.alias.clone(),
                type_params: Vec::new(),
                scheme,
                body,
            })
        })
        .collect::<FinalizeResult<Vec<_>>>()?;
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
) -> FinalizeResult<()> {
    for (root_index, expr) in module.root_exprs.iter_mut().enumerate() {
        let root_solutions = solutions
            .iter()
            .filter(|solution| solution.root == RootGraphRoot::Expr(root_index))
            .collect::<Vec<_>>();
        let mut cursor = 0;
        rewrite_root_expr(expr, &root_solutions, &mut cursor)?;
    }
    Ok(())
}

pub(crate) fn rewrite_binding_exprs(
    module: &mut Module,
    solutions: &[RootGraphSolution],
) -> FinalizeResult<()> {
    for binding in &mut module.bindings {
        let binding_solutions = solutions
            .iter()
            .filter(|solution| solution.root == RootGraphRoot::Binding(binding.name.clone()))
            .collect::<Vec<_>>();
        let mut cursor = 0;
        rewrite_root_expr(&mut binding.body, &binding_solutions, &mut cursor)?;
    }
    Ok(())
}

fn rewrite_root_expr(
    expr: &mut Expr,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> FinalizeResult<()> {
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
) -> FinalizeResult<()> {
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
) -> FinalizeResult<bool> {
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
        RuntimeType::Core(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) => Some(runtime_type_from_core_value_and_effect(
            ret.as_ref().clone(),
            ret_effect.as_ref().clone(),
        )),
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Thunk { .. } => None,
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

fn solution_instance_key(solution: &RootGraphSolution) -> FinalizeInstanceKey {
    FinalizeInstanceKey {
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
