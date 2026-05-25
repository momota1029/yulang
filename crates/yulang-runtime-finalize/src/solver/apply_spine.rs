//! Apply-spine collection and monomorphic solving.
//!
//! For every observed apply spine `f a b c ...` over a polymorphic binding,
//! this module:
//!
//!   - traverses the module to discover spines (`collect_root_expr_graphs`,
//!     `collect_binding_body_graphs`, `collect_expr_graphs`)
//!   - turns each spine into a fresh monomorphic `TypeGraph` by instantiating
//!     the binding's principal and constraining argument/result slots from
//!     the apply evidence (`solve_simple_apply`, `solve_value_arg`,
//!     `ApplySpine`, `ApplyStep`)
//!   - solves the graph and packages the result as a `RootGraphSolution`
//!     (`solve_root_graphs`, `solve_bare_polymorphic_var`,
//!     `solve_monomorphic_contextual_apply`)
//!   - extracts the substitutions implied by the evidence and the apply
//!     spine's value arguments (`collect_spine_substitutions`,
//!     `default_spine_evidence_substitutions`)
//!   - exposes predicates the rest of the pipeline needs:
//!     `apply_evidence_return_value`, `apply_evidence_returns_never_value`.
//!
//! The `ApplySpine` / `ApplyStep` types are the shared representation for the
//! `role` and `rewrite` modules — both consume spines once they are solved.

use std::collections::{BTreeSet, HashMap, HashSet};

use yulang_runtime_ir::{
    FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
    FinalizedModule as Module, FinalizedType as RuntimeType, Root,
};
use yulang_typed_ir as typed_ir;

use crate::{
    FinalizeDiagnostic, FinalizeResult, RootGraphInput, RootGraphSolution, TypeGraph,
    graph::{TypeCastOrder, runtime_type_from_core_value, runtime_type_from_core_value_and_effect},
    materialize_runtime_type,
    output::RootGraphRoot,
};

use super::{rewrite, role};

pub fn collect_root_graph_inputs(module: &Module) -> Vec<RootGraphInput> {
    module
        .roots
        .iter()
        .filter_map(|root| match root {
            Root::Binding(path) => Some(RootGraphInput {
                root: RootGraphRoot::Binding(path.clone()),
                known_type: None,
            }),
            Root::Expr(index) => module.root_exprs.get(*index).map(|expr| RootGraphInput {
                root: RootGraphRoot::Expr(*index),
                known_type: super::runtime_type_is_closed(&expr.ty).then(|| expr.ty.clone()),
            }),
        })
        .collect()
}

pub fn solve_root_graphs(
    module: &Module,
    cast_order: &TypeCastOrder,
) -> FinalizeResult<Vec<RootGraphSolution>> {
    let mut solutions = Vec::new();
    collect_root_expr_graphs(module, cast_order, &mut solutions)?;
    Ok(solutions)
}

pub(crate) fn collect_root_expr_graphs(
    module: &Module,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    for root in &module.roots {
        let Root::Expr(index) = root else {
            continue;
        };
        let expr = module
            .root_exprs
            .get(*index)
            .ok_or(FinalizeDiagnostic::UnsupportedRootShape)?;
        collect_expr_graphs(
            RootGraphRoot::Expr(*index),
            expr,
            &bindings,
            &module.role_impls,
            &HashMap::new(),
            cast_order,
            solutions,
        )?;
    }
    Ok(())
}

pub(crate) fn collect_binding_body_graphs(
    module: &Module,
    aliases: &[typed_ir::Path],
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    for alias in aliases {
        let Some(binding) = bindings.get(alias) else {
            return Err(FinalizeDiagnostic::MissingBinding {
                binding: alias.clone(),
            });
        };
        collect_expr_graphs(
            RootGraphRoot::Binding(alias.clone()),
            &binding.body,
            &bindings,
            &module.role_impls,
            &binding_local_types(binding),
            cast_order,
            solutions,
        )?;
    }
    Ok(())
}

pub(crate) fn next_binding_body_scan_targets(
    module: &Module,
    emitted: &[typed_ir::Path],
    scanned: &mut HashSet<typed_ir::Path>,
) -> Vec<typed_ir::Path> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.type_params.is_empty()))
        .collect::<HashMap<_, _>>();
    let reachable = super::reachable_paths(module);
    let mut targets = Vec::new();
    let mut pushed = HashSet::new();
    for path in emitted {
        if !bindings.contains_key(path) {
            continue;
        }
        if scanned.insert(path.clone()) && pushed.insert(path.clone()) {
            targets.push(path.clone());
        }
    }
    for path in reachable.iter() {
        if !bindings.get(path).copied().unwrap_or(false) {
            continue;
        }
        if scanned.insert(path.clone()) && pushed.insert(path.clone()) {
            targets.push(path.clone());
        }
    }
    targets
}

pub(crate) fn collect_expr_graphs(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    let found = solve_simple_apply(
        owner.clone(),
        expr,
        bindings,
        role_impls,
        local_types,
        cast_order,
        solutions.len(),
    )?;
    if !found.is_empty() {
        collect_apply_spine_arg_graphs(
            owner,
            expr,
            bindings,
            role_impls,
            local_types,
            cast_order,
            solutions,
        )?;
        solutions.extend(found);
        return Ok(());
    }
    if let Some(solution) = solve_bare_polymorphic_var(
        owner.clone(),
        expr,
        bindings,
        local_types,
        cast_order,
        solutions.len(),
    )? {
        solutions.push(solution);
        return Ok(());
    }
    match &expr.kind {
        ExprKind::Lambda { param, body, .. } => {
            let mut scoped_locals = local_types.clone();
            if let Some(param_ty) = super::runtime_function_param(&expr.ty) {
                scoped_locals.insert(super::path_from_name(param), param_ty);
            }
            collect_expr_graphs(
                owner,
                body,
                bindings,
                role_impls,
                &scoped_locals,
                cast_order,
                solutions,
            )
        }
        ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => collect_expr_graphs(
            owner,
            body,
            bindings,
            role_impls,
            local_types,
            cast_order,
            solutions,
        ),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_graphs(
                owner.clone(),
                callee,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            collect_expr_graphs(
                owner,
                arg,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_graphs(
                owner.clone(),
                cond,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            collect_expr_graphs(
                owner.clone(),
                then_branch,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            collect_expr_graphs(
                owner,
                else_branch,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_graphs(
                    owner.clone(),
                    item,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_graphs(
                    owner.clone(),
                    &field.value,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            if let Some(spread) = spread {
                collect_record_spread_graphs(
                    owner,
                    spread,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_graphs(
                    owner,
                    value,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        ExprKind::Select { base, .. } | ExprKind::Thunk { expr: base, .. } => collect_expr_graphs(
            owner,
            base,
            bindings,
            role_impls,
            local_types,
            cast_order,
            solutions,
        ),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_graphs(
                owner.clone(),
                scrutinee,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            let scrutinee_ty = expr_lower_type(scrutinee, local_types);
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.pattern, Some(&scrutinee_ty), &mut arm_locals);
                if let Some(guard) = &arm.guard {
                    collect_expr_graphs(
                        owner.clone(),
                        guard,
                        bindings,
                        role_impls,
                        &arm_locals,
                        cast_order,
                        solutions,
                    )?;
                }
                collect_expr_graphs(
                    owner.clone(),
                    &arm.body,
                    bindings,
                    role_impls,
                    &arm_locals,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, tail } => {
            let mut scoped_locals = local_types.clone();
            for stmt in stmts {
                collect_stmt_graphs(
                    owner.clone(),
                    stmt,
                    bindings,
                    role_impls,
                    &scoped_locals,
                    cast_order,
                    solutions,
                )?;
                collect_stmt_local_types(stmt, &mut scoped_locals);
            }
            if let Some(tail) = tail {
                collect_expr_graphs(
                    owner,
                    tail,
                    bindings,
                    role_impls,
                    &scoped_locals,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_graphs(
                owner.clone(),
                body,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.payload, None, &mut arm_locals);
                if let Some(resume) = &arm.resume {
                    arm_locals.insert(super::path_from_name(&resume.name), resume.ty.clone());
                }
                if let Some(guard) = &arm.guard {
                    collect_expr_graphs(
                        owner.clone(),
                        guard,
                        bindings,
                        role_impls,
                        &arm_locals,
                        cast_order,
                        solutions,
                    )?;
                }
                collect_expr_graphs(
                    owner.clone(),
                    &arm.body,
                    bindings,
                    role_impls,
                    &arm_locals,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

pub(crate) fn collect_apply_spine_arg_graphs(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    let ExprKind::Apply { callee, arg, .. } = &expr.kind else {
        return Ok(());
    };
    collect_apply_spine_arg_graphs(
        owner.clone(),
        callee,
        bindings,
        role_impls,
        local_types,
        cast_order,
        solutions,
    )?;
    collect_expr_graphs(
        owner,
        arg,
        bindings,
        role_impls,
        local_types,
        cast_order,
        solutions,
    )
}

pub(crate) fn solve_bare_polymorphic_var(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    alias_index: usize,
) -> FinalizeResult<Option<RootGraphSolution>> {
    let ExprKind::Var(path) = &expr.kind else {
        return Ok(None);
    };
    let Some(binding) = bindings.get(path) else {
        return Ok(None);
    };
    if binding.type_params.is_empty() {
        return Ok(None);
    }
    let expected = super::runtime_type_to_core(expr_lower_type(expr, local_types));
    if !super::core_type_is_closed(&expected) {
        return Ok(None);
    }
    solve_value_arg(owner, binding, expected, cast_order, alias_index).map(Some)
}

pub(crate) fn solve_simple_apply(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    alias_index: usize,
) -> FinalizeResult<Vec<RootGraphSolution>> {
    let Some(spine) = ApplySpine::new(expr) else {
        return Ok(Vec::new());
    };
    let binding_path = spine.binding;
    let Some(binding) = bindings.get(binding_path) else {
        return Ok(Vec::new());
    };
    let mut solutions = solve_spine_value_args(
        owner.clone(),
        &spine,
        bindings,
        local_types,
        cast_order,
        alias_index,
    )?;
    if binding.type_params.is_empty() {
        if let Some(solution) = solve_monomorphic_contextual_apply(
            owner,
            expr,
            binding_path,
            binding,
            &spine,
            local_types,
            alias_index + solutions.len(),
        ) {
            solutions.push(solution);
        }
        return Ok(solutions);
    }
    let mut graph = TypeGraph::with_cast_order(cast_order.clone());
    let principal = graph.instantiate_principal(binding);
    let role_required_binding = !binding.scheme.requirements.is_empty();
    if !role_required_binding {
        graph.collect_runtime_bounds(
            &principal.principal_type,
            &crate::RuntimeBounds {
                lower: Some(apply_callee_lower_bound(spine.callee.ty.clone())),
                upper: Some(spine.callee.ty.clone()),
            },
        )?;
    }
    if !role_required_binding {
        collect_spine_substitutions(&mut graph, &principal, &spine.steps)?;
    }
    let mut current = principal.principal_type.clone();
    let mut current_template = principal.principal_type.clone();
    let mut apply_value_vars = BTreeSet::new();
    let mut apply_effect_vars = BTreeSet::new();
    for step in &spine.steps {
        let (arg_type, arg_effect) = step.arg_type_and_effect(local_types);
        let template_return = role_required_binding
            .then(|| function_return_template_parts(&current_template))
            .flatten();
        let result = if let Some((result, _)) = &template_return {
            result.clone()
        } else {
            let result = graph.fresh_hole("apply");
            if let typed_ir::Type::Var(var) = &result {
                apply_value_vars.insert(var.clone());
            }
            result
        };
        let result_effect = template_return
            .as_ref()
            .map(|(_, effect)| effect.clone())
            .unwrap_or_else(|| graph.fresh_hole("apply_effect"));
        if let typed_ir::Type::Var(var) = &result_effect {
            apply_effect_vars.insert(var.clone());
        }
        let expected = typed_ir::Type::Fun {
            param: Box::new(arg_type),
            param_effect: Box::new(arg_effect),
            ret_effect: Box::new(result_effect.clone()),
            ret: Box::new(result.clone()),
        };
        graph.constrain_subtype(current, expected)?;
        step.constrain_result_bounds(&mut graph, result.clone(), result_effect, local_types)?;
        current = result;
        current_template =
            function_return_template(current_template).unwrap_or(typed_ir::Type::Unknown);
    }
    default_spine_evidence_substitutions(&mut graph, &principal, &spine.steps)?;
    graph.default_unbound_lower(apply_value_vars, typed_ir::Type::Unknown)?;
    graph.default_unbound_lower(principal.effect_only_type_params(), typed_ir::Type::Never)?;
    graph.default_unbound_lower(apply_effect_vars, typed_ir::Type::Never)?;
    let solved = graph.clone().solve();
    let graph = if role_required_binding
        && (!solved.is_complete() || role::solution_has_unknown_components(&solved))
        && role::close_role_associated_types(&mut graph, binding, &principal, &solved, role_impls)?
    {
        graph.solve()
    } else {
        solved
    };
    if !graph.is_complete() {
        if role::role_required_apply_waiting_for_arguments(binding, &spine, local_types) {
            return Ok(solutions);
        }
        return Err(FinalizeDiagnostic::IncompleteGraph {
            binding: binding_path.clone(),
        });
    }
    let result_type = if role_required_binding {
        runtime_type_from_core_value(graph.materialize_core(current))
    } else {
        solved_expr_result_type(&expr.ty, &graph, current)
    };
    let callee_type = solved_callee_finalized_type(binding, &principal, &graph);
    let callee_type =
        super::finalized_apply_spine_arg_effects(callee_type, &spine.steps, local_types);
    let callee_type =
        super::refine_runtime_spine_return(callee_type, spine.steps.len(), result_type.clone());
    let type_substitutions = principal.original_substitutions(&graph);
    solutions.push(RootGraphSolution {
        root: owner,
        occurrence: alias_index + solutions.len(),
        binding: binding_path.clone(),
        alias: rewrite::alias_path(binding_path, alias_index + solutions.len()),
        callee_type,
        result_type,
        graph,
        type_substitutions,
    });
    Ok(solutions)
}

pub(crate) fn solve_monomorphic_contextual_apply(
    owner: RootGraphRoot,
    expr: &Expr,
    binding_path: &typed_ir::Path,
    binding: &Binding,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    alias_index: usize,
) -> Option<RootGraphSolution> {
    let _ = (
        owner,
        expr,
        binding_path,
        binding,
        spine,
        local_types,
        alias_index,
    );
    None
}

fn solved_expr_result_type(
    expr_ty: &RuntimeType,
    graph: &crate::GraphSolution,
    result: typed_ir::Type,
) -> RuntimeType {
    let materialized = materialize_runtime_type(expr_ty.clone(), &graph.substitutions());
    if super::runtime_type_is_closed(&materialized) {
        materialized
    } else {
        runtime_type_from_core_value(graph.materialize_core(result))
    }
}

fn solved_callee_finalized_type(
    binding: &Binding,
    principal: &crate::PrincipalInstance,
    graph: &crate::GraphSolution,
) -> RuntimeType {
    let principal_runtime =
        runtime_type_from_core_value(graph.materialize_core(principal.principal_type.clone()));
    let materialized = materialize_runtime_type(
        binding.body.ty.clone(),
        &principal.original_substitutions(graph),
    );
    if super::runtime_type_is_closed(&materialized) {
        super::finalized_effect_boundaries_from_principal(materialized, &principal_runtime)
    } else {
        principal_runtime
    }
}

fn solve_spine_value_args(
    owner: RootGraphRoot,
    spine: &ApplySpine<'_>,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    alias_index: usize,
) -> FinalizeResult<Vec<RootGraphSolution>> {
    let mut solutions = Vec::new();
    for step in &spine.steps {
        let ExprKind::Var(arg_binding_path) = &step.arg.kind else {
            continue;
        };
        let Some(binding) = bindings.get(arg_binding_path) else {
            continue;
        };
        if binding.type_params.is_empty() {
            continue;
        }
        let solution = solve_value_arg(
            owner.clone(),
            binding,
            step.arg_type(local_types),
            cast_order,
            alias_index + solutions.len(),
        )?;
        solutions.push(solution);
    }
    Ok(solutions)
}

fn solve_value_arg(
    owner: RootGraphRoot,
    binding: &Binding,
    expected_type: typed_ir::Type,
    cast_order: &TypeCastOrder,
    alias_index: usize,
) -> FinalizeResult<RootGraphSolution> {
    let mut graph = TypeGraph::with_cast_order(cast_order.clone());
    let principal = graph.instantiate_principal(binding);
    graph.constrain_subtype(principal.principal_type.clone(), expected_type)?;
    graph.default_unbound_lower(principal.effect_only_type_params(), typed_ir::Type::Never)?;
    let graph = graph.solve();
    if !graph.is_complete() {
        return Err(FinalizeDiagnostic::IncompleteGraph {
            binding: binding.name.clone(),
        });
    }
    let callee_type =
        runtime_type_from_core_value(graph.materialize_core(principal.principal_type.clone()));
    let type_substitutions = principal.original_substitutions(&graph);
    Ok(RootGraphSolution {
        root: owner,
        occurrence: alias_index,
        binding: binding.name.clone(),
        alias: rewrite::alias_path(&binding.name, alias_index),
        result_type: callee_type.clone(),
        callee_type,
        graph,
        type_substitutions,
    })
}

fn collect_spine_substitutions(
    graph: &mut TypeGraph,
    principal: &crate::PrincipalInstance,
    steps: &[ApplyStep<'_>],
) -> FinalizeResult<()> {
    for step in steps {
        if let Some(instantiation) = step.instantiation {
            for substitution in &instantiation.args {
                collect_spine_substitution(graph, principal, &substitution.var, &substitution.ty)?;
            }
        }
    }
    Ok(())
}

fn collect_spine_substitution(
    graph: &mut TypeGraph,
    principal: &crate::PrincipalInstance,
    var: &typed_ir::TypeVar,
    ty: &typed_ir::Type,
) -> FinalizeResult<()> {
    let Some(param) = principal
        .type_params
        .iter()
        .find(|param| param.original == *var)
    else {
        return Ok(());
    };
    graph.constrain_subtype(ty.clone(), typed_ir::Type::Var(param.fresh.clone()))
}

fn default_spine_evidence_substitutions(
    graph: &mut TypeGraph,
    principal: &crate::PrincipalInstance,
    steps: &[ApplyStep<'_>],
) -> FinalizeResult<()> {
    for step in steps {
        let Some(evidence) = step.evidence else {
            continue;
        };
        for substitution in &evidence.substitutions {
            default_spine_evidence_substitution(
                graph,
                principal,
                &substitution.var,
                &substitution.ty,
            )?;
        }
    }
    Ok(())
}

fn default_spine_evidence_substitution(
    graph: &mut TypeGraph,
    principal: &crate::PrincipalInstance,
    var: &typed_ir::TypeVar,
    ty: &typed_ir::Type,
) -> FinalizeResult<()> {
    let Some(param) = principal
        .type_params
        .iter()
        .find(|param| param.original == *var)
    else {
        return Ok(());
    };
    let is_unbound = graph
        .slot(&param.fresh)
        .is_some_and(|slot| slot.lower.is_none() && slot.upper.is_none());
    if is_unbound {
        graph.constrain_subtype(ty.clone(), typed_ir::Type::Var(param.fresh.clone()))?;
    }
    Ok(())
}

fn function_return_template(ty: typed_ir::Type) -> Option<typed_ir::Type> {
    let typed_ir::Type::Fun { ret, .. } = ty else {
        return None;
    };
    Some(*ret)
}

fn function_return_template_parts(ty: &typed_ir::Type) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let typed_ir::Type::Fun {
        ret_effect, ret, ..
    } = ty
    else {
        return None;
    };
    Some((ret.as_ref().clone(), ret_effect.as_ref().clone()))
}

fn apply_callee_lower_bound(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Fun { param, ret } => RuntimeType::Fun {
            // A polymorphic callee occurrence can carry `Any` in parameter
            // slots before the apply spine has supplied its real arguments.
            // That Top is not an instantiation lower bound; the argument and
            // evidence constraints below provide the actual lower bound.
            param: Box::new(unconstrain_top_param_runtime_bound(*param)),
            ret: Box::new(apply_callee_lower_bound(*ret)),
        },
        RuntimeType::Thunk { effect, value } => RuntimeType::Thunk {
            effect,
            value: Box::new(apply_callee_lower_bound(*value)),
        },
        RuntimeType::Value(ty) => RuntimeType::Value(apply_callee_lower_core_bound(ty)),
        ty => ty,
    }
}

fn unconstrain_top_param_runtime_bound(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Value(ty) => RuntimeType::Value(unconstrain_top_param_core_bound(ty)),
        RuntimeType::Thunk { effect, value } => RuntimeType::Thunk {
            effect,
            value: Box::new(unconstrain_top_param_runtime_bound(*value)),
        },
        RuntimeType::Fun { .. } => apply_callee_lower_bound(ty),
        RuntimeType::Unknown => RuntimeType::Unknown,
    }
}

fn apply_callee_lower_core_bound(ty: typed_ir::Type) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(unconstrain_top_param_core_bound(*param)),
            param_effect,
            ret_effect,
            ret: Box::new(apply_callee_lower_core_bound(*ret)),
        },
        ty => ty,
    }
}

fn unconstrain_top_param_core_bound(ty: typed_ir::Type) -> typed_ir::Type {
    if matches!(ty, typed_ir::Type::Any) {
        typed_ir::Type::Unknown
    } else if matches!(ty, typed_ir::Type::Fun { .. }) {
        apply_callee_lower_core_bound(ty)
    } else {
        ty
    }
}

pub(crate) struct ApplySpine<'a> {
    pub(crate) binding: &'a typed_ir::Path,
    pub(crate) callee: &'a Expr,
    pub(crate) steps: Vec<ApplyStep<'a>>,
}

pub(crate) struct ApplyStep<'a> {
    pub(crate) apply: &'a Expr,
    pub(crate) arg: &'a Expr,
    pub(crate) evidence: Option<&'a typed_ir::ApplyEvidence>,
    pub(crate) instantiation: Option<&'a yulang_runtime_ir::TypeInstantiation>,
}

impl ApplyStep<'_> {
    pub(crate) fn arg_type(
        &self,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> typed_ir::Type {
        self.arg_type_and_effect(local_types).0
    }

    pub(crate) fn arg_type_and_effect(
        &self,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> (typed_ir::Type, typed_ir::Type) {
        if let Some((value, effect)) = bind_here_arg_type_and_effect(self.arg, local_types) {
            return (value, effect);
        }
        let runtime_ty = expr_lower_type(self.arg, local_types);
        if let RuntimeType::Thunk { effect, value } = &runtime_ty {
            if runtime_type_is_never_value(value)
                && let Some(arg_type) = effect_carrier_value_hint(effect)
            {
                return (arg_type, typed_ir::Type::Never);
            }
            let value_is_closed = super::runtime_type_is_closed(value);
            let arg_type = if value_is_closed {
                super::runtime_type_to_core((**value).clone())
            } else {
                let expr_ty = super::runtime_type_to_core(runtime_ty.clone());
                self.evidence.and_then(apply_arg_type).unwrap_or(expr_ty)
            };
            let arg_effect = if super::core_type_is_closed(effect)
                && (value_is_closed || !matches!(effect, typed_ir::Type::Any))
            {
                effect.clone()
            } else {
                typed_ir::Type::Never
            };
            return (arg_type, arg_effect);
        }
        let expr_ty = super::runtime_type_to_core(runtime_ty);
        if super::core_type_is_closed(&expr_ty) {
            return (expr_ty, typed_ir::Type::Never);
        }
        let fallback = self.evidence.and_then(apply_arg_type).unwrap_or(expr_ty);
        (fallback, typed_ir::Type::Never)
    }

    pub(crate) fn constrain_result_bounds(
        &self,
        graph: &mut TypeGraph,
        result: typed_ir::Type,
        result_effect: typed_ir::Type,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> FinalizeResult<()> {
        let evidence_value_bound = self
            .evidence
            .map(|evidence| constrain_core_type_bounds(graph, result.clone(), &evidence.result))
            .transpose()?
            .unwrap_or(false);
        if let Some(evidence) = self.evidence {
            constrain_apply_result_effect_bounds(graph, result_effect.clone(), evidence)?;
        }
        let apply_ty = expr_lower_type(self.apply, local_types);
        match apply_ty {
            RuntimeType::Unknown => Ok(()),
            RuntimeType::Thunk { effect, value } => {
                if !(evidence_value_bound && runtime_type_value_is_function(&value)) {
                    graph
                        .constrain_subtype(result, super::runtime_type_to_core((*value).clone()))?;
                }
                let evidence_returns_never = self
                    .evidence
                    .is_some_and(apply_evidence_returns_never_value);
                let effect = if evidence_returns_never || runtime_type_is_never_value(&value) {
                    effect_carrier_value_hint(&effect).unwrap_or(effect)
                } else {
                    effect
                };
                if matches!(effect, typed_ir::Type::Never | typed_ir::Type::Unknown) {
                    Ok(())
                } else {
                    graph.constrain_subtype(result_effect, effect)
                }
            }
            ty if evidence_value_bound && runtime_type_value_is_function(&ty) => Ok(()),
            ty => graph.constrain_subtype(result, super::runtime_type_to_core(ty)),
        }
    }
}

fn bind_here_arg_type_and_effect(
    arg: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let ExprKind::BindHere { expr } = &arg.kind else {
        return None;
    };
    expr_value_and_effect(expr, local_types)
}

fn expr_value_and_effect(
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    if let RuntimeType::Thunk { effect, value } = expr_lower_type(expr, local_types) {
        let value = super::runtime_type_to_core(*value);
        let effect = closed_or_empty_effect(effect);
        return Some((value, effect));
    }
    let ExprKind::Apply { evidence, .. } = &expr.kind else {
        return None;
    };
    let evidence = evidence.as_ref()?;
    let value = type_from_bounds(&evidence.result)
        .filter(super::core_type_is_closed)
        .or_else(|| {
            let value = super::runtime_type_to_core(expr_lower_type(expr, local_types));
            super::core_type_is_closed(&value).then_some(value)
        })?;
    let effect = apply_evidence_return_effect(evidence)
        .map(closed_or_empty_effect)
        .unwrap_or(typed_ir::Type::Never);
    Some((value, effect))
}

fn closed_or_empty_effect(effect: typed_ir::Type) -> typed_ir::Type {
    if super::core_type_is_closed(&effect) {
        effect
    } else {
        typed_ir::Type::Never
    }
}

fn constrain_core_type_bounds(
    graph: &mut TypeGraph,
    ty: typed_ir::Type,
    bounds: &typed_ir::TypeBounds,
) -> FinalizeResult<bool> {
    let mut constrained = false;
    if let Some(lower) = bounds.lower.as_deref() {
        graph.constrain_subtype(lower.clone(), ty.clone())?;
        constrained = true;
    }
    if let Some(upper) = bounds.upper.as_deref() {
        graph.constrain_subtype(ty.clone(), upper.clone())?;
        constrained = true;
    }
    Ok(constrained)
}

fn constrain_apply_result_effect_bounds(
    graph: &mut TypeGraph,
    effect: typed_ir::Type,
    evidence: &typed_ir::ApplyEvidence,
) -> FinalizeResult<bool> {
    let mut constrained = false;
    if let Some(expected) = &evidence.expected_callee {
        constrained |= constrain_function_ret_effect_bounds(graph, effect.clone(), expected)?;
    }
    constrained |= constrain_function_ret_effect_bounds(graph, effect, &evidence.callee)?;
    Ok(constrained)
}

fn constrain_function_ret_effect_bounds(
    graph: &mut TypeGraph,
    effect: typed_ir::Type,
    bounds: &typed_ir::TypeBounds,
) -> FinalizeResult<bool> {
    let mut constrained = false;
    if let Some(lower) = bounds.lower.as_deref().and_then(function_ret_effect) {
        graph.constrain_subtype(lower.clone(), effect.clone())?;
        constrained = true;
    }
    if let Some(upper) = bounds.upper.as_deref().and_then(function_ret_effect) {
        graph.constrain_subtype(effect, upper.clone())?;
        constrained = true;
    }
    Ok(constrained)
}

fn function_ret_effect(ty: &typed_ir::Type) -> Option<&typed_ir::Type> {
    let typed_ir::Type::Fun { ret_effect, .. } = ty else {
        return None;
    };
    Some(ret_effect)
}

fn apply_evidence_return_effect(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    apply_evidence_return_value(evidence).and_then(|ty| match ty {
        typed_ir::Type::Fun { ret_effect, .. } => Some(*ret_effect),
        _ => None,
    })
}

fn apply_evidence_returns_never_value(evidence: &typed_ir::ApplyEvidence) -> bool {
    apply_evidence_return_value(evidence).is_some_and(|ty| match ty {
        typed_ir::Type::Fun { ret, .. } => matches!(*ret, typed_ir::Type::Never),
        _ => false,
    })
}

fn apply_evidence_return_value(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    evidence
        .expected_callee
        .as_ref()
        .and_then(type_from_bounds)
        .or_else(|| type_from_bounds(&evidence.callee))
}

fn runtime_type_value_is_function(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Fun { .. } | RuntimeType::Value(typed_ir::Type::Fun { .. }) => true,
        RuntimeType::Thunk { value, .. } => runtime_type_value_is_function(value),
        RuntimeType::Unknown | RuntimeType::Value(_) => false,
    }
}

fn runtime_type_is_never_value(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Value(typed_ir::Type::Never) => true,
        RuntimeType::Thunk { value, .. } => runtime_type_is_never_value(value),
        RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Value(_) => false,
    }
}

fn effect_carrier_value_hint(effect: &typed_ir::Type) -> Option<typed_ir::Type> {
    match effect {
        typed_ir::Type::Named { path, .. } => Some(typed_ir::Type::Named {
            path: path.clone(),
            args: Vec::new(),
        }),
        typed_ir::Type::Row { items, .. } => items.iter().find_map(effect_carrier_value_hint),
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().find_map(effect_carrier_value_hint)
        }
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_)
        | typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record(_)
        | typed_ir::Type::Variant(_)
        | typed_ir::Type::Recursive { .. } => None,
    }
}

impl<'a> ApplySpine<'a> {
    pub(crate) fn new(expr: &'a Expr) -> Option<Self> {
        let mut steps = Vec::new();
        let mut current = expr;
        while let ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
            ..
        } = &current.kind
        {
            steps.push(ApplyStep {
                apply: current,
                arg: arg.as_ref(),
                evidence: evidence.as_ref(),
                instantiation: instantiation.as_ref(),
            });
            current = callee;
        }
        if steps.is_empty() {
            return None;
        }
        steps.reverse();
        let ExprKind::Var(binding) = &current.kind else {
            return None;
        };
        Some(Self {
            binding,
            callee: current,
            steps,
        })
    }
}

fn apply_arg_type(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    evidence
        .expected_arg
        .as_ref()
        .and_then(type_from_bounds)
        .or_else(|| type_from_bounds(&evidence.arg))
}

pub(crate) fn apply_observed_arg_type(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<typed_ir::Type> {
    type_from_bounds(&evidence.arg)
}

pub(crate) fn type_from_bounds(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    bounds
        .lower
        .as_deref()
        .cloned()
        .or_else(|| bounds.upper.as_deref().cloned())
}

fn collect_record_spread_graphs(
    owner: RootGraphRoot,
    spread: &yulang_runtime_ir::FinalizedRecordSpreadExpr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => collect_expr_graphs(
            owner,
            expr,
            bindings,
            role_impls,
            local_types,
            cast_order,
            solutions,
        ),
    }
}

fn collect_stmt_graphs(
    owner: RootGraphRoot,
    stmt: &yulang_runtime_ir::FinalizedStmt,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    match stmt {
        yulang_runtime_ir::FinalizedStmt::Let { pattern, value } => {
            collect_pattern_graphs(
                owner.clone(),
                pattern,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            collect_expr_graphs(
                owner,
                value,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )
        }
        yulang_runtime_ir::FinalizedStmt::Expr(expr)
        | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => collect_expr_graphs(
            owner,
            expr,
            bindings,
            role_impls,
            local_types,
            cast_order,
            solutions,
        ),
    }
}

fn collect_pattern_graphs(
    owner: RootGraphRoot,
    pattern: &yulang_runtime_ir::FinalizedPattern,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    use yulang_runtime_ir::FinalizedPattern as Pattern;

    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_graphs(
                    owner.clone(),
                    item,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_graphs(
                    owner.clone(),
                    item,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            if let Some(spread) = spread {
                collect_pattern_graphs(
                    owner.clone(),
                    spread,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            for item in suffix {
                collect_pattern_graphs(
                    owner.clone(),
                    item,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_graphs(
                    owner.clone(),
                    &field.pattern,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
                if let Some(default) = &field.default {
                    collect_expr_graphs(
                        owner.clone(),
                        default,
                        bindings,
                        role_impls,
                        local_types,
                        cast_order,
                        solutions,
                    )?;
                }
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::FinalizedRecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_graphs(
                            owner,
                            pattern,
                            bindings,
                            role_impls,
                            local_types,
                            cast_order,
                            solutions,
                        )?;
                    }
                }
            }
            Ok(())
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_graphs(
                    owner,
                    value,
                    bindings,
                    role_impls,
                    local_types,
                    cast_order,
                    solutions,
                )?;
            }
            Ok(())
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_graphs(
                owner.clone(),
                left,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            collect_pattern_graphs(
                owner,
                right,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )
        }
        Pattern::As { pattern, .. } => collect_pattern_graphs(
            owner,
            pattern,
            bindings,
            role_impls,
            local_types,
            cast_order,
            solutions,
        ),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => Ok(()),
    }
}

pub(crate) fn collect_stmt_local_types(
    stmt: &yulang_runtime_ir::FinalizedStmt,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
) {
    let yulang_runtime_ir::FinalizedStmt::Let { pattern, value } = stmt else {
        return;
    };
    let scrutinee_ty = expr_lower_type(value, local_types);
    collect_pattern_local_types(pattern, Some(&scrutinee_ty), local_types);
}

pub(crate) fn collect_pattern_local_types(
    pattern: &yulang_runtime_ir::FinalizedPattern,
    scrutinee_ty: Option<&RuntimeType>,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
) {
    use yulang_runtime_ir::FinalizedPattern as Pattern;

    match pattern {
        Pattern::Bind { name, ty } => {
            let chosen = choose_pattern_ty(ty, scrutinee_ty);
            local_types.insert(super::path_from_name(name), chosen);
        }
        Pattern::Tuple { items, ty } => {
            let component_tys = tuple_component_runtime_types(scrutinee_ty, ty, items.len());
            for (item, comp) in items.iter().zip(component_tys.iter()) {
                collect_pattern_local_types(item, comp.as_ref(), local_types);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_local_types(item, None, local_types);
            }
            if let Some(spread) = spread {
                collect_pattern_local_types(spread, None, local_types);
            }
            for item in suffix {
                collect_pattern_local_types(item, None, local_types);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_local_types(&field.pattern, None, local_types);
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::FinalizedRecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_local_types(pattern, None, local_types);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_local_types(value, None, local_types);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_local_types(left, scrutinee_ty, local_types);
            collect_pattern_local_types(right, scrutinee_ty, local_types);
        }
        Pattern::As { pattern, name, ty } => {
            let chosen = choose_pattern_ty(ty, scrutinee_ty);
            collect_pattern_local_types(pattern, Some(&chosen), local_types);
            local_types.insert(super::path_from_name(name), chosen);
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn choose_pattern_ty(pattern_ty: &RuntimeType, scrutinee_ty: Option<&RuntimeType>) -> RuntimeType {
    if !super::runtime_type_has_unknown(pattern_ty) {
        return pattern_ty.clone();
    }
    if let Some(scrut) = scrutinee_ty
        && !super::runtime_type_has_unknown(scrut)
    {
        return scrut.clone();
    }
    pattern_ty.clone()
}

fn tuple_component_runtime_types(
    scrutinee_ty: Option<&RuntimeType>,
    pattern_ty: &RuntimeType,
    arity: usize,
) -> Vec<Option<RuntimeType>> {
    let preferred = scrutinee_ty
        .filter(|t| !super::runtime_type_has_unknown(t))
        .cloned();
    let chosen = preferred.unwrap_or_else(|| pattern_ty.clone());
    if let RuntimeType::Value(typed_ir::Type::Tuple(items)) = &chosen
        && items.len() == arity
    {
        return items
            .iter()
            .map(|t| Some(RuntimeType::Value(t.clone())))
            .collect();
    }
    vec![None; arity]
}

pub(crate) fn binding_local_types(binding: &Binding) -> HashMap<typed_ir::Path, RuntimeType> {
    let mut local_types = HashMap::new();
    let ExprKind::Lambda { param, .. } = &binding.body.kind else {
        return local_types;
    };
    if let typed_ir::Type::Fun {
        param: param_ty,
        param_effect,
        ..
    } = &binding.scheme.body
    {
        local_types.insert(
            super::path_from_name(param),
            runtime_type_from_core_value_and_effect(
                param_ty.as_ref().clone(),
                param_effect.as_ref().clone(),
            ),
        );
    }
    local_types
}

pub(crate) fn expr_lower_type(
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeType {
    if let ExprKind::Var(path) = &expr.kind
        && let Some(ty) = local_types.get(path)
    {
        return ty.clone();
    }
    if !matches!(expr.ty, RuntimeType::Unknown) {
        return expr.ty.clone();
    }
    RuntimeType::Unknown
}
