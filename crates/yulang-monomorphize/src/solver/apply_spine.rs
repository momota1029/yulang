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
//!     `apply_evidence_return_value`.
//!
//! The `ApplySpine` / `ApplyStep` types are the shared representation for the
//! `role` and `rewrite` modules — both consume spines once they are solved.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use yulang_runtime_ir::{
    FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
    FinalizedModule as Module, Root, RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::{
    MonomorphizeDiagnostic, MonomorphizeResult, RootGraphInput, RootGraphSolution, TypeGraph,
    graph::{
        RuntimeBounds, TypeCastOrder, runtime_type_from_core_value,
        runtime_type_from_core_value_and_effect,
    },
    materialize_runtime_type,
    output::RootGraphRoot,
};

use super::{
    pattern_types::{
        choose_pattern_ty, record_field_runtime_type, tuple_component_runtime_types,
        variant_payload_runtime_type,
    },
    rewrite, role,
};

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
) -> MonomorphizeResult<Vec<RootGraphSolution>> {
    let mut solutions = Vec::new();
    collect_root_expr_graphs(module, cast_order, &mut solutions)?;
    Ok(solutions)
}

pub(crate) fn collect_root_expr_graphs(
    module: &Module,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> MonomorphizeResult<()> {
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
            .ok_or(MonomorphizeDiagnostic::UnsupportedRootShape)?;
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
) -> MonomorphizeResult<()> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    for alias in aliases {
        let Some(binding) = bindings.get(alias) else {
            return Err(MonomorphizeDiagnostic::MissingBinding {
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
    // The scan order feeds alias occurrence numbers and cursor-based rewrites,
    // so do not let HashSet iteration decide it.
    let mut reachable = super::reachable_paths(module)
        .into_iter()
        .collect::<Vec<_>>();
    reachable.sort_by(|left, right| left.segments.cmp(&right.segments));
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
    for path in &reachable {
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
) -> MonomorphizeResult<()> {
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
        let solved_callee_type = solved_apply_spine_callee_type(expr, &found);
        collect_apply_spine_arg_graphs(
            owner,
            expr,
            bindings,
            role_impls,
            local_types,
            solved_callee_type.as_ref(),
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
                let scrutinee_ty = collect_stmt_graphs(
                    owner.clone(),
                    stmt,
                    bindings,
                    role_impls,
                    &scoped_locals,
                    cast_order,
                    solutions,
                )?;
                collect_stmt_local_types_with_scrutinee(
                    stmt,
                    scrutinee_ty.as_ref(),
                    &mut scoped_locals,
                );
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
    solved_callee_type: Option<&RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> MonomorphizeResult<()> {
    collect_apply_spine_arg_graphs_with_callee_type(
        owner,
        expr,
        bindings,
        role_impls,
        local_types,
        solved_callee_type.cloned(),
        cast_order,
        solutions,
    )
    .map(|_| ())
}

fn collect_apply_spine_arg_graphs_with_callee_type(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    callee_type: Option<RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> MonomorphizeResult<Option<RuntimeType>> {
    let ExprKind::Apply { callee, arg, .. } = &expr.kind else {
        return Ok(callee_type);
    };
    let callee_type = collect_apply_spine_arg_graphs_with_callee_type(
        owner.clone(),
        callee,
        bindings,
        role_impls,
        local_types,
        callee_type,
        cast_order,
        solutions,
    )?;
    let expected_arg = callee_type.as_ref().and_then(runtime_callable_param);
    collect_apply_arg_expr_graphs(
        owner,
        arg,
        bindings,
        role_impls,
        local_types,
        expected_arg.as_ref(),
        cast_order,
        solutions,
    )?;
    Ok(callee_type.as_ref().and_then(runtime_callable_ret))
}

fn collect_apply_arg_expr_graphs(
    owner: RootGraphRoot,
    arg: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    expected_arg: Option<&RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> MonomorphizeResult<()> {
    if let (ExprKind::Lambda { param, body, .. }, Some(expected_arg)) = (&arg.kind, expected_arg)
        && let Some(expected_param) = runtime_callable_param(expected_arg)
    {
        let local = super::path_from_name(param);
        let mut param_ty = super::runtime_function_param(&arg.ty).unwrap_or(RuntimeType::Unknown);
        super::narrow_runtime_type_in_place(&mut param_ty, &expected_param);
        let mut scoped_locals = local_types.clone();
        scoped_locals.insert(local, param_ty);
        return collect_expr_graphs(
            owner,
            body,
            bindings,
            role_impls,
            &scoped_locals,
            cast_order,
            solutions,
        );
    }
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

fn solved_apply_spine_callee_type(
    expr: &Expr,
    solutions: &[RootGraphSolution],
) -> Option<RuntimeType> {
    let spine = ApplySpine::new(expr)?;
    solutions
        .iter()
        .rev()
        .find(|solution| solution.binding == *spine.binding)
        .map(|solution| solution.callee_type.clone())
}

fn runtime_callable_param(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Value(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => Some(runtime_type_from_core_value_and_effect(
            param.as_ref().clone(),
            param_effect.as_ref().clone(),
        )),
        RuntimeType::Unknown | RuntimeType::Value(_) | RuntimeType::Thunk { .. } => None,
    }
}

fn runtime_callable_ret(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { ret, .. } => Some(ret.as_ref().clone()),
        RuntimeType::Value(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) => Some(runtime_type_from_core_value_and_effect(
            ret.as_ref().clone(),
            ret_effect.as_ref().clone(),
        )),
        RuntimeType::Unknown | RuntimeType::Value(_) | RuntimeType::Thunk { .. } => None,
    }
}

pub(crate) fn solve_bare_polymorphic_var(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    alias_index: usize,
) -> MonomorphizeResult<Option<RootGraphSolution>> {
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
) -> MonomorphizeResult<Vec<RootGraphSolution>> {
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
    let role_required_binding = !binding.scheme.requirements.is_empty();
    let evidence_policy = if role_required_binding {
        ApplyEvidencePolicy::full()
    } else {
        ApplyEvidencePolicy::for_owner_spine(&owner, bindings, &spine, local_types)
    };
    let mut graph = TypeGraph::with_cast_order(cast_order.clone());
    graph.mark_external_vars(evidence_policy.owner_vars.iter().cloned());
    let principal = graph.instantiate_principal(binding);
    if !role_required_binding
        && generic_owner_apply_waits_for_inner_solution(
            &spine,
            bindings,
            local_types,
            &evidence_policy,
        )
    {
        return Ok(solutions);
    }
    if !role_required_binding && evidence_policy.collects_callee_runtime(&spine.callee.ty) {
        graph.collect_runtime_bounds(
            &principal.principal_type,
            &crate::RuntimeBounds {
                lower: Some(spine.callee.ty.clone()),
                upper: Some(spine.callee.ty.clone()),
            },
        )?;
    }
    collect_spine_substitutions(&mut graph, &principal, &spine.steps)?;
    let mut current = principal.principal_type.clone();
    let mut current_template = principal.principal_type.clone();
    let mut current_effect = typed_ir::Type::Never;
    let mut apply_value_vars = BTreeSet::new();
    let mut apply_effect_vars = BTreeSet::new();
    for step in &spine.steps {
        let template_param = function_param_template_parts(&current_template);
        let instantiated_param = step
            .closed_instantiation()
            .then(|| template_param.clone())
            .flatten();
        let (arg_type, arg_effect) = instantiated_param.unwrap_or_else(|| {
            let observed = step.arg_type_and_effect_with_policy(local_types, &evidence_policy);
            generic_template_param_for_untrusted_coerce_arg(
                template_param.as_ref(),
                &observed.0,
                step.arg,
                &evidence_policy,
            )
            .unwrap_or(observed)
        });
        let arg_is_never = matches!(arg_type, typed_ir::Type::Never);
        let observed_arg_effect = arg_effect.clone();
        let use_template_return =
            role_required_binding || !evidence_policy.trusts_all_apply_evidence();
        let template_return = use_template_return
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
        let trace_apply_effect = std::env::var_os("YULANG_TRACE_APPLY_EFFECT").is_some()
            && (format!("{current:?}").contains("Any")
                || step
                    .evidence
                    .is_some_and(|evidence| format!("{evidence:?}").contains("Any")));
        if trace_apply_effect {
            eprintln!(
                "TRACE apply binding={binding_path:?}\n  principal={:?}\n  callee_ty={:?}\n  current={current:?}\n  expected={expected:?}\n  evidence={:?}",
                principal.principal_type, spine.callee.ty, step.evidence
            );
        }
        graph.constrain_subtype(current, expected)?;
        if role_required_binding && arg_is_never && informative_effect(&observed_arg_effect) {
            graph.constrain_subtype(observed_arg_effect.clone(), result_effect.clone())?;
            graph.constrain_subtype(result_effect.clone(), observed_arg_effect)?;
        }
        if !role_required_binding {
            step.constrain_result_bounds(
                &mut graph,
                result.clone(),
                result_effect.clone(),
                local_types,
                &evidence_policy,
            )?;
        }
        current = result;
        current_effect = result_effect;
        current_template =
            function_return_template(current_template).unwrap_or(typed_ir::Type::Unknown);
    }
    default_spine_evidence_substitutions(&mut graph, &principal, &spine.steps, &evidence_policy)?;
    default_spine_evidence_candidate_bounds(
        &mut graph,
        &principal,
        &spine.steps,
        &evidence_policy,
    )?;
    // These holes are introduced by this spine solver for intermediate or
    // discarded apply results. If no caller, evidence, or later apply step
    // observes their value, Bottom is the only closed choice that does not
    // invent a runtime value shape.
    graph.default_unbound_lower(apply_value_vars, typed_ir::Type::Never)?;
    graph.default_unbound_lower(principal.effect_only_type_params(), typed_ir::Type::Never)?;
    graph.default_unbound_lower(apply_effect_vars, typed_ir::Type::Never)?;
    let solved = graph.clone().solve();
    let graph = if role_required_binding
        && (!solved.is_complete() || role::solution_has_unknown_components(&solved))
    {
        let associated_changed = role::close_role_associated_types(
            &mut graph, binding, &principal, &solved, role_impls,
        )?;
        let input_changed = role::close_role_inputs_from_associated_types(
            &mut graph, binding, &principal, &solved, role_impls,
        )?;
        if associated_changed || input_changed {
            graph.solve()
        } else {
            solved
        }
    } else {
        solved
    };
    if !graph.is_complete() {
        if role::role_required_apply_waiting_for_arguments(binding, &spine, local_types) {
            return Ok(solutions);
        }
        return Err(MonomorphizeDiagnostic::IncompleteGraph {
            binding: binding_path.clone(),
        });
    }
    let result_type = solved_apply_result_type(&graph, current, current_effect);
    let callee_type = solved_callee_finalized_type(binding, &principal, &graph);
    let callee_type =
        super::finalized_apply_spine_arg_effects(callee_type, &spine.steps, local_types);
    let callee_type =
        super::refine_runtime_spine_return(callee_type, spine.steps.len(), result_type.clone());
    let type_substitutions = principal.original_substitutions(&graph);
    let solution = RootGraphSolution {
        root: owner,
        occurrence: alias_index + solutions.len(),
        binding: binding_path.clone(),
        alias: rewrite::alias_path(binding_path, alias_index + solutions.len()),
        callee_type,
        result_type,
        graph,
        type_substitutions,
    };
    if std::env::var_os("YULANG_TRACE_ROOT_SOLUTIONS").is_some() {
        eprintln!(
            "TRACE solution occurrence={} binding={:?} alias={:?}\n  callee={:?}\n  result={:?}\n  substitutions={:?}",
            solution.occurrence,
            solution.binding,
            solution.alias,
            solution.callee_type,
            solution.result_type,
            solution.type_substitutions
        );
    }
    solutions.push(solution);
    Ok(solutions)
}

pub(crate) fn solve_monomorphic_contextual_apply(
    owner: RootGraphRoot,
    expr: &Expr,
    binding_path: &typed_ir::Path,
    _binding: &Binding,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    alias_index: usize,
) -> Option<RootGraphSolution> {
    let callee_type =
        contextual_monomorphic_callee_type(&spine.callee.ty, &spine.steps, local_types)?;
    let result_type = expr_lower_type(expr, local_types);
    let callee_type =
        super::finalized_apply_spine_arg_effects(callee_type, &spine.steps, local_types);
    let callee_type =
        super::refine_runtime_spine_return(callee_type, spine.steps.len(), result_type.clone());
    Some(RootGraphSolution {
        root: owner,
        occurrence: alias_index,
        binding: binding_path.clone(),
        alias: rewrite::alias_path(binding_path, alias_index),
        callee_type,
        result_type,
        graph: TypeGraph::default().solve(),
        type_substitutions: Vec::new(),
    })
}

fn contextual_monomorphic_callee_type(
    callee_type: &RuntimeType,
    steps: &[ApplyStep<'_>],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<RuntimeType> {
    let mut changed = false;
    let core = contextual_monomorphic_callee_core(
        super::runtime_type_to_core(callee_type.clone()),
        steps,
        local_types,
        &mut changed,
    )?;
    changed.then(|| runtime_type_from_core_value(core))
}

fn contextual_monomorphic_callee_core(
    ty: typed_ir::Type,
    steps: &[ApplyStep<'_>],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    changed: &mut bool,
) -> Option<typed_ir::Type> {
    let Some((step, rest)) = steps.split_first() else {
        return Some(ty);
    };
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = ty
    else {
        return None;
    };
    let (observed_param, observed_effect) = step.arg_type_and_effect(local_types);
    let (param, param_effect) = if contextual_arg_refines_param(&param, &observed_param) {
        *changed = true;
        let effect = if super::core_type_is_closed(&observed_effect) {
            observed_effect
        } else {
            *param_effect
        };
        (Box::new(observed_param), Box::new(effect))
    } else {
        (param, param_effect)
    };
    let ret = Box::new(contextual_monomorphic_callee_core(
        *ret,
        rest,
        local_types,
        changed,
    )?);
    Some(typed_ir::Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    })
}

fn contextual_arg_refines_param(param: &typed_ir::Type, observed: &typed_ir::Type) -> bool {
    matches!(
        param,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Never
    ) && !matches!(
        observed,
        typed_ir::Type::Unknown
            | typed_ir::Type::Any
            | typed_ir::Type::Never
            | typed_ir::Type::Var(_)
    ) && super::core_type_is_closed(observed)
}

fn solved_apply_result_type(
    graph: &crate::GraphSolution,
    result: typed_ir::Type,
    effect: typed_ir::Type,
) -> RuntimeType {
    runtime_type_from_core_value_and_effect(
        graph.materialize_core(result),
        graph.materialize_core(effect),
    )
}

fn informative_effect(effect: &typed_ir::Type) -> bool {
    !matches!(effect, typed_ir::Type::Never | typed_ir::Type::Unknown)
        && super::core_type_is_closed(effect)
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
) -> MonomorphizeResult<Vec<RootGraphSolution>> {
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
        let expected_type = step.arg_type(local_types);
        if !value_arg_expected_shape_matches(binding, &expected_type) {
            continue;
        }
        let solution = match solve_value_arg(
            owner.clone(),
            binding,
            expected_type,
            cast_order,
            alias_index + solutions.len(),
        ) {
            Ok(solution) => solution,
            Err(MonomorphizeDiagnostic::IncompleteGraph {
                binding: incomplete,
            }) if incomplete == binding.name => {
                continue;
            }
            Err(error) => return Err(error),
        };
        solutions.push(solution);
    }
    Ok(solutions)
}

fn value_arg_expected_shape_matches(binding: &Binding, expected: &typed_ir::Type) -> bool {
    if !type_shape_matches(&binding.scheme.body, expected, ShapePosition::Top) {
        return false;
    }
    let body_shape = super::runtime_type_to_core(binding.body.ty.clone());
    type_shape_matches(&body_shape, expected, ShapePosition::Top)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ShapePosition {
    Top,
    Nested,
}

fn type_shape_matches(
    template: &typed_ir::Type,
    expected: &typed_ir::Type,
    position: ShapePosition,
) -> bool {
    match (template, expected) {
        (typed_ir::Type::Unknown, _) | (_, typed_ir::Type::Unknown) => {
            position == ShapePosition::Nested
        }
        (typed_ir::Type::Var(_), _) | (_, typed_ir::Type::Var(_)) => true,
        (typed_ir::Type::Any, typed_ir::Type::Any)
        | (typed_ir::Type::Never, typed_ir::Type::Never) => true,
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: expected_path,
                args: expected_args,
            },
        ) => {
            path == expected_path
                && args.len() == expected_args.len()
                && args
                    .iter()
                    .zip(expected_args)
                    .all(|(arg, expected_arg)| type_arg_shape_matches(arg, expected_arg))
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: expected_param,
                param_effect: expected_param_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            },
        ) => {
            type_shape_matches(param, expected_param, ShapePosition::Nested)
                && type_shape_matches(param_effect, expected_param_effect, ShapePosition::Nested)
                && type_shape_matches(ret_effect, expected_ret_effect, ShapePosition::Nested)
                && type_shape_matches(ret, expected_ret, ShapePosition::Nested)
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(expected_items)) => {
            items.len() == expected_items.len()
                && items
                    .iter()
                    .zip(expected_items)
                    .all(|(item, expected_item)| {
                        type_shape_matches(item, expected_item, ShapePosition::Nested)
                    })
        }
        (typed_ir::Type::Record(_), typed_ir::Type::Record(_)) => true,
        (typed_ir::Type::Variant(_), typed_ir::Type::Variant(_)) => true,
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
                items: expected_items,
                tail: expected_tail,
            },
        ) => {
            items.len() == expected_items.len()
                && items
                    .iter()
                    .zip(expected_items)
                    .all(|(item, expected_item)| {
                        type_shape_matches(item, expected_item, ShapePosition::Nested)
                    })
                && type_shape_matches(tail, expected_tail, ShapePosition::Nested)
        }
        (typed_ir::Type::Union(items), expected) => items
            .iter()
            .any(|item| type_shape_matches(item, expected, position)),
        (template, typed_ir::Type::Union(items)) => items
            .iter()
            .any(|item| type_shape_matches(template, item, position)),
        (typed_ir::Type::Inter(items), expected) => items
            .iter()
            .any(|item| type_shape_matches(item, expected, position)),
        (template, typed_ir::Type::Inter(items)) => items
            .iter()
            .any(|item| type_shape_matches(template, item, position)),
        (typed_ir::Type::Recursive { body, .. }, expected) => {
            type_shape_matches(body, expected, position)
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            type_shape_matches(template, body, position)
        }
        _ => false,
    }
}

fn type_arg_shape_matches(template: &typed_ir::TypeArg, expected: &typed_ir::TypeArg) -> bool {
    match (template, expected) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(expected)) => {
            type_shape_matches(template, expected, ShapePosition::Nested)
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(expected)) => {
            bound_shape_matches(template.lower.as_deref(), expected.lower.as_deref())
                && bound_shape_matches(template.upper.as_deref(), expected.upper.as_deref())
        }
        _ => false,
    }
}

fn bound_shape_matches(
    template: Option<&typed_ir::Type>,
    expected: Option<&typed_ir::Type>,
) -> bool {
    match (template, expected) {
        (Some(template), Some(expected)) => {
            type_shape_matches(template, expected, ShapePosition::Nested)
        }
        (None, None) => true,
        _ => false,
    }
}

fn solve_value_arg(
    owner: RootGraphRoot,
    binding: &Binding,
    expected_type: typed_ir::Type,
    cast_order: &TypeCastOrder,
    alias_index: usize,
) -> MonomorphizeResult<RootGraphSolution> {
    let mut graph = TypeGraph::with_cast_order(cast_order.clone());
    let principal = graph.instantiate_principal(binding);
    graph.collect_runtime_bounds(
        &principal.principal_type,
        &RuntimeBounds::exact(binding.body.ty.clone()),
    )?;
    graph.constrain_subtype(principal.principal_type.clone(), expected_type)?;
    graph.default_unbound_lower(principal.effect_only_type_params(), typed_ir::Type::Never)?;
    let graph = graph.solve();
    if !graph.is_complete() {
        return Err(MonomorphizeDiagnostic::IncompleteGraph {
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
) -> MonomorphizeResult<()> {
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
) -> MonomorphizeResult<()> {
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
    policy: &ApplyEvidencePolicy,
) -> MonomorphizeResult<()> {
    if !policy.trusts_all_apply_evidence() {
        return Ok(());
    }
    for step in steps {
        if step.instantiation.is_some() {
            continue;
        }
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
) -> MonomorphizeResult<()> {
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

fn default_spine_evidence_candidate_bounds(
    graph: &mut TypeGraph,
    principal: &crate::PrincipalInstance,
    steps: &[ApplyStep<'_>],
    policy: &ApplyEvidencePolicy,
) -> MonomorphizeResult<()> {
    if !policy.trusts_all_apply_evidence() {
        return Ok(());
    }
    let mut choices =
        BTreeMap::<(typed_ir::TypeVar, CandidateBoundSide), Vec<typed_ir::Type>>::new();
    for step in steps {
        if step.instantiation.is_some() {
            continue;
        }
        let Some(evidence) = step.evidence else {
            continue;
        };
        for candidate in &evidence.substitution_candidates {
            if principal_candidate_is_callee_param_context(candidate)
                || !candidate_type_usable(&candidate.ty)
            {
                continue;
            }
            let Some(param) = principal
                .type_params
                .iter()
                .find(|param| param.original == candidate.var)
            else {
                continue;
            };
            let sides = candidate_bound_sides(candidate.relation);
            for side in sides {
                let entry = choices.entry((param.fresh.clone(), *side)).or_default();
                if !entry.contains(&candidate.ty) {
                    entry.push(candidate.ty.clone());
                }
            }
        }
    }
    for ((var, side), candidates) in choices {
        if candidates.len() != 1 {
            continue;
        }
        let ty = candidates.into_iter().next().unwrap();
        match side {
            CandidateBoundSide::Lower => {
                graph.constrain_subtype(ty, typed_ir::Type::Var(var))?;
            }
            CandidateBoundSide::Upper => {
                graph.constrain_subtype(typed_ir::Type::Var(var), ty)?;
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CandidateBoundSide {
    Lower,
    Upper,
}

fn candidate_bound_sides(
    relation: typed_ir::PrincipalCandidateRelation,
) -> &'static [CandidateBoundSide] {
    match relation {
        typed_ir::PrincipalCandidateRelation::Lower => &[CandidateBoundSide::Lower],
        typed_ir::PrincipalCandidateRelation::Upper => &[CandidateBoundSide::Upper],
        typed_ir::PrincipalCandidateRelation::Exact => {
            &[CandidateBoundSide::Lower, CandidateBoundSide::Upper]
        }
    }
}

fn principal_candidate_is_callee_param_context(
    candidate: &typed_ir::PrincipalSubstitutionCandidate,
) -> bool {
    matches!(
        candidate.path.as_slice(),
        [
            typed_ir::PrincipalSlotPathSegment::Callee,
            typed_ir::PrincipalSlotPathSegment::FunctionParam,
            ..
        ]
    )
}

fn candidate_type_usable(ty: &typed_ir::Type) -> bool {
    !matches!(
        ty,
        typed_ir::Type::Unknown
            | typed_ir::Type::Any
            | typed_ir::Type::Never
            | typed_ir::Type::Var(_)
    ) && super::core_type_is_closed(ty)
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

fn function_param_template_parts(ty: &typed_ir::Type) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let typed_ir::Type::Fun {
        param,
        param_effect,
        ..
    } = ty
    else {
        return None;
    };
    Some((param.as_ref().clone(), param_effect.as_ref().clone()))
}

fn generic_template_param_for_untrusted_coerce_arg(
    template_param: Option<&(typed_ir::Type, typed_ir::Type)>,
    observed: &typed_ir::Type,
    arg: &Expr,
    policy: &ApplyEvidencePolicy,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    if policy.trusts_all_apply_evidence() || policy.trusts_type(observed) {
        return None;
    }
    if !generic_arg_uses_untrusted_closed_coerce_source(arg, policy) {
        return None;
    }
    let (template, effect) = template_param?;
    if !type_has_type_var(template) || !generic_template_param_matches_observed(template, observed)
    {
        return None;
    }
    Some((template.clone(), effect.clone()))
}

fn generic_arg_uses_untrusted_closed_coerce_source(
    arg: &Expr,
    policy: &ApplyEvidencePolicy,
) -> bool {
    let ExprKind::Coerce { from, .. } = &arg.kind else {
        return false;
    };
    super::core_type_is_closed(from) && !policy.trusts_type(from)
}

fn generic_template_param_matches_observed(
    template: &typed_ir::Type,
    observed: &typed_ir::Type,
) -> bool {
    match (template, observed) {
        (
            typed_ir::Type::Named {
                path: template_path,
                args: template_args,
            },
            typed_ir::Type::Named {
                path: observed_path,
                args: observed_args,
            },
        ) => template_path == observed_path && template_args.len() == observed_args.len(),
        (typed_ir::Type::Fun { .. }, typed_ir::Type::Fun { .. }) => true,
        (typed_ir::Type::Tuple(template), typed_ir::Type::Tuple(observed)) => {
            template.len() == observed.len()
        }
        (typed_ir::Type::Record(template), typed_ir::Type::Record(observed)) => template
            .fields
            .iter()
            .all(|field| observed.fields.iter().any(|other| other.name == field.name)),
        (typed_ir::Type::Variant(template), typed_ir::Type::Variant(observed)) => template
            .cases
            .iter()
            .all(|case| observed.cases.iter().any(|other| other.name == case.name)),
        (typed_ir::Type::Row { .. }, typed_ir::Type::Row { .. }) => true,
        _ => template == observed,
    }
}

fn generic_owner_apply_waits_for_inner_solution(
    spine: &ApplySpine<'_>,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    policy: &ApplyEvidencePolicy,
) -> bool {
    if policy.trusts_all_apply_evidence() {
        return false;
    }
    if spine.steps.iter().any(|step| step.instantiation.is_some()) {
        return false;
    }
    spine.steps.iter().any(|step| {
        generic_owner_arg_waits_for_inner_solution(step.arg, bindings, local_types, policy)
    })
}

fn generic_owner_arg_waits_for_inner_solution(
    arg: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    policy: &ApplyEvidencePolicy,
) -> bool {
    let observed = expr_lower_type(arg, local_types);
    if runtime_type_mentions_any_var(&observed, &policy.owner_vars) {
        return false;
    }
    expr_mentions_any_owner_var(arg, local_types, &policy.owner_vars)
        && expr_contains_unsolved_polymorphic_apply(arg, bindings)
}

fn expr_mentions_any_owner_var(
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    owner_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    if runtime_type_mentions_any_var(&expr_lower_type(expr, local_types), owner_vars) {
        return true;
    }
    expr_children(expr)
        .into_iter()
        .any(|child| expr_mentions_any_owner_var(child, local_types, owner_vars))
}

fn expr_contains_unsolved_polymorphic_apply(
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
) -> bool {
    if let Some(spine) = ApplySpine::new(expr)
        && bindings
            .get(spine.binding)
            .is_some_and(|binding| !binding.type_params.is_empty())
    {
        return true;
    }
    expr_children(expr)
        .into_iter()
        .any(|child| expr_contains_unsolved_polymorphic_apply(child, bindings))
}

fn expr_children(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => vec![body.as_ref()],
        ExprKind::Apply { callee, arg, .. } => vec![callee.as_ref(), arg.as_ref()],
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => vec![cond.as_ref(), then_branch.as_ref(), else_branch.as_ref()],
        ExprKind::Tuple(items) => items.iter().collect(),
        ExprKind::Record { fields, spread } => {
            let mut children = fields.iter().map(|field| &field.value).collect::<Vec<_>>();
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
                    | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
                        children.push(expr.as_ref());
                    }
                }
            }
            children
        }
        ExprKind::Variant { value, .. } => value.iter().map(|value| value.as_ref()).collect(),
        ExprKind::Select { base, .. } => vec![base.as_ref()],
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let mut children = vec![scrutinee.as_ref()];
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    children.push(guard);
                }
                children.push(&arm.body);
            }
            children
        }
        ExprKind::Block { stmts, tail } => {
            let mut children = Vec::new();
            for stmt in stmts {
                match stmt {
                    yulang_runtime_ir::FinalizedStmt::Let { value, .. }
                    | yulang_runtime_ir::FinalizedStmt::Expr(value)
                    | yulang_runtime_ir::FinalizedStmt::Module { body: value, .. } => {
                        children.push(value);
                    }
                }
            }
            if let Some(tail) = tail {
                children.push(tail.as_ref());
            }
            children
        }
        ExprKind::Handle { body, arms, .. } => {
            let mut children = vec![body.as_ref()];
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    children.push(guard);
                }
                children.push(&arm.body);
            }
            children
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => Vec::new(),
    }
}

#[derive(Clone)]
struct ApplyEvidencePolicy {
    owner_vars: BTreeSet<typed_ir::TypeVar>,
    collects_open_callee_runtime: bool,
}

impl ApplyEvidencePolicy {
    fn full() -> Self {
        Self {
            owner_vars: BTreeSet::new(),
            collects_open_callee_runtime: true,
        }
    }

    fn for_owner(owner: &RootGraphRoot, bindings: &HashMap<typed_ir::Path, &Binding>) -> Self {
        let owner_vars = owner_binding_free_type_vars(owner, bindings);
        if !owner_vars.is_empty() {
            return Self {
                owner_vars,
                collects_open_callee_runtime: false,
            };
        }
        Self::full()
    }

    fn for_owner_spine(
        owner: &RootGraphRoot,
        bindings: &HashMap<typed_ir::Path, &Binding>,
        spine: &ApplySpine<'_>,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> Self {
        let policy = Self::for_owner(owner, bindings);
        if policy.owner_vars.is_empty()
            || spine_mentions_any_owner_var(spine, local_types, &policy.owner_vars)
        {
            policy
        } else {
            Self::full()
        }
    }

    fn trusts_all_apply_evidence(&self) -> bool {
        self.owner_vars.is_empty()
    }

    fn trusts_type(&self, ty: &typed_ir::Type) -> bool {
        self.trusts_all_apply_evidence()
            || (type_mentions_any_var(ty, &self.owner_vars) && !type_has_non_runtime_choice(ty))
    }

    fn trusts_observed_bound(&self, ty: &typed_ir::Type) -> bool {
        if self.trusts_all_apply_evidence() {
            return super::core_type_is_closed(ty) && !type_has_non_runtime_choice(ty);
        }
        self.trusts_type(ty)
    }

    fn project_type(&self, ty: typed_ir::Type) -> Option<typed_ir::Type> {
        if self.trusts_all_apply_evidence() {
            return Some(ty);
        }
        project_generic_evidence_type(ty)
    }

    fn collects_callee_runtime(&self, ty: &RuntimeType) -> bool {
        self.collects_open_callee_runtime
            || super::runtime_type_is_closed(ty)
            || self.trusts_open_owner_runtime(ty)
    }

    fn trusts_open_owner_runtime(&self, ty: &RuntimeType) -> bool {
        !self.owner_vars.is_empty()
            && runtime_type_mentions_any_var(ty, &self.owner_vars)
            && !runtime_type_has_non_runtime_choice(ty)
    }
}

fn spine_mentions_any_owner_var(
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    owner_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    runtime_type_mentions_any_var(&spine.callee.ty, owner_vars)
        || spine.steps.iter().any(|step| {
            runtime_type_mentions_any_var(&expr_lower_type(step.arg, local_types), owner_vars)
                || runtime_type_mentions_any_var(
                    &expr_lower_type(step.apply, local_types),
                    owner_vars,
                )
        })
}

fn owner_binding_free_type_vars(
    owner: &RootGraphRoot,
    bindings: &HashMap<typed_ir::Path, &Binding>,
) -> BTreeSet<typed_ir::TypeVar> {
    let RootGraphRoot::Binding(owner_path) = owner else {
        return BTreeSet::new();
    };
    let Some(binding) = bindings.get(owner_path) else {
        return BTreeSet::new();
    };
    let mut vars = BTreeSet::new();
    collect_scheme_type_vars(&binding.scheme, &mut vars);
    collect_runtime_type_vars(&binding.body.ty, &mut vars);
    for param in &binding.type_params {
        vars.remove(param);
    }
    vars
}

fn collect_scheme_type_vars(scheme: &typed_ir::Scheme, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    for requirement in &scheme.requirements {
        for arg in &requirement.args {
            match arg {
                typed_ir::RoleRequirementArg::Input(bounds) => {
                    collect_type_bounds_vars(bounds, vars);
                }
                typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_type_bounds_vars(bounds, vars);
                }
            }
        }
    }
    collect_type_vars(&scheme.body, vars);
}

fn collect_runtime_type_vars(ty: &RuntimeType, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        RuntimeType::Unknown => {}
        RuntimeType::Value(ty) => collect_type_vars(ty, vars),
        RuntimeType::Fun { param, ret } => {
            collect_runtime_type_vars(param, vars);
            collect_runtime_type_vars(ret, vars);
        }
        RuntimeType::Thunk { effect, value } => {
            collect_type_vars(effect, vars);
            collect_runtime_type_vars(value, vars);
        }
    }
}

fn runtime_type_mentions_any_var(ty: &RuntimeType, targets: &BTreeSet<typed_ir::TypeVar>) -> bool {
    let mut vars = BTreeSet::new();
    collect_runtime_type_vars(ty, &mut vars);
    vars.iter().any(|var| targets.contains(var))
}

fn type_mentions_any_var(ty: &typed_ir::Type, targets: &BTreeSet<typed_ir::TypeVar>) -> bool {
    let mut vars = BTreeSet::new();
    collect_type_vars(ty, &mut vars);
    vars.iter().any(|var| targets.contains(var))
}

fn runtime_type_has_non_runtime_choice(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Value(ty) => type_has_non_runtime_choice(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_has_non_runtime_choice(param) || runtime_type_has_non_runtime_choice(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            type_has_non_runtime_choice(effect) || runtime_type_has_non_runtime_choice(value)
        }
    }
}

fn collect_type_bounds_vars(bounds: &typed_ir::TypeBounds, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_type_vars(upper, vars);
    }
}

fn collect_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_vars(arg, vars);
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars(param, vars);
            collect_type_vars(param_effect, vars);
            collect_type_vars(ret_effect, vars);
            collect_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_type_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_type_vars(item, vars);
            }
            collect_type_vars(tail, vars);
        }
        typed_ir::Type::Recursive { var, body } => {
            let inserted = vars.insert(var.clone());
            collect_type_vars(body, vars);
            if inserted {
                vars.remove(var);
            }
        }
    }
}

fn collect_type_arg_vars(arg: &typed_ir::TypeArg, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_type_vars(ty, vars),
        typed_ir::TypeArg::Bounds(bounds) => collect_type_bounds_vars(bounds, vars),
    }
}

fn type_has_non_runtime_choice(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Union(_) | typed_ir::Type::Inter(_) => true,
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_non_runtime_choice),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_has_non_runtime_choice(param)
                || type_has_non_runtime_choice(param_effect)
                || type_has_non_runtime_choice(ret_effect)
                || type_has_non_runtime_choice(ret)
        }
        typed_ir::Type::Tuple(items) => items.iter().any(type_has_non_runtime_choice),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_has_non_runtime_choice(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_has_non_runtime_choice(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_has_non_runtime_choice))
                || variant
                    .tail
                    .as_deref()
                    .is_some_and(type_has_non_runtime_choice)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_has_non_runtime_choice) || type_has_non_runtime_choice(tail)
        }
        typed_ir::Type::Recursive { body, .. } => type_has_non_runtime_choice(body),
    }
}

fn type_arg_has_non_runtime_choice(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_has_non_runtime_choice(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .is_some_and(type_has_non_runtime_choice)
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(type_has_non_runtime_choice)
        }
    }
}

fn project_generic_evidence_type(ty: typed_ir::Type) -> Option<typed_ir::Type> {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => None,
        typed_ir::Type::Var(_) => Some(ty),
        typed_ir::Type::Named { path, args } => Some(typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(project_generic_evidence_type_arg)
                .collect(),
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Some(typed_ir::Type::Fun {
            param: Box::new(
                project_generic_evidence_type(*param).unwrap_or(typed_ir::Type::Unknown),
            ),
            param_effect: Box::new(
                project_generic_evidence_type(*param_effect).unwrap_or(typed_ir::Type::Never),
            ),
            ret_effect: Box::new(
                project_generic_evidence_type(*ret_effect).unwrap_or(typed_ir::Type::Never),
            ),
            ret: Box::new(project_generic_evidence_type(*ret).unwrap_or(typed_ir::Type::Unknown)),
        }),
        typed_ir::Type::Tuple(items) => Some(typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(|item| project_generic_evidence_type(item).unwrap_or(typed_ir::Type::Unknown))
                .collect(),
        )),
        typed_ir::Type::Record(record) => {
            let mut fields = Vec::new();
            for field in record.fields {
                fields.push(typed_ir::RecordField {
                    name: field.name,
                    value: project_generic_evidence_type(field.value)
                        .unwrap_or(typed_ir::Type::Unknown),
                    optional: field.optional,
                });
            }
            let spread = record
                .spread
                .and_then(project_generic_evidence_record_spread);
            Some(typed_ir::Type::Record(typed_ir::RecordType {
                fields,
                spread,
            }))
        }
        typed_ir::Type::Variant(variant) => {
            let mut cases = Vec::new();
            for case in variant.cases {
                let payloads = case
                    .payloads
                    .into_iter()
                    .map(|payload| {
                        project_generic_evidence_type(payload).unwrap_or(typed_ir::Type::Unknown)
                    })
                    .collect();
                cases.push(typed_ir::VariantCase {
                    name: case.name,
                    payloads,
                });
            }
            let tail = variant
                .tail
                .and_then(|tail| project_generic_evidence_type(*tail).map(Box::new));
            Some(typed_ir::Type::Variant(typed_ir::VariantType {
                cases,
                tail,
            }))
        }
        typed_ir::Type::Row { items, tail } => {
            let items = items
                .into_iter()
                .filter_map(project_generic_evidence_type)
                .collect::<Vec<_>>();
            let tail = project_generic_evidence_type(*tail).unwrap_or(typed_ir::Type::Never);
            if items.is_empty() && matches!(tail, typed_ir::Type::Never) {
                None
            } else {
                Some(typed_ir::Type::Row {
                    items,
                    tail: Box::new(tail),
                })
            }
        }
        typed_ir::Type::Union(items) => {
            project_generic_evidence_choice(typed_ir::Type::Union, items)
        }
        typed_ir::Type::Inter(items) => {
            project_generic_evidence_choice(typed_ir::Type::Inter, items)
        }
        typed_ir::Type::Recursive { var, body } => Some(typed_ir::Type::Recursive {
            var,
            body: Box::new(project_generic_evidence_type(*body)?),
        }),
    }
}

fn project_generic_evidence_choice(
    rebuild: fn(Vec<typed_ir::Type>) -> typed_ir::Type,
    items: Vec<typed_ir::Type>,
) -> Option<typed_ir::Type> {
    let projected = items
        .into_iter()
        .filter(|item| type_has_type_var(item))
        .filter_map(project_generic_evidence_type)
        .collect::<Vec<_>>();
    match projected.as_slice() {
        [] => None,
        [single] => Some(single.clone()),
        _ => Some(rebuild(projected)),
    }
}

fn project_generic_evidence_type_arg(arg: typed_ir::TypeArg) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(
            project_generic_evidence_type(ty).unwrap_or(typed_ir::Type::Unknown),
        ),
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .and_then(|ty| project_generic_evidence_type(*ty).map(Box::new)),
            upper: bounds
                .upper
                .and_then(|ty| project_generic_evidence_type(*ty).map(Box::new)),
        }),
    }
}

fn project_generic_evidence_record_spread(
    spread: typed_ir::RecordSpread,
) -> Option<typed_ir::RecordSpread> {
    match spread {
        typed_ir::RecordSpread::Head(ty) => {
            project_generic_evidence_type(*ty).map(|ty| typed_ir::RecordSpread::Head(Box::new(ty)))
        }
        typed_ir::RecordSpread::Tail(ty) => {
            project_generic_evidence_type(*ty).map(|ty| typed_ir::RecordSpread::Tail(Box::new(ty)))
        }
    }
}

fn type_has_type_var(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
        typed_ir::Type::Var(_) => true,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_type_var),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_has_type_var(param)
                || type_has_type_var(param_effect)
                || type_has_type_var(ret_effect)
                || type_has_type_var(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_has_type_var),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_has_type_var(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_has_type_var(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_has_type_var))
                || variant.tail.as_deref().is_some_and(type_has_type_var)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_has_type_var) || type_has_type_var(tail)
        }
        typed_ir::Type::Recursive { body, .. } => type_has_type_var(body),
    }
}

fn type_arg_has_type_var(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_has_type_var(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_has_type_var)
                || bounds.upper.as_deref().is_some_and(type_has_type_var)
        }
    }
}

pub(crate) struct ApplySpine<'a> {
    pub(crate) binding: &'a typed_ir::Path,
    pub(crate) callee: &'a Expr,
    pub(crate) steps: Vec<ApplyStep<'a>>,
}

pub(crate) struct ApplyStep<'a> {
    pub(crate) index: usize,
    pub(crate) apply: &'a Expr,
    pub(crate) arg: &'a Expr,
    pub(crate) evidence: Option<&'a typed_ir::ApplyEvidence>,
    pub(crate) instantiation: Option<&'a yulang_runtime_ir::TypeInstantiation>,
}

impl ApplyStep<'_> {
    fn closed_instantiation(&self) -> bool {
        self.instantiation.is_some_and(|instantiation| {
            instantiation
                .args
                .iter()
                .all(|substitution| super::core_type_is_closed(&substitution.ty))
        })
    }

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
        self.arg_type_and_effect_with_policy(local_types, &ApplyEvidencePolicy::full())
    }

    fn arg_type_and_effect_with_policy(
        &self,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
        policy: &ApplyEvidencePolicy,
    ) -> (typed_ir::Type, typed_ir::Type) {
        if let Some((value, effect)) = bind_here_arg_type_and_effect(self.arg, local_types, policy)
        {
            return (value, effect);
        }
        if let Some((value, effect)) =
            open_coerce_source_arg_type_and_effect(self.arg, local_types, policy)
        {
            return (value, effect);
        }
        let runtime_ty = expr_lower_type(self.arg, local_types);
        if let RuntimeType::Thunk { effect, value } = &runtime_ty {
            let evidence_arg = self.evidence_arg_type(policy);
            let value_is_closed = super::runtime_type_is_closed(value);
            let arg_type = if value_is_closed {
                let runtime_value = super::runtime_type_to_core((**value).clone());
                evidence_arg
                    .filter(|ty| evidence_arg_overrides_thunk_value(ty, &runtime_value))
                    .unwrap_or(runtime_value)
            } else {
                let expr_ty = super::runtime_type_to_core(runtime_ty.clone());
                select_open_runtime_arg_type(expr_ty, evidence_arg, policy)
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
        if let Some((value, effect)) = expr_value_and_effect(self.arg, local_types, policy) {
            let value = if open_runtime_arg_type_is_informative(&value) {
                select_open_runtime_arg_type(value, self.evidence_arg_type(policy), policy)
            } else {
                value
            };
            return (value, effect);
        }
        let expr_ty = super::runtime_type_to_core(runtime_ty);
        let evidence_arg = self.evidence_arg_type(policy);
        if super::core_type_is_closed(&expr_ty) {
            let arg_type = evidence_arg
                .filter(|ty| evidence_arg_overrides_imprecise_runtime_value(ty, &expr_ty))
                .unwrap_or(expr_ty);
            return (arg_type, typed_ir::Type::Never);
        }
        if open_runtime_arg_type_is_informative(&expr_ty) {
            return (
                select_open_runtime_arg_type(expr_ty, evidence_arg, policy),
                typed_ir::Type::Never,
            );
        }
        let fallback = evidence_arg.unwrap_or(expr_ty);
        (fallback, typed_ir::Type::Never)
    }

    fn evidence_arg_type(&self, policy: &ApplyEvidencePolicy) -> Option<typed_ir::Type> {
        self.instantiation
            .is_none()
            .then(|| {
                self.evidence
                    .and_then(|evidence| apply_arg_type(evidence, self.index, policy))
            })
            .flatten()
    }

    fn constrain_result_bounds(
        &self,
        graph: &mut TypeGraph,
        result: typed_ir::Type,
        result_effect: typed_ir::Type,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
        policy: &ApplyEvidencePolicy,
    ) -> MonomorphizeResult<()> {
        let evidence_value_bound = if self.instantiation.is_none()
            && let Some(evidence) = self.evidence
        {
            let mut constrained =
                constrain_observed_type_bounds(graph, &result, &evidence.result, policy)?;
            constrained |=
                constrain_expected_callee_return_bounds(graph, &result, &result_effect, evidence)?;
            constrained
        } else {
            false
        };
        let apply_ty = expr_lower_type(self.apply, local_types);
        match apply_ty {
            RuntimeType::Unknown => Ok(()),
            RuntimeType::Thunk { value, .. } => {
                let observed = super::runtime_type_to_core((*value).clone());
                if policy.trusts_observed_bound(&observed)
                    && !(evidence_value_bound && runtime_type_value_is_function(&value))
                    && let Some(observed) = policy.project_type(observed)
                {
                    constrain_observed_upper_bound(graph, &result, &observed)?;
                }
                Ok(())
            }
            ty if evidence_value_bound && runtime_type_value_is_function(&ty) => Ok(()),
            ty => {
                let observed = super::runtime_type_to_core(ty);
                if policy.trusts_observed_bound(&observed)
                    && let Some(observed) = policy.project_type(observed)
                {
                    constrain_observed_upper_bound(graph, &result, &observed)?;
                }
                Ok(())
            }
        }
    }
}

fn select_open_runtime_arg_type(
    runtime: typed_ir::Type,
    evidence_arg: Option<typed_ir::Type>,
    policy: &ApplyEvidencePolicy,
) -> typed_ir::Type {
    if let Some(evidence_arg) = evidence_arg
        .as_ref()
        .filter(|ty| evidence_arg_refines_open_runtime_arg(ty, &runtime))
    {
        return evidence_arg.clone();
    }
    if !policy.trusts_all_apply_evidence()
        && let Some(evidence_arg) = evidence_arg
    {
        return evidence_arg;
    }
    runtime
}

fn evidence_arg_refines_open_runtime_arg(
    evidence: &typed_ir::Type,
    runtime: &typed_ir::Type,
) -> bool {
    evidence != runtime
        && informative_evidence_type(evidence)
        && !super::core_type_has_unknown(evidence)
        && !type_has_non_runtime_choice(evidence)
        && generic_template_param_matches_observed(evidence, runtime)
}

fn constrain_expected_callee_return_bounds(
    graph: &mut TypeGraph,
    result: &typed_ir::Type,
    result_effect: &typed_ir::Type,
    evidence: &typed_ir::ApplyEvidence,
) -> MonomorphizeResult<bool> {
    let Some(expected_callee) = evidence.expected_callee.as_ref() else {
        return Ok(false);
    };
    let mut constrained = false;
    if let Some(lower) = expected_callee
        .lower
        .as_deref()
        .and_then(function_return_template_parts)
    {
        let (lower_result, lower_effect) = lower;
        if expected_return_value_bound_is_informative(&lower_result) {
            graph.constrain_subtype(lower_result, result.clone())?;
            constrained = true;
        }
        if expected_return_effect_bound_is_informative(&lower_effect) {
            graph.constrain_subtype(lower_effect, result_effect.clone())?;
            constrained = true;
        }
    }
    if let Some(upper) = expected_callee
        .upper
        .as_deref()
        .and_then(function_return_template_parts)
    {
        let (upper_result, upper_effect) = upper;
        if expected_return_value_bound_is_informative(&upper_result) {
            graph.constrain_subtype(result.clone(), upper_result)?;
            constrained = true;
        }
        if expected_return_effect_bound_is_informative(&upper_effect) {
            graph.constrain_subtype(result_effect.clone(), upper_effect)?;
            constrained = true;
        }
    }
    Ok(constrained)
}

fn expected_return_value_bound_is_informative(ty: &typed_ir::Type) -> bool {
    !type_has_non_runtime_choice(ty) && runtime_arg_type_has_head(ty)
}

fn expected_return_effect_bound_is_informative(ty: &typed_ir::Type) -> bool {
    !type_has_non_runtime_choice(ty)
        && !matches!(
            ty,
            typed_ir::Type::Unknown | typed_ir::Type::Var(_) | typed_ir::Type::Any
        )
}

fn open_coerce_source_arg_type_and_effect(
    arg: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    policy: &ApplyEvidencePolicy,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let ExprKind::Coerce { from, expr, .. } = &arg.kind else {
        return None;
    };
    let target = super::runtime_type_to_core(expr_lower_type(arg, local_types));
    if !super::core_type_is_closed(from) {
        return None;
    }
    if super::core_type_is_closed(&target) && !coerce_preserves_runtime_head(from, &target) {
        return None;
    }
    let effect = expr_value_and_effect(expr, local_types, policy)
        .map(|(_, effect)| effect)
        .unwrap_or(typed_ir::Type::Never);
    Some((from.clone(), effect))
}

fn coerce_preserves_runtime_head(source: &typed_ir::Type, target: &typed_ir::Type) -> bool {
    match (source, target) {
        (
            typed_ir::Type::Named {
                path: source_path,
                args: source_args,
            },
            typed_ir::Type::Named {
                path: target_path,
                args: target_args,
            },
        ) => source_path == target_path && source_args.len() == target_args.len(),
        (typed_ir::Type::Tuple(source), typed_ir::Type::Tuple(target)) => {
            source.len() == target.len()
        }
        _ => false,
    }
}

fn open_runtime_arg_type_is_informative(ty: &typed_ir::Type) -> bool {
    if super::core_type_is_closed(ty) {
        return false;
    }
    runtime_arg_type_has_head(ty)
}

fn runtime_arg_type_has_head(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Named { .. } | typed_ir::Type::Fun { .. } => true,
        typed_ir::Type::Tuple(items) => !items.is_empty(),
        typed_ir::Type::Record(record) => !record.fields.is_empty() || record.spread.is_some(),
        typed_ir::Type::Variant(variant) => !variant.cases.is_empty() || variant.tail.is_some(),
        typed_ir::Type::Row { items, tail } => {
            !items.is_empty() || !matches!(tail.as_ref(), typed_ir::Type::Never)
        }
        typed_ir::Type::Recursive { body, .. } => runtime_arg_type_has_head(body),
        typed_ir::Type::Var(_)
        | typed_ir::Type::Union(_)
        | typed_ir::Type::Inter(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => false,
    }
}

fn evidence_arg_overrides_thunk_value(
    evidence: &typed_ir::Type,
    runtime_value: &typed_ir::Type,
) -> bool {
    if evidence == runtime_value || !informative_evidence_type(evidence) {
        return false;
    }
    super::core_type_is_closed(evidence)
}

fn evidence_arg_overrides_imprecise_runtime_value(
    evidence: &typed_ir::Type,
    runtime_value: &typed_ir::Type,
) -> bool {
    matches!(runtime_value, typed_ir::Type::Any)
        && informative_evidence_type(evidence)
        && super::core_type_is_closed(evidence)
}

fn informative_evidence_type(ty: &typed_ir::Type) -> bool {
    !matches!(
        ty,
        typed_ir::Type::Unknown
            | typed_ir::Type::Var(_)
            | typed_ir::Type::Any
            | typed_ir::Type::Never
    )
}

fn bind_here_arg_type_and_effect(
    arg: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    policy: &ApplyEvidencePolicy,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    let ExprKind::BindHere { expr } = &arg.kind else {
        return None;
    };
    let (value, _) = expr_value_and_effect(expr, local_types, policy)?;
    Some((value, typed_ir::Type::Never))
}

fn expr_value_and_effect(
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    policy: &ApplyEvidencePolicy,
) -> Option<(typed_ir::Type, typed_ir::Type)> {
    if let RuntimeType::Thunk { effect, value } = expr_lower_type(expr, local_types) {
        let value = super::runtime_type_to_core(*value);
        let effect = closed_or_empty_effect(effect);
        return Some((value, effect));
    }
    match &expr.kind {
        ExprKind::Thunk { effect, value, .. } => {
            let value = super::runtime_type_to_core(value.clone());
            let effect = closed_or_empty_effect(effect.clone());
            return Some((value, effect));
        }
        ExprKind::Block {
            tail: Some(tail), ..
        } => {
            if let Some((value, effect)) = expr_value_and_effect(tail, local_types, policy) {
                return Some((value, effect));
            }
        }
        ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Pack { expr: body, .. } => {
            if let Some((value, effect)) = expr_value_and_effect(body, local_types, policy) {
                return Some((value, effect));
            }
        }
        ExprKind::Coerce { to, expr, .. } => {
            if let Some((_, effect)) = expr_value_and_effect(expr, local_types, policy) {
                return Some((to.clone(), effect));
            }
        }
        _ => {}
    }
    let ExprKind::Apply { evidence, .. } = &expr.kind else {
        return None;
    };
    let evidence = evidence.as_ref()?;
    let value = type_from_bounds_with_policy(&evidence.result, policy)
        .filter(|ty| policy.trusts_observed_bound(ty))
        .or_else(|| {
            let value = super::runtime_type_to_core(expr_lower_type(expr, local_types));
            policy.trusts_observed_bound(&value).then_some(value)
        })?;
    let effect = apply_evidence_return_effect(evidence, policy)
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

fn constrain_observed_type_bounds(
    graph: &mut TypeGraph,
    template: &typed_ir::Type,
    bounds: &typed_ir::TypeBounds,
    policy: &ApplyEvidencePolicy,
) -> MonomorphizeResult<bool> {
    let mut constrained = false;
    if let Some(lower) = bounds.lower.as_deref() {
        if policy.trusts_observed_bound(lower)
            && let Some(lower) = policy.project_type(lower.clone())
        {
            constrained |= constrain_observed_lower_bound(graph, template, &lower)?;
        }
    }
    if let Some(upper) = bounds.upper.as_deref() {
        if policy.trusts_observed_bound(upper)
            && let Some(upper) = policy.project_type(upper.clone())
        {
            constrained |= constrain_observed_upper_bound(graph, template, &upper)?;
        }
    }
    Ok(constrained)
}

fn constrain_observed_lower_bound(
    graph: &mut TypeGraph,
    template: &typed_ir::Type,
    observed: &typed_ir::Type,
) -> MonomorphizeResult<bool> {
    if matches!(observed, typed_ir::Type::Unknown) {
        return Ok(false);
    }
    graph.constrain_subtype(observed.clone(), template.clone())?;
    Ok(true)
}

fn constrain_observed_upper_bound(
    graph: &mut TypeGraph,
    template: &typed_ir::Type,
    observed: &typed_ir::Type,
) -> MonomorphizeResult<bool> {
    if matches!(observed, typed_ir::Type::Unknown) {
        return Ok(false);
    }
    graph.constrain_subtype(template.clone(), observed.clone())?;
    Ok(true)
}

fn apply_evidence_return_effect(
    evidence: &typed_ir::ApplyEvidence,
    policy: &ApplyEvidencePolicy,
) -> Option<typed_ir::Type> {
    apply_evidence_return_value(evidence, policy).and_then(|ty| match ty {
        typed_ir::Type::Fun { ret_effect, .. } => Some(*ret_effect),
        _ => None,
    })
}

fn apply_evidence_return_value(
    evidence: &typed_ir::ApplyEvidence,
    policy: &ApplyEvidencePolicy,
) -> Option<typed_ir::Type> {
    evidence
        .expected_callee
        .as_ref()
        .and_then(|bounds| type_from_bounds_with_policy(bounds, policy))
        .or_else(|| type_from_bounds_with_policy(&evidence.callee, policy))
}

fn runtime_type_value_is_function(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Fun { .. } | RuntimeType::Value(typed_ir::Type::Fun { .. }) => true,
        RuntimeType::Thunk { value, .. } => runtime_type_value_is_function(value),
        RuntimeType::Unknown | RuntimeType::Value(_) => false,
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
                index: 0,
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
        for (index, step) in steps.iter_mut().enumerate() {
            step.index = index;
        }
        let binding = match &current.kind {
            ExprKind::Var(binding) | ExprKind::EffectOp(binding) => binding,
            _ => return None,
        };
        Some(Self {
            binding,
            callee: current,
            steps,
        })
    }
}

fn apply_arg_type(
    evidence: &typed_ir::ApplyEvidence,
    index: usize,
    policy: &ApplyEvidencePolicy,
) -> Option<typed_ir::Type> {
    if !policy.trusts_all_apply_evidence()
        && let Some(arg) = principal_elaboration_step_arg_type(evidence, index, policy)
    {
        return Some(arg);
    }
    type_from_bounds_with_policy(&evidence.arg, policy)
        .or_else(|| {
            evidence
                .expected_arg
                .as_ref()
                .and_then(|bounds| type_from_bounds_with_policy(bounds, policy))
        })
        .or_else(|| principal_elaboration_step_arg_type(evidence, index, policy))
}

fn principal_elaboration_step_arg_type(
    evidence: &typed_ir::ApplyEvidence,
    index: usize,
    policy: &ApplyEvidencePolicy,
) -> Option<typed_ir::Type> {
    evidence
        .principal_elaboration
        .as_ref()
        .and_then(|plan| plan.args.iter().find(|arg| arg.index == index))
        .and_then(|arg| principal_elaboration_arg_type(arg, policy))
}

fn principal_elaboration_arg_type(
    arg: &typed_ir::PrincipalElaborationArg,
    policy: &ApplyEvidencePolicy,
) -> Option<typed_ir::Type> {
    arg.contextual
        .as_ref()
        .and_then(|bounds| type_from_bounds_with_policy(bounds, policy))
        .or_else(|| type_from_bounds_with_policy(&arg.intrinsic, policy))
        .or_else(|| {
            arg.expected_runtime
                .as_ref()
                .filter(|ty| policy.trusts_type(ty))
                .cloned()
        })
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

fn type_from_bounds_with_policy(
    bounds: &typed_ir::TypeBounds,
    policy: &ApplyEvidencePolicy,
) -> Option<typed_ir::Type> {
    bounds
        .lower
        .as_deref()
        .filter(|ty| policy.trusts_type(ty))
        .cloned()
        .and_then(|ty| policy.project_type(ty))
        .or_else(|| {
            bounds
                .upper
                .as_deref()
                .filter(|ty| policy.trusts_type(ty))
                .cloned()
                .and_then(|ty| policy.project_type(ty))
        })
}

fn collect_record_spread_graphs(
    owner: RootGraphRoot,
    spread: &yulang_runtime_ir::FinalizedRecordSpreadExpr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> MonomorphizeResult<()> {
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
) -> MonomorphizeResult<Option<RuntimeType>> {
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
            let value_solution_start = solutions.len();
            collect_expr_graphs(
                owner,
                value,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            Ok(Some(collected_expr_result_type(
                value,
                &solutions[value_solution_start..],
                local_types,
            )))
        }
        yulang_runtime_ir::FinalizedStmt::Expr(expr)
        | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => {
            collect_expr_graphs(
                owner,
                expr,
                bindings,
                role_impls,
                local_types,
                cast_order,
                solutions,
            )?;
            Ok(None)
        }
    }
}

fn collected_expr_result_type(
    expr: &Expr,
    collected_solutions: &[RootGraphSolution],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeType {
    solved_expr_result_type_from(collected_solutions, expr)
        .unwrap_or_else(|| expr_lower_type(expr, local_types))
}

fn solved_expr_result_type_from(
    solutions: &[RootGraphSolution],
    expr: &Expr,
) -> Option<RuntimeType> {
    if let Some(spine) = ApplySpine::new(expr) {
        return solutions
            .iter()
            .rev()
            .find(|solution| solution.binding == *spine.binding)
            .map(|solution| solution.result_type.clone());
    }
    let ExprKind::Var(path) = &expr.kind else {
        return None;
    };
    solutions
        .iter()
        .rev()
        .find(|solution| solution.binding == *path)
        .map(|solution| solution.result_type.clone())
}

fn collect_pattern_graphs(
    owner: RootGraphRoot,
    pattern: &yulang_runtime_ir::FinalizedPattern,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> MonomorphizeResult<()> {
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
    collect_stmt_local_types_with_scrutinee(stmt, None, local_types);
}

fn collect_stmt_local_types_with_scrutinee(
    stmt: &yulang_runtime_ir::FinalizedStmt,
    scrutinee_ty: Option<&RuntimeType>,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
) {
    let yulang_runtime_ir::FinalizedStmt::Let { pattern, value } = stmt else {
        return;
    };
    let fallback;
    let scrutinee_ty = match scrutinee_ty {
        Some(scrutinee_ty) => scrutinee_ty,
        None => {
            fallback = expr_lower_type(value, local_types);
            &fallback
        }
    };
    collect_pattern_local_types(pattern, Some(scrutinee_ty), local_types);
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
        Pattern::Record { fields, spread, ty } => {
            for field in fields {
                let field_ty = record_field_runtime_type(scrutinee_ty, ty, &field.name);
                collect_pattern_local_types(&field.pattern, field_ty.as_ref(), local_types);
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
        Pattern::Variant { tag, value, ty } => {
            if let Some(value) = value {
                let payload_ty = variant_payload_runtime_type(scrutinee_ty, ty, tag);
                collect_pattern_local_types(value, payload_ty.as_ref(), local_types);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn open_structural_runtime_arg_wins_over_closed_apply_evidence() {
        let item = typed_ir::TypeVar("a".to_string());
        let open_list = list_type(typed_ir::Type::Var(item));
        let closed_list = list_type(typed_ir::Type::Union(vec![
            named_type("char"),
            named_type("str"),
        ]));
        let arg_name = typed_ir::Name("xs".to_string());
        let arg_path = super::super::path_from_name(&arg_name);
        let arg = Expr::typed(ExprKind::Var(arg_path.clone()), RuntimeType::Unknown);
        let apply = Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), RuntimeType::Unknown);
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::default(),
            expected_callee: None,
            arg: typed_ir::TypeBounds::exact(closed_list),
            expected_arg: None,
            result: typed_ir::TypeBounds::default(),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };
        let step = ApplyStep {
            index: 0,
            apply: &apply,
            arg: &arg,
            evidence: Some(&evidence),
            instantiation: None,
        };
        let mut local_types = HashMap::new();
        local_types.insert(arg_path, RuntimeType::Value(open_list.clone()));

        assert_eq!(
            step.arg_type_and_effect(&local_types),
            (open_list, typed_ir::Type::Never)
        );
    }

    #[test]
    fn outer_apply_evidence_refines_inner_open_variant_result() {
        let ok_variant = variant_type(vec![("ok", vec![named_type("str")])], None);
        let open_variant = variant_type(
            vec![
                (
                    "ok",
                    vec![typed_ir::Type::Var(typed_ir::TypeVar("ok#0".to_string()))],
                ),
                (
                    "err",
                    vec![typed_ir::Type::Var(typed_ir::TypeVar("err#0".to_string()))],
                ),
                ("pending", Vec::new()),
            ],
            None,
        );
        let inner_evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::default(),
            expected_callee: None,
            arg: typed_ir::TypeBounds::default(),
            expected_arg: None,
            result: typed_ir::TypeBounds::exact(open_variant),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };
        let outer_evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::default(),
            expected_callee: None,
            arg: typed_ir::TypeBounds::exact(ok_variant.clone()),
            expected_arg: None,
            result: typed_ir::TypeBounds::default(),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };
        let inner_apply = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(typed_ir::Path::new(vec![typed_ir::Name(
                        "make".to_string(),
                    )])),
                    RuntimeType::Unknown,
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::Unknown,
                )),
                evidence: Some(inner_evidence),
                instantiation: None,
            },
            RuntimeType::Unknown,
        );
        let apply = Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), RuntimeType::Unknown);
        let step = ApplyStep {
            index: 0,
            apply: &apply,
            arg: &inner_apply,
            evidence: Some(&outer_evidence),
            instantiation: None,
        };

        assert_eq!(
            step.arg_type_and_effect(&HashMap::new()),
            (ok_variant, typed_ir::Type::Never)
        );
    }

    #[test]
    fn generic_template_param_wins_over_untrusted_closed_coerce_source() {
        let owner_var = typed_ir::TypeVar("a".to_string());
        let fresh_var = typed_ir::TypeVar("a#0".to_string());
        let owner_list = list_type(typed_ir::Type::Var(owner_var.clone()));
        let widened_list = list_type(typed_ir::Type::Union(vec![
            named_type("char"),
            named_type("str"),
        ]));
        let template = (
            list_type(typed_ir::Type::Var(fresh_var)),
            typed_ir::Type::Never,
        );
        let stale_closed = list_type(named_type("char"));
        let stale_coerce_arg = Expr::typed(
            ExprKind::Coerce {
                from: stale_closed.clone(),
                to: widened_list.clone(),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::Unknown,
                )),
            },
            RuntimeType::Value(widened_list),
        );
        let plain_arg = Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), RuntimeType::Unknown);
        let mut owner_vars = BTreeSet::new();
        owner_vars.insert(owner_var);
        let policy = ApplyEvidencePolicy {
            owner_vars,
            collects_open_callee_runtime: false,
        };

        assert_eq!(
            generic_template_param_for_untrusted_coerce_arg(
                Some(&template),
                &stale_closed,
                &stale_coerce_arg,
                &policy
            ),
            Some(template.clone())
        );
        assert_eq!(
            generic_template_param_for_untrusted_coerce_arg(
                Some(&template),
                &owner_list,
                &stale_coerce_arg,
                &policy
            ),
            None
        );
        assert_eq!(
            generic_template_param_for_untrusted_coerce_arg(
                Some(&template),
                &stale_closed,
                &plain_arg,
                &policy
            ),
            None
        );
    }

    #[test]
    fn expected_callee_return_constrains_generic_spine_result() {
        let mut graph = TypeGraph::default();
        let effect_var = typed_ir::TypeVar("e#0".to_string());
        let value_var = typed_ir::TypeVar("a#0".to_string());
        let result = ref_type(
            typed_ir::Type::Var(effect_var.clone()),
            typed_ir::Type::Var(value_var.clone()),
        );
        let result_effect = typed_ir::Type::Never;
        let list_int = list_type(named_type("int"));
        let expected_ref = ref_type(local_effect_type("xs", list_int.clone()), list_int.clone());
        let evidence = typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::default(),
            expected_callee: Some(typed_ir::TypeBounds {
                lower: None,
                upper: Some(Box::new(typed_ir::Type::Fun {
                    param: Box::new(named_type("unit")),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(local_effect_type("xs", list_int.clone())),
                    ret: Box::new(expected_ref),
                })),
            }),
            arg: typed_ir::TypeBounds::default(),
            expected_arg: None,
            result: typed_ir::TypeBounds::default(),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };

        assert!(
            constrain_expected_callee_return_bounds(&mut graph, &result, &result_effect, &evidence)
                .unwrap()
        );

        assert_eq!(
            graph.slot(&value_var).and_then(|slot| slot.solution_ref()),
            Some(&list_int)
        );
    }

    fn ref_type(effect: typed_ir::Type, value: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("var".to_string()),
                typed_ir::Name("ref".to_string()),
            ]),
            args: vec![
                typed_ir::TypeArg::Type(effect),
                typed_ir::TypeArg::Type(value),
            ],
        }
    }

    fn local_effect_type(name: &str, value: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![typed_ir::Name(name.to_string())]),
            args: vec![typed_ir::TypeArg::Type(value)],
        }
    }

    fn list_type(item: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("list".to_string()),
                typed_ir::Name("list".to_string()),
            ]),
            args: vec![typed_ir::TypeArg::Type(item)],
        }
    }

    fn variant_type(
        cases: Vec<(&str, Vec<typed_ir::Type>)>,
        tail: Option<typed_ir::Type>,
    ) -> typed_ir::Type {
        typed_ir::Type::Variant(typed_ir::VariantType {
            cases: cases
                .into_iter()
                .map(|(name, payloads)| typed_ir::VariantCase {
                    name: typed_ir::Name(name.to_string()),
                    payloads,
                })
                .collect(),
            tail: tail.map(Box::new),
        })
    }

    fn named_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![typed_ir::Name(name.to_string())]),
            args: Vec::new(),
        }
    }
}
