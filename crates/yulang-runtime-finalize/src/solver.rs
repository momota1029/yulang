use std::collections::{HashMap, HashSet};

use yulang_runtime_ir::{Binding, Expr, ExprKind, Module, Root, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{
    CachedFinalizeInstance, FinalizeDiagnostic, FinalizeInstanceCache, FinalizeInstanceKey,
    FinalizeOutput, FinalizeReport, FinalizeResult, RootGraphInput, RootGraphSolution, TypeGraph,
    materialize_core_type, materialize_runtime_type, output::RootGraphRoot,
};

pub fn finalize_module(module: Module) -> FinalizeResult<FinalizeOutput> {
    let mut cache = FinalizeInstanceCache::default();
    finalize_module_with_cache(module, &mut cache)
}

pub fn finalize_module_with_cache(
    mut module: Module,
    cache: &mut FinalizeInstanceCache,
) -> FinalizeResult<FinalizeOutput> {
    let root_graph_inputs = collect_root_graph_inputs(&module);
    let mut root_graph_solutions = solve_root_graphs(&module)?;
    loop {
        canonicalize_aliases(&mut root_graph_solutions);
        let emitted = append_monomorphic_bindings(&mut module, &root_graph_solutions, cache)?;
        rewrite_root_exprs(&mut module, &root_graph_solutions)?;
        rewrite_binding_exprs(&mut module, &root_graph_solutions)?;

        let solution_count = root_graph_solutions.len();
        collect_binding_body_graphs(&module, &emitted, &mut root_graph_solutions)?;
        if emitted.is_empty() && root_graph_solutions.len() == solution_count {
            break;
        }
    }
    prune_specialized_polymorphic_bindings(&mut module, &root_graph_solutions);
    Ok(FinalizeOutput {
        module,
        report: FinalizeReport {
            root_graph_inputs,
            root_graph_solutions,
            cache_profile: cache.profile(),
        },
    })
}

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
                known_type: runtime_type_is_closed(&expr.ty).then(|| expr.ty.clone()),
            }),
        })
        .collect()
}

pub fn solve_root_graphs(module: &Module) -> FinalizeResult<Vec<RootGraphSolution>> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut solutions = Vec::new();
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
            &HashMap::new(),
            &mut solutions,
        )?;
    }
    Ok(solutions)
}

fn collect_binding_body_graphs(
    module: &Module,
    aliases: &[typed_ir::Path],
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
            &binding_local_types(binding),
            solutions,
        )?;
    }
    Ok(())
}

fn collect_expr_graphs(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    let found = solve_simple_apply(owner.clone(), expr, bindings, local_types, solutions.len())?;
    if !found.is_empty() {
        collect_apply_spine_arg_graphs(owner, expr, bindings, local_types, solutions)?;
        solutions.extend(found);
        return Ok(());
    }
    if let Some(solution) =
        solve_bare_polymorphic_var(owner.clone(), expr, bindings, local_types, solutions.len())?
    {
        solutions.push(solution);
        return Ok(());
    }
    match &expr.kind {
        ExprKind::Lambda { param, body, .. } => {
            let mut scoped_locals = local_types.clone();
            if let Some(param_ty) = runtime_function_param(&expr.ty) {
                scoped_locals.insert(path_from_name(param), param_ty);
            }
            collect_expr_graphs(owner, body, bindings, &scoped_locals, solutions)
        }
        ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => {
            collect_expr_graphs(owner, body, bindings, local_types, solutions)
        }
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_graphs(owner.clone(), callee, bindings, local_types, solutions)?;
            collect_expr_graphs(owner, arg, bindings, local_types, solutions)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_graphs(owner.clone(), cond, bindings, local_types, solutions)?;
            collect_expr_graphs(owner.clone(), then_branch, bindings, local_types, solutions)?;
            collect_expr_graphs(owner, else_branch, bindings, local_types, solutions)
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_graphs(owner.clone(), item, bindings, local_types, solutions)?;
            }
            Ok(())
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_graphs(
                    owner.clone(),
                    &field.value,
                    bindings,
                    local_types,
                    solutions,
                )?;
            }
            if let Some(spread) = spread {
                collect_record_spread_graphs(owner, spread, bindings, local_types, solutions)?;
            }
            Ok(())
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_graphs(owner, value, bindings, local_types, solutions)?;
            }
            Ok(())
        }
        ExprKind::Select { base, .. } | ExprKind::Thunk { expr: base, .. } => {
            collect_expr_graphs(owner, base, bindings, local_types, solutions)
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_graphs(owner.clone(), scrutinee, bindings, local_types, solutions)?;
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.pattern, &mut arm_locals);
                if let Some(guard) = &arm.guard {
                    collect_expr_graphs(owner.clone(), guard, bindings, &arm_locals, solutions)?;
                }
                collect_expr_graphs(owner.clone(), &arm.body, bindings, &arm_locals, solutions)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, tail } => {
            let mut scoped_locals = local_types.clone();
            for stmt in stmts {
                collect_stmt_graphs(owner.clone(), stmt, bindings, &scoped_locals, solutions)?;
                collect_stmt_local_types(stmt, &mut scoped_locals);
            }
            if let Some(tail) = tail {
                collect_expr_graphs(owner, tail, bindings, &scoped_locals, solutions)?;
            }
            Ok(())
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_graphs(owner.clone(), body, bindings, local_types, solutions)?;
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.payload, &mut arm_locals);
                if let Some(resume) = &arm.resume {
                    arm_locals.insert(path_from_name(&resume.name), resume.ty.clone());
                }
                if let Some(guard) = &arm.guard {
                    collect_expr_graphs(owner.clone(), guard, bindings, &arm_locals, solutions)?;
                }
                collect_expr_graphs(owner.clone(), &arm.body, bindings, &arm_locals, solutions)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn collect_apply_spine_arg_graphs(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    let ExprKind::Apply { callee, arg, .. } = &expr.kind else {
        return Ok(());
    };
    collect_apply_spine_arg_graphs(owner.clone(), callee, bindings, local_types, solutions)?;
    collect_expr_graphs(owner, arg, bindings, local_types, solutions)
}

fn solve_bare_polymorphic_var(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
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
    let expected = runtime_type_to_core(expr_lower_type(expr, local_types));
    if !core_type_is_closed(&expected) {
        return Ok(None);
    }
    solve_value_arg(owner, binding, expected, alias_index).map(Some)
}

fn solve_simple_apply(
    owner: RootGraphRoot,
    expr: &Expr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    alias_index: usize,
) -> FinalizeResult<Vec<RootGraphSolution>> {
    let Some(spine) = ApplySpine::new(expr) else {
        return Ok(Vec::new());
    };
    let binding_path = spine.binding;
    let Some(binding) = bindings.get(binding_path) else {
        return Ok(Vec::new());
    };
    if binding.type_params.is_empty() {
        return Ok(Vec::new());
    }
    let mut solutions =
        solve_spine_value_args(owner.clone(), &spine, bindings, local_types, alias_index)?;
    let mut graph = TypeGraph::default();
    let principal = graph.instantiate_principal(binding);
    graph.collect_runtime_bounds(
        &principal.principal_type,
        &crate::RuntimeBounds::exact(spine.callee.ty.clone()),
    )?;
    collect_spine_substitutions(&mut graph, &principal, &spine.steps)?;
    let mut current = principal.principal_type.clone();
    for step in &spine.steps {
        let result = graph.fresh_hole("apply");
        let (arg_type, arg_effect) = step.arg_type_and_effect(local_types);
        let expected = typed_ir::Type::Fun {
            param: Box::new(arg_type),
            param_effect: Box::new(arg_effect),
            ret_effect: Box::new(typed_ir::Type::Unknown),
            ret: Box::new(result.clone()),
        };
        graph.constrain_subtype(current, expected)?;
        current = result;
    }
    let graph = graph.solve();
    if !graph.is_complete() {
        return Err(FinalizeDiagnostic::IncompleteGraph {
            binding: binding_path.clone(),
        });
    }
    let callee_type = RuntimeType::Core(graph.materialize_core(principal.principal_type.clone()));
    let result_type = solved_expr_result_type(&expr.ty, &graph, current);
    let type_substitutions = principal.original_substitutions(&graph);
    solutions.push(RootGraphSolution {
        root: owner,
        occurrence: alias_index + solutions.len(),
        binding: binding_path.clone(),
        alias: alias_path(binding_path, alias_index + solutions.len()),
        callee_type,
        result_type,
        graph,
        type_substitutions,
    });
    Ok(solutions)
}

fn solved_expr_result_type(
    expr_ty: &RuntimeType,
    graph: &crate::GraphSolution,
    result: typed_ir::Type,
) -> RuntimeType {
    let materialized = materialize_runtime_type(expr_ty.clone(), &graph.substitutions());
    if runtime_type_is_closed(&materialized) {
        materialized
    } else {
        RuntimeType::Core(graph.materialize_core(result))
    }
}

fn solve_spine_value_args(
    owner: RootGraphRoot,
    spine: &ApplySpine<'_>,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
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
    alias_index: usize,
) -> FinalizeResult<RootGraphSolution> {
    let mut graph = TypeGraph::default();
    let principal = graph.instantiate_principal(binding);
    graph.constrain_subtype(principal.principal_type.clone(), expected_type)?;
    let graph = graph.solve();
    if !graph.is_complete() {
        return Err(FinalizeDiagnostic::IncompleteGraph {
            binding: binding.name.clone(),
        });
    }
    let callee_type = RuntimeType::Core(graph.materialize_core(principal.principal_type.clone()));
    let type_substitutions = principal.original_substitutions(&graph);
    Ok(RootGraphSolution {
        root: owner,
        occurrence: alias_index,
        binding: binding.name.clone(),
        alias: alias_path(&binding.name, alias_index),
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
        if let Some(evidence) = step.evidence {
            for substitution in evidence_complete_substitutions(evidence) {
                collect_spine_substitution(graph, principal, &substitution.var, &substitution.ty)?;
            }
        }
        if let Some(instantiation) = step.instantiation {
            for substitution in &instantiation.args {
                collect_spine_substitution(graph, principal, &substitution.var, &substitution.ty)?;
            }
        }
    }
    Ok(())
}

fn evidence_complete_substitutions(
    evidence: &typed_ir::ApplyEvidence,
) -> &[typed_ir::TypeSubstitution] {
    match &evidence.principal_elaboration {
        Some(plan) if !plan.complete => &[],
        Some(plan) => &plan.substitutions,
        None => &evidence.substitutions,
    }
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

struct ApplySpine<'a> {
    binding: &'a typed_ir::Path,
    callee: &'a Expr,
    steps: Vec<ApplyStep<'a>>,
}

struct ApplyStep<'a> {
    arg: &'a Expr,
    evidence: Option<&'a typed_ir::ApplyEvidence>,
    instantiation: Option<&'a yulang_runtime_ir::TypeInstantiation>,
}

impl ApplyStep<'_> {
    fn arg_type(&self, local_types: &HashMap<typed_ir::Path, RuntimeType>) -> typed_ir::Type {
        self.arg_type_and_effect(local_types).0
    }

    fn arg_type_and_effect(
        &self,
        local_types: &HashMap<typed_ir::Path, RuntimeType>,
    ) -> (typed_ir::Type, typed_ir::Type) {
        let runtime_ty = expr_lower_type(self.arg, local_types);
        if let RuntimeType::Thunk { effect, value } = &runtime_ty {
            let value_is_closed = runtime_type_is_closed(value);
            let arg_type = if value_is_closed {
                runtime_type_to_core((**value).clone())
            } else {
                let expr_ty = runtime_type_to_core(runtime_ty.clone());
                self.evidence.and_then(apply_arg_type).unwrap_or(expr_ty)
            };
            let arg_effect = if core_type_is_closed(effect)
                && (value_is_closed || !matches!(effect, typed_ir::Type::Any))
            {
                effect.clone()
            } else {
                typed_ir::Type::Never
            };
            return (arg_type, arg_effect);
        }
        let expr_ty = runtime_type_to_core(runtime_ty);
        if core_type_is_closed(&expr_ty) {
            return (expr_ty, typed_ir::Type::Never);
        }
        let fallback = self.evidence.and_then(apply_arg_type).unwrap_or(expr_ty);
        (fallback, typed_ir::Type::Never)
    }
}

impl<'a> ApplySpine<'a> {
    fn new(expr: &'a Expr) -> Option<Self> {
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

fn type_from_bounds(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    bounds
        .lower
        .as_deref()
        .cloned()
        .or_else(|| bounds.upper.as_deref().cloned())
}

fn collect_record_spread_graphs(
    owner: RootGraphRoot,
    spread: &yulang_runtime_ir::RecordSpreadExpr,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            collect_expr_graphs(owner, expr, bindings, local_types, solutions)
        }
    }
}

fn collect_stmt_graphs(
    owner: RootGraphRoot,
    stmt: &yulang_runtime_ir::Stmt,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => {
            collect_pattern_graphs(owner.clone(), pattern, bindings, local_types, solutions)?;
            collect_expr_graphs(owner, value, bindings, local_types, solutions)
        }
        yulang_runtime_ir::Stmt::Expr(expr)
        | yulang_runtime_ir::Stmt::Module { body: expr, .. } => {
            collect_expr_graphs(owner, expr, bindings, local_types, solutions)
        }
    }
}

fn collect_pattern_graphs(
    owner: RootGraphRoot,
    pattern: &yulang_runtime_ir::Pattern,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    use yulang_runtime_ir::Pattern;

    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_graphs(owner.clone(), item, bindings, local_types, solutions)?;
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
                collect_pattern_graphs(owner.clone(), item, bindings, local_types, solutions)?;
            }
            if let Some(spread) = spread {
                collect_pattern_graphs(owner.clone(), spread, bindings, local_types, solutions)?;
            }
            for item in suffix {
                collect_pattern_graphs(owner.clone(), item, bindings, local_types, solutions)?;
            }
            Ok(())
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_graphs(
                    owner.clone(),
                    &field.pattern,
                    bindings,
                    local_types,
                    solutions,
                )?;
                if let Some(default) = &field.default {
                    collect_expr_graphs(owner.clone(), default, bindings, local_types, solutions)?;
                }
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::RecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_graphs(owner, pattern, bindings, local_types, solutions)?;
                    }
                }
            }
            Ok(())
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_graphs(owner, value, bindings, local_types, solutions)?;
            }
            Ok(())
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_graphs(owner.clone(), left, bindings, local_types, solutions)?;
            collect_pattern_graphs(owner, right, bindings, local_types, solutions)
        }
        Pattern::As { pattern, .. } => {
            collect_pattern_graphs(owner, pattern, bindings, local_types, solutions)
        }
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => Ok(()),
    }
}

fn collect_stmt_local_types(
    stmt: &yulang_runtime_ir::Stmt,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
) {
    let yulang_runtime_ir::Stmt::Let { pattern, .. } = stmt else {
        return;
    };
    collect_pattern_local_types(pattern, local_types);
}

fn collect_pattern_local_types(
    pattern: &yulang_runtime_ir::Pattern,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
) {
    use yulang_runtime_ir::Pattern;

    match pattern {
        Pattern::Bind { name, ty } => {
            local_types.insert(path_from_name(name), ty.clone());
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_local_types(item, local_types);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_local_types(item, local_types);
            }
            if let Some(spread) = spread {
                collect_pattern_local_types(spread, local_types);
            }
            for item in suffix {
                collect_pattern_local_types(item, local_types);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_local_types(&field.pattern, local_types);
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::RecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_local_types(pattern, local_types);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_local_types(value, local_types);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_local_types(left, local_types);
            collect_pattern_local_types(right, local_types);
        }
        Pattern::As { pattern, name, ty } => {
            collect_pattern_local_types(pattern, local_types);
            local_types.insert(path_from_name(name), ty.clone());
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn binding_local_types(binding: &Binding) -> HashMap<typed_ir::Path, RuntimeType> {
    let mut local_types = HashMap::new();
    let ExprKind::Lambda { param, .. } = &binding.body.kind else {
        return local_types;
    };
    if let Some((param_ty, _)) = function_parts(&binding.scheme.body) {
        local_types.insert(path_from_name(param), RuntimeType::Core(param_ty.clone()));
    }
    local_types
}

fn expr_lower_type(expr: &Expr, local_types: &HashMap<typed_ir::Path, RuntimeType>) -> RuntimeType {
    if !matches!(expr.ty, RuntimeType::Unknown) {
        return expr.ty.clone();
    }
    let ExprKind::Var(path) = &expr.kind else {
        return RuntimeType::Unknown;
    };
    local_types
        .get(path)
        .cloned()
        .unwrap_or(RuntimeType::Unknown)
}

fn runtime_type_to_core(ty: RuntimeType) -> typed_ir::Type {
    match ty {
        RuntimeType::Unknown => typed_ir::Type::Unknown,
        RuntimeType::Core(ty) => ty,
        RuntimeType::Fun { param, ret } => typed_ir::Type::Fun {
            param: Box::new(runtime_type_to_core(*param)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Unknown),
            ret: Box::new(runtime_type_to_core(*ret)),
        },
        RuntimeType::Thunk { value, .. } => runtime_type_to_core(*value),
    }
}

fn runtime_function_param(ty: &RuntimeType) -> Option<RuntimeType> {
    let RuntimeType::Fun { param, .. } = ty else {
        return None;
    };
    Some((**param).clone())
}

fn path_from_name(name: &typed_ir::Name) -> typed_ir::Path {
    typed_ir::Path::from_name(name.clone())
}

fn canonicalize_aliases(solutions: &mut [RootGraphSolution]) {
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

fn append_monomorphic_bindings(
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
            let scheme = typed_ir::Scheme {
                requirements: Vec::new(),
                body: materialize_core_type(
                    binding.scheme.body.clone(),
                    &solution.type_substitutions,
                ),
            };
            let body = materialize_expr(binding.body.clone(), &solution.type_substitutions);
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

fn rewrite_root_exprs(module: &mut Module, solutions: &[RootGraphSolution]) -> FinalizeResult<()> {
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

fn rewrite_binding_exprs(
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
    let is_apply_spine =
        matches!(expr.kind, ExprKind::Apply { .. }) && apply_spine_binding(expr).is_some();
    match &mut expr.kind {
        ExprKind::Apply { .. } if is_apply_spine => {
            rewrite_apply_spine_args(expr, solutions, cursor)?;
            if rewrite_simple_apply(expr, solutions, cursor)? {
                return Ok(());
            }
            Ok(())
        }
        ExprKind::Apply { callee, arg, .. } => {
            rewrite_root_expr(callee, solutions, cursor)?;
            rewrite_root_expr(arg, solutions, cursor)
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => rewrite_root_expr(body, solutions, cursor),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            rewrite_root_expr(cond, solutions, cursor)?;
            rewrite_root_expr(then_branch, solutions, cursor)?;
            rewrite_root_expr(else_branch, solutions, cursor)
        }
        ExprKind::Tuple(items) => {
            for item in items {
                rewrite_root_expr(item, solutions, cursor)?;
            }
            Ok(())
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                rewrite_root_expr(&mut field.value, solutions, cursor)?;
            }
            if let Some(spread) = spread {
                rewrite_record_spread_expr(spread, solutions, cursor)?;
            }
            Ok(())
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                rewrite_root_expr(value, solutions, cursor)?;
            }
            Ok(())
        }
        ExprKind::Select { base, .. } | ExprKind::Thunk { expr: base, .. } => {
            rewrite_root_expr(base, solutions, cursor)
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            rewrite_root_expr(scrutinee, solutions, cursor)?;
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    rewrite_root_expr(guard, solutions, cursor)?;
                }
                rewrite_root_expr(&mut arm.body, solutions, cursor)?;
            }
            Ok(())
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                rewrite_stmt(stmt, solutions, cursor)?;
            }
            if let Some(tail) = tail {
                rewrite_root_expr(tail, solutions, cursor)?;
            }
            Ok(())
        }
        ExprKind::Handle { body, arms, .. } => {
            rewrite_root_expr(body, solutions, cursor)?;
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    rewrite_root_expr(guard, solutions, cursor)?;
                }
                rewrite_root_expr(&mut arm.body, solutions, cursor)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
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
    materialize_expr_in_place(expr, &solution.type_substitutions);
    expr.ty = solution.result_type.clone();
    *cursor += 1;
    Ok(true)
}

fn apply_spine_binding(expr: &Expr) -> Option<&typed_ir::Path> {
    let mut current = expr;
    while let ExprKind::Apply { callee, .. } = &current.kind {
        current = callee;
    }
    let ExprKind::Var(path) = &current.kind else {
        return None;
    };
    Some(path)
}

fn replace_apply_spine_binding(expr: &mut Expr, alias: &typed_ir::Path, callee_type: &RuntimeType) {
    match &mut expr.kind {
        ExprKind::Apply { callee, .. } => replace_apply_spine_binding(callee, alias, callee_type),
        ExprKind::Var(path) => {
            *path = alias.clone();
            expr.ty = callee_type.clone();
        }
        _ => {}
    }
}

fn rewrite_record_spread_expr(
    spread: &mut yulang_runtime_ir::RecordSpreadExpr,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> FinalizeResult<()> {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            rewrite_root_expr(expr, solutions, cursor)
        }
    }
}

fn rewrite_stmt(
    stmt: &mut yulang_runtime_ir::Stmt,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> FinalizeResult<()> {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => {
            rewrite_pattern(pattern, solutions, cursor)?;
            rewrite_root_expr(value, solutions, cursor)
        }
        yulang_runtime_ir::Stmt::Expr(expr)
        | yulang_runtime_ir::Stmt::Module { body: expr, .. } => {
            rewrite_root_expr(expr, solutions, cursor)
        }
    }
}

fn rewrite_pattern(
    pattern: &mut yulang_runtime_ir::Pattern,
    solutions: &[&RootGraphSolution],
    cursor: &mut usize,
) -> FinalizeResult<()> {
    use yulang_runtime_ir::Pattern;

    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                rewrite_pattern(item, solutions, cursor)?;
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
                rewrite_pattern(item, solutions, cursor)?;
            }
            if let Some(spread) = spread {
                rewrite_pattern(spread, solutions, cursor)?;
            }
            for item in suffix {
                rewrite_pattern(item, solutions, cursor)?;
            }
            Ok(())
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                rewrite_pattern(&mut field.pattern, solutions, cursor)?;
                if let Some(default) = &mut field.default {
                    rewrite_root_expr(default, solutions, cursor)?;
                }
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::RecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
                        rewrite_pattern(pattern, solutions, cursor)?;
                    }
                }
            }
            Ok(())
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                rewrite_pattern(value, solutions, cursor)?;
            }
            Ok(())
        }
        Pattern::Or { left, right, .. } => {
            rewrite_pattern(left, solutions, cursor)?;
            rewrite_pattern(right, solutions, cursor)
        }
        Pattern::As { pattern, .. } => rewrite_pattern(pattern, solutions, cursor),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => Ok(()),
    }
}

fn prune_specialized_polymorphic_bindings(module: &mut Module, solutions: &[RootGraphSolution]) {
    let specialized = solutions
        .iter()
        .map(|solution| solution.binding.clone())
        .collect::<HashSet<_>>();
    let reachable = reachable_paths(module);
    module.bindings.retain(|binding| {
        binding.type_params.is_empty()
            || (reachable.contains(&binding.name) && !specialized.contains(&binding.name))
    });
}

fn reachable_paths(module: &Module) -> HashSet<typed_ir::Path> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut pending = Vec::new();
    for expr in &module.root_exprs {
        collect_expr_paths(expr, &mut pending);
    }
    for root in &module.roots {
        if let Root::Binding(path) = root {
            pending.push(path.clone());
        }
    }
    while let Some(path) = pending.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        if let Some(binding) = bindings.get(&path) {
            collect_expr_paths(&binding.body, &mut pending);
        }
    }
    reachable
}

fn materialize_expr(expr: Expr, substitutions: &[typed_ir::TypeSubstitution]) -> Expr {
    let ty = materialize_runtime_type(expr.ty, substitutions);
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
            body: Box::new(materialize_expr(*body, substitutions)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(materialize_expr(*callee, substitutions)),
            arg: Box::new(materialize_expr(*arg, substitutions)),
            evidence,
            instantiation,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| materialize_expr(item, substitutions))
                .collect(),
        ),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(materialize_expr(*cond, substitutions)),
            then_branch: Box::new(materialize_expr(*then_branch, substitutions)),
            else_branch: Box::new(materialize_expr(*else_branch, substitutions)),
            evidence: evidence.map(|evidence| materialize_join_evidence(evidence, substitutions)),
        },
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordExprField {
                    name: field.name,
                    value: materialize_expr(field.value, substitutions),
                })
                .collect(),
            spread: spread.map(|spread| materialize_record_spread_expr(spread, substitutions)),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(materialize_expr(*value, substitutions))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(materialize_expr(*base, substitutions)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(materialize_expr(*scrutinee, substitutions)),
            arms: arms
                .into_iter()
                .map(|arm| materialize_match_arm(arm, substitutions))
                .collect(),
            evidence: materialize_join_evidence(evidence, substitutions),
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| materialize_stmt(stmt, substitutions))
                .collect(),
            tail: tail.map(|tail| Box::new(materialize_expr(*tail, substitutions))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(materialize_expr(*body, substitutions)),
            arms: arms
                .into_iter()
                .map(|arm| materialize_handle_arm(arm, substitutions))
                .collect(),
            evidence: materialize_join_evidence(evidence, substitutions),
            handler: materialize_handle_effect(handler, substitutions),
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(materialize_expr(*expr, substitutions)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect: materialize_core_type(effect, substitutions),
            value: materialize_runtime_type(value, substitutions),
            expr: Box::new(materialize_expr(*expr, substitutions)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(materialize_expr(*body, substitutions)),
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
            allowed: materialize_core_type(allowed, substitutions),
            active,
            thunk: Box::new(materialize_expr(*thunk, substitutions)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from: materialize_core_type(from, substitutions),
            to: materialize_core_type(to, substitutions),
            expr: Box::new(materialize_expr(*expr, substitutions)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(materialize_expr(*expr, substitutions)),
        },
    };
    Expr::typed(kind, ty)
}

fn materialize_expr_in_place(expr: &mut Expr, substitutions: &[typed_ir::TypeSubstitution]) {
    *expr = materialize_expr(expr.clone(), substitutions);
}

fn materialize_stmt(
    stmt: yulang_runtime_ir::Stmt,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::Stmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: materialize_pattern(pattern, substitutions),
            value: materialize_expr(value, substitutions),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(materialize_expr(expr, substitutions))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: materialize_expr(body, substitutions),
        },
    }
}

fn materialize_pattern(
    pattern: yulang_runtime_ir::Pattern,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::Pattern {
    use yulang_runtime_ir::Pattern;

    match pattern {
        Pattern::Wildcard { ty } => Pattern::Wildcard {
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Bind { name, ty } => Pattern::Bind {
            name,
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Lit { lit, ty } => Pattern::Lit {
            lit,
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| materialize_pattern(item, substitutions))
                .collect(),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(|item| materialize_pattern(item, substitutions))
                .collect(),
            spread: spread.map(|spread| Box::new(materialize_pattern(*spread, substitutions))),
            suffix: suffix
                .into_iter()
                .map(|item| materialize_pattern(item, substitutions))
                .collect(),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordPatternField {
                    name: field.name,
                    pattern: materialize_pattern(field.pattern, substitutions),
                    default: field
                        .default
                        .map(|expr| materialize_expr(expr, substitutions)),
                })
                .collect(),
            spread,
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(materialize_pattern(*value, substitutions))),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(materialize_pattern(*left, substitutions)),
            right: Box::new(materialize_pattern(*right, substitutions)),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(materialize_pattern(*pattern, substitutions)),
            name,
            ty: materialize_runtime_type(ty, substitutions),
        },
    }
}

fn materialize_record_spread_expr(
    spread: yulang_runtime_ir::RecordSpreadExpr,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::RecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(materialize_expr(
                *expr,
                substitutions,
            )))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(materialize_expr(
                *expr,
                substitutions,
            )))
        }
    }
}

fn materialize_match_arm(
    arm: yulang_runtime_ir::MatchArm,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::MatchArm {
    yulang_runtime_ir::MatchArm {
        pattern: materialize_pattern(arm.pattern, substitutions),
        guard: arm
            .guard
            .map(|guard| materialize_expr(guard, substitutions)),
        body: materialize_expr(arm.body, substitutions),
    }
}

fn materialize_handle_arm(
    arm: yulang_runtime_ir::HandleArm,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::HandleArm {
    yulang_runtime_ir::HandleArm {
        effect: arm.effect,
        payload: materialize_pattern(arm.payload, substitutions),
        resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
            name: resume.name,
            ty: materialize_runtime_type(resume.ty, substitutions),
        }),
        guard: arm
            .guard
            .map(|guard| materialize_expr(guard, substitutions)),
        body: materialize_expr(arm.body, substitutions),
    }
}

fn materialize_join_evidence(
    evidence: yulang_runtime_ir::JoinEvidence,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::JoinEvidence {
    yulang_runtime_ir::JoinEvidence {
        result: materialize_core_type(evidence.result, substitutions),
    }
}

fn materialize_handle_effect(
    handler: yulang_runtime_ir::HandleEffect,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::HandleEffect {
    yulang_runtime_ir::HandleEffect {
        consumes: handler.consumes,
        residual_before: handler
            .residual_before
            .map(|ty| materialize_core_type(ty, substitutions)),
        residual_after: handler
            .residual_after
            .map(|ty| materialize_core_type(ty, substitutions)),
    }
}

fn collect_expr_paths(expr: &Expr, paths: &mut Vec<typed_ir::Path>) {
    match &expr.kind {
        ExprKind::Var(path) | ExprKind::EffectOp(path) => {
            paths.push(path.clone());
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => collect_expr_paths(body, paths),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_paths(callee, paths);
            collect_expr_paths(arg, paths);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_paths(cond, paths);
            collect_expr_paths(then_branch, paths);
            collect_expr_paths(else_branch, paths);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_paths(item, paths);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_paths(&field.value, paths);
            }
            if let Some(spread) = spread {
                collect_record_spread_expr_paths(spread, paths);
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_paths(value, paths);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_paths(base, paths),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_paths(scrutinee, paths);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_paths(guard, paths);
                }
                collect_expr_paths(&arm.body, paths);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_paths(stmt, paths);
            }
            if let Some(tail) = tail {
                collect_expr_paths(tail, paths);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_paths(body, paths);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_paths(guard, paths);
                }
                collect_expr_paths(&arm.body, paths);
            }
        }
        ExprKind::Thunk { expr, .. } => collect_expr_paths(expr, paths),
        ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_record_spread_expr_paths(
    spread: &yulang_runtime_ir::RecordSpreadExpr,
    paths: &mut Vec<typed_ir::Path>,
) {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => collect_expr_paths(expr, paths),
    }
}

fn collect_stmt_paths(stmt: &yulang_runtime_ir::Stmt, paths: &mut Vec<typed_ir::Path>) {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => {
            collect_pattern_paths(pattern, paths);
            collect_expr_paths(value, paths);
        }
        yulang_runtime_ir::Stmt::Expr(expr)
        | yulang_runtime_ir::Stmt::Module { body: expr, .. } => {
            collect_expr_paths(expr, paths);
        }
    }
}

fn collect_pattern_paths(pattern: &yulang_runtime_ir::Pattern, paths: &mut Vec<typed_ir::Path>) {
    use yulang_runtime_ir::Pattern;

    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_paths(item, paths);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_paths(item, paths);
            }
            if let Some(spread) = spread {
                collect_pattern_paths(spread, paths);
            }
            for item in suffix {
                collect_pattern_paths(item, paths);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_paths(&field.pattern, paths);
                if let Some(default) = &field.default {
                    collect_expr_paths(default, paths);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::RecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_paths(pattern, paths);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_paths(value, paths);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_paths(left, paths);
            collect_pattern_paths(right, paths);
        }
        Pattern::As { pattern, .. } => collect_pattern_paths(pattern, paths),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
}

fn solution_instance_key(solution: &RootGraphSolution) -> FinalizeInstanceKey {
    FinalizeInstanceKey {
        binding: solution.binding.clone(),
        substitutions: solution.type_substitutions.clone(),
    }
}

fn alias_path(original: &typed_ir::Path, index: usize) -> typed_ir::Path {
    let mut segments = original.segments.clone();
    segments.push(typed_ir::Name(format!("mono{index}")));
    typed_ir::Path::new(segments)
}

fn function_parts(ty: &typed_ir::Type) -> Option<(&typed_ir::Type, &typed_ir::Type)> {
    let typed_ir::Type::Fun { param, ret, .. } = ty else {
        return None;
    };
    Some((param, ret))
}

fn runtime_type_is_closed(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Core(ty) => core_type_is_closed(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_is_closed(param) && runtime_type_is_closed(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_is_closed(effect) && runtime_type_is_closed(value)
        }
    }
}

fn core_type_is_closed(ty: &yulang_typed_ir::Type) -> bool {
    use yulang_typed_ir::Type;

    match ty {
        Type::Unknown | Type::Var(_) => false,
        Type::Never | Type::Any => true,
        Type::Named { args, .. } => args.iter().all(type_arg_is_closed),
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_is_closed(param)
                && core_type_is_closed(param_effect)
                && core_type_is_closed(ret_effect)
                && core_type_is_closed(ret)
        }
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => {
            items.iter().all(core_type_is_closed)
        }
        Type::Record(record) => record
            .fields
            .iter()
            .all(|field| core_type_is_closed(&field.value)),
        Type::Variant(variant) => variant
            .cases
            .iter()
            .all(|case| case.payloads.iter().all(core_type_is_closed)),
        Type::Row { items, tail } => {
            items.iter().all(core_type_is_closed) && core_type_is_closed(tail)
        }
        Type::Recursive { body, .. } => core_type_is_closed(body),
    }
}

fn type_arg_is_closed(arg: &yulang_typed_ir::TypeArg) -> bool {
    match arg {
        yulang_typed_ir::TypeArg::Type(ty) => core_type_is_closed(ty),
        yulang_typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_none_or(|ty| core_type_is_closed(ty))
                && bounds
                    .upper
                    .as_ref()
                    .is_none_or(|ty| core_type_is_closed(ty))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FinalizeInstanceArtifactCache;
    use yulang_runtime_ir::{Expr, ExprKind};
    use yulang_sources::{
        CompiledSourceFileIdentity, CompiledUnitDependency, CompiledUnitManifest,
        SourceCompilationUnitOrigin, SourceOrigin,
    };
    use yulang_typed_ir as typed_ir;

    #[test]
    fn closed_root_expr_becomes_root_graph_input() {
        let ty = RuntimeType::Core(typed_ir::Type::Tuple(Vec::new()));
        let module = Module {
            path: path("test"),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(ExprKind::Tuple(Vec::new()), ty.clone())],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        assert_eq!(
            collect_root_graph_inputs(&module),
            vec![RootGraphInput {
                root: RootGraphRoot::Expr(0),
                known_type: Some(ty),
            }]
        );
    }

    #[test]
    fn open_root_expr_does_not_make_fake_any_input() {
        let module = Module {
            path: path("test"),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Tuple(Vec::new()),
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        assert_eq!(collect_root_graph_inputs(&module)[0].known_type, None);
    }

    #[test]
    fn root_apply_solves_id_one_graph() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(ExprKind::Var(path("id")), RuntimeType::Unknown)),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Core(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 1);
        let solution = &output.report.root_graph_solutions[0];
        assert_eq!(solution.binding, path("id"));
        assert_eq!(solution.result_type, RuntimeType::Core(int.clone()));
        assert!(solution.graph.is_complete());
        assert_eq!(solution.graph.substitutions()[0].ty, int);
        assert_eq!(solution.alias, path(&["id", "mono0"]));
        assert_eq!(output.module.bindings.len(), 1);
        assert_eq!(output.module.bindings[0].name, path(&["id", "mono0"]));
        assert!(output.module.bindings[0].type_params.is_empty());
        assert_eq!(
            simple_apply_callee_path(&output.module.root_exprs[0]),
            Some(path(&["id", "mono0"]))
        );
        assert_eq!(
            output.module.root_exprs[0].ty,
            RuntimeType::Core(int.clone())
        );
    }

    #[test]
    fn finalize_instance_cache_surface_reuses_materialized_binding() {
        let mut cache = FinalizeInstanceCache::default();
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let first = finalize_module_with_cache(module.clone(), &mut cache).unwrap();
        assert_eq!(first.report.cache_profile.inserts, 1);
        assert_eq!(cache.to_surface().instances.len(), 1);

        let second = finalize_module_with_cache(module.clone(), &mut cache).unwrap();
        assert!(second.report.cache_profile.hits >= 1);
        assert_eq!(second.module.bindings[0].name, path(&["id", "mono0"]));

        let surface = cache.to_surface();
        let mut restored = FinalizeInstanceCache::from_surface(surface);
        let third = finalize_module_with_cache(module, &mut restored).unwrap();
        assert_eq!(third.report.cache_profile.hits, 1);
        assert_eq!(third.module.bindings[0].name, path(&["id", "mono0"]));

        let mut stale_surface = cache.to_surface();
        stale_surface.format_version += 1;
        assert!(
            FinalizeInstanceCache::from_surface(stale_surface)
                .to_surface()
                .instances
                .is_empty()
        );
    }

    #[test]
    fn finalize_instance_artifact_cache_rehydrates_solver_cache() {
        let root = artifact_cache_root("solver-rehydrate");
        let _ = std::fs::remove_dir_all(&root);
        let artifact_cache = FinalizeInstanceArtifactCache::new(&root);
        let manifests = vec![compiled_manifest(0, 11), compiled_manifest(1, 29)];
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let mut first_cache = FinalizeInstanceCache::default();
        let first = finalize_module_with_cache(module.clone(), &mut first_cache).unwrap();
        assert_eq!(first.report.cache_profile.inserts, 1);
        artifact_cache
            .write_cache_for_manifests(&manifests, &first_cache)
            .unwrap();

        let mut restored = artifact_cache.read_cache_for_manifests(&manifests);
        let second = finalize_module_with_cache(module, &mut restored).unwrap();
        let _ = std::fs::remove_dir_all(&root);

        assert_eq!(second.report.cache_profile.hits, 1);
        assert_eq!(second.module.bindings[0].name, path(&["id", "mono0"]));
    }

    #[test]
    fn root_tuple_solves_two_id_uses_separately() {
        let int = int_type();
        let bool_ty = bool_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Tuple(vec![
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Core(int.clone()),
                    )),
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Bool(true)),
                        RuntimeType::Core(bool_ty.clone()),
                    )),
                ]),
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 2);
        assert_eq!(
            output.report.root_graph_solutions[0].result_type,
            RuntimeType::Core(int.clone())
        );
        assert_eq!(
            output.report.root_graph_solutions[1].result_type,
            RuntimeType::Core(bool_ty.clone())
        );
        assert_eq!(
            output.report.root_graph_solutions[0].graph.substitutions()[0].ty,
            int
        );
        assert_eq!(
            output.report.root_graph_solutions[1].graph.substitutions()[0].ty,
            bool_ty
        );
        assert_eq!(output.module.bindings.len(), 2);
        assert_eq!(output.module.bindings[0].name, path(&["id", "mono0"]));
        assert_eq!(output.module.bindings[1].name, path(&["id", "mono1"]));
        let ExprKind::Tuple(items) = &output.module.root_exprs[0].kind else {
            panic!("root should stay a tuple");
        };
        assert_eq!(
            simple_apply_callee_path(&items[0]),
            Some(path(&["id", "mono0"]))
        );
        assert_eq!(
            simple_apply_callee_path(&items[1]),
            Some(path(&["id", "mono1"]))
        );
        assert_eq!(items[0].ty, RuntimeType::Core(int.clone()));
        assert_eq!(items[1].ty, RuntimeType::Core(bool_ty.clone()));
    }

    #[test]
    fn repeated_same_instance_reuses_one_alias() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Tuple(vec![
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Core(int.clone()),
                    )),
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("2".into())),
                        RuntimeType::Core(int.clone()),
                    )),
                ]),
                RuntimeType::Unknown,
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 2);
        assert_eq!(
            output.report.root_graph_solutions[0].alias,
            output.report.root_graph_solutions[1].alias
        );
        assert_eq!(output.module.bindings.len(), 1);
        assert_eq!(output.module.bindings[0].name, path(&["id", "mono0"]));
        let ExprKind::Tuple(items) = &output.module.root_exprs[0].kind else {
            panic!("root should stay a tuple");
        };
        assert_eq!(
            simple_apply_callee_path(&items[0]),
            Some(path(&["id", "mono0"]))
        );
        assert_eq!(
            simple_apply_callee_path(&items[1]),
            Some(path(&["id", "mono0"]))
        );
    }

    #[test]
    fn source_my_id_x_eq_x_id_1_solves_root_graph() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 1);
        let solution = &output.report.root_graph_solutions[0];
        assert!(solution.graph.is_complete());
        assert!(matches!(solution.result_type, RuntimeType::Core(_)));
    }

    #[test]
    fn source_my_id_x_eq_x_two_roots_solve_separate_graphs() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\nid true\n");

        let output = finalize_module(module).unwrap();

        assert_eq!(output.report.root_graph_solutions.len(), 2);
        assert!(
            output
                .report
                .root_graph_solutions
                .iter()
                .all(|solution| solution.graph.is_complete())
        );
        assert_ne!(
            output.report.root_graph_solutions[0].result_type,
            output.report.root_graph_solutions[1].result_type
        );
        assert!(output.module.bindings.iter().any(|binding| {
            binding.name == path(&["id", "mono0"]) && binding.type_params.is_empty()
        }));
        assert!(output.module.bindings.iter().any(|binding| {
            binding.name == path(&["id", "mono1"]) && binding.type_params.is_empty()
        }));
    }

    #[test]
    fn finalized_source_id_1_runs_on_vm() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_solves_polymorphic_call_inside_monomorphic_body() {
        let module = runtime_module_from_source_without_std("my id x = x\nmy f y = id y\nf 1\n");

        let output = finalize_module(module).unwrap();
        let aliases = output
            .module
            .bindings
            .iter()
            .map(|binding| binding.name.clone())
            .collect::<Vec<_>>();
        assert!(aliases.contains(&path(&["f", "mono0"])));
        assert!(aliases.contains(&path(&["id", "mono1"])));
        assert!(
            output
                .module
                .bindings
                .iter()
                .all(|binding| binding.type_params.is_empty())
        );

        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_first_1_true_from_apply_constraints() {
        let module = runtime_module_from_source_without_std("my first x y = x\nfirst 1 true\n");

        let output = finalize_module(module).unwrap();
        let solution = &output.report.root_graph_solutions[0];
        assert_eq!(
            solution.result_type,
            RuntimeType::Core(typed_ir::Type::Named {
                path: path("int"),
                args: Vec::new(),
            })
        );
        assert!(
            output
                .module
                .bindings
                .iter()
                .all(|binding| binding.type_params.is_empty())
        );

        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_twice_id_1() {
        let module = runtime_module_from_source_without_std(
            "my id x = x\nmy twice f x = f (f x)\ntwice id 1\n",
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "1".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_flip_pair_1_2() {
        let module = runtime_module_from_source_without_std(
            "my pair x y = (x, y)\nmy flip f x y = f y x\nflip pair 1 2\n",
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Tuple(vec![
                yulang_vm::VmValue::Int("2".into()),
                yulang_vm::VmValue::Int("1".into()),
            ]))]
        );
    }

    #[test]
    #[ignore = "requires a prewarmed project compiled dependency cache"]
    fn prewarmed_std_runtime_ir_cache_can_enter_runtime_finalize() {
        let cache_start = std::time::Instant::now();
        let cached =
            runtime_module_from_source_with_prewarmed_std_cache_large_stack("\"hello\".println\n");
        let cache_read = cache_start.elapsed();

        assert!(cached.dependency_cache_hit);
        assert!(!cached.dependency_manifests.is_empty());

        let finalize_start = std::time::Instant::now();
        let output = finalize_module(cached.module).unwrap();
        let finalize = finalize_start.elapsed();
        eprintln!(
            "prewarmed std runtime-ir finalize profile: cache_read={:?} finalize={:?}",
            cache_read, finalize
        );

        assert_eq!(output.module.root_exprs.len(), 1);
    }

    #[test]
    #[ignore = "requires a prewarmed project compiled dependency cache"]
    fn prewarmed_std_finalize_runs_ref_scalar_assignment() {
        let results = finalized_values_from_prewarmed_std_cache(
            r#"{
    my $x = 10
    &x = 11
    $x
}
"#,
        );

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "11".into()
            ))]
        );
    }

    #[test]
    #[ignore = "requires a prewarmed project compiled dependency cache"]
    fn prewarmed_std_finalize_compiles_ref_assignment_from_ref_read() {
        assert_prewarmed_std_ref_source_finalizes_to_vm_input(
            r#"{
    my $x = 13
    my $y = 0

    &y = $x

    $y
}
"#,
        );
    }

    #[test]
    #[ignore = "requires a prewarmed project compiled dependency cache"]
    fn prewarmed_std_finalize_runs_ref_assignment_inside_nested_block() {
        let results = finalized_values_from_prewarmed_std_cache(
            r#"{
    my $x = 0
    {
        &x = 9
    }
    $x
}
"#,
        );

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "9".into()
            ))]
        );
    }

    fn finalized_values_from_prewarmed_std_cache(src: &str) -> Vec<yulang_vm::VmResult> {
        let cached = runtime_module_from_source_with_prewarmed_std_cache_large_stack(src);
        let output = finalize_module(cached.module).unwrap();
        assert!(
            output
                .module
                .bindings
                .iter()
                .all(|binding| binding.type_params.is_empty())
        );
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        vm.eval_roots().unwrap()
    }

    fn assert_prewarmed_std_ref_source_finalizes_to_vm_input(src: &str) {
        let cached = runtime_module_from_source_with_prewarmed_std_cache_large_stack(src);
        let output = finalize_module(cached.module).unwrap();
        assert!(
            output
                .module
                .bindings
                .iter()
                .all(|binding| binding.type_params.is_empty())
        );
        yulang_vm::compile_vm_module(output.module).unwrap();
    }

    fn id_call(arg: Expr) -> Expr {
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(path("id")), RuntimeType::Unknown)),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::Unknown,
        )
    }

    fn simple_apply_callee_path(expr: &Expr) -> Option<typed_ir::Path> {
        let ExprKind::Apply { callee, .. } = &expr.kind else {
            return None;
        };
        let ExprKind::Var(path) = &callee.kind else {
            return None;
        };
        Some(path.clone())
    }

    fn id_binding() -> Binding {
        Binding {
            name: path("id"),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                },
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: typed_ir::Name("x".into()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path("x")),
                        RuntimeType::Core(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    )),
                },
                RuntimeType::Unknown,
            ),
        }
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path("Int"),
            args: Vec::new(),
        }
    }

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path("Bool"),
            args: Vec::new(),
        }
    }

    fn path(name: impl IntoPathArg) -> typed_ir::Path {
        name.into_path()
    }

    trait IntoPathArg {
        fn into_path(self) -> typed_ir::Path;
    }

    impl IntoPathArg for &str {
        fn into_path(self) -> typed_ir::Path {
            typed_ir::Path::from_name(typed_ir::Name(self.into()))
        }
    }

    impl<const N: usize> IntoPathArg for &[&str; N] {
        fn into_path(self) -> typed_ir::Path {
            typed_ir::Path::new(
                self.iter()
                    .map(|segment| typed_ir::Name((*segment).into()))
                    .collect(),
            )
        }
    }

    fn runtime_module_from_source_without_std(src: &str) -> Module {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            src,
            None,
            yulang_infer::SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = yulang_infer::export_core_program(&mut lowered.state);
        yulang_runtime::lower_core_program(program).unwrap()
    }

    fn runtime_module_from_source_with_prewarmed_std_cache_large_stack(
        src: &str,
    ) -> yulang_compile::CachedRuntimeIrModule {
        let src = src.to_string();
        run_with_large_stack(move || {
            let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            let cache_paths = yulang_compile::YulangCachePaths::for_project(&repo_root);
            let std_root = yulang_sources::resolve_or_install_std_root(None, None)
                .expect("resolve installed std root")
                .expect("installed std root should be available");
            let options = yulang_compile::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            };

            yulang_compile::runtime_ir_module_from_virtual_source_with_dependency_cache_read_only(
                &src,
                None,
                options,
                &cache_paths,
            )
            .expect("read prewarmed std compiled dependency cache")
        })
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        std::thread::Builder::new()
            .name("runtime-finalize-large-stack".into())
            .stack_size(128 * 1024 * 1024)
            .spawn(f)
            .expect("spawn large-stack runtime-finalize test thread")
            .join()
            .expect("large-stack runtime-finalize test panicked")
    }

    fn artifact_cache_root(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-finalize-cache-{name}-{}",
            std::process::id()
        ))
    }

    fn compiled_manifest(unit_index: usize, hash: u64) -> CompiledUnitManifest {
        CompiledUnitManifest {
            artifact_format_version: 17,
            parser_format_version: 1,
            unit_index,
            origin: SourceCompilationUnitOrigin::Std,
            realms: Vec::new(),
            bands: Vec::new(),
            files: vec![CompiledSourceFileIdentity {
                path: format!("std/{unit_index}.yu"),
                module_path: path(&["std", "cache_test"]),
                origin: SourceOrigin::Std,
                source_len: 10,
                source_hash: hash,
            }],
            dependencies: (unit_index > 0)
                .then(|| CompiledUnitDependency {
                    unit_index: unit_index - 1,
                    source_hash: hash - 1,
                    interface_hash: hash + 1,
                })
                .into_iter()
                .collect(),
            source_hash: hash,
            syntax_hash: hash + 10,
            interface_hash: hash + 20,
        }
    }
}
