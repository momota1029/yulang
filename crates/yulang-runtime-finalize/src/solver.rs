use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use yulang_runtime_ir::{Binding, Expr, ExprKind, Module, Root, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{
    CachedFinalizeInstance, FinalizeDiagnostic, FinalizeInstanceCache, FinalizeInstanceKey,
    FinalizeMonomorphizeError, FinalizeOutput, FinalizeReport, FinalizeResult, RootGraphInput,
    RootGraphSolution, TypeGraph,
    graph::should_thunk_effect,
    graph::{TypeCastOrder, runtime_type_from_core_value, runtime_type_from_core_value_and_effect},
    materialize_core_type, materialize_runtime_type,
    output::RootGraphRoot,
};

pub fn finalize_module(module: Module) -> FinalizeResult<FinalizeOutput> {
    let mut cache = FinalizeInstanceCache::default();
    finalize_module_with_cache(module, &mut cache)
}

pub fn finalize_monomorphize_module(module: Module) -> Result<Module, FinalizeMonomorphizeError> {
    Ok(finalize_monomorphize_module_with_report(module)?.module)
}

pub fn finalize_monomorphize_module_with_report(
    module: Module,
) -> Result<FinalizeOutput, FinalizeMonomorphizeError> {
    let output = finalize_module(module)?;
    validate_monomorphized_output(&output.module)?;
    Ok(output)
}

fn validate_monomorphized_output(module: &Module) -> Result<(), yulang_runtime::RuntimeError> {
    yulang_runtime::check_runtime_invariants(module, yulang_runtime::RuntimeStage::Monomorphized)?;
    yulang_runtime::validate_module(module)
}

pub fn finalize_module_with_cache(
    mut module: Module,
    cache: &mut FinalizeInstanceCache,
) -> FinalizeResult<FinalizeOutput> {
    let root_graph_inputs = collect_root_graph_inputs(&module);
    rewrite_root_role_method_calls(&mut module);
    let cast_order = type_cast_order(&module.role_impls);
    let mut root_graph_solutions = solve_root_graphs(&module, &cast_order)?;
    let mut scanned_binding_bodies = HashSet::new();
    let mut applied_solution_count = 0;
    loop {
        canonicalize_aliases(&mut root_graph_solutions);
        let emitted = append_monomorphic_bindings(&mut module, &root_graph_solutions, cache)?;
        let unapplied_solutions = &root_graph_solutions[applied_solution_count..];
        rewrite_root_exprs(&mut module, unapplied_solutions)?;
        rewrite_binding_exprs(&mut module, unapplied_solutions)?;
        applied_solution_count = root_graph_solutions.len();
        let role_rewrites = rewrite_role_method_calls(&mut module);

        let solution_count = root_graph_solutions.len();
        collect_root_expr_graphs(&module, &cast_order, &mut root_graph_solutions)?;
        let scan_targets =
            next_binding_body_scan_targets(&module, &emitted, &mut scanned_binding_bodies);
        collect_binding_body_graphs(
            &module,
            &scan_targets,
            &cast_order,
            &mut root_graph_solutions,
        )?;
        if emitted.is_empty()
            && scan_targets.is_empty()
            && !role_rewrites
            && root_graph_solutions.len() == solution_count
        {
            break;
        }
    }
    prune_specialized_polymorphic_bindings(&mut module, &root_graph_solutions);
    prune_unbound_binding_roots(&mut module);
    monomorphize_phantom_nullary_variant_bindings(&mut module);
    normalize_materialized_module(&mut module);
    normalize_semantic_cast_coercions(&mut module);
    // Fill local Var types first (using enclosing-binder scope), so the apply
    // evidence pass sees concrete arg/callee types when reconciling.
    fill_local_var_types(&mut module);
    fill_apply_evidence_types(&mut module);
    // Run scope walk again — apply reconciliation may have concretized
    // pattern/handler types that earlier scope walk skipped.
    fill_local_var_types(&mut module);
    Ok(FinalizeOutput {
        module,
        report: FinalizeReport {
            root_graph_inputs,
            root_graph_solutions,
            cache_profile: cache.profile(),
        },
    })
}

fn normalize_materialized_module(module: &mut Module) {
    let substitutions = [];
    let reachable = reachable_paths(module);
    for binding in &mut module.bindings {
        if reachable.contains(&binding.name) {
            materialize_expr_in_place(&mut binding.body, &substitutions);
        }
    }
    for expr in &mut module.root_exprs {
        materialize_expr_in_place(expr, &substitutions);
    }
}

fn normalize_semantic_cast_coercions(module: &mut Module) {
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
                .map(|field| yulang_runtime_ir::RecordExprField {
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
    stmt: yulang_runtime_ir::Stmt,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::Stmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: normalize_semantic_cast_pattern(pattern, role_impls),
            value: normalize_semantic_cast_expr(value, role_impls),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(normalize_semantic_cast_expr(expr, role_impls))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: normalize_semantic_cast_expr(body, role_impls),
        },
    }
}

fn normalize_semantic_cast_match_arm(
    arm: yulang_runtime_ir::MatchArm,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::MatchArm {
    yulang_runtime_ir::MatchArm {
        pattern: normalize_semantic_cast_pattern(arm.pattern, role_impls),
        guard: arm
            .guard
            .map(|guard| normalize_semantic_cast_expr(guard, role_impls)),
        body: normalize_semantic_cast_expr(arm.body, role_impls),
    }
}

fn normalize_semantic_cast_handle_arm(
    arm: yulang_runtime_ir::HandleArm,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::HandleArm {
    yulang_runtime_ir::HandleArm {
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
    pattern: yulang_runtime_ir::Pattern,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::Pattern {
    use yulang_runtime_ir::Pattern;

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
                .map(|field| yulang_runtime_ir::RecordPatternField {
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
    spread: yulang_runtime_ir::RecordSpreadExpr,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::RecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(normalize_semantic_cast_expr(
                *expr, role_impls,
            )))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(normalize_semantic_cast_expr(
                *expr, role_impls,
            )))
        }
    }
}

fn normalize_semantic_cast_record_pattern_spread(
    spread: yulang_runtime_ir::RecordSpreadPattern,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> yulang_runtime_ir::RecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(normalize_semantic_cast_pattern(
                *pattern, role_impls,
            )))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(normalize_semantic_cast_pattern(
                *pattern, role_impls,
            )))
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
            RuntimeType::core(step.from.clone()),
            RuntimeType::core(step.to.clone()),
        );
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(step.method), callee_ty)),
                arg: Box::new(value),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::core(step.to),
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
            let from = role_impl.inputs.first().and_then(type_from_bounds)?;
            let to = role_impl
                .associated_types
                .iter()
                .find(|associated| associated.name.0 == "to")
                .and_then(|associated| type_from_bounds(&associated.value))?;
            let method = role_impl
                .members
                .iter()
                .find(|member| member.name.0 == "cast")
                .map(|member| member.value.clone())?;
            Some(SemanticCastStep { method, from, to })
        })
        .collect()
}

fn type_cast_order(role_impls: &[typed_ir::RoleImplGraphNode]) -> TypeCastOrder {
    TypeCastOrder::from_edges(
        semantic_cast_edges(role_impls)
            .into_iter()
            .map(|step| (step.from, step.to))
            .collect(),
    )
}

fn precise_coerce_actual_type(expr: &Expr, fallback: &typed_ir::Type) -> typed_ir::Type {
    let actual = runtime_type_to_core(expr.ty.clone());
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
    ) || !core_type_is_closed(ty)
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
    core_subtype_match_score(left, right).is_some()
        && core_subtype_match_score(right, left).is_some()
}

fn monomorphize_phantom_nullary_variant_bindings(module: &mut Module) {
    for binding in &mut module.bindings {
        if binding.type_params.is_empty() || !is_phantom_nullary_variant_binding(binding) {
            continue;
        }
        let substitutions = binding
            .type_params
            .iter()
            .map(|var| typed_ir::TypeSubstitution {
                var: var.clone(),
                ty: typed_ir::Type::Never,
            })
            .collect::<Vec<_>>();
        binding.scheme.body = materialize_core_type(binding.scheme.body.clone(), &substitutions);
        materialize_expr_in_place(&mut binding.body, &substitutions);
        binding.type_params.clear();
    }
}

fn is_phantom_nullary_variant_binding(binding: &Binding) -> bool {
    let ExprKind::Coerce { from, to, expr } = &binding.body.kind else {
        return false;
    };
    if !type_mentions_any_var(to, &binding.type_params) {
        return false;
    }
    let typed_ir::Type::Variant(variant) = from else {
        return false;
    };
    if !variant.cases.iter().all(|case| case.payloads.is_empty()) {
        return false;
    }
    let ExprKind::Variant { value: None, .. } = &expr.kind else {
        return false;
    };
    true
}

fn type_mentions_any_var(ty: &typed_ir::Type, vars: &[typed_ir::TypeVar]) -> bool {
    match ty {
        typed_ir::Type::Var(var) => vars.iter().any(|candidate| candidate == var),
        typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            typed_ir::TypeArg::Type(ty) => type_mentions_any_var(ty, vars),
            typed_ir::TypeArg::Bounds(bounds) => {
                bounds
                    .lower
                    .as_deref()
                    .is_some_and(|ty| type_mentions_any_var(ty, vars))
                    || bounds
                        .upper
                        .as_deref()
                        .is_some_and(|ty| type_mentions_any_var(ty, vars))
            }
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_mentions_any_var(param, vars)
                || type_mentions_any_var(param_effect, vars)
                || type_mentions_any_var(ret_effect, vars)
                || type_mentions_any_var(ret, vars)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            items.iter().any(|item| type_mentions_any_var(item, vars))
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(|item| type_mentions_any_var(item, vars))
                || type_mentions_any_var(tail, vars)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_mentions_any_var(&field.value, vars))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_mentions_any_var(ty, vars)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|ty| type_mentions_any_var(ty, vars))
            }) || variant
                .tail
                .as_deref()
                .is_some_and(|tail| type_mentions_any_var(tail, vars))
        }
        typed_ir::Type::Recursive { body, .. } => type_mentions_any_var(body, vars),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

/// Post-pass that fills `Unknown` slots in `Apply{ callee: EffectOp(..) }`
/// nodes (and the EffectOp callee itself) using the apply's evidence.
///
/// At lowering time the runtime IR records each EffectOp's `.ty` with the
/// operation's signature template, but the operation's payload type variable
/// is sometimes left as `Unknown` instead of as a `Type::Var` that the
/// finalize substitutions could resolve. The Apply's `ApplyEvidence` carries
/// the inferred callee bounds (with type variables that map cleanly to the
/// surrounding binding's substitutions), so we can recover the full
/// operation signature here.
fn fill_apply_evidence_types(module: &mut Module) {
    for binding in &mut module.bindings {
        fill_apply_evidence_in(&mut binding.body);
    }
    for expr in &mut module.root_exprs {
        fill_apply_evidence_in(expr);
    }
}

fn fill_apply_evidence_in(expr: &mut Expr) {
    // Two-direction propagation:
    // 1. Reconcile this node with whatever we know from the outside (the
    //    apply.ty may have been pushed down by an enclosing context).
    // 2. Recurse into children so they pull what they can from the now-better
    //    sibling slots and propagate concrete types up from the leaves.
    // 3. Reconcile again so the parent picks up anything the children
    //    concretized that the first pass couldn't see.
    reconcile_node(expr);
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            fill_apply_evidence_in(callee);
            fill_apply_evidence_in(arg);
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. } => fill_apply_evidence_in(body),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            fill_apply_evidence_in(cond);
            fill_apply_evidence_in(then_branch);
            fill_apply_evidence_in(else_branch);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                fill_apply_evidence_in(item);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                fill_apply_evidence_in(&mut field.value);
            }
            if let Some(spread) = spread {
                let e = match spread {
                    yulang_runtime_ir::RecordSpreadExpr::Head(e)
                    | yulang_runtime_ir::RecordSpreadExpr::Tail(e) => e,
                };
                fill_apply_evidence_in(e);
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                fill_apply_evidence_in(value);
            }
        }
        ExprKind::Select { base, .. } => fill_apply_evidence_in(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            fill_apply_evidence_in(scrutinee);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    fill_apply_evidence_in(guard);
                }
                fill_apply_evidence_in(&mut arm.body);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    yulang_runtime_ir::Stmt::Let { value, .. } => fill_apply_evidence_in(value),
                    yulang_runtime_ir::Stmt::Expr(e) => fill_apply_evidence_in(e),
                    yulang_runtime_ir::Stmt::Module { body, .. } => fill_apply_evidence_in(body),
                }
            }
            if let Some(tail) = tail {
                fill_apply_evidence_in(tail);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            fill_apply_evidence_in(body);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    fill_apply_evidence_in(guard);
                }
                fill_apply_evidence_in(&mut arm.body);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }

    reconcile_node(expr);
}

fn reconcile_node(expr: &mut Expr) {
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            reconcile_apply_triple(&mut callee.ty, &mut arg.ty, &mut expr.ty);
        }
        ExprKind::BindHere { expr: body } => {
            // BindHere forces a Thunk[E, T] and produces T. Pull T up when the
            // body's Thunk value is concrete.
            if runtime_type_has_unknown(&expr.ty)
                && let RuntimeType::Thunk { value, .. } = &body.ty
                && !runtime_type_has_unknown(value)
            {
                expr.ty = (**value).clone();
            }
            // Conversely, if the bind's outer ty is known but the body's
            // Thunk value is Unknown, push the outer type down into the body.
            if !runtime_type_has_unknown(&expr.ty)
                && let RuntimeType::Thunk { effect, value } = &body.ty
                && runtime_type_has_unknown(value)
            {
                let merged =
                    merge_partial_runtime_type(value, &expr.ty).unwrap_or_else(|| expr.ty.clone());
                body.ty = RuntimeType::Thunk {
                    effect: effect.clone(),
                    value: Box::new(merged),
                };
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr: body,
        } => {
            // Thunk wraps body into Thunk[effect, value]. Cross-fill value
            // from the body's .ty.
            if runtime_type_has_unknown(value) && !runtime_type_has_unknown(&body.ty) {
                *value = body.ty.clone();
            }
            // Update the Thunk expr's own .ty to match.
            if runtime_type_has_unknown(&expr.ty) {
                expr.ty = RuntimeType::Thunk {
                    effect: effect.clone(),
                    value: Box::new(value.clone()),
                };
            }
        }
        ExprKind::Lambda { body, .. } => {
            // Pull the body's type into the lambda's ret slot if the lambda
            // ty is Fun and its ret is Unknown.
            if let RuntimeType::Fun { ret, .. } = &mut expr.ty
                && runtime_type_has_unknown(ret)
                && !runtime_type_has_unknown(&body.ty)
            {
                **ret = body.ty.clone();
            }
        }
        ExprKind::Block { tail, .. } => {
            if let Some(tail) = tail
                && runtime_type_has_unknown(&expr.ty)
                && !runtime_type_has_unknown(&tail.ty)
            {
                expr.ty = tail.ty.clone();
            }
        }
        _ => {}
    }
}

/// Cross-fill the three known type slots of an `Apply` node:
/// `callee : Fun{ param, ret }`, `arg : param`, `apply.ty : ret`.
///
/// Each slot may carry partial `Unknown` after materialization (especially for
/// `EffectOp` callees, whose stored signature template often leaves the
/// payload type variable as `Unknown` instead of as a substitutable
/// `Type::Var`). When two of the three sides are concrete, the third can be
/// derived deterministically. We repeat the propagation until nothing
/// changes, so partial information on either side gets pulled across.
fn reconcile_apply_triple(
    callee_ty: &mut RuntimeType,
    arg_ty: &mut RuntimeType,
    apply_ty: &mut RuntimeType,
) {
    loop {
        let mut changed = false;

        if let Some((param, ret)) = runtime_fun_split(callee_ty) {
            if runtime_type_has_unknown(arg_ty) && !runtime_type_has_unknown(&param) {
                *arg_ty = param.clone();
                changed = true;
            }
            if runtime_type_has_unknown(apply_ty) && !runtime_type_has_unknown(&ret) {
                *apply_ty = ret.clone();
                changed = true;
            }
        }

        if runtime_type_has_unknown(callee_ty)
            && !runtime_type_has_unknown(arg_ty)
            && !runtime_type_has_unknown(apply_ty)
        {
            let new_callee = RuntimeType::Fun {
                param: Box::new(arg_ty.clone()),
                ret: Box::new(apply_ty.clone()),
            };
            if !runtime_types_equivalent(callee_ty, &new_callee) {
                *callee_ty = new_callee;
                changed = true;
            }
        }

        if let Some((param, ret)) = runtime_fun_split(callee_ty) {
            let merged_param = merge_partial_runtime_type(&param, arg_ty);
            if let Some(merged) = merged_param {
                if !runtime_types_equivalent(arg_ty, &merged) {
                    *arg_ty = merged.clone();
                    changed = true;
                }
                if !runtime_types_equivalent(&param, &merged) {
                    rewrite_fun_param(callee_ty, merged);
                    changed = true;
                }
            }
            let merged_ret = merge_partial_runtime_type(&ret, apply_ty);
            if let Some(merged) = merged_ret {
                if !runtime_types_equivalent(apply_ty, &merged) {
                    *apply_ty = merged.clone();
                    changed = true;
                }
                if !runtime_types_equivalent(&ret, &merged) {
                    rewrite_fun_ret(callee_ty, merged);
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }
}

fn runtime_fun_split(ty: &RuntimeType) -> Option<(RuntimeType, RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Some(((**param).clone(), (**ret).clone())),
        _ => None,
    }
}

fn rewrite_fun_param(ty: &mut RuntimeType, new_param: RuntimeType) {
    if let RuntimeType::Fun { param, .. } = ty {
        *param = Box::new(new_param);
    }
}

fn rewrite_fun_ret(ty: &mut RuntimeType, new_ret: RuntimeType) {
    if let RuntimeType::Fun { ret, .. } = ty {
        *ret = Box::new(new_ret);
    }
}

fn runtime_types_equivalent(left: &RuntimeType, right: &RuntimeType) -> bool {
    left == right
}

/// Merge two runtime-type views of the same logical type, preferring the
/// concrete-ist of the two at each tree position. Returns `None` if the
/// shapes diverge in a way we can't bridge.
fn merge_partial_runtime_type(a: &RuntimeType, b: &RuntimeType) -> Option<RuntimeType> {
    match (a, b) {
        (RuntimeType::Unknown, _) => Some(b.clone()),
        (_, RuntimeType::Unknown) => Some(a.clone()),
        (RuntimeType::Core(ax), RuntimeType::Core(bx)) => {
            Some(RuntimeType::Core(merge_partial_core_type(ax, bx)?))
        }
        (RuntimeType::Fun { param: ap, ret: ar }, RuntimeType::Fun { param: bp, ret: br }) => {
            Some(RuntimeType::Fun {
                param: Box::new(merge_partial_runtime_type(ap, bp)?),
                ret: Box::new(merge_partial_runtime_type(ar, br)?),
            })
        }
        (
            RuntimeType::Thunk {
                effect: ae,
                value: av,
            },
            RuntimeType::Thunk {
                effect: be,
                value: bv,
            },
        ) => Some(RuntimeType::Thunk {
            effect: merge_partial_core_type(ae, be)?,
            value: Box::new(merge_partial_runtime_type(av, bv)?),
        }),
        // Bridging Core <-> Fun / Thunk: if one side is Core(typed_ir::Fun)
        // and the other is RuntimeType::Fun, prefer the Fun form (Thunk-aware)
        // when it carries strictly more structure.
        (RuntimeType::Fun { .. }, RuntimeType::Core(typed_ir::Type::Fun { .. })) => Some(a.clone()),
        (RuntimeType::Core(typed_ir::Type::Fun { .. }), RuntimeType::Fun { .. }) => Some(b.clone()),
        (RuntimeType::Thunk { .. }, RuntimeType::Core(_)) => Some(a.clone()),
        (RuntimeType::Core(_), RuntimeType::Thunk { .. }) => Some(b.clone()),
        _ => None,
    }
}

fn merge_partial_core_type(a: &typed_ir::Type, b: &typed_ir::Type) -> Option<typed_ir::Type> {
    match (a, b) {
        (typed_ir::Type::Unknown, _) => Some(b.clone()),
        (_, typed_ir::Type::Unknown) => Some(a.clone()),
        (left, right) if left == right => Some(left.clone()),
        _ => None,
    }
}

fn runtime_type_has_unknown(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_has_unknown(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_has_unknown(param) || runtime_type_has_unknown(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_has_unknown(effect) || runtime_type_has_unknown(value)
        }
    }
}

fn core_type_has_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Var(_) | typed_ir::Type::Never | typed_ir::Type::Any => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            typed_ir::TypeArg::Type(t) => core_type_has_unknown(t),
            typed_ir::TypeArg::Bounds(b) => {
                b.lower.as_deref().is_some_and(core_type_has_unknown)
                    || b.upper.as_deref().is_some_and(core_type_has_unknown)
            }
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_has_unknown(param)
                || core_type_has_unknown(param_effect)
                || core_type_has_unknown(ret_effect)
                || core_type_has_unknown(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(core_type_has_unknown),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_has_unknown) || core_type_has_unknown(tail)
        }
        typed_ir::Type::Record(record) => record
            .fields
            .iter()
            .any(|f| core_type_has_unknown(&f.value)),
        typed_ir::Type::Variant(variant) => variant
            .cases
            .iter()
            .any(|c| c.payloads.iter().any(core_type_has_unknown)),
        typed_ir::Type::Recursive { body, .. } => core_type_has_unknown(body),
    }
}

/// Scope-aware post-pass that fills `Unknown` `Var.ty` slots whose binding
/// type is recoverable from the enclosing Lambda/Pattern/Handle arm.
///
/// The lowering pipeline sometimes records a local `Var` reference with
/// `.ty = Unknown` even when the surrounding binder carries a concrete type
/// after monomorphization. We do not have a Var-table at materialize time,
/// so we walk the finalized module here with a flat name -> RuntimeType
/// scope (hygiene guarantees no shadowing collisions) and patch
/// `Var.ty == Unknown` references.
fn fill_local_var_types(module: &mut Module) {
    let bindings: HashMap<typed_ir::Path, RuntimeType> = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.body.ty.clone()))
        .collect();
    for binding in &mut module.bindings {
        let mut scope = HashMap::new();
        fill_local_var_types_in(&mut binding.body, &mut scope, &bindings);
    }
    for expr in &mut module.root_exprs {
        let mut scope = HashMap::new();
        fill_local_var_types_in(expr, &mut scope, &bindings);
    }
}

fn fill_local_var_types_in(
    expr: &mut Expr,
    scope: &mut HashMap<typed_ir::Path, RuntimeType>,
    bindings: &HashMap<typed_ir::Path, RuntimeType>,
) {
    match &mut expr.kind {
        ExprKind::Var(path) => {
            if runtime_type_has_unknown(&expr.ty)
                && let Some(known) = scope
                    .get(path)
                    .or_else(|| bindings.get(path))
                    .filter(|known| !runtime_type_has_unknown(known))
            {
                expr.ty = known.clone();
            }
        }
        ExprKind::Lambda { param, body, .. } => {
            let param_path = path_from_name(param);
            let param_ty = if let RuntimeType::Fun { param, .. } = &expr.ty {
                Some((**param).clone())
            } else {
                None
            };
            let prev = scope.remove(&param_path);
            if let Some(pty) = param_ty {
                scope.insert(param_path.clone(), pty);
            }
            fill_local_var_types_in(body, scope, bindings);
            scope.remove(&param_path);
            if let Some(p) = prev {
                scope.insert(param_path, p);
            }
        }
        ExprKind::Apply { callee, arg, .. } => {
            fill_local_var_types_in(callee, scope, bindings);
            fill_local_var_types_in(arg, scope, bindings);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            fill_local_var_types_in(cond, scope, bindings);
            fill_local_var_types_in(then_branch, scope, bindings);
            fill_local_var_types_in(else_branch, scope, bindings);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                fill_local_var_types_in(item, scope, bindings);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                fill_local_var_types_in(&mut field.value, scope, bindings);
            }
            if let Some(spread) = spread {
                let e = match spread {
                    yulang_runtime_ir::RecordSpreadExpr::Head(e)
                    | yulang_runtime_ir::RecordSpreadExpr::Tail(e) => e,
                };
                fill_local_var_types_in(e, scope, bindings);
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                fill_local_var_types_in(value, scope, bindings);
            }
        }
        ExprKind::Select { base, .. } => fill_local_var_types_in(base, scope, bindings),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            fill_local_var_types_in(scrutinee, scope, bindings);
            for arm in arms {
                let added = collect_pattern_scope_bindings(&arm.pattern, scope);
                if let Some(guard) = &mut arm.guard {
                    fill_local_var_types_in(guard, scope, bindings);
                }
                fill_local_var_types_in(&mut arm.body, scope, bindings);
                for path in added {
                    scope.remove(&path);
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut added = Vec::new();
            for stmt in stmts.iter_mut() {
                match stmt {
                    yulang_runtime_ir::Stmt::Let { pattern, value } => {
                        fill_local_var_types_in(value, scope, bindings);
                        added.extend(collect_pattern_scope_bindings(pattern, scope));
                    }
                    yulang_runtime_ir::Stmt::Expr(e) => {
                        fill_local_var_types_in(e, scope, bindings);
                    }
                    yulang_runtime_ir::Stmt::Module { body, .. } => {
                        fill_local_var_types_in(body, scope, bindings);
                    }
                }
            }
            if let Some(tail) = tail {
                fill_local_var_types_in(tail, scope, bindings);
            }
            for path in added {
                scope.remove(&path);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            fill_local_var_types_in(body, scope, bindings);
            for arm in arms {
                let mut added = collect_pattern_scope_bindings(&arm.payload, scope);
                if let Some(resume) = &arm.resume {
                    let resume_path = path_from_name(&resume.name);
                    if !runtime_type_has_unknown(&resume.ty) {
                        scope.insert(resume_path.clone(), resume.ty.clone());
                        added.push(resume_path);
                    }
                }
                if let Some(guard) = &mut arm.guard {
                    fill_local_var_types_in(guard, scope, bindings);
                }
                fill_local_var_types_in(&mut arm.body, scope, bindings);
                for path in added {
                    scope.remove(&path);
                }
            }
        }
        ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. } => {
            fill_local_var_types_in(body, scope, bindings);
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_pattern_scope_bindings(
    pattern: &yulang_runtime_ir::Pattern,
    scope: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> Vec<typed_ir::Path> {
    use yulang_runtime_ir::Pattern;
    let mut added = Vec::new();
    match pattern {
        Pattern::Bind { name, ty } => {
            if !runtime_type_has_unknown(ty) {
                let path = path_from_name(name);
                scope.insert(path.clone(), ty.clone());
                added.push(path);
            }
        }
        Pattern::As { pattern, name, ty } => {
            if !runtime_type_has_unknown(ty) {
                let path = path_from_name(name);
                scope.insert(path.clone(), ty.clone());
                added.push(path);
            }
            added.extend(collect_pattern_scope_bindings(pattern, scope));
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                added.extend(collect_pattern_scope_bindings(item, scope));
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix.iter()) {
                added.extend(collect_pattern_scope_bindings(item, scope));
            }
            if let Some(spread) = spread {
                added.extend(collect_pattern_scope_bindings(spread, scope));
            }
        }
        Pattern::Record { fields, .. } => {
            for field in fields {
                added.extend(collect_pattern_scope_bindings(&field.pattern, scope));
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                added.extend(collect_pattern_scope_bindings(value, scope));
            }
        }
        Pattern::Or { left, .. } => {
            added.extend(collect_pattern_scope_bindings(left, scope));
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
    added
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

pub fn solve_root_graphs(
    module: &Module,
    cast_order: &TypeCastOrder,
) -> FinalizeResult<Vec<RootGraphSolution>> {
    let mut solutions = Vec::new();
    collect_root_expr_graphs(module, cast_order, &mut solutions)?;
    Ok(solutions)
}

fn collect_root_expr_graphs(
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

fn collect_binding_body_graphs(
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

fn next_binding_body_scan_targets(
    module: &Module,
    emitted: &[typed_ir::Path],
    scanned: &mut HashSet<typed_ir::Path>,
) -> Vec<typed_ir::Path> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding.type_params.is_empty()))
        .collect::<HashMap<_, _>>();
    let reachable = reachable_paths(module);
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

fn collect_expr_graphs(
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
            if let Some(param_ty) = runtime_function_param(&expr.ty) {
                scoped_locals.insert(path_from_name(param), param_ty);
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
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.pattern, &mut arm_locals);
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
                collect_pattern_local_types(&arm.payload, &mut arm_locals);
                if let Some(resume) = &arm.resume {
                    arm_locals.insert(path_from_name(&resume.name), resume.ty.clone());
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

fn collect_apply_spine_arg_graphs(
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

fn solve_bare_polymorphic_var(
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
    let expected = runtime_type_to_core(expr_lower_type(expr, local_types));
    if !core_type_is_closed(&expected) {
        return Ok(None);
    }
    solve_value_arg(owner, binding, expected, cast_order, alias_index).map(Some)
}

fn solve_simple_apply(
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
        && !solved.is_complete()
        && close_role_associated_types(&mut graph, binding, &principal, &solved, role_impls)?
    {
        graph.solve()
    } else {
        solved
    };
    if !graph.is_complete() {
        if role_required_apply_waiting_for_arguments(binding, &spine, local_types) {
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
    let callee_type = solved_callee_runtime_type(binding, &principal, &graph);
    let callee_type = restore_apply_spine_arg_effects(callee_type, &spine.steps, local_types);
    let callee_type =
        refine_runtime_spine_return(callee_type, spine.steps.len(), result_type.clone());
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

fn solve_monomorphic_contextual_apply(
    owner: RootGraphRoot,
    expr: &Expr,
    binding_path: &typed_ir::Path,
    binding: &Binding,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    alias_index: usize,
) -> Option<RootGraphSolution> {
    if !binding_handles_first_param(binding) {
        return None;
    }
    let base_callee_type = binding.body.ty.clone();
    let callee_type =
        restore_apply_spine_arg_effects(base_callee_type.clone(), &spine.steps, local_types);
    if callee_type == base_callee_type || !runtime_type_is_closed(&callee_type) {
        return None;
    }
    let result_type = expr_lower_type(expr, local_types);
    let result_type = if runtime_type_is_closed(&result_type) {
        result_type
    } else {
        runtime_spine_return(&callee_type, spine.steps.len())?
    };
    let callee_type =
        refine_runtime_spine_return(callee_type, spine.steps.len(), result_type.clone());
    Some(RootGraphSolution {
        root: owner,
        occurrence: alias_index,
        binding: binding_path.clone(),
        alias: alias_path(binding_path, alias_index),
        callee_type,
        result_type,
        graph: crate::GraphSolution {
            type_vars: Vec::new(),
        },
        type_substitutions: Vec::new(),
    })
}

fn binding_handles_first_param(binding: &Binding) -> bool {
    let ExprKind::Lambda { param, body, .. } = &binding.body.kind else {
        return false;
    };
    let param_path = path_from_name(param);
    expr_handles_path(body, &param_path)
}

fn expr_handles_path(expr: &Expr, path: &typed_ir::Path) -> bool {
    match &expr.kind {
        ExprKind::Handle { body, arms, .. } => {
            expr_references_path(body, path)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_handles_path(guard, path))
                        || expr_handles_path(&arm.body, path)
                })
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Thunk { expr: body, .. } => expr_handles_path(body, path),
        ExprKind::Apply { callee, arg, .. } => {
            expr_handles_path(callee, path) || expr_handles_path(arg, path)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_handles_path(cond, path)
                || expr_handles_path(then_branch, path)
                || expr_handles_path(else_branch, path)
        }
        ExprKind::Tuple(items) => items.iter().any(|item| expr_handles_path(item, path)),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_handles_path(&field.value, path))
                || spread
                    .as_ref()
                    .is_some_and(|spread| record_spread_expr_handles_path(spread, path))
        }
        ExprKind::Variant { value, .. } => value
            .as_ref()
            .is_some_and(|value| expr_handles_path(value, path)),
        ExprKind::Select { base, .. } => expr_handles_path(base, path),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_handles_path(scrutinee, path)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_handles_path(guard, path))
                        || expr_handles_path(&arm.body, path)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| stmt_handles_path(stmt, path))
                || tail
                    .as_ref()
                    .is_some_and(|tail| expr_handles_path(tail, path))
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}

fn expr_references_path(expr: &Expr, path: &typed_ir::Path) -> bool {
    let mut paths = Vec::new();
    collect_expr_paths(expr, &mut paths);
    paths.iter().any(|candidate| candidate == path)
}

fn record_spread_expr_handles_path(
    spread: &yulang_runtime_ir::RecordSpreadExpr,
    path: &typed_ir::Path,
) -> bool {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => expr_handles_path(expr, path),
    }
}

fn stmt_handles_path(stmt: &yulang_runtime_ir::Stmt, path: &typed_ir::Path) -> bool {
    match stmt {
        yulang_runtime_ir::Stmt::Let { value, .. }
        | yulang_runtime_ir::Stmt::Expr(value)
        | yulang_runtime_ir::Stmt::Module { body: value, .. } => expr_handles_path(value, path),
    }
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
        runtime_type_from_core_value(graph.materialize_core(result))
    }
}

fn solved_callee_runtime_type(
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
    if runtime_type_is_closed(&materialized) {
        restore_runtime_effect_boundaries(materialized, &principal_runtime)
    } else {
        principal_runtime
    }
}

fn restore_runtime_effect_boundaries(base: RuntimeType, principal: &RuntimeType) -> RuntimeType {
    match (base, principal) {
        (
            RuntimeType::Fun { param, ret },
            RuntimeType::Fun {
                param: principal_param,
                ret: principal_ret,
            },
        ) => RuntimeType::Fun {
            param: Box::new(restore_runtime_effect_boundaries(*param, principal_param)),
            ret: Box::new(restore_runtime_effect_boundaries(*ret, principal_ret)),
        },
        (
            RuntimeType::Thunk { effect, value },
            RuntimeType::Thunk {
                effect: principal_effect,
                value: principal_value,
            },
        ) => RuntimeType::Thunk {
            effect: if should_thunk_effect(principal_effect) {
                principal_effect.clone()
            } else {
                effect
            },
            value: Box::new(restore_runtime_effect_boundaries(*value, principal_value)),
        },
        (
            base,
            RuntimeType::Thunk {
                effect,
                value: principal_value,
            },
        ) if should_thunk_effect(effect)
            && runtime_effect_boundary_value_matches(&base, principal_value) =>
        {
            RuntimeType::Thunk {
                effect: effect.clone(),
                value: Box::new(restore_runtime_effect_boundaries(base, principal_value)),
            }
        }
        (base, _) => base,
    }
}

fn runtime_effect_boundary_value_matches(base: &RuntimeType, principal: &RuntimeType) -> bool {
    if base == principal {
        return true;
    }
    let base = runtime_type_to_core(base.clone());
    let principal = runtime_type_to_core(principal.clone());
    core_subtype_match_score(&base, &principal).is_some()
        || core_subtype_match_score(&principal, &base).is_some()
}

fn restore_apply_spine_arg_effects(
    callee: RuntimeType,
    steps: &[ApplyStep<'_>],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> RuntimeType {
    let Some((step, rest)) = steps.split_first() else {
        return callee;
    };
    let RuntimeType::Fun { param, ret } = callee else {
        return callee;
    };
    let (arg_value, arg_effect) = step.arg_type_and_effect(local_types);
    let param = restore_apply_arg_effect(*param, arg_value, arg_effect);
    RuntimeType::Fun {
        param: Box::new(param),
        ret: Box::new(restore_apply_spine_arg_effects(*ret, rest, local_types)),
    }
}

fn restore_apply_arg_effect(
    param: RuntimeType,
    arg_value: typed_ir::Type,
    arg_effect: typed_ir::Type,
) -> RuntimeType {
    if !should_thunk_effect(&arg_effect) || matches!(param, RuntimeType::Thunk { .. }) {
        return param;
    }
    let param_value = runtime_type_to_core(param.clone());
    if core_subtype_match_score(&arg_value, &param_value).is_none()
        && core_subtype_match_score(&param_value, &arg_value).is_none()
    {
        return param;
    }
    RuntimeType::Thunk {
        effect: arg_effect,
        value: Box::new(param),
    }
}

fn runtime_spine_return(callee: &RuntimeType, arity: usize) -> Option<RuntimeType> {
    if arity == 0 {
        return Some(callee.clone());
    }
    let RuntimeType::Fun { ret, .. } = callee else {
        return None;
    };
    runtime_spine_return(ret, arity - 1)
}

fn refine_runtime_spine_return(
    callee: RuntimeType,
    arity: usize,
    result_type: RuntimeType,
) -> RuntimeType {
    if arity == 0 {
        return callee;
    }
    let RuntimeType::Fun { param, ret } = callee else {
        return callee;
    };
    let ret = if arity == 1 {
        if runtime_return_needs_result_refinement(&ret) {
            result_type
        } else {
            *ret
        }
    } else {
        refine_runtime_spine_return(*ret, arity - 1, result_type)
    };
    RuntimeType::Fun {
        param,
        ret: Box::new(ret),
    }
}

fn runtime_return_needs_result_refinement(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_contains_non_runtime_choice(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_return_needs_result_refinement(param)
                || runtime_return_needs_result_refinement(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_contains_non_runtime_choice(effect)
                || runtime_return_needs_result_refinement(value)
        }
    }
}

fn core_type_contains_non_runtime_choice(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Union(_) | typed_ir::Type::Inter(_) => true,
        typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            typed_ir::TypeArg::Type(ty) => core_type_contains_non_runtime_choice(ty),
            typed_ir::TypeArg::Bounds(bounds) => {
                bounds
                    .lower
                    .as_deref()
                    .is_some_and(core_type_contains_non_runtime_choice)
                    || bounds
                        .upper
                        .as_deref()
                        .is_some_and(core_type_contains_non_runtime_choice)
            }
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_non_runtime_choice(param)
                || core_type_contains_non_runtime_choice(param_effect)
                || core_type_contains_non_runtime_choice(ret_effect)
                || core_type_contains_non_runtime_choice(ret)
        }
        typed_ir::Type::Tuple(items) => items.iter().any(core_type_contains_non_runtime_choice),
        typed_ir::Type::Record(record) => record
            .fields
            .iter()
            .any(|field| core_type_contains_non_runtime_choice(&field.value)),
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(core_type_contains_non_runtime_choice)
            }) || variant
                .tail
                .as_deref()
                .is_some_and(core_type_contains_non_runtime_choice)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_non_runtime_choice)
                || core_type_contains_non_runtime_choice(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_contains_non_runtime_choice(body),
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
    }
}

fn role_required_apply_waiting_for_arguments(
    binding: &Binding,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> bool {
    !binding.scheme.requirements.is_empty()
        && spine
            .steps
            .iter()
            .any(|step| !core_type_is_closed(&step.arg_type(local_types)))
}

fn close_role_associated_types(
    graph: &mut TypeGraph,
    binding: &Binding,
    principal: &crate::PrincipalInstance,
    solution: &crate::GraphSolution,
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> FinalizeResult<bool> {
    let mut changed = false;
    let principal_renames = principal_rename_substitutions(principal);
    let solution_substitutions = solution.substitutions();
    for requirement in &binding.scheme.requirements {
        // Role method defaults expose associated slots through the requirement,
        // not through the apply spine. Close those slots from the selected impl
        // before deciding that a graph is genuinely incomplete.
        let Some(inputs) = solved_role_requirement_inputs(
            requirement,
            &principal_renames,
            &solution_substitutions,
        ) else {
            continue;
        };
        for arg in &requirement.args {
            let typed_ir::RoleRequirementArg::Associated { name, bounds } = arg else {
                continue;
            };
            let Some(projected) =
                resolve_associated_requirement_from_impls(requirement, name, &inputs, role_impls)
            else {
                continue;
            };
            let target = materialize_type_bounds(bounds.clone(), &principal_renames);
            let Some(target) = type_from_bounds(&target) else {
                continue;
            };
            graph.constrain_subtype(projected.clone(), target.clone())?;
            graph.constrain_subtype(target, projected)?;
            changed = true;
        }
    }
    Ok(changed)
}

fn principal_rename_substitutions(
    principal: &crate::PrincipalInstance,
) -> Vec<typed_ir::TypeSubstitution> {
    principal
        .type_params
        .iter()
        .map(|param| typed_ir::TypeSubstitution {
            var: param.original.clone(),
            ty: typed_ir::Type::Var(param.fresh.clone()),
        })
        .collect()
}

fn solved_role_requirement_inputs(
    requirement: &typed_ir::RoleRequirement,
    principal_renames: &[typed_ir::TypeSubstitution],
    solution_substitutions: &[typed_ir::TypeSubstitution],
) -> Option<Vec<typed_ir::Type>> {
    let mut inputs = Vec::new();
    for arg in &requirement.args {
        let typed_ir::RoleRequirementArg::Input(bounds) = arg else {
            continue;
        };
        let bounds = materialize_type_bounds(bounds.clone(), principal_renames);
        let bounds = materialize_type_bounds(bounds, solution_substitutions);
        let ty = type_from_bounds(&bounds)?;
        if !core_type_is_closed(&ty) {
            return None;
        }
        inputs.push(ty);
    }
    Some(inputs)
}

fn resolve_associated_requirement_from_impls(
    requirement: &typed_ir::RoleRequirement,
    name: &typed_ir::Name,
    inputs: &[typed_ir::Type],
    role_impls: &[typed_ir::RoleImplGraphNode],
) -> Option<typed_ir::Type> {
    let mut resolved = None;
    for role_impl in role_impls.iter().filter(|role_impl| {
        role_impl.role == requirement.role && role_impl.inputs.len() == inputs.len()
    }) {
        let Some(associated) = role_impl
            .associated_types
            .iter()
            .find(|associated| associated.name == *name)
        else {
            continue;
        };
        let Some(candidate) =
            project_role_impl_associated_type(&role_impl.inputs, inputs, &associated.value)
        else {
            continue;
        };
        match &resolved {
            Some(existing) if existing != &candidate => return None,
            Some(_) => {}
            None => resolved = Some(candidate),
        }
    }
    resolved
}

fn project_role_impl_associated_type(
    impl_inputs: &[typed_ir::TypeBounds],
    actual_inputs: &[typed_ir::Type],
    associated: &typed_ir::TypeBounds,
) -> Option<typed_ir::Type> {
    let mut impl_vars = BTreeSet::new();
    let templates = impl_inputs
        .iter()
        .map(|bounds| {
            let template = type_from_bounds(bounds)?;
            collect_type_vars(&template, &mut impl_vars);
            Some(template)
        })
        .collect::<Option<Vec<_>>>()?;
    collect_type_bounds_vars(associated, &mut impl_vars);
    let mut substitutions = BTreeMap::new();
    for (template, actual) in templates.iter().zip(actual_inputs) {
        infer_type_substitutions(template, actual, &impl_vars, &mut substitutions);
    }
    let substitution_list = substitution_map_to_list(&substitutions);
    if templates
        .iter()
        .zip(actual_inputs)
        .any(|(template, actual)| {
            materialize_core_type(template.clone(), &substitution_list) != *actual
        })
    {
        return None;
    }
    type_from_bounds(&materialize_type_bounds(
        associated.clone(),
        &substitution_list,
    ))
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

fn infer_type_substitutions(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) {
    infer_type_substitutions_inner(template, actual, params, substitutions, 64);
}

fn infer_type_substitutions_inner(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
) {
    if depth == 0 {
        return;
    }
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
            substitutions
                .entry(var.clone())
                .or_insert_with(|| actual.clone());
        }
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                infer_type_arg_substitutions(
                    template_arg,
                    actual_arg,
                    params,
                    substitutions,
                    depth - 1,
                );
            }
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => {
            infer_type_substitutions_inner(param, actual_param, params, substitutions, depth - 1);
            infer_type_substitutions_inner(
                param_effect,
                actual_param_effect,
                params,
                substitutions,
                depth - 1,
            );
            infer_type_substitutions_inner(
                ret_effect,
                actual_ret_effect,
                params,
                substitutions,
                depth - 1,
            );
            infer_type_substitutions_inner(ret, actual_ret, params, substitutions, depth - 1);
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_type_substitutions_inner(item, actual_item, params, substitutions, depth - 1);
            }
        }
        (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
            for field in &record.fields {
                if let Some(actual_field) = actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                {
                    infer_type_substitutions_inner(
                        &field.value,
                        &actual_field.value,
                        params,
                        substitutions,
                        depth - 1,
                    );
                }
            }
        }
        (typed_ir::Type::Variant(variant), typed_ir::Type::Variant(actual_variant)) => {
            for case in &variant.cases {
                let Some(actual_case) = actual_variant
                    .cases
                    .iter()
                    .find(|actual| actual.name == case.name)
                else {
                    continue;
                };
                if case.payloads.len() != actual_case.payloads.len() {
                    continue;
                }
                for (payload, actual_payload) in case.payloads.iter().zip(&actual_case.payloads) {
                    infer_type_substitutions_inner(
                        payload,
                        actual_payload,
                        params,
                        substitutions,
                        depth - 1,
                    );
                }
            }
        }
        (
            typed_ir::Type::Row { items, tail },
            typed_ir::Type::Row {
                items: actual_items,
                tail: actual_tail,
            },
        ) if items.len() == actual_items.len() => {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_type_substitutions_inner(item, actual_item, params, substitutions, depth - 1);
            }
            infer_type_substitutions_inner(tail, actual_tail, params, substitutions, depth - 1);
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
            for item in items {
                infer_type_substitutions_inner(item, actual, params, substitutions, depth - 1);
            }
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            infer_type_substitutions_inner(body, actual, params, substitutions, depth - 1);
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            infer_type_substitutions_inner(template, body, params, substitutions, depth - 1);
        }
        _ => {}
    }
}

fn infer_type_arg_substitutions(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            infer_type_substitutions_inner(template, actual, params, substitutions, depth);
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            infer_type_bounds_substitutions(template, actual, params, substitutions, depth);
        }
        _ => {}
    }
}

fn infer_type_bounds_substitutions(
    template: &typed_ir::TypeBounds,
    actual: &typed_ir::TypeBounds,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    depth: usize,
) {
    if let (Some(template), Some(actual)) = (template.lower.as_deref(), actual.lower.as_deref()) {
        infer_type_substitutions_inner(template, actual, params, substitutions, depth);
    }
    if let (Some(template), Some(actual)) = (template.upper.as_deref(), actual.upper.as_deref()) {
        infer_type_substitutions_inner(template, actual, params, substitutions, depth);
    }
}

fn substitution_map_to_list(
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> Vec<typed_ir::TypeSubstitution> {
    substitutions
        .iter()
        .map(|(var, ty)| typed_ir::TypeSubstitution {
            var: var.clone(),
            ty: ty.clone(),
        })
        .collect()
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
        RuntimeType::Core(ty) => RuntimeType::Core(apply_callee_lower_core_bound(ty)),
        ty => ty,
    }
}

fn unconstrain_top_param_runtime_bound(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Core(ty) => RuntimeType::Core(unconstrain_top_param_core_bound(ty)),
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

struct ApplySpine<'a> {
    binding: &'a typed_ir::Path,
    callee: &'a Expr,
    steps: Vec<ApplyStep<'a>>,
}

struct ApplyStep<'a> {
    apply: &'a Expr,
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

    fn constrain_result_bounds(
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
                    graph.constrain_subtype(result, runtime_type_to_core((*value).clone()))?;
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
            ty => graph.constrain_subtype(result, runtime_type_to_core(ty)),
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
        let value = runtime_type_to_core(*value);
        let effect = closed_or_empty_effect(effect);
        return Some((value, effect));
    }
    let ExprKind::Apply { evidence, .. } = &expr.kind else {
        return None;
    };
    let evidence = evidence.as_ref()?;
    let value = type_from_bounds(&evidence.result)
        .filter(core_type_is_closed)
        .or_else(|| {
            let value = runtime_type_to_core(expr_lower_type(expr, local_types));
            core_type_is_closed(&value).then_some(value)
        })?;
    let effect = apply_evidence_return_effect(evidence)
        .map(closed_or_empty_effect)
        .unwrap_or(typed_ir::Type::Never);
    Some((value, effect))
}

fn closed_or_empty_effect(effect: typed_ir::Type) -> typed_ir::Type {
    if core_type_is_closed(&effect) {
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
        RuntimeType::Fun { .. } | RuntimeType::Core(typed_ir::Type::Fun { .. }) => true,
        RuntimeType::Thunk { value, .. } => runtime_type_value_is_function(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => false,
    }
}

fn runtime_type_is_never_value(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Core(typed_ir::Type::Never) => true,
        RuntimeType::Thunk { value, .. } => runtime_type_is_never_value(value),
        RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Core(_) => false,
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

fn apply_observed_arg_type(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    type_from_bounds(&evidence.arg)
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
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => collect_expr_graphs(
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
    stmt: &yulang_runtime_ir::Stmt,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => {
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
        yulang_runtime_ir::Stmt::Expr(expr)
        | yulang_runtime_ir::Stmt::Module { body: expr, .. } => collect_expr_graphs(
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
    pattern: &yulang_runtime_ir::Pattern,
    bindings: &HashMap<typed_ir::Path, &Binding>,
    role_impls: &[typed_ir::RoleImplGraphNode],
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    cast_order: &TypeCastOrder,
    solutions: &mut Vec<RootGraphSolution>,
) -> FinalizeResult<()> {
    use yulang_runtime_ir::Pattern;

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
                    yulang_runtime_ir::RecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
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
    if let typed_ir::Type::Fun {
        param: param_ty,
        param_effect,
        ..
    } = &binding.scheme.body
    {
        local_types.insert(
            path_from_name(param),
            runtime_type_from_core_value_and_effect(
                param_ty.as_ref().clone(),
                param_effect.as_ref().clone(),
            ),
        );
    }
    local_types
}

fn expr_lower_type(expr: &Expr, local_types: &HashMap<typed_ir::Path, RuntimeType>) -> RuntimeType {
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

fn runtime_type_to_core(ty: RuntimeType) -> typed_ir::Type {
    runtime_type_to_effected_core(ty).value
}

struct EffectedCoreType {
    value: typed_ir::Type,
    effect: typed_ir::Type,
}

fn runtime_type_to_effected_core(ty: RuntimeType) -> EffectedCoreType {
    match ty {
        RuntimeType::Unknown => EffectedCoreType {
            value: typed_ir::Type::Unknown,
            effect: typed_ir::Type::Unknown,
        },
        RuntimeType::Core(ty) => EffectedCoreType {
            value: ty,
            effect: typed_ir::Type::Never,
        },
        RuntimeType::Fun { param, ret } => {
            let param = runtime_type_to_effected_core(*param);
            let ret = runtime_type_to_effected_core(*ret);
            EffectedCoreType {
                value: typed_ir::Type::Fun {
                    param: Box::new(param.value),
                    param_effect: Box::new(param.effect),
                    ret_effect: Box::new(ret.effect),
                    ret: Box::new(ret.value),
                },
                effect: typed_ir::Type::Never,
            }
        }
        RuntimeType::Thunk { effect, value } => {
            let value = runtime_type_to_core(*value);
            EffectedCoreType { value, effect }
        }
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
            let scheme_body = runtime_type_to_core(solution.callee_type.clone());
            let scheme = typed_ir::Scheme {
                requirements: Vec::new(),
                body: scheme_body,
            };
            let body = materialize_expr_with_expected(
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

fn rewrite_role_method_calls(module: &mut Module) -> bool {
    let candidates = role_method_candidates(module);
    if candidates.is_empty() {
        return false;
    }
    let reachable = reachable_paths(module);
    let mut changed = false;
    for binding in &mut module.bindings {
        if !reachable.contains(&binding.name) {
            continue;
        }
        let mut local_types = binding_local_types(binding);
        changed |= rewrite_role_method_expr(&mut binding.body, &mut local_types, &candidates);
    }
    for expr in &mut module.root_exprs {
        changed |= rewrite_role_method_expr(expr, &mut HashMap::new(), &candidates);
    }
    changed
}

fn rewrite_root_role_method_calls(module: &mut Module) -> bool {
    let candidates = role_method_candidates(module);
    if candidates.is_empty() {
        return false;
    }
    let mut changed = false;
    for expr in &mut module.root_exprs {
        changed |= rewrite_role_method_expr(expr, &mut HashMap::new(), &candidates);
    }
    changed
}

#[derive(Clone)]
struct RoleMethodCandidate {
    role: typed_ir::Path,
    member: typed_ir::Name,
    value: typed_ir::Path,
    inputs: Vec<typed_ir::TypeBounds>,
    callee_type: RuntimeType,
}

fn role_method_candidates(module: &Module) -> Vec<RoleMethodCandidate> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut seen = HashSet::new();
    let mut candidates = Vec::new();
    for role_impl in &module.role_impls {
        for member in &role_impl.members {
            let key = (
                role_impl.role.clone(),
                member.name.clone(),
                member.value.clone(),
            );
            if !seen.insert(key) {
                continue;
            }
            let Some(binding) = bindings.get(&member.value) else {
                continue;
            };
            candidates.push(RoleMethodCandidate {
                role: role_impl.role.clone(),
                member: member.name.clone(),
                value: member.value.clone(),
                inputs: role_impl.inputs.clone(),
                callee_type: runtime_type_from_core_value(binding.scheme.body.clone()),
            });
        }
    }
    candidates
}

fn rewrite_role_method_expr(
    expr: &mut Expr,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> bool {
    let mut changed = false;
    match &mut expr.kind {
        ExprKind::Apply { callee, arg, .. } => {
            changed |= rewrite_role_method_expr(callee, local_types, candidates);
            changed |= rewrite_role_method_expr(arg, local_types, candidates);
        }
        ExprKind::Lambda { param, body, .. } => {
            let previous = runtime_function_param(&expr.ty)
                .map(|param_ty| local_types.insert(path_from_name(param), param_ty));
            changed |= rewrite_role_method_expr(body, local_types, candidates);
            restore_local_type(local_types, path_from_name(param), previous);
        }
        ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. }
        | ExprKind::Select { base: body, .. }
        | ExprKind::Thunk { expr: body, .. } => {
            changed |= rewrite_role_method_expr(body, local_types, candidates);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            changed |= rewrite_role_method_expr(cond, local_types, candidates);
            changed |= rewrite_role_method_expr(then_branch, local_types, candidates);
            changed |= rewrite_role_method_expr(else_branch, local_types, candidates);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                changed |= rewrite_role_method_expr(item, local_types, candidates);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                changed |= rewrite_role_method_expr(&mut field.value, local_types, candidates);
            }
            if let Some(spread) = spread {
                changed |= rewrite_role_method_record_spread(spread, local_types, candidates);
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                changed |= rewrite_role_method_expr(value, local_types, candidates);
            }
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            changed |= rewrite_role_method_expr(scrutinee, local_types, candidates);
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.pattern, &mut arm_locals);
                if let Some(guard) = &mut arm.guard {
                    changed |= rewrite_role_method_expr(guard, &mut arm_locals, candidates);
                }
                changed |= rewrite_role_method_expr(&mut arm.body, &mut arm_locals, candidates);
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut scoped_locals = local_types.clone();
            for stmt in stmts {
                changed |= rewrite_role_method_stmt(stmt, &mut scoped_locals, candidates);
                collect_stmt_local_types(stmt, &mut scoped_locals);
            }
            if let Some(tail) = tail {
                changed |= rewrite_role_method_expr(tail, &mut scoped_locals, candidates);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            changed |= rewrite_role_method_expr(body, local_types, candidates);
            for arm in arms {
                let mut arm_locals = local_types.clone();
                collect_pattern_local_types(&arm.payload, &mut arm_locals);
                if let Some(resume) = &arm.resume {
                    arm_locals.insert(path_from_name(&resume.name), resume.ty.clone());
                }
                if let Some(guard) = &mut arm.guard {
                    changed |= rewrite_role_method_expr(guard, &mut arm_locals, candidates);
                }
                changed |= rewrite_role_method_expr(&mut arm.body, &mut arm_locals, candidates);
            }
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
    if let Some((path, callee_type)) = resolve_role_method_apply(expr, local_types, candidates) {
        replace_apply_spine_binding(expr, &path, &callee_type);
        changed = true;
    }
    changed
}

fn restore_local_type(
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    path: typed_ir::Path,
    previous: Option<Option<RuntimeType>>,
) {
    match previous {
        Some(Some(ty)) => {
            local_types.insert(path, ty);
        }
        Some(None) => {
            local_types.remove(&path);
        }
        None => {}
    }
}

fn rewrite_role_method_record_spread(
    spread: &mut yulang_runtime_ir::RecordSpreadExpr,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> bool {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            rewrite_role_method_expr(expr, local_types, candidates)
        }
    }
}

fn rewrite_role_method_stmt(
    stmt: &mut yulang_runtime_ir::Stmt,
    local_types: &mut HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> bool {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern: _, value } => {
            rewrite_role_method_expr(value, local_types, candidates)
        }
        yulang_runtime_ir::Stmt::Expr(expr)
        | yulang_runtime_ir::Stmt::Module { body: expr, .. } => {
            rewrite_role_method_expr(expr, local_types, candidates)
        }
    }
}

fn resolve_role_method_apply(
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> Option<(typed_ir::Path, RuntimeType)> {
    let spine = ApplySpine::new(expr)?;
    if let Some(resolution) = resolve_role_method_spine(&spine, local_types, candidates) {
        return Some(resolution);
    }
    resolve_impl_method_spine(&spine, local_types, candidates)
}

fn resolve_role_method_spine(
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> Option<(typed_ir::Path, RuntimeType)> {
    let (role, member) = role_method_parts(spine.binding)?;
    let receiver = spine.steps.first()?;
    let receiver_types = role_receiver_types(receiver, local_types);
    let mut best = None;
    let mut ambiguous = false;
    for candidate in candidates
        .iter()
        .filter(|candidate| candidate.role == role && candidate.member == member)
    {
        let Some(score) =
            role_method_candidate_score(candidate, &receiver_types, spine, local_types)
        else {
            continue;
        };
        match best {
            None => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score > best_score => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score == best_score => {
                ambiguous = true;
            }
            Some(_) => {}
        }
    }
    if ambiguous {
        return None;
    }
    best.map(|(_, candidate)| (candidate.value.clone(), candidate.callee_type.clone()))
}

fn resolve_impl_method_spine(
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
    candidates: &[RoleMethodCandidate],
) -> Option<(typed_ir::Path, RuntimeType)> {
    let member = impl_method_member(spine.binding)?;
    let receiver = spine.steps.first()?;
    let receiver_types = role_receiver_types(receiver, local_types);
    let mut best = None;
    let mut ambiguous = false;
    for candidate in candidates
        .iter()
        .filter(|candidate| candidate.member == *member)
    {
        let Some(score) =
            role_method_candidate_score(candidate, &receiver_types, spine, local_types)
        else {
            continue;
        };
        match best {
            None => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score > best_score => {
                best = Some((score, candidate));
                ambiguous = false;
            }
            Some((best_score, _)) if score == best_score => {
                ambiguous = true;
            }
            Some(_) => {}
        }
    }
    if ambiguous {
        return None;
    }
    let (_, candidate) = best?;
    if candidate.value == *spine.binding {
        return None;
    }
    Some((candidate.value.clone(), candidate.callee_type.clone()))
}

fn role_method_parts(path: &typed_ir::Path) -> Option<(typed_ir::Path, typed_ir::Name)> {
    let (member, role) = path.segments.split_last()?;
    if role.is_empty() {
        return None;
    }
    Some((typed_ir::Path::new(role.to_vec()), member.clone()))
}

fn impl_method_member(path: &typed_ir::Path) -> Option<&typed_ir::Name> {
    if !path
        .segments
        .iter()
        .any(|segment| segment.0.starts_with("&impl#"))
    {
        return None;
    }
    path.segments.last()
}

fn role_receiver_types(
    receiver: &ApplyStep<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Vec<typed_ir::Type> {
    let mut out = Vec::new();
    if let Some(ty) = receiver.evidence.and_then(apply_observed_arg_type) {
        push_unique_type(&mut out, ty);
    }
    push_unique_type(&mut out, receiver.arg_type(local_types));
    push_role_receiver_expr_types(&mut out, receiver.arg, local_types);
    out
}

fn push_role_receiver_expr_types(
    out: &mut Vec<typed_ir::Type>,
    expr: &Expr,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) {
    push_unique_type(
        out,
        runtime_type_to_core(expr_lower_type(expr, local_types)),
    );
    match &expr.kind {
        ExprKind::BindHere { expr } => {
            if let RuntimeType::Thunk { value, .. } = &expr.ty {
                push_unique_type(out, runtime_type_to_core((**value).clone()));
            }
            push_role_receiver_expr_types(out, expr, local_types);
        }
        ExprKind::Coerce { expr, to, .. } => {
            push_unique_type(out, to.clone());
            push_role_receiver_expr_types(out, expr, local_types);
        }
        _ => {}
    }
}

fn push_unique_type(out: &mut Vec<typed_ir::Type>, ty: typed_ir::Type) {
    if !out.iter().any(|existing| existing == &ty) {
        out.push(ty);
    }
}

fn role_method_candidate_score(
    candidate: &RoleMethodCandidate,
    receiver_types: &[typed_ir::Type],
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> Option<usize> {
    let receiver_bounds = candidate.inputs.first()?;
    let receiver_score = receiver_types
        .iter()
        .filter_map(|receiver_ty| type_bounds_match_score(receiver_bounds, receiver_ty))
        .max()?;
    let spine_score = role_method_spine_score(&candidate.callee_type, spine, local_types);
    Some(receiver_score + spine_score)
}

fn role_method_spine_score(
    callee_type: &RuntimeType,
    spine: &ApplySpine<'_>,
    local_types: &HashMap<typed_ir::Path, RuntimeType>,
) -> usize {
    let mut current = runtime_type_to_core(callee_type.clone());
    let mut score = 0;
    for step in &spine.steps {
        let typed_ir::Type::Fun { param, ret, .. } = current else {
            break;
        };
        let arg_type = step.arg_type(local_types);
        score += soft_core_match_score(&param, &arg_type);
        if let Some(evidence) = step.evidence {
            score += soft_type_bounds_match_score(&evidence.arg, &param);
            if let Some(expected) = &evidence.expected_arg {
                score += soft_type_bounds_match_score(expected, &param);
            }
            score += soft_type_bounds_match_score(&evidence.result, &ret);
        }
        current = *ret;
    }
    score
}

fn soft_type_bounds_match_score(bounds: &typed_ir::TypeBounds, actual: &typed_ir::Type) -> usize {
    let mut score = 0;
    if let Some(lower) = bounds.lower.as_deref() {
        score += soft_core_match_score(lower, actual);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        score += soft_core_match_score(actual, upper);
    }
    score
}

fn soft_core_match_score(left: &typed_ir::Type, right: &typed_ir::Type) -> usize {
    core_subtype_match_score(left, right).unwrap_or(0)
}

fn type_bounds_match_score(
    bounds: &typed_ir::TypeBounds,
    actual: &typed_ir::Type,
) -> Option<usize> {
    let mut score = 0;
    if let Some(lower) = bounds.lower.as_deref() {
        let lower_score = core_subtype_match_score(lower, actual)?;
        score += lower_score;
    }
    if let Some(upper) = bounds.upper.as_deref() {
        let upper_score = core_subtype_match_score(actual, upper)?;
        score += upper_score;
    }
    Some(score)
}

fn core_subtype_match_score(sub: &typed_ir::Type, sup: &typed_ir::Type) -> Option<usize> {
    if sub == sup {
        return Some(8);
    }
    match (sub, sup) {
        (typed_ir::Type::Never, _) | (_, typed_ir::Type::Any) => Some(1),
        (typed_ir::Type::Var(_), _) | (_, typed_ir::Type::Var(_)) => Some(2),
        (typed_ir::Type::Union(items), sup) => items
            .iter()
            .map(|item| core_subtype_match_score(item, sup))
            .try_fold(1, |acc, score| score.map(|score| acc + score)),
        (sub, typed_ir::Type::Union(items)) => items
            .iter()
            .filter_map(|item| core_subtype_match_score(sub, item))
            .max()
            .map(|score| score + 1),
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => args
            .iter()
            .zip(actual_args)
            .map(|(left, right)| type_arg_match_score(left, right))
            .try_fold(4, |acc, score| score.map(|score| acc + score)),
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => Some(
            core_subtype_match_score(actual_param, param)?
                + core_subtype_match_score(param_effect, actual_param_effect)?
                + core_subtype_match_score(ret_effect, actual_ret_effect)?
                + core_subtype_match_score(ret, actual_ret)?,
        ),
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            items
                .iter()
                .zip(actual_items)
                .map(|(left, right)| core_subtype_match_score(left, right))
                .try_fold(4, |acc, score| score.map(|score| acc + score))
        }
        _ => None,
    }
}

fn type_arg_match_score(left: &typed_ir::TypeArg, right: &typed_ir::TypeArg) -> Option<usize> {
    match (left, right) {
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) => {
            core_subtype_match_score(left, right)
        }
        (typed_ir::TypeArg::Bounds(left), typed_ir::TypeArg::Bounds(right)) => {
            let lower = match (left.lower.as_deref(), right.lower.as_deref()) {
                (Some(left), Some(right)) => core_subtype_match_score(left, right)?,
                (None, None) => 1,
                _ => return None,
            };
            let upper = match (left.upper.as_deref(), right.upper.as_deref()) {
                (Some(left), Some(right)) => core_subtype_match_score(left, right)?,
                (None, None) => 1,
                _ => return None,
            };
            Some(lower + upper)
        }
        _ => None,
    }
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
    clear_apply_spine_instantiations(expr, &solution.binding);
    refresh_apply_spine_runtime_types(expr, solution.callee_type.clone());
    expr.ty = solution.result_type.clone();
    *cursor += 1;
    Ok(true)
}

fn refresh_apply_spine_runtime_types(expr: &mut Expr, callee_type: RuntimeType) -> RuntimeType {
    match &mut expr.kind {
        ExprKind::Apply { callee, .. } => {
            let callee_type = refresh_apply_spine_runtime_types(callee, callee_type);
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

fn prune_unbound_binding_roots(module: &mut Module) {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    module.roots.retain(|root| match root {
        Root::Binding(path) => bindings.contains(path),
        Root::Expr(_) => true,
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
    materialize_expr_with_expected(expr, substitutions, None)
}

fn materialize_expr_with_expected(
    expr: Expr,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: Option<&RuntimeType>,
) -> Expr {
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
        } => {
            let kind = ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body: Box::new(materialize_expr(*body, substitutions)),
            };
            let ty = expected
                .filter(|expected| matches!(expected, RuntimeType::Fun { .. }))
                .cloned()
                .unwrap_or(ty);
            return Expr::typed(kind, ty);
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            let evidence =
                evidence.map(|evidence| materialize_apply_evidence(evidence, substitutions));
            let callee = materialize_expr(*callee, substitutions);
            let expected_arg = materialized_runtime_callee_arg(&callee.ty)
                .or_else(|| evidence.as_ref().and_then(materialized_apply_expected_arg));
            ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(materialize_apply_arg(
                    *arg,
                    substitutions,
                    expected_arg.as_ref(),
                )),
                evidence,
                instantiation,
            }
        }
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
        ExprKind::Block { stmts, tail } => {
            let stmts = stmts
                .into_iter()
                .map(|stmt| materialize_stmt(stmt, substitutions))
                .collect();
            let tail = tail.map(|tail| {
                Box::new(materialize_expr_with_expected(
                    *tail,
                    substitutions,
                    expected,
                ))
            });
            let block_ty = tail
                .as_ref()
                .map(|tail| tail.ty.clone())
                .unwrap_or_else(|| RuntimeType::Core(unit_type()));
            return Expr::typed(ExprKind::Block { stmts, tail }, block_ty);
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let evidence = materialize_join_evidence(evidence, substitutions);
            let result = expected_core_type(expected).unwrap_or(evidence.result);
            let expected_result = runtime_type_from_core_value(result.clone());
            let kind = ExprKind::Handle {
                body: Box::new(materialize_expr(*body, substitutions)),
                arms: arms
                    .into_iter()
                    .map(|arm| materialize_handle_arm(arm, substitutions, &expected_result))
                    .collect(),
                handler: materialize_handle_effect(handler, substitutions),
                evidence: yulang_runtime_ir::JoinEvidence {
                    result: result.clone(),
                },
            };
            return Expr::typed(kind, expected_result);
        }
        ExprKind::BindHere { expr } => {
            let expr = materialize_expr_with_expected(*expr, substitutions, expected);
            let RuntimeType::Thunk { value, .. } = &expr.ty else {
                return expr;
            };
            let value = (**value).clone();
            let kind = ExprKind::BindHere {
                expr: Box::new(expr),
            };
            return Expr::typed(kind, value);
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let (effect, expected_value) = match expected {
                Some(RuntimeType::Thunk { effect, value }) => {
                    (effect.clone(), Some((**value).clone()))
                }
                Some(expected) => (
                    materialize_core_type(effect, substitutions),
                    Some(expected.clone()),
                ),
                None => (materialize_core_type(effect, substitutions), None),
            };
            let value =
                expected_value.unwrap_or_else(|| materialize_runtime_type(value, substitutions));
            let kind = ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(materialize_expr_with_expected(
                    *expr,
                    substitutions,
                    Some(&value),
                )),
            };
            return Expr::typed(
                kind,
                RuntimeType::Thunk {
                    effect,
                    value: Box::new(value),
                },
            );
        }
        ExprKind::LocalPushId { id, body } => {
            let body = materialize_expr_with_expected(*body, substitutions, expected);
            let ty = body.ty.clone();
            let kind = ExprKind::LocalPushId {
                id,
                body: Box::new(body),
            };
            return Expr::typed(kind, ty);
        }
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => {
            let thunk = materialize_expr_with_expected(*thunk, substitutions, expected);
            let ty = thunk.ty.clone();
            let kind = ExprKind::AddId {
                id,
                allowed: materialize_core_type(allowed, substitutions),
                active,
                thunk: Box::new(thunk),
            };
            return Expr::typed(kind, ty);
        }
        ExprKind::Coerce { from, to, expr } => {
            let to = expected_core_type(expected)
                .unwrap_or_else(|| materialize_core_type(to, substitutions));
            let expected = runtime_type_from_core_value(to.clone());
            let expr = materialize_expr_with_expected(*expr, substitutions, Some(&expected));
            let materialized_from = materialize_core_type(from, substitutions);
            let from = match &expr.ty {
                RuntimeType::Unknown => materialized_from,
                _ => runtime_type_to_core(expr.ty.clone()),
            };
            if from == to && runtime_type_to_core(expr.ty.clone()) == to {
                return expr;
            }
            let kind = ExprKind::Coerce {
                from,
                to: to.clone(),
                expr: Box::new(expr),
            };
            return Expr::typed(kind, runtime_type_from_core_value(to));
        }
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
    expected: &RuntimeType,
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
        body: materialize_expr_with_expected(arm.body, substitutions, Some(expected)),
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

fn materialize_apply_evidence(
    evidence: typed_ir::ApplyEvidence,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::ApplyEvidence {
    typed_ir::ApplyEvidence {
        callee_source_edge: evidence.callee_source_edge,
        arg_source_edge: evidence.arg_source_edge,
        callee: materialize_type_bounds(evidence.callee, substitutions),
        expected_callee: evidence
            .expected_callee
            .map(|bounds| materialize_type_bounds(bounds, substitutions)),
        arg: materialize_type_bounds(evidence.arg, substitutions),
        expected_arg: evidence
            .expected_arg
            .map(|bounds| materialize_type_bounds(bounds, substitutions)),
        result: materialize_type_bounds(evidence.result, substitutions),
        principal_callee: evidence
            .principal_callee
            .map(|ty| materialize_core_type(ty, substitutions)),
        substitutions: evidence
            .substitutions
            .into_iter()
            .map(|subst| typed_ir::TypeSubstitution {
                var: subst.var,
                ty: materialize_core_type(subst.ty, substitutions),
            })
            .collect(),
        substitution_candidates: evidence
            .substitution_candidates
            .into_iter()
            .map(|candidate| typed_ir::PrincipalSubstitutionCandidate {
                var: candidate.var,
                relation: candidate.relation,
                ty: materialize_core_type(candidate.ty, substitutions),
                source_edge: candidate.source_edge,
                path: candidate.path,
            })
            .collect(),
        role_method: evidence.role_method,
        principal_elaboration: evidence
            .principal_elaboration
            .map(|plan| materialize_principal_elaboration_plan(plan, substitutions)),
    }
}

fn materialize_principal_elaboration_plan(
    plan: typed_ir::PrincipalElaborationPlan,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::PrincipalElaborationPlan {
    typed_ir::PrincipalElaborationPlan {
        target: plan.target,
        principal_callee: materialize_core_type(plan.principal_callee, substitutions),
        substitutions: plan
            .substitutions
            .into_iter()
            .map(|subst| typed_ir::TypeSubstitution {
                var: subst.var,
                ty: materialize_core_type(subst.ty, substitutions),
            })
            .collect(),
        args: plan
            .args
            .into_iter()
            .map(|arg| typed_ir::PrincipalElaborationArg {
                index: arg.index,
                intrinsic: materialize_type_bounds(arg.intrinsic, substitutions),
                contextual: arg
                    .contextual
                    .map(|bounds| materialize_type_bounds(bounds, substitutions)),
                expected_runtime: arg
                    .expected_runtime
                    .map(|ty| materialize_core_type(ty, substitutions)),
                source_edge: arg.source_edge,
            })
            .collect(),
        result: typed_ir::PrincipalElaborationResult {
            intrinsic: materialize_type_bounds(plan.result.intrinsic, substitutions),
            contextual: plan
                .result
                .contextual
                .map(|bounds| materialize_type_bounds(bounds, substitutions)),
            expected_runtime: plan
                .result
                .expected_runtime
                .map(|ty| materialize_core_type(ty, substitutions)),
        },
        adapters: plan
            .adapters
            .into_iter()
            .map(|adapter| typed_ir::PrincipalAdapterHole {
                kind: adapter.kind,
                source_edge: adapter.source_edge,
                actual: materialize_core_type(adapter.actual, substitutions),
                expected: materialize_core_type(adapter.expected, substitutions),
            })
            .collect(),
        complete: plan.complete,
        incomplete_reasons: plan.incomplete_reasons,
    }
}

fn materialize_type_bounds(
    bounds: typed_ir::TypeBounds,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: bounds
            .lower
            .map(|ty| Box::new(materialize_core_type(*ty, substitutions))),
        upper: bounds
            .upper
            .map(|ty| Box::new(materialize_core_type(*ty, substitutions))),
    }
}

fn materialized_apply_expected_arg(evidence: &typed_ir::ApplyEvidence) -> Option<RuntimeType> {
    evidence
        .expected_arg
        .as_ref()
        .and_then(type_from_bounds)
        .map(runtime_type_from_core_value)
        .filter(should_materialize_runtime_apply_arg_to)
}

fn materialized_runtime_callee_arg(ty: &RuntimeType) -> Option<RuntimeType> {
    let arg = match ty {
        RuntimeType::Fun { param, .. } => param.as_ref().clone(),
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => runtime_type_from_core_value_and_effect(
            param.as_ref().clone(),
            param_effect.as_ref().clone(),
        ),
        RuntimeType::Unknown | RuntimeType::Core(_) | RuntimeType::Thunk { .. } => return None,
    };
    should_materialize_runtime_apply_arg_to(&arg).then_some(arg)
}

fn should_materialize_runtime_apply_arg_to(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Core(ty) => should_materialize_core_apply_arg_to(ty),
        RuntimeType::Thunk { effect, value } => {
            should_thunk_effect(effect)
                && runtime_type_is_closed(value)
                && should_materialize_core_apply_arg_to(&runtime_type_to_core(
                    value.as_ref().clone(),
                ))
        }
        RuntimeType::Fun { .. } => runtime_type_is_closed(ty),
        RuntimeType::Unknown => false,
    }
}

fn should_materialize_core_apply_arg_to(ty: &typed_ir::Type) -> bool {
    core_type_is_closed(ty) && !matches!(ty, typed_ir::Type::Any | typed_ir::Type::Never)
}

fn materialize_apply_arg(
    arg: Expr,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: Option<&RuntimeType>,
) -> Expr {
    let arg = materialize_expr_with_expected(arg, substitutions, expected);
    let Some(expected) = expected else {
        return arg;
    };
    if let RuntimeType::Thunk { effect, value } = expected {
        return materialize_thunk_apply_arg(arg, effect, value);
    }
    let Some(expected) = expected_core_type(Some(expected)) else {
        return arg;
    };
    let actual = runtime_type_to_core(arg.ty.clone());
    if actual == expected || matches!(actual, typed_ir::Type::Unknown) {
        return arg;
    }
    Expr::typed(
        ExprKind::Coerce {
            from: actual,
            to: expected.clone(),
            expr: Box::new(arg),
        },
        runtime_type_from_core_value(expected),
    )
}

fn materialize_thunk_apply_arg(arg: Expr, effect: &typed_ir::Type, value: &RuntimeType) -> Expr {
    let expected_core = runtime_type_to_core(value.clone());
    let actual_core = runtime_type_to_core(arg.ty.clone());
    if matches!(arg.ty, RuntimeType::Thunk { .. }) {
        return arg;
    }
    let expr = if actual_core == expected_core || matches!(actual_core, typed_ir::Type::Unknown) {
        arg
    } else {
        Expr::typed(
            ExprKind::Coerce {
                from: actual_core,
                to: expected_core,
                expr: Box::new(arg),
            },
            value.clone(),
        )
    };
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(expr),
        },
        RuntimeType::Thunk {
            effect: effect.clone(),
            value: Box::new(value.clone()),
        },
    )
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

fn expected_core_type(expected: Option<&RuntimeType>) -> Option<typed_ir::Type> {
    match expected {
        Some(RuntimeType::Unknown) | None => None,
        Some(RuntimeType::Core(ty)) => Some(ty.clone()),
        Some(expected) => Some(runtime_type_to_core(expected.clone())),
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
        callee_type: solution.callee_type.clone(),
    }
}

fn alias_path(original: &typed_ir::Path, index: usize) -> typed_ir::Path {
    let mut segments = original.segments.clone();
    segments.push(typed_ir::Name(format!("mono{index}")));
    typed_ir::Path::new(segments)
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

fn unit_type() -> typed_ir::Type {
    typed_ir::Type::Named {
        path: typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
        args: Vec::new(),
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
    fn root_apply_top_callee_param_annotation_does_not_force_top_solution() {
        let int = int_type();
        let module = Module {
            path: path("test"),
            bindings: vec![id_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id")),
                        RuntimeType::Fun {
                            param: Box::new(RuntimeType::Core(typed_ir::Type::Any)),
                            ret: Box::new(RuntimeType::Core(int.clone())),
                        },
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Core(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Core(int.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let output = finalize_module(module).unwrap();
        let solution = &output.report.root_graph_solutions[0];

        assert_eq!(solution.binding, path("id"));
        assert_eq!(solution.graph.substitutions()[0].ty, int);
    }

    #[test]
    fn local_scope_type_overrides_stale_var_annotation_in_apply_arg() {
        let int = int_type();
        let original = typed_ir::TypeVar("a".into());
        let stale = RuntimeType::Core(typed_ir::Type::Named {
            path: path("list"),
            args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Var(original))],
        });
        let concrete = RuntimeType::Core(typed_ir::Type::Named {
            path: path("list"),
            args: vec![typed_ir::TypeArg::Type(int.clone())],
        });
        let local_path = path("xs");
        let mut local_types = HashMap::new();
        local_types.insert(local_path.clone(), concrete.clone());
        let expr = Expr::typed(ExprKind::Var(local_path), stale);

        assert_eq!(expr_lower_type(&expr, &local_types), concrete);
    }

    #[test]
    fn root_apply_result_type_bounds_open_return_var() {
        let int = int_type();
        let bool_ty = bool_type();
        let module = Module {
            path: path("test"),
            bindings: vec![poly_return_binding()],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("poly_return")),
                        RuntimeType::Unknown,
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Core(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Core(bool_ty.clone()),
            )],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let solutions = solve_root_graphs(&module, &TypeCastOrder::default()).unwrap();

        assert_eq!(solutions.len(), 1);
        let substitutions = &solutions[0].type_substitutions;
        assert!(substitutions.iter().any(|substitution| {
            substitution.var == typed_ir::TypeVar("a".into()) && substitution.ty == int
        }));
        assert!(substitutions.iter().any(|substitution| {
            substitution.var == typed_ir::TypeVar("b".into()) && substitution.ty == bool_ty
        }));
        assert!(solutions[0].graph.is_complete());
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
    fn finalize_monomorphize_module_returns_valid_mainline_output() {
        let module = runtime_module_from_source_without_std("my id x = x\nid 1\n");

        let module = finalize_monomorphize_module(module).unwrap();

        yulang_runtime::check_runtime_invariants(
            &module,
            yulang_runtime::RuntimeStage::Monomorphized,
        )
        .unwrap();
        yulang_runtime::validate_module(&module).unwrap();
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
    fn finalized_source_runs_if_int_float_join() {
        let module =
            runtime_module_from_source_without_std("my x = if true { 1 } else { 2.0 }\nx\n");

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Float(
                "1.0".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_nested_lexical_block() {
        let module = runtime_module_from_source_without_std(
            r#"{
    my x = 1
    {
        my y = 2
        y
    }
}
"#,
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "2".into()
            ))]
        );
    }

    #[test]
    fn finalized_source_runs_polymorphic_body_with_lexical_block() {
        let module = runtime_module_from_source_without_std(
            r#"my f x = {
    my y = x
    y
}
f 3
"#,
        );

        let output = finalize_module(module).unwrap();
        let vm = yulang_vm::compile_vm_module(output.module).unwrap();
        let results = vm.eval_roots().unwrap();

        assert_eq!(
            results,
            vec![yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(
                "3".into()
            ))]
        );
    }

    #[test]
    fn materialize_block_type_from_tail_before_deciding_bind_here() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let thunk = RuntimeType::Thunk {
            effect: typed_ir::Type::Never,
            value: Box::new(RuntimeType::Core(int.clone())),
        };
        let stale_block = Expr::typed(
            ExprKind::Block {
                stmts: Vec::new(),
                tail: Some(Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: typed_ir::Type::Never,
                        value: RuntimeType::Core(int.clone()),
                        expr: Box::new(Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                            RuntimeType::Core(int.clone()),
                        )),
                    },
                    thunk.clone(),
                ))),
            },
            RuntimeType::Core(int.clone()),
        );
        let bind_here = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(stale_block),
            },
            RuntimeType::Core(int),
        );

        let materialized = materialize_expr(bind_here, &[]);
        let ExprKind::BindHere { expr } = materialized.kind else {
            panic!("bind_here should be kept when the materialized block tail is a thunk");
        };

        assert_eq!(expr.ty, thunk);
    }

    #[test]
    fn runtime_function_projection_preserves_thunk_effect_slots() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let bool_ty = typed_ir::Type::Named {
            path: path("bool"),
            args: Vec::new(),
        };
        let arg_effect = typed_ir::Type::Named {
            path: path("arg_effect"),
            args: Vec::new(),
        };
        let ret_effect = typed_ir::Type::Named {
            path: path("ret_effect"),
            args: Vec::new(),
        };

        let projected = runtime_type_to_core(RuntimeType::Fun {
            param: Box::new(RuntimeType::Thunk {
                effect: arg_effect.clone(),
                value: Box::new(RuntimeType::Core(int.clone())),
            }),
            ret: Box::new(RuntimeType::Thunk {
                effect: ret_effect.clone(),
                value: Box::new(RuntimeType::Core(bool_ty.clone())),
            }),
        });

        assert_eq!(
            projected,
            typed_ir::Type::Fun {
                param: Box::new(int),
                param_effect: Box::new(arg_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(bool_ty),
            }
        );
    }

    #[test]
    fn materialize_handle_type_from_materialized_evidence() {
        let int = typed_ir::Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let stale_unit = RuntimeType::Core(unit_type());
        let handle = Expr::typed(
            ExprKind::Handle {
                body: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    stale_unit.clone(),
                )),
                arms: Vec::new(),
                evidence: yulang_runtime_ir::JoinEvidence {
                    result: typed_ir::Type::Var(typed_ir::TypeVar("a".into())),
                },
                handler: yulang_runtime_ir::HandleEffect {
                    consumes: Vec::new(),
                    residual_before: None,
                    residual_after: None,
                },
            },
            stale_unit,
        );

        let materialized = materialize_expr(
            handle,
            &[typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int.clone(),
            }],
        );

        assert_eq!(materialized.ty, RuntimeType::Core(int.clone()));
        let ExprKind::Handle { evidence, .. } = materialized.kind else {
            panic!("expected handle expression");
        };
        assert_eq!(evidence.result, int);
    }

    #[test]
    fn cached_std_runtime_ir_cache_can_enter_runtime_finalize() {
        let cache_start = std::time::Instant::now();
        let cached =
            runtime_module_from_source_with_std_dependency_cache_large_stack("\"hello\".println\n");
        let cache_read = cache_start.elapsed();

        assert!(!cached.dependency_manifests.is_empty());

        let finalize_start = std::time::Instant::now();
        let output = finalize_module(cached.module).unwrap();
        let finalize = finalize_start.elapsed();
        eprintln!(
            "cached std runtime-ir finalize profile: cache_read={:?} finalize={:?}",
            cache_read, finalize
        );

        assert_eq!(output.module.root_exprs.len(), 1);
    }

    #[test]
    fn cached_std_finalize_runs_ref_scalar_assignment() {
        let results = finalized_int_values_from_std_dependency_cache(
            r#"{
    my $x = 10
    &x = 11
    $x
}
"#,
        );

        assert_eq!(results, vec!["11".to_string()]);
    }

    #[test]
    fn cached_std_finalize_compiles_ref_assignment_from_ref_read() {
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(
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
    fn legacy_runtime_and_finalize_match_small_sources_without_std() {
        for case in [
            RuntimeOracleCase {
                name: "identity",
                source: "my id x = x\nid 1\n",
            },
            RuntimeOracleCase {
                name: "lexical block",
                source: r#"my f x = {
    my y = x
    y
}
f 3
"#,
            },
            RuntimeOracleCase {
                name: "first argument",
                source: "my first x y = x\nfirst 1 true\n",
            },
            RuntimeOracleCase {
                name: "tuple payload",
                source: "my pair x y = (x, y)\npair 1 true\n",
            },
        ] {
            assert_legacy_and_finalize_match_without_std(case);
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_playground_core_examples() {
        for case in [
            RuntimeOracleCase {
                name: "prelude operators",
                source: r#"1 + 2
2 * 3
1 == 1
1 < 2
2 <= 2
"#,
            },
            RuntimeOracleCase {
                name: "undet list",
                source: r#"(each [1, 2, 3] + each [4, 5, 6]).list
"#,
            },
            RuntimeOracleCase {
                name: "undet once range",
                source: r#"{
    my a = each 1..
    guard: a == 3
    a
}.once
"#,
            },
        ] {
            assert_legacy_and_finalize_match_with_std_dependency_cache(case);
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_playground_state_examples() {
        for case in [
            RuntimeOracleCase {
                name: "ref list assignment",
                source: r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
            },
            RuntimeOracleCase {
                name: "console output",
                source: r#"println "hello"
1 + 2
"#,
            },
            RuntimeOracleCase {
                name: "callback hygiene",
                source: r#"// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
            },
        ] {
            assert_legacy_and_finalize_match_with_std_dependency_cache(case);
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_playground_tour() {
        assert_legacy_and_finalize_match_with_std_dependency_cache(RuntimeOracleCase {
            name: "playground tour",
            source: playground_tour_source(),
        });
    }

    #[test]
    fn control_vm_legacy_runtime_and_finalize_match_small_sources_without_std() {
        for case in [
            RuntimeOracleCase {
                name: "identity",
                source: "my id x = x\nid 1\n",
            },
            RuntimeOracleCase {
                name: "lexical block",
                source: r#"my f x = {
    my y = x
    y
}
f 3
"#,
            },
            RuntimeOracleCase {
                name: "tuple payload",
                source: "my pair x y = (x, y)\npair 1 true\n",
            },
        ] {
            assert_legacy_and_finalize_match_without_std_on_vm(case, OracleVm::Control);
        }
    }

    #[test]
    fn cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples() {
        for case in [
            RuntimeOracleCase {
                name: "prelude operators",
                source: r#"1 + 2
2 * 3
1 == 1
"#,
            },
            RuntimeOracleCase {
                name: "ref list assignment",
                source: r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
            },
            RuntimeOracleCase {
                name: "callback hygiene",
                source: r#"// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
            },
        ] {
            assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(
                case,
                OracleVm::Control,
            );
        }
    }

    #[test]
    fn cached_std_legacy_runtime_and_finalize_match_examples() {
        for case in example_oracle_cases() {
            assert_legacy_and_finalize_match_with_std_dependency_cache(case);
        }
    }

    #[test]
    fn cached_std_finalize_accepts_showcase_example() {
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(&playground_source(
            include_str!("../../../examples/showcase.yu"),
        ));
    }

    #[test]
    fn cached_std_finalize_accepts_refs_example() {
        // The legacy monomorphizer still loses the `+` receiver through the
        // compiled dependency path; keep this as a finalize-only mainline gate.
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(&playground_source(
            include_str!("../../../examples/02_refs.yu"),
        ));
    }

    #[test]
    fn cached_std_finalize_runs_playground_core_examples() {
        for case in [
            PlaygroundCase {
                name: "undet list",
                source: r#"(each [1, 2, 3] + each [4, 5, 6]).list
"#,
                stdout: "",
                results: &["[5, 6, 7, 6, 7, 8, 7, 8, 9]"],
            },
            PlaygroundCase {
                name: "undet once range",
                source: r#"{
    my a = each 1..
    guard: a == 3
    a
}.once
"#,
                stdout: "",
                results: &["just 3"],
            },
            PlaygroundCase {
                name: "undet pythagorean",
                source: r#"({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once
"#,
                stdout: "",
                results: &["just (3, 4, 5)"],
            },
            PlaygroundCase {
                name: "prelude operators",
                source: r#"1 + 2
2 * 3
1 == 1
1 < 2
2 <= 2
"#,
                stdout: "",
                results: &["3", "6", "true", "true", "true"],
            },
            PlaygroundCase {
                name: "multiple roots",
                source: r#"1 + 2
3 + 4
"#,
                stdout: "",
                results: &["3", "7"],
            },
        ] {
            assert_playground_case_finalizes(case);
        }
    }

    #[test]
    fn cold_std_finalize_runs_range_each_sum_without_prewarmed_cache() {
        let source = playground_source("((1..3).each + (1..3).each).list\n");
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_cold_std_dependency_cache_large_stack(
                &source,
                "cold-range-each",
            );
            let output = finalize_module(cached.module)
                .unwrap_or_else(|error| panic!("cold range each finalize failed: {error:?}"));
            let vm = yulang_vm::compile_vm_module(output.module)
                .unwrap_or_else(|error| panic!("cold range each VM compile failed: {error:?}"));
            let host_output = yulang_vm::eval_roots_with_basic_host(&vm)
                .unwrap_or_else(|error| panic!("cold range each VM eval failed: {error:?}"));
            let actual = host_output
                .results
                .iter()
                .map(format_vm_result)
                .collect::<Vec<_>>();
            assert_eq!(actual, ["[2, 3, 4, 3, 4, 5, 4, 5, 6]"]);
        });
    }

    #[test]
    fn cached_std_finalize_runs_playground_state_and_host_examples() {
        for case in [
            PlaygroundCase {
                name: "ref list assignment",
                source: r#"{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
"#,
                stdout: "",
                results: &["[2, 6, 4]"],
            },
            PlaygroundCase {
                name: "console output",
                source: r#"println "hello"
1 + 2
"#,
                stdout: "hello\n",
                results: &["()", "3"],
            },
            PlaygroundCase {
                name: "callback hygiene",
                source: r#"// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
"#,
                stdout: "",
                results: &["0"],
            },
        ] {
            assert_playground_case_finalizes(case);
        }
    }

    #[test]
    fn cached_std_finalize_runs_playground_tour() {
        assert_playground_case_finalizes(PlaygroundCase {
            name: "playground tour",
            source: playground_tour_source(),
            stdout: "",
            results: &["7", "[2, 6, 4]", "5", "just 18"],
        });
    }

    #[test]
    fn std_no_cache_finalize_runs_reported_graph_unification_regressions() {
        for case in [
            PlaygroundCase {
                name: "handler function preserves effectful argument boundary",
                source: r#"act log:
    pub put: str -> ()

my collect_logs comp = catch comp:
    log::put _, k -> k ()
    v -> v

collect_logs: log::put "a"
"#,
                stdout: "",
                results: &["()"],
            },
            PlaygroundCase {
                name: "handler function with state preserves effectful argument boundary",
                source: r#"act log:
    pub put: str -> ()

my collect_logs comp =
    my $count = 0
    catch comp:
        log::put _, k ->
            &count = $count + 1
            k ()
        v -> v
    $count

collect_logs: log::put "a"
"#,
                stdout: "",
                results: &["1"],
            },
            PlaygroundCase {
                name: "record pattern field receiver feeds role method",
                source: r#"my f { port: p } = p.show
f { port: 8080 }
"#,
                stdout: "",
                results: &["\"8080\""],
            },
            PlaygroundCase {
                name: "record default field receiver feeds role method",
                source: r#"my f { port = 80 } = port.show
f {}
"#,
                stdout: "",
                results: &["\"80\""],
            },
            PlaygroundCase {
                name: "list index raw preserves callback function element",
                source: r#"use std::flow::*

our f() = return 0

our g h = sub:
    my hs = [h]
    ((std::list::index_raw hs) 0)()
    return 1

sub:
    my b = g f
    2
"#,
                stdout: "",
                results: &["0"],
            },
            PlaygroundCase {
                name: "error wrap fail flow keeps carrier and payload apart",
                source: r#"error fs_err:
    not_found str

my read_or_throw(p: str): [fs_err] str =
    fail fs_err::not_found p

my safe_read(p: str): result str fs_err = fs_err::wrap:
    read_or_throw p

safe_read "missing"
"#,
                stdout: "",
                results: &["err not_found \"missing\""],
            },
            PlaygroundCase {
                name: "inline conditional wrap keeps error carrier and payload apart",
                source: r#"error fail_err:
    bad str

fail_err::wrap:
    if true: fail fail_err::bad "x"
    else: 1
"#,
                stdout: "",
                results: &["err bad \"x\""],
            },
        ] {
            assert_std_source_no_cache_finalizes_to_results(case);
        }
    }

    #[test]
    #[ignore = "diagnostic: report typed/untyped expression coverage"]
    fn rina_finalize_type_coverage_report() {
        let src = r#"{
    my $x = 0
    {
        &x = 9
    }
    $x
}
"#
        .to_string();
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&src);
            let output = finalize_module(cached.module).unwrap();
            let mut stats = TypeCoverageStats::default();
            for binding in &output.module.bindings {
                stats.set_owner(format!("binding {:?}", binding.name));
                walk_expr_for_coverage(&binding.body, &mut stats);
            }
            for (i, expr) in output.module.root_exprs.iter().enumerate() {
                stats.set_owner(format!("root_expr[{i}]"));
                walk_expr_for_coverage(expr, &mut stats);
            }
            eprintln!("=== type coverage report ===");
            eprintln!("total: {}", stats.total);
            eprintln!("concrete: {}", stats.concrete);
            eprintln!("with Unknown: {}", stats.with_unknown);
            eprintln!("with Var: {}", stats.with_var);
            eprintln!("by kind missing concrete:");
            let mut entries: Vec<_> = stats.by_kind_unconcrete.iter().collect();
            entries.sort_by_key(|(k, _)| k.to_string());
            for (kind, count) in entries {
                eprintln!("  {kind}: {count}");
            }
            eprintln!("by owner missing concrete:");
            let mut owner_entries: Vec<_> = stats.by_owner_unconcrete.iter().collect();
            owner_entries.sort_by_key(|(o, _)| *o);
            for (owner, count) in owner_entries {
                eprintln!("  {owner}: {count}");
            }
            eprintln!("=== first 40 unconcrete samples ===");
            for (i, sample) in stats.samples.iter().enumerate().take(40) {
                eprintln!("  [{i}] {sample}");
            }
        });
    }

    #[derive(Default)]
    struct TypeCoverageStats {
        total: usize,
        concrete: usize,
        with_unknown: usize,
        with_var: usize,
        by_kind_unconcrete: std::collections::BTreeMap<&'static str, usize>,
        by_owner_unconcrete: std::collections::BTreeMap<String, usize>,
        samples: Vec<String>,
        current_owner: String,
    }

    impl TypeCoverageStats {
        fn set_owner(&mut self, owner: String) {
            self.current_owner = owner;
        }
    }

    fn expr_kind_tag(expr: &Expr) -> &'static str {
        match &expr.kind {
            ExprKind::Var(_) => "Var",
            ExprKind::EffectOp(_) => "EffectOp",
            ExprKind::PrimitiveOp(_) => "PrimitiveOp",
            ExprKind::Lit(_) => "Lit",
            ExprKind::Lambda { .. } => "Lambda",
            ExprKind::Apply { .. } => "Apply",
            ExprKind::If { .. } => "If",
            ExprKind::Tuple(_) => "Tuple",
            ExprKind::Record { .. } => "Record",
            ExprKind::Variant { .. } => "Variant",
            ExprKind::Select { .. } => "Select",
            ExprKind::Match { .. } => "Match",
            ExprKind::Block { .. } => "Block",
            ExprKind::Handle { .. } => "Handle",
            ExprKind::BindHere { .. } => "BindHere",
            ExprKind::Thunk { .. } => "Thunk",
            ExprKind::LocalPushId { .. } => "LocalPushId",
            ExprKind::PeekId => "PeekId",
            ExprKind::FindId { .. } => "FindId",
            ExprKind::AddId { .. } => "AddId",
            ExprKind::Coerce { .. } => "Coerce",
            ExprKind::Pack { .. } => "Pack",
        }
    }

    fn type_has_unknown(ty: &RuntimeType) -> bool {
        match ty {
            RuntimeType::Unknown => true,
            RuntimeType::Core(ty) => core_type_contains_unknown(ty),
            RuntimeType::Fun { param, ret } => type_has_unknown(param) || type_has_unknown(ret),
            RuntimeType::Thunk { effect, value } => {
                core_type_contains_unknown(effect) || type_has_unknown(value)
            }
        }
    }

    fn type_has_var(ty: &RuntimeType) -> bool {
        match ty {
            RuntimeType::Unknown => false,
            RuntimeType::Core(ty) => core_type_contains_var(ty),
            RuntimeType::Fun { param, ret } => type_has_var(param) || type_has_var(ret),
            RuntimeType::Thunk { effect, value } => {
                core_type_contains_var(effect) || type_has_var(value)
            }
        }
    }

    fn core_type_contains_unknown(ty: &typed_ir::Type) -> bool {
        match ty {
            typed_ir::Type::Unknown => true,
            typed_ir::Type::Var(_) | typed_ir::Type::Never | typed_ir::Type::Any => false,
            typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
                typed_ir::TypeArg::Type(t) => core_type_contains_unknown(t),
                typed_ir::TypeArg::Bounds(b) => {
                    b.lower.as_deref().is_some_and(core_type_contains_unknown)
                        || b.upper.as_deref().is_some_and(core_type_contains_unknown)
                }
            }),
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                core_type_contains_unknown(param)
                    || core_type_contains_unknown(param_effect)
                    || core_type_contains_unknown(ret_effect)
                    || core_type_contains_unknown(ret)
            }
            typed_ir::Type::Tuple(items)
            | typed_ir::Type::Union(items)
            | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_unknown),
            typed_ir::Type::Row { items, tail } => {
                items.iter().any(core_type_contains_unknown) || core_type_contains_unknown(tail)
            }
            typed_ir::Type::Record(record) => record
                .fields
                .iter()
                .any(|f| core_type_contains_unknown(&f.value)),
            typed_ir::Type::Variant(variant) => variant
                .cases
                .iter()
                .any(|c| c.payloads.iter().any(core_type_contains_unknown)),
            typed_ir::Type::Recursive { body, .. } => core_type_contains_unknown(body),
        }
    }

    fn core_type_contains_var(ty: &typed_ir::Type) -> bool {
        match ty {
            typed_ir::Type::Var(_) => true,
            typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
            typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
                typed_ir::TypeArg::Type(t) => core_type_contains_var(t),
                typed_ir::TypeArg::Bounds(b) => {
                    b.lower.as_deref().is_some_and(core_type_contains_var)
                        || b.upper.as_deref().is_some_and(core_type_contains_var)
                }
            }),
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                core_type_contains_var(param)
                    || core_type_contains_var(param_effect)
                    || core_type_contains_var(ret_effect)
                    || core_type_contains_var(ret)
            }
            typed_ir::Type::Tuple(items)
            | typed_ir::Type::Union(items)
            | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_var),
            typed_ir::Type::Row { items, tail } => {
                items.iter().any(core_type_contains_var) || core_type_contains_var(tail)
            }
            typed_ir::Type::Record(record) => record
                .fields
                .iter()
                .any(|f| core_type_contains_var(&f.value)),
            typed_ir::Type::Variant(variant) => variant
                .cases
                .iter()
                .any(|c| c.payloads.iter().any(core_type_contains_var)),
            typed_ir::Type::Recursive { body, .. } => core_type_contains_var(body),
        }
    }

    fn walk_expr_for_coverage(expr: &Expr, stats: &mut TypeCoverageStats) {
        stats.total += 1;
        let kind = expr_kind_tag(expr);
        let has_unknown = type_has_unknown(&expr.ty);
        let has_var = type_has_var(&expr.ty);
        if has_unknown {
            stats.with_unknown += 1;
        }
        if has_var {
            stats.with_var += 1;
        }
        if has_unknown || has_var {
            *stats.by_kind_unconcrete.entry(kind).or_default() += 1;
            *stats
                .by_owner_unconcrete
                .entry(stats.current_owner.clone())
                .or_default() += 1;
            if stats.samples.len() < 40 {
                let owner = stats.current_owner.clone();
                let detail = match &expr.kind {
                    ExprKind::Var(path) => format!("Var({path:?})"),
                    ExprKind::EffectOp(path) => format!("EffectOp({path:?})"),
                    _ => kind.to_string(),
                };
                stats
                    .samples
                    .push(format!("[{owner}] {detail} ty={:?}", &expr.ty));
            }
        } else {
            stats.concrete += 1;
        }
        match &expr.kind {
            ExprKind::Lambda { body, .. }
            | ExprKind::BindHere { expr: body }
            | ExprKind::LocalPushId { body, .. }
            | ExprKind::AddId { thunk: body, .. }
            | ExprKind::Coerce { expr: body, .. }
            | ExprKind::Pack { expr: body, .. }
            | ExprKind::Thunk { expr: body, .. } => walk_expr_for_coverage(body, stats),
            ExprKind::Apply { callee, arg, .. } => {
                walk_expr_for_coverage(callee, stats);
                walk_expr_for_coverage(arg, stats);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                walk_expr_for_coverage(cond, stats);
                walk_expr_for_coverage(then_branch, stats);
                walk_expr_for_coverage(else_branch, stats);
            }
            ExprKind::Tuple(items) => {
                for item in items {
                    walk_expr_for_coverage(item, stats);
                }
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    walk_expr_for_coverage(&field.value, stats);
                }
                if let Some(spread) = spread {
                    let e = match spread {
                        yulang_runtime_ir::RecordSpreadExpr::Head(e)
                        | yulang_runtime_ir::RecordSpreadExpr::Tail(e) => e,
                    };
                    walk_expr_for_coverage(e, stats);
                }
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    walk_expr_for_coverage(value, stats);
                }
            }
            ExprKind::Select { base, .. } => walk_expr_for_coverage(base, stats),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                walk_expr_for_coverage(scrutinee, stats);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        walk_expr_for_coverage(guard, stats);
                    }
                    walk_expr_for_coverage(&arm.body, stats);
                }
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    match stmt {
                        yulang_runtime_ir::Stmt::Let { value, .. } => {
                            walk_expr_for_coverage(value, stats);
                        }
                        yulang_runtime_ir::Stmt::Expr(e) => walk_expr_for_coverage(e, stats),
                        yulang_runtime_ir::Stmt::Module { body, .. } => {
                            walk_expr_for_coverage(body, stats);
                        }
                    }
                }
                if let Some(tail) = tail {
                    walk_expr_for_coverage(tail, stats);
                }
            }
            ExprKind::Handle { body, arms, .. } => {
                walk_expr_for_coverage(body, stats);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        walk_expr_for_coverage(guard, stats);
                    }
                    walk_expr_for_coverage(&arm.body, stats);
                }
            }
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
    }

    #[test]
    fn cached_std_finalize_runs_ref_assignment_inside_nested_block() {
        let results = finalized_int_values_from_std_dependency_cache(
            r#"{
    my $x = 0
    {
        &x = 9
    }
    $x
}
"#,
        );

        assert_eq!(results, vec!["9".to_string()]);
    }

    #[test]
    fn cached_std_finalize_runs_ref_assignment_inside_nested_for_loops() {
        let results = finalized_int_values_from_std_dependency_cache(
            r#"{
    my $total = 0
    for x in 1..3:
        for y in 1..2:
            &total = $total + x + y
    $total
}
"#,
        );

        assert_eq!(results, vec!["21".to_string()]);
    }

    fn finalized_int_values_from_std_dependency_cache(src: &str) -> Vec<String> {
        let src = src.to_string();
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&src);
            let output = finalize_module(cached.module).unwrap();
            assert!(
                output
                    .module
                    .bindings
                    .iter()
                    .all(|binding| binding.type_params.is_empty())
            );
            let vm = yulang_vm::compile_vm_module(output.module).unwrap();
            vm.eval_roots()
                .unwrap()
                .into_iter()
                .map(|result| match result {
                    yulang_vm::VmResult::Value(yulang_vm::VmValue::Int(value)) => value.to_string(),
                    yulang_vm::VmResult::Request(request) => {
                        let continuation = format!("{:?}", request.continuation);
                        panic!(
                            "expected int VM result, got request {:?}, blocked {:?}, handle_frames={}, bind_frames={}",
                            request.effect,
                            request.blocked_id,
                            continuation.matches("Handle {").count(),
                            continuation.matches("BindHere").count(),
                        )
                    }
                    other => panic!("expected int VM result, got {other:?}"),
                })
                .collect()
        })
    }

    fn assert_std_dependency_cache_ref_source_finalizes_to_vm_input(src: &str) {
        let src = src.to_string();
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&src);
            let output = finalize_module(cached.module).unwrap();
            assert!(
                output
                    .module
                    .bindings
                    .iter()
                    .all(|binding| binding.type_params.is_empty())
            );
            yulang_vm::compile_vm_module(output.module).unwrap();
        });
    }

    struct RuntimeOracleCase {
        name: &'static str,
        source: &'static str,
    }

    #[derive(Clone, Copy)]
    enum OracleVm {
        Tree,
        Control,
    }

    #[derive(Debug, PartialEq, Eq)]
    struct RuntimeOracleOutput {
        stdout: String,
        results: Vec<String>,
    }

    fn assert_legacy_and_finalize_match_without_std(case: RuntimeOracleCase) {
        assert_legacy_and_finalize_match_without_std_on_vm(case, OracleVm::Tree);
    }

    fn assert_legacy_and_finalize_match_without_std_on_vm(case: RuntimeOracleCase, vm: OracleVm) {
        let module = runtime_module_from_source_without_std(case.source);
        assert_legacy_and_finalize_match_module(case.name, module, vm);
    }

    fn assert_legacy_and_finalize_match_with_std_dependency_cache(case: RuntimeOracleCase) {
        assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(case, OracleVm::Tree);
    }

    fn assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(
        case: RuntimeOracleCase,
        vm: OracleVm,
    ) {
        let source = playground_source(case.source);
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&source);
            assert_legacy_and_finalize_match_module(case.name, cached.module, vm);
        });
    }

    fn example_oracle_cases() -> [RuntimeOracleCase; 12] {
        [
            RuntimeOracleCase {
                name: "01_struct_with",
                source: include_str!("../../../examples/01_struct_with.yu"),
            },
            RuntimeOracleCase {
                name: "03_for_last",
                source: include_str!("../../../examples/03_for_last.yu"),
            },
            RuntimeOracleCase {
                name: "04_sub_return",
                source: include_str!("../../../examples/04_sub_return.yu"),
            },
            RuntimeOracleCase {
                name: "05_undet_all",
                source: include_str!("../../../examples/05_undet_all.yu"),
            },
            RuntimeOracleCase {
                name: "06_undet_once",
                source: include_str!("../../../examples/06_undet_once.yu"),
            },
            RuntimeOracleCase {
                name: "07_junction",
                source: include_str!("../../../examples/07_junction.yu"),
            },
            RuntimeOracleCase {
                name: "08_types",
                source: include_str!("../../../examples/08_types.yu"),
            },
            RuntimeOracleCase {
                name: "09_optional_record_args",
                source: include_str!("../../../examples/09_optional_record_args.yu"),
            },
            RuntimeOracleCase {
                name: "10_effect_handler",
                source: include_str!("../../../examples/10_effect_handler.yu"),
            },
            RuntimeOracleCase {
                name: "11_attached_impl",
                source: include_str!("../../../examples/11_attached_impl.yu"),
            },
            RuntimeOracleCase {
                name: "12_cast",
                source: include_str!("../../../examples/12_cast.yu"),
            },
            RuntimeOracleCase {
                name: "13_console",
                source: include_str!("../../../examples/13_console.yu"),
            },
        ]
    }

    fn assert_legacy_and_finalize_match_module(name: &str, module: Module, vm: OracleVm) {
        let legacy = run_legacy_runtime_module(name, module.clone(), vm);
        let finalized = run_finalize_runtime_module(name, module, vm);
        assert_eq!(finalized, legacy, "{name}");
    }

    fn run_legacy_runtime_module(name: &str, module: Module, vm: OracleVm) -> RuntimeOracleOutput {
        let module = yulang_runtime::monomorphize_module(module)
            .unwrap_or_else(|error| panic!("{name} legacy monomorphize failed: {error}"));
        assert_mainline_runtime_output_valid(name, "legacy", &module);
        run_vm_module(name, "legacy", module, vm)
    }

    fn run_finalize_runtime_module(
        name: &str,
        module: Module,
        vm: OracleVm,
    ) -> RuntimeOracleOutput {
        let output = finalize_module(module)
            .unwrap_or_else(|error| panic!("{name} finalize failed: {error:?}"));
        assert_mainline_runtime_output_valid(name, "finalize", &output.module);
        run_vm_module(name, "finalize", output.module, vm)
    }

    fn assert_mainline_runtime_output_valid(name: &str, runtime: &str, module: &Module) {
        yulang_runtime::check_runtime_invariants(
            module,
            yulang_runtime::RuntimeStage::Monomorphized,
        )
        .unwrap_or_else(|error| {
            panic!("{name} {runtime} monomorphized runtime invariant failed: {error}")
        });
        yulang_runtime::validate_module(module)
            .unwrap_or_else(|error| panic!("{name} {runtime} runtime validation failed: {error}"));
    }

    fn run_vm_module(
        name: &str,
        runtime: &str,
        module: Module,
        vm: OracleVm,
    ) -> RuntimeOracleOutput {
        match vm {
            OracleVm::Tree => run_tree_vm_module(name, runtime, module),
            OracleVm::Control => run_control_vm_module(name, runtime, module),
        }
    }

    fn run_tree_vm_module(name: &str, runtime: &str, module: Module) -> RuntimeOracleOutput {
        let module = yulang_vm::compile_vm_module(module)
            .unwrap_or_else(|error| panic!("{name} {runtime} VM compile failed: {error:?}"));
        let host_output = yulang_vm::eval_roots_with_basic_host(&module)
            .unwrap_or_else(|error| panic!("{name} {runtime} VM eval failed: {error:?}"));
        RuntimeOracleOutput {
            stdout: host_output.stdout,
            results: host_output.results.iter().map(format_vm_result).collect(),
        }
    }

    fn run_control_vm_module(name: &str, runtime: &str, module: Module) -> RuntimeOracleOutput {
        let module = yulang_vm::compile_control_vm_module(module).unwrap_or_else(|error| {
            panic!("{name} {runtime} control VM compile failed: {error:?}")
        });
        let mut stdout = String::new();
        let mut results = Vec::with_capacity(module.root_count());
        for index in 0..module.root_count() {
            let (result, _) = module
                .eval_root_expr_with_basic_host_profiled(index, &mut stdout)
                .unwrap_or_else(|error| {
                    panic!("{name} {runtime} control VM eval failed: {error:?}")
                });
            results.push(format_vm_result(&result));
        }
        RuntimeOracleOutput { stdout, results }
    }

    struct PlaygroundCase {
        name: &'static str,
        source: &'static str,
        stdout: &'static str,
        results: &'static [&'static str],
    }

    fn assert_playground_case_finalizes(case: PlaygroundCase) {
        let source = playground_source(case.source);
        assert_std_source_finalizes_to_results_owned(case.name, source, case.stdout, case.results);
    }

    fn assert_std_source_no_cache_finalizes_to_results(case: PlaygroundCase) {
        let source = case.source.to_string();
        run_with_large_stack(move || {
            let module = runtime_module_from_source_with_std_no_cache(&source);
            let output = finalize_module(module)
                .unwrap_or_else(|error| panic!("{} finalize failed: {error:?}", case.name));
            let vm = yulang_vm::compile_vm_module(output.module)
                .unwrap_or_else(|error| panic!("{} VM compile failed: {error:?}", case.name));
            let host_output = yulang_vm::eval_roots_with_basic_host(&vm)
                .unwrap_or_else(|error| panic!("{} VM eval failed: {error:?}", case.name));
            let actual = host_output
                .results
                .iter()
                .map(format_vm_result)
                .collect::<Vec<_>>();
            assert_eq!(host_output.stdout, case.stdout, "{} stdout", case.name);
            assert_eq!(actual, case.results, "{} roots", case.name);
        });
    }

    fn assert_std_source_finalizes_to_results_owned(
        name: &'static str,
        source: String,
        stdout: &'static str,
        results: &'static [&'static str],
    ) {
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&source);
            let output = finalize_module(cached.module)
                .unwrap_or_else(|error| panic!("{name} finalize failed: {error:?}"));
            let vm = yulang_vm::compile_vm_module(output.module)
                .unwrap_or_else(|error| panic!("{name} VM compile failed: {error:?}"));
            let host_output = yulang_vm::eval_roots_with_basic_host(&vm)
                .unwrap_or_else(|error| panic!("{name} VM eval failed: {error:?}"));
            let actual = host_output
                .results
                .iter()
                .map(format_vm_result)
                .collect::<Vec<_>>();
            assert_eq!(host_output.stdout, stdout, "{name} stdout");
            assert_eq!(actual, results, "{name} roots");
        });
    }

    fn playground_source(source: &str) -> String {
        format!("use std::undet::*\n{source}")
    }

    fn playground_tour_source() -> &'static str {
        r#"// A compact tour of Yulang's current shape.

use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

my inflate({base = 1, extra = base + 1}) = base + extra

inflate { base: 3 }

{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
"#
    }

    fn format_vm_result(result: &yulang_vm::VmResult) -> String {
        match result {
            yulang_vm::VmResult::Value(value) => format_vm_value(value),
            yulang_vm::VmResult::Request(request) => format!("<request {:?}>", request.effect),
        }
    }

    fn format_vm_value(value: &yulang_vm::VmValue) -> String {
        match value {
            yulang_vm::VmValue::Int(value) | yulang_vm::VmValue::Float(value) => value.clone(),
            yulang_vm::VmValue::String(value) => format!("{:?}", value.to_flat_string()),
            yulang_vm::VmValue::Bool(value) => value.to_string(),
            yulang_vm::VmValue::Unit => "()".to_string(),
            yulang_vm::VmValue::List(items) => {
                let mut out = String::from("[");
                format_vm_list_items(&mut out, items);
                out.push(']');
                out
            }
            yulang_vm::VmValue::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|value| format_vm_value(value))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            yulang_vm::VmValue::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|(name, value)| format!("{}: {}", name.0, format_vm_value(value)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{fields}}}")
            }
            yulang_vm::VmValue::Variant { tag, value } => match value {
                Some(value) => format!("{} {}", tag.0, format_vm_value(value)),
                None => tag.0.clone(),
            },
            yulang_vm::VmValue::Bytes(value) => format!("<bytes len={}>", value.len()),
            yulang_vm::VmValue::Path(value) => format!("{:?}", value.display().to_string()),
            yulang_vm::VmValue::FileHandle(_) => "<file>".to_string(),
            yulang_vm::VmValue::EffectOp(path) => format!("<effect-op {path:?}>"),
            yulang_vm::VmValue::PrimitiveOp(_) => "<primitive>".to_string(),
            yulang_vm::VmValue::Resume(_) => "<resume>".to_string(),
            yulang_vm::VmValue::Closure(_) => "<closure>".to_string(),
            yulang_vm::VmValue::Thunk(_) => "<thunk>".to_string(),
            yulang_vm::VmValue::EffectId(id) => format!("<effect-id {id}>"),
        }
    }

    fn format_vm_list_items(
        out: &mut String,
        items: &yulang_vm::runtime::list_tree::ListTree<std::rc::Rc<yulang_vm::VmValue>>,
    ) {
        match items {
            yulang_vm::runtime::list_tree::ListTree::Empty => {}
            yulang_vm::runtime::list_tree::ListTree::Leaf(value) => {
                out.push_str(&format_vm_value(value));
            }
            yulang_vm::runtime::list_tree::ListTree::Node(node) => {
                format_vm_list_items(out, &node.left);
                if !node.left.is_empty() && !node.right.is_empty() {
                    out.push_str(", ");
                }
                format_vm_list_items(out, &node.right);
            }
        }
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

    fn poly_return_binding() -> Binding {
        Binding {
            name: path("poly_return"),
            type_params: vec![typed_ir::TypeVar("a".into()), typed_ir::TypeVar("b".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("b".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
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

    fn runtime_module_from_source_with_std_no_cache(src: &str) -> Module {
        let std_root = yulang_sources::resolve_or_install_std_root(None, None)
            .expect("resolve installed std root")
            .expect("installed std root should be available");
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            src,
            None,
            yulang_infer::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap();
        let program = yulang_infer::export_core_program(&mut lowered.state);
        yulang_runtime::lower_core_program(program).unwrap()
    }

    fn runtime_module_from_source_with_std_dependency_cache_large_stack(
        src: &str,
    ) -> yulang_compile::CachedRuntimeIrModule {
        let src = src.to_string();
        run_with_large_stack(move || {
            let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            // Compiled dependency artifacts carry format/source hashes, so a
            // stable test root can reuse valid std cache across cargo runs
            // while read errors still fall back to warming this same cache.
            let cache_paths = yulang_compile::YulangCachePaths::with_user_cache_root(
                &repo_root,
                persistent_artifact_cache_root(&repo_root, "std-runtime-ir"),
            );
            let std_root = yulang_sources::resolve_or_install_std_root(None, None)
                .expect("resolve installed std root")
                .expect("installed std root should be available");
            let options = yulang_compile::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            };
            let _guard = std_runtime_ir_cache_lock()
                .lock()
                .expect("lock std runtime IR dependency cache");

            if let Ok(cached) =
                yulang_compile::runtime_ir_module_from_virtual_source_with_dependency_cache_read_only(
                    &src,
                    None,
                    options.clone(),
                    &cache_paths,
                )
            {
                return cached;
            }

            yulang_compile::runtime_ir_module_from_virtual_source_with_dependency_cache(
                &src,
                None,
                options,
                &cache_paths,
            )
            .expect("lower std runtime IR with dependency cache fallback")
        })
    }

    fn runtime_module_from_source_with_cold_std_dependency_cache_large_stack(
        src: &str,
        cache_name: &str,
    ) -> yulang_compile::CachedRuntimeIrModule {
        let src = src.to_string();
        let cache_name = cache_name.to_string();
        run_with_large_stack(move || {
            let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            let cache_root = artifact_cache_root(&cache_name);
            let _ = std::fs::remove_dir_all(&cache_root);
            let cache_paths =
                yulang_compile::YulangCachePaths::with_user_cache_root(&repo_root, &cache_root);
            let std_root = yulang_sources::resolve_or_install_std_root(None, None)
                .expect("resolve installed std root")
                .expect("installed std root should be available");
            let options = yulang_compile::SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            };
            let cached =
                yulang_compile::runtime_ir_module_from_virtual_source_with_dependency_cache(
                    &src,
                    None,
                    options,
                    &cache_paths,
                )
                .expect("lower std runtime IR with cold dependency cache");
            let _ = std::fs::remove_dir_all(&cache_root);
            cached
        })
    }

    fn std_runtime_ir_cache_lock() -> &'static std::sync::Mutex<()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        if std::thread::current().name() == Some("runtime-finalize-large-stack") {
            return f();
        }
        let _guard = large_stack_test_lock()
            .lock()
            .expect("lock runtime-finalize large-stack test");
        std::thread::Builder::new()
            .name("runtime-finalize-large-stack".into())
            .stack_size(512 * 1024 * 1024)
            .spawn(f)
            .expect("spawn large-stack runtime-finalize test thread")
            .join()
            .expect("large-stack runtime-finalize test panicked")
    }

    fn large_stack_test_lock() -> &'static std::sync::Mutex<()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    fn artifact_cache_root(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "yulang-finalize-cache-{name}-{}",
            std::process::id()
        ))
    }

    fn persistent_artifact_cache_root(
        repo_root: &std::path::Path,
        name: &str,
    ) -> std::path::PathBuf {
        repo_root.join("target/yulang/test-cache").join(name)
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
