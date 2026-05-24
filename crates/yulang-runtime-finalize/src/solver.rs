use std::collections::{BTreeSet, HashMap, HashSet};

use yulang_runtime_ir::{Binding, Expr, ExprKind, Module, Root, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{
    CachedFinalizeInstance, FinalizeDiagnostic, FinalizeInstanceCache, FinalizeInstanceKey,
    FinalizeMonomorphizeError, FinalizeOutput, FinalizeReport, FinalizeResult, RootGraphInput,
    RootGraphSolution, TypeGraph,
    graph::{runtime_type_from_core_value, runtime_type_from_core_value_and_effect},
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
    let mut root_graph_solutions = solve_root_graphs(&module)?;
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
        collect_root_expr_graphs(&module, &mut root_graph_solutions)?;
        let scan_targets =
            next_binding_body_scan_targets(&module, &emitted, &mut scanned_binding_bodies);
        collect_binding_body_graphs(&module, &scan_targets, &mut root_graph_solutions)?;
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

pub fn solve_root_graphs(module: &Module) -> FinalizeResult<Vec<RootGraphSolution>> {
    let mut solutions = Vec::new();
    collect_root_expr_graphs(module, &mut solutions)?;
    Ok(solutions)
}

fn collect_root_expr_graphs(
    module: &Module,
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
            &HashMap::new(),
            solutions,
        )?;
    }
    Ok(())
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
    let mut apply_effect_vars = BTreeSet::new();
    for step in &spine.steps {
        let result = graph.fresh_hole("apply");
        let result_effect = graph.fresh_hole("apply_effect");
        if let typed_ir::Type::Var(var) = &result_effect {
            apply_effect_vars.insert(var.clone());
        }
        let (arg_type, arg_effect) = step.arg_type_and_effect(local_types);
        let expected = typed_ir::Type::Fun {
            param: Box::new(arg_type),
            param_effect: Box::new(arg_effect),
            ret_effect: Box::new(result_effect.clone()),
            ret: Box::new(result.clone()),
        };
        graph.constrain_subtype(current, expected)?;
        step.constrain_result_bounds(&mut graph, result.clone(), result_effect, local_types)?;
        current = result;
    }
    graph.default_unbound_lower(principal.effect_only_type_params(), typed_ir::Type::Never)?;
    graph.default_unbound_lower(apply_effect_vars, typed_ir::Type::Never)?;
    let graph = graph.solve();
    if !graph.is_complete() {
        if role_required_apply_waiting_for_arguments(binding, &spine, local_types) {
            return Ok(solutions);
        }
        return Err(FinalizeDiagnostic::IncompleteGraph {
            binding: binding_path.clone(),
        });
    }
    let callee_type = solved_callee_runtime_type(binding, &principal, &graph);
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
        runtime_type_from_core_value(graph.materialize_core(result))
    }
}

fn solved_callee_runtime_type(
    binding: &Binding,
    principal: &crate::PrincipalInstance,
    graph: &crate::GraphSolution,
) -> RuntimeType {
    let materialized = materialize_runtime_type(
        binding.body.ty.clone(),
        &principal.original_substitutions(graph),
    );
    if runtime_type_is_closed(&materialized) {
        materialized
    } else {
        runtime_type_from_core_value(graph.materialize_core(principal.principal_type.clone()))
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
        match expr_lower_type(self.apply, local_types) {
            RuntimeType::Unknown => Ok(()),
            RuntimeType::Thunk { effect, value } => {
                if !(evidence_value_bound && runtime_type_value_is_function(&value)) {
                    graph.constrain_subtype(result, runtime_type_to_core(*value))?;
                }
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

fn runtime_type_value_is_function(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Fun { .. } | RuntimeType::Core(typed_ir::Type::Fun { .. }) => true,
        RuntimeType::Thunk { value, .. } => runtime_type_value_is_function(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => false,
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
    module
        .role_impls
        .iter()
        .flat_map(|role_impl| {
            role_impl.members.iter().filter_map(|member| {
                let binding = bindings.get(&member.value)?;
                Some(RoleMethodCandidate {
                    role: role_impl.role.clone(),
                    member: member.name.clone(),
                    value: member.value.clone(),
                    inputs: role_impl.inputs.clone(),
                    callee_type: runtime_type_from_core_value(binding.scheme.body.clone()),
                })
            })
        })
        .collect()
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
    for candidate in candidates
        .iter()
        .filter(|candidate| candidate.role == role && candidate.member == member)
    {
        let Some(score) = role_method_candidate_score(candidate, &receiver_types) else {
            continue;
        };
        if best
            .as_ref()
            .is_none_or(|(best_score, _): &(usize, &RoleMethodCandidate)| score > *best_score)
        {
            best = Some((score, candidate));
        }
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
        let Some(score) = role_method_candidate_score(candidate, &receiver_types) else {
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
) -> Option<usize> {
    let receiver_bounds = candidate.inputs.first()?;
    receiver_types
        .iter()
        .filter_map(|receiver_ty| type_bounds_match_score(receiver_bounds, receiver_ty))
        .max()
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

        let solutions = solve_root_graphs(&module).unwrap();

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

        assert!(cached.dependency_cache_hit);
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
    fn cached_std_control_vm_legacy_runtime_and_finalize_match_examples() {
        for case in control_vm_example_oracle_cases() {
            assert_legacy_and_finalize_match_with_std_dependency_cache_on_vm(
                case,
                OracleVm::Control,
            );
        }
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

    fn control_vm_example_oracle_cases() -> [RuntimeOracleCase; 12] {
        // showcase is covered by the finalize/VM-input gate above; the control
        // VM currently overflows its own execution stack on that full tour.
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
        run_with_large_stack(move || {
            let cached = runtime_module_from_source_with_std_dependency_cache_large_stack(&source);
            let output = finalize_module(cached.module)
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

    fn runtime_module_from_source_with_std_dependency_cache_large_stack(
        src: &str,
    ) -> yulang_compile::CachedRuntimeIrModule {
        let src = src.to_string();
        run_with_large_stack(move || {
            let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
            // Keep std dependency-cache coverage without trusting artifacts from
            // a developer's long-lived cache across solver/runtime changes.
            let cache_paths = yulang_compile::YulangCachePaths::with_user_cache_root(
                &repo_root,
                artifact_cache_root("std-runtime-ir"),
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
                options.clone(),
                &cache_paths,
            )
            .expect("warm std compiled dependency cache");

            yulang_compile::runtime_ir_module_from_virtual_source_with_dependency_cache_read_only(
                &src,
                None,
                options,
                &cache_paths,
            )
            .expect("read warmed std compiled dependency cache")
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
