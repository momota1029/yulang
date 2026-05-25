//! Whole-module post-passes and shared runtime-type-shape helpers.
//!
//! After the main loop converges, these finishing passes run once each on the
//! whole module:
//!
//!   - `normalize_materialized_module` — runs `materialize_expr` with an empty
//!     substitution to canonicalize already-materialized types.
//!   - `monomorphize_phantom_nullary_variant_bindings` — special-case for
//!     `Variant`-returning nullary lambdas whose type parameters are phantom.
//!   - `fill_local_var_types` / `fill_apply_evidence_types` — repair Unknown
//!     slots that lowering left in `.ty` of expressions, by walking enclosing
//!     scope (`fill_local_var_types_in`) and reconciling apply triples
//!     (`reconcile_apply_triple`).
//!   - `prune_specialized_polymorphic_bindings` / `prune_unbound_binding_roots`
//!     — drop bindings made dead by monomorphization
//!     (`reachable_paths`, `collect_expr_paths`).
//!
//! It also hosts the runtime-type-shape predicates and surgery helpers shared
//! across all solver submodules: `runtime_type_has_unknown`,
//! `runtime_type_is_closed`, `core_type_is_closed`, `runtime_fun_split`,
//! `merge_partial_runtime_type`, `narrow_runtime_type_in_place`,
//! `restore_runtime_effect_boundaries`, `refine_runtime_spine_return`, and
//! various effect/never/function probes used by both apply-spine resolution
//! and apply-evidence reconciliation.

use std::collections::{HashMap, HashSet};

use yulang_runtime_ir::{Binding, Expr, ExprKind, Module, Root, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{
    RootGraphSolution,
    graph::should_thunk_effect,
    materialize_core_type,
};

use super::{apply_spine::ApplyStep, materialize, role};

pub(crate) fn normalize_materialized_module(module: &mut Module) {
    let substitutions = [];
    let reachable = reachable_paths(module);
    for binding in &mut module.bindings {
        if reachable.contains(&binding.name) {
            materialize::materialize_expr_in_place(&mut binding.body, &substitutions);
        }
    }
    for expr in &mut module.root_exprs {
        materialize::materialize_expr_in_place(expr, &substitutions);
    }
}

pub(crate) fn monomorphize_phantom_nullary_variant_bindings(module: &mut Module) {
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
        materialize::materialize_expr_in_place(&mut binding.body, &substitutions);
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
pub(crate) fn fill_apply_evidence_types(module: &mut Module) {
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
    yulang_runtime_ir::walk::walk_children_mut(expr, fill_apply_evidence_in);
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

pub(crate) fn runtime_type_has_unknown(ty: &RuntimeType) -> bool {
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

pub(crate) fn core_type_has_unknown(ty: &typed_ir::Type) -> bool {
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
pub(crate) fn fill_local_var_types(module: &mut Module) {
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

pub(crate) fn restore_runtime_effect_boundaries(base: RuntimeType, principal: &RuntimeType) -> RuntimeType {
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
    role::core_subtype_match_score(&base, &principal).is_some()
        || role::core_subtype_match_score(&principal, &base).is_some()
}

pub(crate) fn restore_apply_spine_arg_effects(
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
    if role::core_subtype_match_score(&arg_value, &param_value).is_none()
        && role::core_subtype_match_score(&param_value, &arg_value).is_none()
    {
        return param;
    }
    RuntimeType::Thunk {
        effect: arg_effect,
        value: Box::new(param),
    }
}

pub(crate) fn runtime_spine_return(callee: &RuntimeType, arity: usize) -> Option<RuntimeType> {
    if arity == 0 {
        return Some(callee.clone());
    }
    let RuntimeType::Fun { ret, .. } = callee else {
        return None;
    };
    runtime_spine_return(ret, arity - 1)
}

pub(crate) fn refine_runtime_spine_return(
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


pub(crate) fn runtime_type_to_core(ty: RuntimeType) -> typed_ir::Type {
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

pub(crate) fn runtime_function_param(ty: &RuntimeType) -> Option<RuntimeType> {
    let RuntimeType::Fun { param, .. } = ty else {
        return None;
    };
    Some((**param).clone())
}

pub(crate) fn path_from_name(name: &typed_ir::Name) -> typed_ir::Path {
    typed_ir::Path::from_name(name.clone())
}


/// Replace `Unknown` components of `target` with the more concrete `source`.
/// Preserves any structure `target` already has when `source` doesn't refine it.
pub(crate) fn narrow_runtime_type_in_place(target: &mut RuntimeType, source: &RuntimeType) {
    if !runtime_type_has_unknown(target) {
        return;
    }
    if !runtime_type_has_unknown(source) {
        *target = source.clone();
        return;
    }
    match (target, source) {
        (RuntimeType::Fun { param: tp, ret: tr }, RuntimeType::Fun { param: sp, ret: sr }) => {
            narrow_runtime_type_in_place(tp, sp);
            narrow_runtime_type_in_place(tr, sr);
        }
        (
            RuntimeType::Thunk {
                effect: te,
                value: tv,
            },
            RuntimeType::Thunk {
                effect: se,
                value: sv,
            },
        ) => {
            if matches!(te, typed_ir::Type::Unknown) {
                *te = se.clone();
            }
            narrow_runtime_type_in_place(tv, sv);
        }
        (RuntimeType::Core(t), RuntimeType::Core(s)) => {
            narrow_core_type_in_place(t, s);
        }
        _ => {}
    }
}

fn narrow_core_type_in_place(target: &mut typed_ir::Type, source: &typed_ir::Type) {
    use typed_ir::Type;
    if matches!(target, Type::Unknown) {
        *target = source.clone();
        return;
    }
    match (target, source) {
        (Type::Tuple(t_items), Type::Tuple(s_items)) if t_items.len() == s_items.len() => {
            for (t, s) in t_items.iter_mut().zip(s_items.iter()) {
                narrow_core_type_in_place(t, s);
            }
        }
        (
            Type::Named {
                path: t_path,
                args: t_args,
            },
            Type::Named {
                path: s_path,
                args: s_args,
            },
        ) if t_path == s_path && t_args.len() == s_args.len() => {
            for (t_arg, s_arg) in t_args.iter_mut().zip(s_args.iter()) {
                if let (typed_ir::TypeArg::Type(t), typed_ir::TypeArg::Type(s)) = (t_arg, s_arg) {
                    narrow_core_type_in_place(t, s);
                }
            }
        }
        (
            Type::Fun {
                param: tp,
                ret: tr,
                param_effect: tpe,
                ret_effect: tre,
            },
            Type::Fun {
                param: sp,
                ret: sr,
                param_effect: spe,
                ret_effect: sre,
            },
        ) => {
            narrow_core_type_in_place(tp, sp);
            narrow_core_type_in_place(tr, sr);
            if matches!(**tpe, Type::Unknown) {
                **tpe = (**spe).clone();
            }
            if matches!(**tre, Type::Unknown) {
                **tre = (**sre).clone();
            }
        }
        _ => {}
    }
}

pub(crate) fn prune_specialized_polymorphic_bindings(module: &mut Module, solutions: &[RootGraphSolution]) {
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

pub(crate) fn prune_unbound_binding_roots(module: &mut Module) {
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

pub(crate) fn reachable_paths(module: &Module) -> HashSet<typed_ir::Path> {
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

fn collect_expr_paths(expr: &Expr, paths: &mut Vec<typed_ir::Path>) {
    if let ExprKind::Var(path) | ExprKind::EffectOp(path) = &expr.kind {
        paths.push(path.clone());
    }
    yulang_runtime_ir::walk::walk_children(expr, |child| collect_expr_paths(child, paths));
}

pub(crate) fn runtime_type_is_closed(ty: &RuntimeType) -> bool {
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

pub(crate) fn unit_type() -> typed_ir::Type {
    typed_ir::Type::Named {
        path: typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
        args: Vec::new(),
    }
}

pub(crate) fn core_type_is_closed(ty: &yulang_typed_ir::Type) -> bool {
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
