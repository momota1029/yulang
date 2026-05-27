//! Whole-module post-passes and shared runtime-type-shape helpers.
//!
//! After the main loop converges, these finishing passes run once each on the
//! whole module:
//!
//!   - `normalize_materialized_module` — runs `materialize_expr` with an empty
//!     substitution to canonicalize already-materialized types.
//!   - `monomorphize_phantom_nullary_variant_bindings` — special-case for
//!     `Variant`-returning nullary lambdas whose type parameters are phantom.
//!   - `inline_small_direct_calls` — beta-reduces direct calls to tiny
//!     forwarding lambda bindings while preserving single evaluation of the
//!     argument.
//!   - `eliminate_immediate_thunk_forces` — removes direct
//!     `BindHere(Thunk(body))` pairs after materialization has made the
//!     thunk/value boundary explicit.
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
//! `refine_runtime_spine_return`, and various effect/never/function probes
//! used by both apply-spine resolution and apply-evidence reconciliation.

use std::collections::{HashMap, HashSet};

use yulang_runtime_ir::{
    FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
    FinalizedModule as Module, FinalizedPattern as Pattern, FinalizedStmt as Stmt, Root,
    RuntimeType,
};
use yulang_typed_ir as typed_ir;

use crate::{RootGraphSolution, graph::should_thunk_effect, materialize_core_type};

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

const SMALL_DIRECT_CALL_INLINE_NODE_LIMIT: usize = 10;

pub(crate) fn inline_small_direct_calls(module: &mut Module) {
    let candidates = small_direct_call_candidates(module);
    if candidates.is_empty() {
        return;
    }
    for binding in &mut module.bindings {
        inline_small_direct_calls_in(&mut binding.body, &candidates);
    }
    for expr in &mut module.root_exprs {
        inline_small_direct_calls_in(expr, &candidates);
    }
}

#[derive(Clone)]
struct InlineCandidate {
    param: typed_ir::Name,
    body: Expr,
}

fn small_direct_call_candidates(module: &Module) -> HashMap<typed_ir::Path, InlineCandidate> {
    let binding_paths = module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    module
        .bindings
        .iter()
        .filter_map(|binding| {
            let ExprKind::Lambda { param, body, .. } = &binding.body.kind else {
                return None;
            };
            let param_path = path_from_name(param);
            if forwarding_wrapper_cost(body, &param_path)? > SMALL_DIRECT_CALL_INLINE_NODE_LIMIT {
                return None;
            }
            let mut referenced = Vec::new();
            collect_expr_paths(body, &binding_paths, &mut HashSet::new(), &mut referenced);
            if referenced.iter().any(|path| path == &binding.name) {
                return None;
            }
            Some((
                binding.name.clone(),
                InlineCandidate {
                    param: param.clone(),
                    body: (**body).clone(),
                },
            ))
        })
        .collect()
}

fn forwarding_wrapper_cost(expr: &Expr, param_path: &typed_ir::Path) -> Option<usize> {
    match &expr.kind {
        ExprKind::Apply { callee, arg, .. } => (matches!(&callee.kind, ExprKind::Var(_))
            && expr_is_var_path(arg, param_path))
        .then_some(1),
        ExprKind::Block { stmts, tail } => {
            if !stmts
                .iter()
                .all(|stmt| is_param_alias_let(stmt, param_path))
            {
                return None;
            }
            let tail = tail.as_deref()?;
            Some(1 + stmts.len() + forwarding_wrapper_cost(tail, param_path)?)
        }
        _ => None,
    }
}

fn is_param_alias_let(stmt: &Stmt, param_path: &typed_ir::Path) -> bool {
    let Stmt::Let { pattern, value } = stmt else {
        return false;
    };
    matches!(pattern, Pattern::Bind { .. }) && expr_is_var_path(value, param_path)
}

fn expr_is_var_path(expr: &Expr, expected: &typed_ir::Path) -> bool {
    matches!(&expr.kind, ExprKind::Var(path) if path == expected)
}

fn inline_small_direct_calls_in(
    expr: &mut Expr,
    candidates: &HashMap<typed_ir::Path, InlineCandidate>,
) {
    yulang_runtime_ir::walk::walk_children_mut(expr, |child| {
        inline_small_direct_calls_in(child, candidates);
    });
    let ExprKind::Apply {
        callee,
        arg,
        instantiation,
        ..
    } = &mut expr.kind
    else {
        return;
    };
    let ExprKind::Var(path) = &callee.kind else {
        return;
    };
    let Some(candidate) = candidates.get(path) else {
        return;
    };
    let mut body = candidate.body.clone();
    if let Some(instantiation) = instantiation
        && instantiation.target == *path
    {
        let substitutions = instantiation
            .args
            .iter()
            .map(|subst| typed_ir::TypeSubstitution {
                var: subst.var.clone(),
                ty: subst.ty.clone(),
            })
            .collect::<Vec<_>>();
        materialize::materialize_expr_in_place(&mut body, &substitutions);
    }
    let param_ty = runtime_function_param(&callee.ty).unwrap_or_else(|| arg.ty.clone());
    let result_ty = expr.ty.clone();
    let arg = (**arg).clone();
    *expr = Expr::typed(
        ExprKind::Block {
            stmts: vec![Stmt::Let {
                pattern: Pattern::Bind {
                    name: candidate.param.clone(),
                    ty: param_ty,
                },
                value: arg,
            }],
            tail: Some(Box::new(body)),
        },
        result_ty,
    );
}

pub(crate) fn eliminate_immediate_thunk_forces(module: &mut Module) {
    for binding in &mut module.bindings {
        eliminate_immediate_thunk_forces_in(&mut binding.body);
    }
    for expr in &mut module.root_exprs {
        eliminate_immediate_thunk_forces_in(expr);
    }
}

fn eliminate_immediate_thunk_forces_in(expr: &mut Expr) {
    yulang_runtime_ir::walk::walk_children_mut(expr, eliminate_immediate_thunk_forces_in);

    let ExprKind::BindHere { expr: thunk } = &mut expr.kind else {
        return;
    };
    let RuntimeType::Thunk { value, .. } = &thunk.ty else {
        return;
    };
    let Some(result_ty) = merge_force_result_type(&expr.ty, value) else {
        return;
    };
    let ExprKind::Thunk {
        effect,
        value: declared_value,
        expr: body,
    } = &mut thunk.kind
    else {
        return;
    };
    let Some(result_ty) = merge_force_result_type(&result_ty, declared_value) else {
        return;
    };
    let Some(result_ty) = merge_force_result_type(&result_ty, &body.ty) else {
        return;
    };
    if !effect_is_empty_row(effect) || !immediate_thunk_body_is_context_free(body) {
        return;
    }

    let mut body = (**body).clone();
    body.ty = result_ty;
    *expr = body;
}

fn immediate_thunk_body_is_context_free(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lit(_) => true,
        ExprKind::Tuple(items) => items.iter().all(immediate_thunk_body_is_context_free),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .all(|field| immediate_thunk_body_is_context_free(&field.value))
                && spread
                    .as_ref()
                    .is_none_or(immediate_thunk_record_spread_is_context_free)
        }
        ExprKind::Variant { value, .. } => value
            .as_deref()
            .is_none_or(immediate_thunk_body_is_context_free),
        ExprKind::Select { base, .. } | ExprKind::Coerce { expr: base, .. } => {
            immediate_thunk_body_is_context_free(base)
        }
        ExprKind::Pack { expr, .. } => immediate_thunk_body_is_context_free(expr),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lambda { .. }
        | ExprKind::Apply { .. }
        | ExprKind::If { .. }
        | ExprKind::Match { .. }
        | ExprKind::Block { .. }
        | ExprKind::Handle { .. }
        | ExprKind::BindHere { .. }
        | ExprKind::Thunk { .. }
        | ExprKind::LocalPushId { .. }
        | ExprKind::PeekId
        | ExprKind::FindId { .. }
        | ExprKind::AddId { .. } => false,
    }
}

fn immediate_thunk_record_spread_is_context_free(
    spread: &yulang_runtime_ir::FinalizedRecordSpreadExpr,
) -> bool {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
        | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
            immediate_thunk_body_is_context_free(expr)
        }
    }
}

fn effect_is_empty_row(effect: &typed_ir::Type) -> bool {
    matches!(
        effect,
        typed_ir::Type::Row { items, tail }
            if items.is_empty() && matches!(tail.as_ref(), typed_ir::Type::Never)
    )
}

fn merge_force_result_type(left: &RuntimeType, right: &RuntimeType) -> Option<RuntimeType> {
    match (left, right) {
        (RuntimeType::Unknown, _) => Some(right.clone()),
        (_, RuntimeType::Unknown) => Some(left.clone()),
        (left, right) if runtime_types_equivalent(left, right) => Some(left.clone()),
        (RuntimeType::Value(left), RuntimeType::Value(right)) => {
            Some(RuntimeType::Value(merge_partial_core_type(left, right)?))
        }
        (
            RuntimeType::Fun {
                param: left_param,
                ret: left_ret,
            },
            RuntimeType::Fun {
                param: right_param,
                ret: right_ret,
            },
        ) => Some(RuntimeType::Fun {
            param: Box::new(merge_force_result_type(left_param, right_param)?),
            ret: Box::new(merge_force_result_type(left_ret, right_ret)?),
        }),
        (
            RuntimeType::Thunk {
                effect: left_effect,
                value: left_value,
            },
            RuntimeType::Thunk {
                effect: right_effect,
                value: right_value,
            },
        ) => Some(RuntimeType::Thunk {
            effect: merge_partial_core_type(left_effect, right_effect)?,
            value: Box::new(merge_force_result_type(left_value, right_value)?),
        }),
        _ => None,
    }
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
            if !runtime_type_has_unknown(&param) && !runtime_types_equivalent(arg_ty, &param) {
                *arg_ty = param.clone();
                changed = true;
            }
            if !runtime_type_has_unknown(&ret) && !runtime_types_equivalent(apply_ty, &ret) {
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
        (RuntimeType::Value(ax), RuntimeType::Value(bx)) => {
            Some(RuntimeType::Value(merge_partial_core_type(ax, bx)?))
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
        (RuntimeType::Fun { .. }, RuntimeType::Value(typed_ir::Type::Fun { .. })) => {
            Some(a.clone())
        }
        (RuntimeType::Value(typed_ir::Type::Fun { .. }), RuntimeType::Fun { .. }) => {
            Some(b.clone())
        }
        (RuntimeType::Thunk { .. }, RuntimeType::Value(_)) => Some(a.clone()),
        (RuntimeType::Value(_), RuntimeType::Thunk { .. }) => Some(b.clone()),
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
        RuntimeType::Value(ty) => core_type_has_unknown(ty),
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
/// so we walk the finalized module here with a scoped name -> RuntimeType
/// table and patch `Var.ty == Unknown` references.
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
            if let Some(known) = scope
                .get(path)
                .or_else(|| bindings.get(path))
                .filter(|known| !runtime_type_has_unknown(known))
                && !runtime_types_equivalent(&expr.ty, known)
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
                    yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(e)
                    | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(e) => e,
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
                restore_pattern_scope_bindings(scope, added);
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut added = Vec::new();
            for stmt in stmts.iter_mut() {
                match stmt {
                    yulang_runtime_ir::FinalizedStmt::Let { pattern, value } => {
                        fill_local_var_types_in(value, scope, bindings);
                        added.extend(collect_pattern_scope_bindings(pattern, scope));
                    }
                    yulang_runtime_ir::FinalizedStmt::Expr(e) => {
                        fill_local_var_types_in(e, scope, bindings);
                    }
                    yulang_runtime_ir::FinalizedStmt::Module { body, .. } => {
                        fill_local_var_types_in(body, scope, bindings);
                    }
                }
            }
            if let Some(tail) = tail {
                fill_local_var_types_in(tail, scope, bindings);
            }
            restore_pattern_scope_bindings(scope, added);
        }
        ExprKind::Handle { body, arms, .. } => {
            fill_local_var_types_in(body, scope, bindings);
            for arm in arms {
                let mut added = collect_pattern_scope_bindings(&arm.payload, scope);
                if let Some(resume) = &arm.resume {
                    let resume_path = path_from_name(&resume.name);
                    if !runtime_type_has_unknown(&resume.ty) {
                        added.push(push_scoped_type(
                            scope,
                            resume_path.clone(),
                            resume.ty.clone(),
                        ));
                    }
                }
                if let Some(guard) = &mut arm.guard {
                    fill_local_var_types_in(guard, scope, bindings);
                }
                fill_local_var_types_in(&mut arm.body, scope, bindings);
                restore_pattern_scope_bindings(scope, added);
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

struct ScopedTypeBinding {
    path: typed_ir::Path,
    previous: Option<RuntimeType>,
}

fn collect_pattern_scope_bindings(
    pattern: &yulang_runtime_ir::FinalizedPattern,
    scope: &mut HashMap<typed_ir::Path, RuntimeType>,
) -> Vec<ScopedTypeBinding> {
    use yulang_runtime_ir::FinalizedPattern as Pattern;
    let mut added = Vec::new();
    match pattern {
        Pattern::Bind { name, ty } => {
            if !runtime_type_has_unknown(ty) {
                let path = path_from_name(name);
                added.push(push_scoped_type(scope, path, ty.clone()));
            }
        }
        Pattern::As { pattern, name, ty } => {
            if !runtime_type_has_unknown(ty) {
                let path = path_from_name(name);
                added.push(push_scoped_type(scope, path, ty.clone()));
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

fn push_scoped_type(
    scope: &mut HashMap<typed_ir::Path, RuntimeType>,
    path: typed_ir::Path,
    ty: RuntimeType,
) -> ScopedTypeBinding {
    let previous = scope.insert(path.clone(), ty);
    ScopedTypeBinding { path, previous }
}

fn restore_pattern_scope_bindings(
    scope: &mut HashMap<typed_ir::Path, RuntimeType>,
    added: Vec<ScopedTypeBinding>,
) {
    for binding in added.into_iter().rev() {
        match binding.previous {
            Some(previous) => {
                scope.insert(binding.path, previous);
            }
            None => {
                scope.remove(&binding.path);
            }
        }
    }
}

pub(crate) fn finalized_effect_boundaries_from_principal(
    base: RuntimeType,
    principal: &RuntimeType,
) -> RuntimeType {
    match (base, principal) {
        (
            RuntimeType::Fun { param, ret },
            RuntimeType::Fun {
                param: principal_param,
                ret: principal_ret,
            },
        ) => RuntimeType::Fun {
            param: Box::new(finalized_effect_boundaries_from_principal(
                *param,
                principal_param,
            )),
            ret: Box::new(finalized_effect_boundaries_from_principal(
                *ret,
                principal_ret,
            )),
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
            value: Box::new(finalized_effect_boundaries_from_principal(
                *value,
                principal_value,
            )),
        },
        (RuntimeType::Thunk { value, .. }, principal)
            if principal_can_drop_base_thunk(&principal)
                && finalized_effect_boundary_value_matches(&value, &principal) =>
        {
            finalized_effect_boundaries_from_principal(*value, &principal)
        }
        (
            base,
            RuntimeType::Thunk {
                effect,
                value: principal_value,
            },
        ) if should_thunk_effect(effect)
            && finalized_effect_boundary_value_matches(&base, principal_value) =>
        {
            RuntimeType::Thunk {
                effect: effect.clone(),
                value: Box::new(finalized_effect_boundaries_from_principal(
                    base,
                    principal_value,
                )),
            }
        }
        (base, _) => base,
    }
}

fn principal_can_drop_base_thunk(principal: &RuntimeType) -> bool {
    !matches!(
        principal,
        RuntimeType::Unknown | RuntimeType::Value(typed_ir::Type::Any)
    )
}

fn finalized_effect_boundary_value_matches(base: &RuntimeType, principal: &RuntimeType) -> bool {
    if base == principal {
        return true;
    }
    let base = runtime_type_to_core(base.clone());
    let principal = runtime_type_to_core(principal.clone());
    role::core_subtype_match_score(&base, &principal).is_some()
        || role::core_subtype_match_score(&principal, &base).is_some()
}

pub(crate) fn finalized_apply_spine_arg_effects(
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
    let param = finalized_apply_arg_effect(*param, arg_value, arg_effect);
    RuntimeType::Fun {
        param: Box::new(param),
        ret: Box::new(finalized_apply_spine_arg_effects(*ret, rest, local_types)),
    }
}

fn finalized_apply_arg_effect(
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
        RuntimeType::Value(ty) => core_type_contains_non_runtime_choice(ty),
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
        RuntimeType::Value(ty) => EffectedCoreType {
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
        (RuntimeType::Value(t), RuntimeType::Value(s)) => {
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

pub(crate) fn prune_specialized_polymorphic_bindings(
    module: &mut Module,
    solutions: &[RootGraphSolution],
) {
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

/// Drop bindings that no `root_expr` or root binding can reach. After
/// monomorphization the module otherwise retains every primitive stdlib
/// binding even when the user program never touches it; the resulting
/// 100+ entry `bindings` vector inflates the VM's expression/symbol tables
/// and hurts cache behavior. role_impls entries already had their member
/// dispatch sites rewritten to direct `Var` calls during monomorphize, so
/// they are not seeds — anything still needed will be reached through
/// the rewritten `Var` references.
pub(crate) fn prune_unreachable_bindings(module: &mut Module) {
    let reachable = reachable_paths(module);
    module
        .bindings
        .retain(|binding| reachable.contains(&binding.name));
}

pub(crate) fn reachable_paths(module: &Module) -> HashSet<typed_ir::Path> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let binding_paths = bindings.keys().cloned().collect::<HashSet<_>>();
    let mut reachable = HashSet::new();
    let mut pending = Vec::new();
    for expr in &module.root_exprs {
        collect_expr_paths(expr, &binding_paths, &mut HashSet::new(), &mut pending);
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
            collect_expr_paths(
                &binding.body,
                &binding_paths,
                &mut HashSet::new(),
                &mut pending,
            );
        }
    }
    reachable
}

fn collect_expr_paths(
    expr: &Expr,
    bindings: &HashSet<typed_ir::Path>,
    locals: &mut HashSet<typed_ir::Path>,
    paths: &mut Vec<typed_ir::Path>,
) {
    match &expr.kind {
        ExprKind::Var(path) => {
            if bindings.contains(path) && !locals.contains(path) {
                paths.push(path.clone());
            }
        }
        ExprKind::EffectOp(path) => {
            if bindings.contains(path) {
                paths.push(path.clone());
            }
        }
        ExprKind::Lambda { param, body, .. } => {
            with_local_path(locals, path_from_name(param), |locals| {
                collect_expr_paths(body, bindings, locals, paths);
            });
        }
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_paths(callee, bindings, locals, paths);
            collect_expr_paths(arg, bindings, locals, paths);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_paths(cond, bindings, locals, paths);
            collect_expr_paths(then_branch, bindings, locals, paths);
            collect_expr_paths(else_branch, bindings, locals, paths);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_paths(item, bindings, locals, paths);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_paths(&field.value, bindings, locals, paths);
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
                    | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
                        collect_expr_paths(expr, bindings, locals, paths);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_paths(value, bindings, locals, paths);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_paths(base, bindings, locals, paths),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_paths(scrutinee, bindings, locals, paths);
            for arm in arms {
                collect_pattern_default_expr_paths(&arm.pattern, bindings, locals, paths);
                with_pattern_locals(locals, &arm.pattern, |locals| {
                    if let Some(guard) = &arm.guard {
                        collect_expr_paths(guard, bindings, locals, paths);
                    }
                    collect_expr_paths(&arm.body, bindings, locals, paths);
                });
            }
        }
        ExprKind::Block { stmts, tail } => {
            let mut block_locals = locals.clone();
            for stmt in stmts {
                match stmt {
                    yulang_runtime_ir::FinalizedStmt::Let { pattern, value } => {
                        collect_expr_paths(value, bindings, &mut block_locals, paths);
                        collect_pattern_default_expr_paths(
                            pattern,
                            bindings,
                            &mut block_locals,
                            paths,
                        );
                        insert_pattern_local_paths(&mut block_locals, pattern);
                    }
                    yulang_runtime_ir::FinalizedStmt::Expr(expr)
                    | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => {
                        collect_expr_paths(expr, bindings, &mut block_locals, paths);
                    }
                }
            }
            if let Some(tail) = tail {
                collect_expr_paths(tail, bindings, &mut block_locals, paths);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_paths(body, bindings, locals, paths);
            for arm in arms {
                collect_pattern_default_expr_paths(&arm.payload, bindings, locals, paths);
                with_pattern_locals(locals, &arm.payload, |locals| {
                    let resume = arm
                        .resume
                        .as_ref()
                        .map(|resume| path_from_name(&resume.name));
                    if let Some(resume) = resume {
                        with_local_path(locals, resume, |locals| {
                            if let Some(guard) = &arm.guard {
                                collect_expr_paths(guard, bindings, locals, paths);
                            }
                            collect_expr_paths(&arm.body, bindings, locals, paths);
                        });
                    } else {
                        if let Some(guard) = &arm.guard {
                            collect_expr_paths(guard, bindings, locals, paths);
                        }
                        collect_expr_paths(&arm.body, bindings, locals, paths);
                    }
                });
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::LocalPushId { body: expr, .. }
        | ExprKind::AddId { thunk: expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. }
        | ExprKind::Thunk { expr, .. } => collect_expr_paths(expr, bindings, locals, paths),
        ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn with_local_path(
    locals: &mut HashSet<typed_ir::Path>,
    path: typed_ir::Path,
    f: impl FnOnce(&mut HashSet<typed_ir::Path>),
) {
    let inserted = locals.insert(path.clone());
    f(locals);
    if inserted {
        locals.remove(&path);
    }
}

fn with_pattern_locals(
    locals: &mut HashSet<typed_ir::Path>,
    pattern: &yulang_runtime_ir::FinalizedPattern,
    f: impl FnOnce(&mut HashSet<typed_ir::Path>),
) {
    let mut scoped = locals.clone();
    insert_pattern_local_paths(&mut scoped, pattern);
    f(&mut scoped);
}

fn insert_pattern_local_paths(
    locals: &mut HashSet<typed_ir::Path>,
    pattern: &yulang_runtime_ir::FinalizedPattern,
) {
    use yulang_runtime_ir::FinalizedPattern as Pattern;
    match pattern {
        Pattern::Bind { name, .. } => {
            locals.insert(path_from_name(name));
        }
        Pattern::As { pattern, name, .. } => {
            locals.insert(path_from_name(name));
            insert_pattern_local_paths(locals, pattern);
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                insert_pattern_local_paths(locals, item);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix.iter()) {
                insert_pattern_local_paths(locals, item);
            }
            if let Some(spread) = spread {
                insert_pattern_local_paths(locals, spread);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                insert_pattern_local_paths(locals, &field.pattern);
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::FinalizedRecordSpreadPattern::Tail(pattern) => {
                        insert_pattern_local_paths(locals, pattern);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                insert_pattern_local_paths(locals, value);
            }
        }
        Pattern::Or { left, .. } => insert_pattern_local_paths(locals, left),
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn collect_pattern_default_expr_paths(
    pattern: &yulang_runtime_ir::FinalizedPattern,
    bindings: &HashSet<typed_ir::Path>,
    locals: &mut HashSet<typed_ir::Path>,
    paths: &mut Vec<typed_ir::Path>,
) {
    use yulang_runtime_ir::FinalizedPattern as Pattern;
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_default_expr_paths(item, bindings, locals, paths);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix.iter().chain(suffix.iter()) {
                collect_pattern_default_expr_paths(item, bindings, locals, paths);
            }
            if let Some(spread) = spread {
                collect_pattern_default_expr_paths(spread, bindings, locals, paths);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                if let Some(default) = &field.default {
                    collect_expr_paths(default, bindings, locals, paths);
                }
                collect_pattern_default_expr_paths(&field.pattern, bindings, locals, paths);
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadPattern::Head(pattern)
                    | yulang_runtime_ir::FinalizedRecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_default_expr_paths(pattern, bindings, locals, paths);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_default_expr_paths(value, bindings, locals, paths);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_default_expr_paths(left, bindings, locals, paths);
            collect_pattern_default_expr_paths(right, bindings, locals, paths);
        }
        Pattern::As { pattern, .. } => {
            collect_pattern_default_expr_paths(pattern, bindings, locals, paths);
        }
        Pattern::Bind { .. } | Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

pub(crate) fn runtime_type_is_closed(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Value(ty) => core_type_is_closed(ty),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eliminate_immediate_thunk_force_replaces_direct_bind_here_thunk_pair() {
        let int = named_type("int");
        let mut module = module_with_root(bind_here(thunk(
            Expr::typed(ExprKind::Lit(typed_ir::Lit::Int("1".into())), int.clone()),
            int.clone(),
        )));

        eliminate_immediate_thunk_forces(&mut module);

        let root = &module.root_exprs[0];
        assert_eq!(root.ty, int);
        assert!(matches!(&root.kind, ExprKind::Lit(typed_ir::Lit::Int(value)) if value == "1"));
    }

    #[test]
    fn eliminate_immediate_thunk_force_keeps_incompatible_body_type() {
        let int = named_type("int");
        let str_ty = named_type("str");
        let mut module = module_with_root(bind_here(thunk(var("x", str_ty), int.clone())));

        eliminate_immediate_thunk_forces(&mut module);

        assert!(matches!(
            module.root_exprs[0].kind,
            ExprKind::BindHere { .. }
        ));
    }

    #[test]
    fn eliminate_immediate_thunk_force_does_not_cross_value_thunk_shapes() {
        let int = named_type("int");
        let inner_thunk = RuntimeType::Thunk {
            effect: empty_row(),
            value: Box::new(int.clone()),
        };
        let mut module = module_with_root(bind_here(thunk(var("x", inner_thunk), int.clone())));

        eliminate_immediate_thunk_forces(&mut module);

        assert!(matches!(
            module.root_exprs[0].kind,
            ExprKind::BindHere { .. }
        ));
    }

    #[test]
    fn eliminate_immediate_thunk_force_keeps_context_observing_body() {
        let bool_ty = named_type("bool");
        let mut module = module_with_root(bind_here(thunk(
            Expr::typed(
                ExprKind::FindId {
                    id: yulang_runtime_ir::EffectIdRef::Peek,
                },
                bool_ty.clone(),
            ),
            bool_ty,
        )));

        eliminate_immediate_thunk_forces(&mut module);

        assert!(matches!(
            module.root_exprs[0].kind,
            ExprKind::BindHere { .. }
        ));
    }

    #[test]
    fn eliminate_immediate_thunk_force_keeps_var_body() {
        let int = named_type("int");
        let mut module = module_with_root(bind_here(thunk(var("x", int.clone()), int)));

        eliminate_immediate_thunk_forces(&mut module);

        assert!(matches!(
            module.root_exprs[0].kind,
            ExprKind::BindHere { .. }
        ));
    }

    fn module_with_root(expr: Expr) -> Module {
        Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    fn bind_here(expr: Expr) -> Expr {
        let ty = match &expr.ty {
            RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
            _ => RuntimeType::Unknown,
        };
        Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(expr),
            },
            ty,
        )
    }

    fn thunk(body: Expr, value: RuntimeType) -> Expr {
        let effect = empty_row();
        Expr::typed(
            ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(body),
            },
            RuntimeType::Thunk {
                effect,
                value: Box::new(value),
            },
        )
    }

    fn var(name: &str, ty: RuntimeType) -> Expr {
        Expr::typed(ExprKind::Var(path_from_str(name)), ty)
    }

    fn named_type(name: &str) -> RuntimeType {
        RuntimeType::Value(typed_ir::Type::Named {
            path: path_from_str(name),
            args: Vec::new(),
        })
    }

    fn empty_row() -> typed_ir::Type {
        typed_ir::Type::Row {
            items: Vec::new(),
            tail: Box::new(typed_ir::Type::Never),
        }
    }

    fn path_from_str(name: &str) -> typed_ir::Path {
        typed_ir::Path::new(vec![typed_ir::Name(name.into())])
    }
}
