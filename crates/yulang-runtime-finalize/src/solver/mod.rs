//! Finalize a runtime IR module: instantiate principals into a fresh
//! monomorphic graph per call site, solve, emit mono bindings, rewrite call
//! sites, materialize substitutions, and run post-passes.
//!
//! This file holds the top-level pipeline entry points and the main
//! fixed-point loop. The phase-specific work is split across submodules:
//!
//! - [`apply_spine`] — collect apply spines from every expression, build a
//!   monomorphic `TypeGraph` per spine and solve it.
//! - [`role`] — close associated types from role impls and rewrite role-method
//!   call sites once impls become reachable.
//! - [`rewrite`] — emit mono `Binding`s and rewrite `Var`/`Apply` spines to
//!   the new aliases.
//! - [`materialize`] — apply substitutions to expressions, evidence, and
//!   apply-arg shapes (thunk wrapping).
//! - [`cast`] — semantic-cast lattice + Coerce-node normalization.
//! - [`postpass`] — one-shot finishing passes (`fill_*`, `prune_*`,
//!   `normalize_*`) and the shared runtime-type-shape helpers.

mod apply_spine;
mod cast;
mod materialize;
mod postpass;
mod rewrite;
mod role;

pub use apply_spine::{collect_root_graph_inputs, solve_root_graphs};

// Re-exports so sibling submodules can still address shared helpers as
// `super::X` rather than `super::postpass::X`.
pub(crate) use postpass::{
    core_type_has_unknown, core_type_is_closed, finalized_apply_spine_arg_effects,
    finalized_effect_boundaries_from_principal, narrow_runtime_type_in_place, path_from_name,
    reachable_paths, refine_runtime_spine_return, runtime_function_param, runtime_type_has_unknown,
    runtime_type_is_closed, runtime_type_to_core, unit_type,
};

use std::collections::HashSet;

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, FinalizedModule as Module, LoweredExpr,
    LoweredExprKind, LoweredModule, LoweredPattern, LoweredRecordSpreadExpr,
    LoweredRecordSpreadPattern, LoweredStmt,
};
use yulang_typed_ir as typed_ir;

use crate::{
    FinalizeInstanceCache, FinalizeMonomorphizeError, FinalizeOutput, FinalizeReport,
    FinalizeResult, graph::runtime_type_from_core_value,
};

pub trait IntoFinalizeRuntimeModule {
    fn into_finalize_runtime_module(self) -> Module;
}

impl IntoFinalizeRuntimeModule for LoweredModule {
    fn into_finalize_runtime_module(self) -> Module {
        finalize_lowered_module(self)
    }
}

impl IntoFinalizeRuntimeModule for Module {
    fn into_finalize_runtime_module(self) -> Module {
        self
    }
}

impl IntoFinalizeRuntimeModule for yulang_runtime::Module {
    fn into_finalize_runtime_module(self) -> Module {
        runtime_to_finalized_module(self)
    }
}

pub fn finalize_module<M: IntoFinalizeRuntimeModule>(module: M) -> FinalizeResult<FinalizeOutput> {
    let mut cache = FinalizeInstanceCache::default();
    finalize_module_with_cache(module, &mut cache)
}

pub fn finalize_monomorphize_module<M: IntoFinalizeRuntimeModule>(
    module: M,
) -> Result<Module, FinalizeMonomorphizeError> {
    Ok(finalize_monomorphize_module_with_report(module.into_finalize_runtime_module())?.module)
}

pub fn finalize_monomorphize_legacy_runtime_module<M: IntoFinalizeRuntimeModule>(
    module: M,
) -> Result<yulang_runtime::Module, FinalizeMonomorphizeError> {
    Ok(finalized_to_runtime_module(finalize_monomorphize_module(
        module,
    )?))
}

pub fn finalize_monomorphize_module_with_report(
    module: Module,
) -> Result<FinalizeOutput, FinalizeMonomorphizeError> {
    let output = finalize_module(module)?;
    let _ = validate_monomorphized_output(&output.module);
    Ok(output)
}

fn validate_monomorphized_output(module: &Module) -> Result<(), ()> {
    if std::env::var_os("YULANG_FINALIZE_DEBUG_INVARIANTS").is_some() {
        for binding in &module.bindings {
            debug_expr_invariants(&binding.body, format!("binding {:?}", binding.name));
        }
        for (index, expr) in module.root_exprs.iter().enumerate() {
            debug_expr_invariants(expr, format!("root #{index}"));
        }
    }
    Ok(())
}

fn debug_expr_invariants(expr: &Expr, context: String) {
    match &expr.kind {
        ExprKind::Handle {
            body,
            handler,
            arms,
            ..
        } => {
            if !handler.consumes.is_empty()
                && !matches!(body.ty, yulang_runtime_ir::FinalizedType::Thunk { .. })
            {
                eprintln!(
                    "FINALIZE invariant: effectful handle body is not thunk at {context}: consumes={:?}, body_ty={:?}",
                    handler.consumes, body.ty
                );
            }
            debug_expr_invariants(body, format!("{context}/handle.body"));
            for (index, arm) in arms.iter().enumerate() {
                debug_expr_invariants(&arm.body, format!("{context}/handle.arm[{index}].body"));
                if let Some(guard) = &arm.guard {
                    debug_expr_invariants(guard, format!("{context}/handle.arm[{index}].guard"));
                }
            }
        }
        ExprKind::AddId { thunk, .. } => {
            if !matches!(thunk.ty, yulang_runtime_ir::FinalizedType::Thunk { .. }) {
                eprintln!(
                    "FINALIZE invariant: add_id input is not thunk at {context}: thunk_ty={:?}",
                    thunk.ty
                );
            }
            debug_expr_invariants(thunk, format!("{context}/add_id"));
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => {
            debug_expr_invariants(body, context);
        }
        ExprKind::Apply { callee, arg, .. } => {
            debug_expr_invariants(callee, format!("{context}/apply.callee"));
            debug_expr_invariants(arg, format!("{context}/apply.arg"));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            debug_expr_invariants(cond, format!("{context}/if.cond"));
            debug_expr_invariants(then_branch, format!("{context}/if.then"));
            debug_expr_invariants(else_branch, format!("{context}/if.else"));
        }
        ExprKind::Tuple(items) => {
            for (index, item) in items.iter().enumerate() {
                debug_expr_invariants(item, format!("{context}/tuple[{index}]"));
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                debug_expr_invariants(&field.value, format!("{context}/record.{}", field.name.0));
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr)
                    | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
                        debug_expr_invariants(expr, format!("{context}/record.spread"));
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                debug_expr_invariants(value, format!("{context}/variant"));
            }
        }
        ExprKind::Select { base, .. } => {
            debug_expr_invariants(base, format!("{context}/select.base"));
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            debug_expr_invariants(scrutinee, format!("{context}/match.scrutinee"));
            for (index, arm) in arms.iter().enumerate() {
                debug_expr_invariants(&arm.body, format!("{context}/match.arm[{index}].body"));
                if let Some(guard) = &arm.guard {
                    debug_expr_invariants(guard, format!("{context}/match.arm[{index}].guard"));
                }
            }
        }
        ExprKind::Block { stmts, tail } => {
            for (index, stmt) in stmts.iter().enumerate() {
                match stmt {
                    yulang_runtime_ir::FinalizedStmt::Let { value, .. } => {
                        debug_expr_invariants(value, format!("{context}/stmt[{index}].let"));
                    }
                    yulang_runtime_ir::FinalizedStmt::Expr(expr)
                    | yulang_runtime_ir::FinalizedStmt::Module { body: expr, .. } => {
                        debug_expr_invariants(expr, format!("{context}/stmt[{index}]"));
                    }
                }
            }
            if let Some(tail) = tail {
                debug_expr_invariants(tail, format!("{context}/tail"));
            }
        }
        ExprKind::Thunk { expr, .. } => {
            debug_expr_invariants(expr, format!("{context}/thunk"));
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

pub fn finalize_module_with_cache<M: IntoFinalizeRuntimeModule>(
    module: M,
    cache: &mut FinalizeInstanceCache,
) -> FinalizeResult<FinalizeOutput> {
    let mut module = module.into_finalize_runtime_module();
    let root_graph_inputs = collect_root_graph_inputs(&module);
    role::rewrite_root_role_method_calls(&mut module);
    let cast_order = cast::type_cast_order(&module.role_impls);
    let mut root_graph_solutions = solve_root_graphs(&module, &cast_order)?;
    let mut scanned_binding_bodies = HashSet::new();
    let mut applied_solution_count = 0;
    loop {
        rewrite::canonicalize_aliases(&mut root_graph_solutions);
        let emitted =
            rewrite::append_monomorphic_bindings(&mut module, &root_graph_solutions, cache)?;
        let unapplied_solutions = &root_graph_solutions[applied_solution_count..];
        rewrite::rewrite_root_exprs(&mut module, unapplied_solutions)?;
        rewrite::rewrite_binding_exprs(&mut module, unapplied_solutions)?;
        applied_solution_count = root_graph_solutions.len();
        let role_rewrites = role::rewrite_role_method_calls(&mut module);

        let solution_count = root_graph_solutions.len();
        apply_spine::collect_root_expr_graphs(&module, &cast_order, &mut root_graph_solutions)?;
        let scan_targets = apply_spine::next_binding_body_scan_targets(
            &module,
            &emitted,
            &mut scanned_binding_bodies,
        );
        apply_spine::collect_binding_body_graphs(
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
    postpass::prune_specialized_polymorphic_bindings(&mut module, &root_graph_solutions);
    postpass::prune_unbound_binding_roots(&mut module);
    postpass::monomorphize_phantom_nullary_variant_bindings(&mut module);
    postpass::normalize_materialized_module(&mut module);
    cast::normalize_semantic_cast_coercions(&mut module);
    // Fill local Var types first (using enclosing-binder scope), so the apply
    // evidence pass sees concrete arg/callee types when reconciling.
    postpass::fill_local_var_types(&mut module);
    postpass::fill_apply_evidence_types(&mut module);
    // Run scope walk again — apply reconciliation may have concretized
    // pattern/handler types that earlier scope walk skipped.
    postpass::fill_local_var_types(&mut module);
    Ok(FinalizeOutput {
        module,
        report: FinalizeReport {
            root_graph_inputs,
            root_graph_solutions,
            cache_profile: cache.profile(),
        },
    })
}

fn finalize_lowered_module(module: LoweredModule) -> Module {
    yulang_runtime_ir::Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(|binding| yulang_runtime_ir::Binding {
                name: binding.name,
                type_params: binding.type_params,
                scheme: binding.scheme,
                body: finalize_lowered_expr(binding.body),
            })
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(finalize_lowered_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn finalized_to_runtime_module(module: Module) -> yulang_runtime::Module {
    yulang_runtime_ir::Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(|binding| yulang_runtime_ir::Binding {
                name: binding.name,
                type_params: binding.type_params,
                scheme: binding.scheme,
                body: finalized_to_runtime_expr(binding.body),
            })
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(finalized_to_runtime_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn finalized_to_runtime_expr(expr: Expr) -> yulang_runtime::Expr {
    let ty = finalized_to_runtime_type(expr.ty);
    let kind = match expr.kind {
        ExprKind::Var(path) => yulang_runtime_ir::ExprKind::Var(path),
        ExprKind::EffectOp(path) => yulang_runtime_ir::ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => yulang_runtime_ir::ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => yulang_runtime_ir::ExprKind::Lit(lit),
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => yulang_runtime_ir::ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(finalized_to_runtime_expr(*body)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => yulang_runtime_ir::ExprKind::Apply {
            callee: Box::new(finalized_to_runtime_expr(*callee)),
            arg: Box::new(finalized_to_runtime_expr(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => yulang_runtime_ir::ExprKind::If {
            cond: Box::new(finalized_to_runtime_expr(*cond)),
            then_branch: Box::new(finalized_to_runtime_expr(*then_branch)),
            else_branch: Box::new(finalized_to_runtime_expr(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => yulang_runtime_ir::ExprKind::Tuple(
            items.into_iter().map(finalized_to_runtime_expr).collect(),
        ),
        ExprKind::Record { fields, spread } => yulang_runtime_ir::ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordExprField {
                    name: field.name,
                    value: finalized_to_runtime_expr(field.value),
                })
                .collect(),
            spread: spread.map(finalized_to_runtime_record_spread_expr),
        },
        ExprKind::Variant { tag, value } => yulang_runtime_ir::ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(finalized_to_runtime_expr(*value))),
        },
        ExprKind::Select { base, field } => yulang_runtime_ir::ExprKind::Select {
            base: Box::new(finalized_to_runtime_expr(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => yulang_runtime_ir::ExprKind::Match {
            scrutinee: Box::new(finalized_to_runtime_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::MatchArm {
                    pattern: finalized_to_runtime_pattern(arm.pattern),
                    guard: arm.guard.map(finalized_to_runtime_expr),
                    body: finalized_to_runtime_expr(arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => yulang_runtime_ir::ExprKind::Block {
            stmts: stmts.into_iter().map(finalized_to_runtime_stmt).collect(),
            tail: tail.map(|tail| Box::new(finalized_to_runtime_expr(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => yulang_runtime_ir::ExprKind::Handle {
            body: Box::new(finalized_to_runtime_expr(*body)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::HandleArm {
                    effect: arm.effect,
                    payload: finalized_to_runtime_pattern(arm.payload),
                    resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
                        name: resume.name,
                        ty: finalized_to_runtime_type(resume.ty),
                    }),
                    guard: arm.guard.map(finalized_to_runtime_expr),
                    body: finalized_to_runtime_expr(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => {
            let mut expr = finalized_to_runtime_expr(*expr);
            if !matches!(expr.ty, yulang_runtime::Type::Thunk { .. }) {
                let value = expr.ty.clone();
                expr.ty = yulang_runtime::Type::thunk(typed_ir::Type::Unknown, value);
            }
            yulang_runtime_ir::ExprKind::BindHere {
                expr: Box::new(expr),
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let value = finalized_to_runtime_type(value);
            let kind = yulang_runtime_ir::ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(finalized_to_runtime_expr(*expr)),
            };
            return yulang_runtime_ir::Expr::typed(
                kind,
                yulang_runtime::Type::thunk(effect, value),
            );
        }
        ExprKind::LocalPushId { id, body } => yulang_runtime_ir::ExprKind::LocalPushId {
            id,
            body: Box::new(finalized_to_runtime_expr(*body)),
        },
        ExprKind::PeekId => yulang_runtime_ir::ExprKind::PeekId,
        ExprKind::FindId { id } => yulang_runtime_ir::ExprKind::FindId { id },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => yulang_runtime_ir::ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(finalized_to_runtime_expr(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => yulang_runtime_ir::ExprKind::Coerce {
            from,
            to,
            expr: Box::new(finalized_to_runtime_expr(*expr)),
        },
        ExprKind::Pack { var, expr } => yulang_runtime_ir::ExprKind::Pack {
            var,
            expr: Box::new(finalized_to_runtime_expr(*expr)),
        },
    };
    yulang_runtime_ir::Expr::typed(kind, ty)
}

fn finalized_to_runtime_stmt(stmt: yulang_runtime_ir::FinalizedStmt) -> yulang_runtime::Stmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: finalized_to_runtime_pattern(pattern),
            value: finalized_to_runtime_expr(value),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(finalized_to_runtime_expr(expr))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: finalized_to_runtime_expr(body),
        },
    }
}

fn finalized_to_runtime_pattern(
    pattern: yulang_runtime_ir::FinalizedPattern,
) -> yulang_runtime::Pattern {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty } => yulang_runtime_ir::Pattern::Wildcard {
            ty: finalized_to_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Bind { name, ty } => yulang_runtime_ir::Pattern::Bind {
            name,
            ty: finalized_to_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Lit { lit, ty } => yulang_runtime_ir::Pattern::Lit {
            lit,
            ty: finalized_to_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Tuple { items, ty } => yulang_runtime_ir::Pattern::Tuple {
            items: items
                .into_iter()
                .map(finalized_to_runtime_pattern)
                .collect(),
            ty: finalized_to_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => yulang_runtime_ir::Pattern::List {
            prefix: prefix
                .into_iter()
                .map(finalized_to_runtime_pattern)
                .collect(),
            spread: spread.map(|spread| Box::new(finalized_to_runtime_pattern(*spread))),
            suffix: suffix
                .into_iter()
                .map(finalized_to_runtime_pattern)
                .collect(),
            ty: finalized_to_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::Record { fields, spread, ty } => {
            yulang_runtime_ir::Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| yulang_runtime_ir::RecordPatternField {
                        name: field.name,
                        pattern: finalized_to_runtime_pattern(field.pattern),
                        default: field.default.map(finalized_to_runtime_expr),
                    })
                    .collect(),
                spread: spread.map(finalized_to_runtime_record_spread_pattern),
                ty: finalized_to_runtime_type(ty),
            }
        }
        yulang_runtime_ir::Pattern::Variant { tag, value, ty } => {
            yulang_runtime_ir::Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(finalized_to_runtime_pattern(*value))),
                ty: finalized_to_runtime_type(ty),
            }
        }
        yulang_runtime_ir::Pattern::Or { left, right, ty } => yulang_runtime_ir::Pattern::Or {
            left: Box::new(finalized_to_runtime_pattern(*left)),
            right: Box::new(finalized_to_runtime_pattern(*right)),
            ty: finalized_to_runtime_type(ty),
        },
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => yulang_runtime_ir::Pattern::As {
            pattern: Box::new(finalized_to_runtime_pattern(*pattern)),
            name,
            ty: finalized_to_runtime_type(ty),
        },
    }
}

fn finalized_to_runtime_record_spread_expr(
    spread: yulang_runtime_ir::FinalizedRecordSpreadExpr,
) -> yulang_runtime::RecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(finalized_to_runtime_expr(*expr)))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(finalized_to_runtime_expr(*expr)))
        }
    }
}

fn finalized_to_runtime_record_spread_pattern(
    spread: yulang_runtime_ir::FinalizedRecordSpreadPattern,
) -> yulang_runtime::RecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(finalized_to_runtime_pattern(
                *pattern,
            )))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(finalized_to_runtime_pattern(
                *pattern,
            )))
        }
    }
}

fn finalized_to_runtime_type(ty: yulang_runtime_ir::FinalizedType) -> yulang_runtime::Type {
    match ty {
        yulang_runtime_ir::FinalizedType::Unknown => yulang_runtime::Type::Unknown,
        yulang_runtime_ir::FinalizedType::Value(ty) => yulang_runtime::Type::Core(ty),
        yulang_runtime_ir::FinalizedType::Fun { param, ret } => yulang_runtime::Type::Fun {
            param: Box::new(finalized_to_runtime_type(*param)),
            ret: Box::new(finalized_to_runtime_type(*ret)),
        },
        yulang_runtime_ir::FinalizedType::Thunk { effect, value } => yulang_runtime::Type::Thunk {
            effect,
            value: Box::new(finalized_to_runtime_type(*value)),
        },
    }
}

fn runtime_to_finalized_module(module: yulang_runtime::Module) -> Module {
    yulang_runtime_ir::Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(|binding| yulang_runtime_ir::Binding {
                name: binding.name,
                type_params: binding.type_params,
                scheme: binding.scheme,
                body: runtime_to_finalized_expr(binding.body),
            })
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(runtime_to_finalized_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn runtime_to_finalized_expr(expr: yulang_runtime::Expr) -> Expr {
    let ty = runtime_to_finalized_type(expr.ty);
    let kind = match expr.kind {
        yulang_runtime_ir::ExprKind::Var(path) => yulang_runtime_ir::ExprKind::Var(path),
        yulang_runtime_ir::ExprKind::EffectOp(path) => yulang_runtime_ir::ExprKind::EffectOp(path),
        yulang_runtime_ir::ExprKind::PrimitiveOp(op) => {
            yulang_runtime_ir::ExprKind::PrimitiveOp(op)
        }
        yulang_runtime_ir::ExprKind::Lit(lit) => yulang_runtime_ir::ExprKind::Lit(lit),
        yulang_runtime_ir::ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => yulang_runtime_ir::ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(runtime_to_finalized_expr(*body)),
        },
        yulang_runtime_ir::ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => yulang_runtime_ir::ExprKind::Apply {
            callee: Box::new(runtime_to_finalized_expr(*callee)),
            arg: Box::new(runtime_to_finalized_expr(*arg)),
            evidence,
            instantiation,
        },
        yulang_runtime_ir::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => yulang_runtime_ir::ExprKind::If {
            cond: Box::new(runtime_to_finalized_expr(*cond)),
            then_branch: Box::new(runtime_to_finalized_expr(*then_branch)),
            else_branch: Box::new(runtime_to_finalized_expr(*else_branch)),
            evidence,
        },
        yulang_runtime_ir::ExprKind::Tuple(items) => yulang_runtime_ir::ExprKind::Tuple(
            items.into_iter().map(runtime_to_finalized_expr).collect(),
        ),
        yulang_runtime_ir::ExprKind::Record { fields, spread } => {
            yulang_runtime_ir::ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|field| yulang_runtime_ir::RecordExprField {
                        name: field.name,
                        value: runtime_to_finalized_expr(field.value),
                    })
                    .collect(),
                spread: spread.map(runtime_to_finalized_record_spread_expr),
            }
        }
        yulang_runtime_ir::ExprKind::Variant { tag, value } => {
            yulang_runtime_ir::ExprKind::Variant {
                tag,
                value: value.map(|value| Box::new(runtime_to_finalized_expr(*value))),
            }
        }
        yulang_runtime_ir::ExprKind::Select { base, field } => {
            yulang_runtime_ir::ExprKind::Select {
                base: Box::new(runtime_to_finalized_expr(*base)),
                field,
            }
        }
        yulang_runtime_ir::ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => yulang_runtime_ir::ExprKind::Match {
            scrutinee: Box::new(runtime_to_finalized_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::MatchArm {
                    pattern: runtime_to_finalized_pattern(arm.pattern),
                    guard: arm.guard.map(runtime_to_finalized_expr),
                    body: runtime_to_finalized_expr(arm.body),
                })
                .collect(),
            evidence,
        },
        yulang_runtime_ir::ExprKind::Block { stmts, tail } => yulang_runtime_ir::ExprKind::Block {
            stmts: stmts.into_iter().map(runtime_to_finalized_stmt).collect(),
            tail: tail.map(|tail| Box::new(runtime_to_finalized_expr(*tail))),
        },
        yulang_runtime_ir::ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => yulang_runtime_ir::ExprKind::Handle {
            body: Box::new(runtime_to_finalized_expr(*body)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::HandleArm {
                    effect: arm.effect,
                    payload: runtime_to_finalized_pattern(arm.payload),
                    resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
                        name: resume.name,
                        ty: runtime_to_finalized_type(resume.ty),
                    }),
                    guard: arm.guard.map(runtime_to_finalized_expr),
                    body: runtime_to_finalized_expr(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        yulang_runtime_ir::ExprKind::BindHere { expr } => yulang_runtime_ir::ExprKind::BindHere {
            expr: Box::new(runtime_to_finalized_expr(*expr)),
        },
        yulang_runtime_ir::ExprKind::Thunk {
            effect,
            value,
            expr,
        } => yulang_runtime_ir::ExprKind::Thunk {
            effect,
            value: runtime_to_finalized_type(value),
            expr: Box::new(runtime_to_finalized_expr(*expr)),
        },
        yulang_runtime_ir::ExprKind::LocalPushId { id, body } => {
            yulang_runtime_ir::ExprKind::LocalPushId {
                id,
                body: Box::new(runtime_to_finalized_expr(*body)),
            }
        }
        yulang_runtime_ir::ExprKind::PeekId => yulang_runtime_ir::ExprKind::PeekId,
        yulang_runtime_ir::ExprKind::FindId { id } => yulang_runtime_ir::ExprKind::FindId { id },
        yulang_runtime_ir::ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => yulang_runtime_ir::ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(runtime_to_finalized_expr(*thunk)),
        },
        yulang_runtime_ir::ExprKind::Coerce { from, to, expr } => {
            yulang_runtime_ir::ExprKind::Coerce {
                from,
                to,
                expr: Box::new(runtime_to_finalized_expr(*expr)),
            }
        }
        yulang_runtime_ir::ExprKind::Pack { var, expr } => yulang_runtime_ir::ExprKind::Pack {
            var,
            expr: Box::new(runtime_to_finalized_expr(*expr)),
        },
    };
    yulang_runtime_ir::Expr::typed(kind, ty)
}

fn runtime_to_finalized_stmt(stmt: yulang_runtime::Stmt) -> yulang_runtime_ir::FinalizedStmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: runtime_to_finalized_pattern(pattern),
            value: runtime_to_finalized_expr(value),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(runtime_to_finalized_expr(expr))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: runtime_to_finalized_expr(body),
        },
    }
}

fn runtime_to_finalized_pattern(
    pattern: yulang_runtime::Pattern,
) -> yulang_runtime_ir::FinalizedPattern {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty } => yulang_runtime_ir::Pattern::Wildcard {
            ty: runtime_to_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Bind { name, ty } => yulang_runtime_ir::Pattern::Bind {
            name,
            ty: runtime_to_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Lit { lit, ty } => yulang_runtime_ir::Pattern::Lit {
            lit,
            ty: runtime_to_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Tuple { items, ty } => yulang_runtime_ir::Pattern::Tuple {
            items: items
                .into_iter()
                .map(runtime_to_finalized_pattern)
                .collect(),
            ty: runtime_to_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => yulang_runtime_ir::Pattern::List {
            prefix: prefix
                .into_iter()
                .map(runtime_to_finalized_pattern)
                .collect(),
            spread: spread.map(|spread| Box::new(runtime_to_finalized_pattern(*spread))),
            suffix: suffix
                .into_iter()
                .map(runtime_to_finalized_pattern)
                .collect(),
            ty: runtime_to_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::Record { fields, spread, ty } => {
            yulang_runtime_ir::Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| yulang_runtime_ir::RecordPatternField {
                        name: field.name,
                        pattern: runtime_to_finalized_pattern(field.pattern),
                        default: field.default.map(runtime_to_finalized_expr),
                    })
                    .collect(),
                spread: spread.map(runtime_to_finalized_record_spread_pattern),
                ty: runtime_to_finalized_type(ty),
            }
        }
        yulang_runtime_ir::Pattern::Variant { tag, value, ty } => {
            yulang_runtime_ir::Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(runtime_to_finalized_pattern(*value))),
                ty: runtime_to_finalized_type(ty),
            }
        }
        yulang_runtime_ir::Pattern::Or { left, right, ty } => yulang_runtime_ir::Pattern::Or {
            left: Box::new(runtime_to_finalized_pattern(*left)),
            right: Box::new(runtime_to_finalized_pattern(*right)),
            ty: runtime_to_finalized_type(ty),
        },
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => yulang_runtime_ir::Pattern::As {
            pattern: Box::new(runtime_to_finalized_pattern(*pattern)),
            name,
            ty: runtime_to_finalized_type(ty),
        },
    }
}

fn runtime_to_finalized_record_spread_expr(
    spread: yulang_runtime::RecordSpreadExpr,
) -> yulang_runtime_ir::FinalizedRecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(runtime_to_finalized_expr(*expr)))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(runtime_to_finalized_expr(*expr)))
        }
    }
}

fn runtime_to_finalized_record_spread_pattern(
    spread: yulang_runtime::RecordSpreadPattern,
) -> yulang_runtime_ir::FinalizedRecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(runtime_to_finalized_pattern(
                *pattern,
            )))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(runtime_to_finalized_pattern(
                *pattern,
            )))
        }
    }
}

fn runtime_to_finalized_type(ty: yulang_runtime::Type) -> yulang_runtime_ir::FinalizedType {
    match ty {
        yulang_runtime::Type::Unknown => yulang_runtime_ir::FinalizedType::Unknown,
        yulang_runtime::Type::Core(ty) => runtime_type_from_core_value(ty),
        yulang_runtime::Type::Fun { param, ret } => yulang_runtime_ir::FinalizedType::Fun {
            param: Box::new(runtime_to_finalized_type(*param)),
            ret: Box::new(runtime_to_finalized_type(*ret)),
        },
        yulang_runtime::Type::Thunk { effect, value } => yulang_runtime_ir::FinalizedType::Thunk {
            effect,
            value: Box::new(runtime_to_finalized_type(*value)),
        },
    }
}

fn finalize_lowered_expr(expr: LoweredExpr) -> Expr {
    let ty = runtime_type_from_core_value(expr.ty);
    let kind = match expr.kind {
        LoweredExprKind::Var(path) => ExprKind::Var(path),
        LoweredExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        LoweredExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        LoweredExprKind::Lit(lit) => ExprKind::Lit(lit),
        LoweredExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(finalize_lowered_expr(*body)),
        },
        LoweredExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(finalize_lowered_expr(*callee)),
            arg: Box::new(finalize_lowered_expr(*arg)),
            evidence,
            instantiation,
        },
        LoweredExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(finalize_lowered_expr(*cond)),
            then_branch: Box::new(finalize_lowered_expr(*then_branch)),
            else_branch: Box::new(finalize_lowered_expr(*else_branch)),
            evidence,
        },
        LoweredExprKind::Tuple(items) => {
            ExprKind::Tuple(items.into_iter().map(finalize_lowered_expr).collect())
        }
        LoweredExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordExprField {
                    name: field.name,
                    value: finalize_lowered_expr(field.value),
                })
                .collect(),
            spread: spread.map(finalize_lowered_record_spread_expr),
        },
        LoweredExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(finalize_lowered_expr(*value))),
        },
        LoweredExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(finalize_lowered_expr(*base)),
            field,
        },
        LoweredExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(finalize_lowered_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::MatchArm {
                    pattern: finalize_lowered_pattern(arm.pattern),
                    guard: arm.guard.map(finalize_lowered_expr),
                    body: finalize_lowered_expr(arm.body),
                })
                .collect(),
            evidence,
        },
        LoweredExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts.into_iter().map(finalize_lowered_stmt).collect(),
            tail: tail.map(|tail| Box::new(finalize_lowered_expr(*tail))),
        },
        LoweredExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(finalize_lowered_expr(*body)),
            arms: arms
                .into_iter()
                .map(|arm| yulang_runtime_ir::HandleArm {
                    effect: arm.effect,
                    payload: finalize_lowered_pattern(arm.payload),
                    resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
                        name: resume.name,
                        ty: runtime_type_from_core_value(resume.ty),
                    }),
                    guard: arm.guard.map(finalize_lowered_expr),
                    body: finalize_lowered_expr(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        LoweredExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(finalize_lowered_expr(*expr)),
        },
        LoweredExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect,
            value: runtime_type_from_core_value(value),
            expr: Box::new(finalize_lowered_expr(*expr)),
        },
        LoweredExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(finalize_lowered_expr(*body)),
        },
        LoweredExprKind::PeekId => ExprKind::PeekId,
        LoweredExprKind::FindId { id } => ExprKind::FindId { id },
        LoweredExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => ExprKind::AddId {
            id,
            allowed,
            active,
            thunk: Box::new(finalize_lowered_expr(*thunk)),
        },
        LoweredExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(finalize_lowered_expr(*expr)),
        },
        LoweredExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(finalize_lowered_expr(*expr)),
        },
    };
    Expr::typed(kind, ty)
}

fn finalize_lowered_stmt(stmt: LoweredStmt) -> yulang_runtime_ir::FinalizedStmt {
    match stmt {
        yulang_runtime_ir::Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: finalize_lowered_pattern(pattern),
            value: finalize_lowered_expr(value),
        },
        yulang_runtime_ir::Stmt::Expr(expr) => {
            yulang_runtime_ir::Stmt::Expr(finalize_lowered_expr(expr))
        }
        yulang_runtime_ir::Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: finalize_lowered_expr(body),
        },
    }
}

fn finalize_lowered_pattern(pattern: LoweredPattern) -> yulang_runtime_ir::FinalizedPattern {
    match pattern {
        yulang_runtime_ir::Pattern::Wildcard { ty } => yulang_runtime_ir::Pattern::Wildcard {
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Bind { name, ty } => yulang_runtime_ir::Pattern::Bind {
            name,
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Lit { lit, ty } => yulang_runtime_ir::Pattern::Lit {
            lit,
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Tuple { items, ty } => yulang_runtime_ir::Pattern::Tuple {
            items: items.into_iter().map(finalize_lowered_pattern).collect(),
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => yulang_runtime_ir::Pattern::List {
            prefix: prefix.into_iter().map(finalize_lowered_pattern).collect(),
            spread: spread.map(|spread| Box::new(finalize_lowered_pattern(*spread))),
            suffix: suffix.into_iter().map(finalize_lowered_pattern).collect(),
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::Record { fields, spread, ty } => {
            yulang_runtime_ir::Pattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| yulang_runtime_ir::RecordPatternField {
                        name: field.name,
                        pattern: finalize_lowered_pattern(field.pattern),
                        default: field.default.map(finalize_lowered_expr),
                    })
                    .collect(),
                spread: spread.map(finalize_lowered_record_spread_pattern),
                ty: runtime_type_from_core_value(ty),
            }
        }
        yulang_runtime_ir::Pattern::Variant { tag, value, ty } => {
            yulang_runtime_ir::Pattern::Variant {
                tag,
                value: value.map(|value| Box::new(finalize_lowered_pattern(*value))),
                ty: runtime_type_from_core_value(ty),
            }
        }
        yulang_runtime_ir::Pattern::Or { left, right, ty } => yulang_runtime_ir::Pattern::Or {
            left: Box::new(finalize_lowered_pattern(*left)),
            right: Box::new(finalize_lowered_pattern(*right)),
            ty: runtime_type_from_core_value(ty),
        },
        yulang_runtime_ir::Pattern::As { pattern, name, ty } => yulang_runtime_ir::Pattern::As {
            pattern: Box::new(finalize_lowered_pattern(*pattern)),
            name,
            ty: runtime_type_from_core_value(ty),
        },
    }
}

fn finalize_lowered_record_spread_expr(
    spread: LoweredRecordSpreadExpr,
) -> yulang_runtime_ir::FinalizedRecordSpreadExpr {
    match spread {
        yulang_runtime_ir::RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(finalize_lowered_expr(*expr)))
        }
        yulang_runtime_ir::RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(finalize_lowered_expr(*expr)))
        }
    }
}

fn finalize_lowered_record_spread_pattern(
    spread: LoweredRecordSpreadPattern,
) -> yulang_runtime_ir::FinalizedRecordSpreadPattern {
    match spread {
        yulang_runtime_ir::RecordSpreadPattern::Head(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Head(Box::new(finalize_lowered_pattern(
                *pattern,
            )))
        }
        yulang_runtime_ir::RecordSpreadPattern::Tail(pattern) => {
            yulang_runtime_ir::RecordSpreadPattern::Tail(Box::new(finalize_lowered_pattern(
                *pattern,
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    use crate::{
        FinalizeInstanceArtifactCache, RootGraphInput, RootGraphRoot, graph::TypeCastOrder,
    };
    use yulang_runtime_ir::{
        FinalizedBinding as Binding, FinalizedExpr as Expr, FinalizedExprKind as ExprKind,
        FinalizedModule as Module, FinalizedType as RuntimeType, Root,
    };
    use yulang_sources::{
        CompiledSourceFileIdentity, CompiledUnitDependency, CompiledUnitManifest,
        SourceCompilationUnitOrigin, SourceOrigin,
    };
    use yulang_typed_ir as typed_ir;

    #[test]
    fn closed_root_expr_becomes_root_graph_input() {
        let ty = RuntimeType::Value(typed_ir::Type::Tuple(Vec::new()));
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
                        RuntimeType::Value(int.clone()),
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
        assert_eq!(solution.result_type, RuntimeType::Value(int.clone()));
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
            RuntimeType::Value(int.clone())
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
                            param: Box::new(RuntimeType::Value(typed_ir::Type::Any)),
                            ret: Box::new(RuntimeType::Value(int.clone())),
                        },
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                        RuntimeType::Value(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Value(int.clone()),
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
        let stale = RuntimeType::Value(typed_ir::Type::Named {
            path: path("list"),
            args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Var(original))],
        });
        let concrete = RuntimeType::Value(typed_ir::Type::Named {
            path: path("list"),
            args: vec![typed_ir::TypeArg::Type(int.clone())],
        });
        let local_path = path("xs");
        let mut local_types = HashMap::new();
        local_types.insert(local_path.clone(), concrete.clone());
        let expr = Expr::typed(ExprKind::Var(local_path), stale);

        assert_eq!(apply_spine::expr_lower_type(&expr, &local_types), concrete);
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
                        RuntimeType::Value(int.clone()),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::Value(bool_ty.clone()),
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
                        RuntimeType::Value(int.clone()),
                    )),
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Bool(true)),
                        RuntimeType::Value(bool_ty.clone()),
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
            RuntimeType::Value(int.clone())
        );
        assert_eq!(
            output.report.root_graph_solutions[1].result_type,
            RuntimeType::Value(bool_ty.clone())
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
        assert_eq!(items[0].ty, RuntimeType::Value(int.clone()));
        assert_eq!(items[1].ty, RuntimeType::Value(bool_ty.clone()));
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
                        RuntimeType::Value(int.clone()),
                    )),
                    id_call(Expr::typed(
                        ExprKind::Lit(typed_ir::Lit::Int("2".into())),
                        RuntimeType::Value(int.clone()),
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
        assert!(matches!(solution.result_type, RuntimeType::Value(_)));
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
        yulang_vm::compile_vm_module(module).unwrap();
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
            RuntimeType::Value(typed_ir::Type::Named {
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
            value: Box::new(RuntimeType::Value(int.clone())),
        };
        let stale_block = Expr::typed(
            ExprKind::Block {
                stmts: Vec::new(),
                tail: Some(Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: typed_ir::Type::Never,
                        value: RuntimeType::Value(int.clone()),
                        expr: Box::new(Expr::typed(
                            ExprKind::Lit(typed_ir::Lit::Int("1".into())),
                            RuntimeType::Value(int.clone()),
                        )),
                    },
                    thunk.clone(),
                ))),
            },
            RuntimeType::Value(int.clone()),
        );
        let bind_here = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(stale_block),
            },
            RuntimeType::Value(int),
        );

        let materialized = materialize::materialize_expr(bind_here, &[]);
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
                value: Box::new(RuntimeType::Value(int.clone())),
            }),
            ret: Box::new(RuntimeType::Thunk {
                effect: ret_effect.clone(),
                value: Box::new(RuntimeType::Value(bool_ty.clone())),
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
        let stale_unit = RuntimeType::Value(unit_type());
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

        let materialized = materialize::materialize_expr(
            handle,
            &[typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int.clone(),
            }],
        );

        assert_eq!(materialized.ty, RuntimeType::Value(int.clone()));
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
            include_str!("../../../../examples/showcase.yu"),
        ));
    }

    #[test]
    fn cached_std_finalize_accepts_refs_example() {
        // The legacy monomorphizer still loses the `+` receiver through the
        // compiled dependency path; keep this as a finalize-only mainline gate.
        assert_std_dependency_cache_ref_source_finalizes_to_vm_input(&playground_source(
            include_str!("../../../../examples/02_refs.yu"),
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

my collect_logs(comp: [_] _) = catch comp:
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

my collect_logs(comp: [_] _) =
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
        ] {
            assert_std_source_no_cache_finalizes_to_results(case);
        }
    }

    // TODO: re-enable once the synthetic `error`/`Throw` role resolution
    // closes the role-method bound in finalize (or at runtime). Currently
    // `fail e` / `e.throw` inside `fs_err::wrap:` leaves the apply graph for
    // `#op:prefix:fail` with an unresolved `Throw<_, throws = γ>` constraint,
    // so finalize either raises `IncompleteGraph` (with `fail`) or the VM
    // sees the role method as an unhandled request (with explicit `.throw`).
    #[test]
    #[ignore = "tracked: synthetic error wrap leaves Throw role unresolved in finalize"]
    fn std_no_cache_finalize_runs_error_wrap_fail_flow_regressions() {
        for case in [
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
            RuntimeType::Value(ty) => core_type_contains_unknown(ty),
            RuntimeType::Fun { param, ret } => type_has_unknown(param) || type_has_unknown(ret),
            RuntimeType::Thunk { effect, value } => {
                core_type_contains_unknown(effect) || type_has_unknown(value)
            }
        }
    }

    fn type_has_var(ty: &RuntimeType) -> bool {
        match ty {
            RuntimeType::Unknown => false,
            RuntimeType::Value(ty) => core_type_contains_var(ty),
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
                        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(e)
                        | yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(e) => e,
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
                        yulang_runtime_ir::FinalizedStmt::Let { value, .. } => {
                            walk_expr_for_coverage(value, stats);
                        }
                        yulang_runtime_ir::FinalizedStmt::Expr(e) => {
                            walk_expr_for_coverage(e, stats)
                        }
                        yulang_runtime_ir::FinalizedStmt::Module { body, .. } => {
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
                source: include_str!("../../../../examples/01_struct_with.yu"),
            },
            RuntimeOracleCase {
                name: "03_for_last",
                source: include_str!("../../../../examples/03_for_last.yu"),
            },
            RuntimeOracleCase {
                name: "04_sub_return",
                source: include_str!("../../../../examples/04_sub_return.yu"),
            },
            RuntimeOracleCase {
                name: "05_undet_all",
                source: include_str!("../../../../examples/05_undet_all.yu"),
            },
            RuntimeOracleCase {
                name: "06_undet_once",
                source: include_str!("../../../../examples/06_undet_once.yu"),
            },
            RuntimeOracleCase {
                name: "07_junction",
                source: include_str!("../../../../examples/07_junction.yu"),
            },
            RuntimeOracleCase {
                name: "08_types",
                source: include_str!("../../../../examples/08_types.yu"),
            },
            RuntimeOracleCase {
                name: "09_optional_record_args",
                source: include_str!("../../../../examples/09_optional_record_args.yu"),
            },
            RuntimeOracleCase {
                name: "10_effect_handler",
                source: include_str!("../../../../examples/10_effect_handler.yu"),
            },
            RuntimeOracleCase {
                name: "11_attached_impl",
                source: include_str!("../../../../examples/11_attached_impl.yu"),
            },
            RuntimeOracleCase {
                name: "12_cast",
                source: include_str!("../../../../examples/12_cast.yu"),
            },
            RuntimeOracleCase {
                name: "13_console",
                source: include_str!("../../../../examples/13_console.yu"),
            },
        ]
    }

    fn assert_legacy_and_finalize_match_module<M>(name: &str, module: M, vm: OracleVm)
    where
        M: IntoFinalizeRuntimeModule + Clone,
    {
        let legacy = run_legacy_runtime_module(name, module.clone(), vm);
        let finalized = run_finalize_runtime_module(name, module, vm);
        assert_eq!(finalized, legacy, "{name}");
    }

    fn run_legacy_runtime_module<M>(name: &str, module: M, vm: OracleVm) -> RuntimeOracleOutput
    where
        M: IntoFinalizeRuntimeModule,
    {
        run_finalize_runtime_module(name, module, vm)
    }

    fn run_finalize_runtime_module<M>(name: &str, module: M, vm: OracleVm) -> RuntimeOracleOutput
    where
        M: IntoFinalizeRuntimeModule,
    {
        let module = finalize_monomorphize_module(module)
            .unwrap_or_else(|error| panic!("{name} finalize failed: {error}"));
        run_vm_module(name, "finalize", module, vm)
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
                        RuntimeType::Value(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
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

    fn runtime_module_from_source_without_std(src: &str) -> LoweredModule {
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

    fn runtime_module_from_source_with_std_no_cache(src: &str) -> LoweredModule {
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
