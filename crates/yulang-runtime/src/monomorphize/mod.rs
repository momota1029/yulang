//! Specialize runtime IR until it is executable by the VM.
//!
//! This stage may clone bindings at concrete use sites, refine runtime types,
//! resolve residual role calls, and remove unreachable helpers.  It should not
//! invent new source semantics.  In particular, thunk shape and effect hygiene
//! introduced by runtime lowering must be preserved rather than reconstructed
//! from erased value types.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use yulang_core_ir as core_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult};
use crate::invariant::{RuntimeStage, check_runtime_invariants};
use crate::ir::{
    Binding, Expr, ExprKind, HandleArm, MatchArm, Module, Pattern, RecordExprField,
    RecordPatternField, RecordSpreadExpr, RecordSpreadPattern, ResumeBinding, Root, Stmt,
    Type as RuntimeType, TypeInstantiation,
};
use crate::refine::refine_module_types;
use crate::types::{
    BoundsChoice, choose_bounds_type, choose_hir_bounds_type, collect_expr_type_vars,
    collect_hir_type_vars, collect_type_vars as collect_core_type_vars, core_type_has_vars,
    core_types_compatible, diagnostic_core_type, effect_is_empty, effect_paths, effect_paths_match,
    hir_type_has_vars, hir_type_is_hole, infer_effectful_type_substitutions,
    infer_type_substitutions, is_nullary_constructor_path_for_type, project_runtime_effect,
    project_runtime_hir_type_with_vars, project_runtime_type_with_vars, should_thunk_effect,
    substitute_apply_evidence, substitute_join_evidence, substitute_scheme, substitute_type,
    type_compatible, type_path_last_is,
};
use crate::validate::validate_module;

mod canonicalize;
mod locals;
mod normalize;
mod reachability;
mod residual_roles;
mod rewrite;
mod shape;
mod specialize;
mod substitute;

use canonicalize::*;
use locals::*;
use normalize::*;
use reachability::*;
use residual_roles::*;
use rewrite::*;
use shape::*;
use specialize::*;
use substitute::*;

pub fn monomorphize_module(module: Module) -> RuntimeResult<Module> {
    let lowered = run_mono_pipeline(module)?;
    ensure_monomorphic_bindings(&lowered)?;
    check_runtime_invariants(&lowered, RuntimeStage::Monomorphized)?;
    validate_module(&lowered)?;
    Ok(lowered)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MonoPass {
    RewriteUses,
    RefineTypes,
    RefreshClosedSchemes,
    CanonicalizeSpecializations,
    InlineNullaryConstructors,
    ResolveSpecializedResidualAssociated,
    ResolveResidualRoleMethods,
    Stabilize,
    PruneUnreachable,
    ResolveResidualAssociated,
}

impl MonoPass {
    fn name(self) -> &'static str {
        match self {
            MonoPass::RewriteUses => "rewrite-uses",
            MonoPass::RefineTypes => "refine-types",
            MonoPass::RefreshClosedSchemes => "refresh-closed-schemes",
            MonoPass::CanonicalizeSpecializations => "canonicalize-specializations",
            MonoPass::InlineNullaryConstructors => "inline-nullary-constructors",
            MonoPass::ResolveSpecializedResidualAssociated => {
                "resolve-specialized-residual-associated"
            }
            MonoPass::ResolveResidualRoleMethods => "resolve-residual-role-methods",
            MonoPass::Stabilize => "stabilize",
            MonoPass::PruneUnreachable => "prune-unreachable",
            MonoPass::ResolveResidualAssociated => "resolve-residual-associated",
        }
    }
}

const MONO_PIPELINE: &[MonoPass] = &[
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::CanonicalizeSpecializations,
    MonoPass::InlineNullaryConstructors,
    MonoPass::ResolveSpecializedResidualAssociated,
    MonoPass::ResolveResidualRoleMethods,
    MonoPass::Stabilize,
    MonoPass::PruneUnreachable,
    MonoPass::ResolveResidualRoleMethods,
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::ResolveResidualAssociated,
];

fn run_mono_pipeline(module: Module) -> RuntimeResult<Module> {
    let debug = std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some();
    let mut module = module;
    for pass in MONO_PIPELINE {
        let before = debug.then(|| MonoStats::from_module(&module));
        let step = apply_mono_pass(module, *pass)?;
        module = step.module;
        if let Some(before) = before {
            let after = MonoStats::from_module(&module);
            eprintln!(
                "mono pass {:>38}: bindings {} -> {}, roots {} -> {}, progress {}",
                pass.name(),
                before.bindings,
                after.bindings,
                before.roots,
                after.roots,
                step.progress.format()
            );
        }
    }
    Ok(module)
}

fn apply_mono_pass(module: Module, pass: MonoPass) -> RuntimeResult<MonoStep> {
    match pass {
        MonoPass::RewriteUses => Ok(rewrite_monomorphic_uses(module, false)),
        MonoPass::RefineTypes => run_tracked_pass(module, refine_module_types),
        MonoPass::RefreshClosedSchemes => {
            run_tracked_infallible_pass(module, refresh_closed_specialized_schemes)
        }
        MonoPass::CanonicalizeSpecializations => {
            run_tracked_infallible_pass(module, canonicalize_equivalent_specializations)
        }
        MonoPass::InlineNullaryConstructors => {
            run_tracked_infallible_pass(module, inline_polymorphic_nullary_constructors)
        }
        MonoPass::ResolveSpecializedResidualAssociated => {
            run_tracked_infallible_pass(module, resolve_specialized_residual_associated_bindings)
        }
        MonoPass::ResolveResidualRoleMethods => {
            run_tracked_infallible_pass(module, resolve_residual_role_method_calls)
        }
        MonoPass::Stabilize => run_stabilization_loop(module),
        MonoPass::PruneUnreachable => {
            run_tracked_infallible_pass(module, prune_unreachable_bindings)
        }
        MonoPass::ResolveResidualAssociated => {
            run_tracked_infallible_pass(module, resolve_residual_associated_bindings)
        }
    }
}

const STABILIZATION_ROUND: &[MonoPass] = &[
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::ResolveResidualRoleMethods,
];

fn run_stabilization_loop(module: Module) -> RuntimeResult<MonoStep> {
    let debug = std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some();
    let mut module = module;
    let mut total_progress = MonoProgress::default();
    for round in 0..8 {
        let mut round_progress = MonoProgress::default();
        for pass in STABILIZATION_ROUND {
            let step = apply_mono_pass(module, *pass)?;
            module = step.module;
            round_progress.merge(step.progress);
        }
        total_progress.merge(round_progress);
        if !round_progress.changed() {
            if debug {
                eprintln!("mono stabilize converged after {round} rounds");
            }
            return Ok(MonoStep {
                module,
                progress: total_progress,
            });
        } else if debug {
            eprintln!(
                "mono stabilize round {round}: progress {}",
                round_progress.format()
            );
        }
    }
    if debug {
        eprintln!("mono stabilize reached round limit");
    }
    Ok(MonoStep {
        module,
        progress: total_progress,
    })
}

struct MonoStats {
    bindings: usize,
    roots: usize,
}

impl MonoStats {
    fn from_module(module: &Module) -> Self {
        Self {
            bindings: module.bindings.len(),
            roots: module.root_exprs.len(),
        }
    }
}

struct MonoStep {
    module: Module,
    progress: MonoProgress,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct MonoProgress {
    changed_bindings: usize,
    changed_roots: usize,
    added_specializations: usize,
}

impl MonoProgress {
    fn changed(self) -> bool {
        self.changed_bindings > 0 || self.changed_roots > 0 || self.added_specializations > 0
    }

    fn merge(&mut self, other: Self) {
        self.changed_bindings += other.changed_bindings;
        self.changed_roots += other.changed_roots;
        self.added_specializations += other.added_specializations;
    }

    fn from_modules(before: &Module, after: &Module) -> Self {
        let changed_roots = changed_item_count(&before.root_exprs, &after.root_exprs);
        let changed_bindings = changed_item_count(&before.bindings, &after.bindings);
        Self {
            changed_bindings,
            changed_roots,
            added_specializations: after.bindings.len().saturating_sub(before.bindings.len()),
        }
    }

    fn format(self) -> String {
        if !self.changed() {
            return "none".to_string();
        }
        format!(
            "bindings={}, roots={}, new-specializations={}",
            self.changed_bindings, self.changed_roots, self.added_specializations
        )
    }
}

fn changed_item_count<T: PartialEq>(before: &[T], after: &[T]) -> usize {
    let pair_changes = before
        .iter()
        .zip(after.iter())
        .filter(|(before, after)| before != after)
        .count();
    let length_delta = before.len().abs_diff(after.len());
    pair_changes + length_delta
}

fn run_tracked_pass<F>(module: Module, f: F) -> RuntimeResult<MonoStep>
where
    F: FnOnce(Module) -> RuntimeResult<Module>,
{
    let before = module.clone();
    let module = f(module)?;
    let progress = MonoProgress::from_modules(&before, &module);
    Ok(MonoStep { module, progress })
}

fn run_tracked_infallible_pass<F>(module: Module, f: F) -> RuntimeResult<MonoStep>
where
    F: FnOnce(Module) -> Module,
{
    run_tracked_pass(module, |module| Ok(f(module)))
}

fn rewrite_monomorphic_uses(module: Module, prune: bool) -> MonoStep {
    let mut monomorphizer = Monomorphizer::new(&module);
    let original_len = module.bindings.len();
    let reachable_originals =
        reachable_binding_paths(&module.bindings, &module.root_exprs, &module.roots);
    let mut progress = MonoProgress::default();
    let mut lowered = Module {
        path: module.path,
        bindings: module.bindings,
        root_exprs: module.root_exprs,
        roots: module.roots,
    };
    for _ in 0..64 {
        let mut changed = false;

        let root_exprs = monomorphizer.rewrite_exprs(lowered.root_exprs.clone());
        if root_exprs != lowered.root_exprs {
            lowered.root_exprs = root_exprs;
            progress.changed_roots += 1;
            changed = true;
        }

        let current_len = lowered.bindings.len();
        for index in 0..current_len {
            if !should_rewrite_binding(
                index,
                original_len,
                &reachable_originals,
                &lowered.bindings[index],
            ) {
                continue;
            }
            let body = lowered.bindings[index].body.clone();
            let body_ty = body.ty.clone();
            let rewritten = monomorphizer.rewrite_expr_with_expected(body, Some(&body_ty));
            if rewritten != lowered.bindings[index].body {
                lowered.bindings[index].body = rewritten;
                progress.changed_bindings += 1;
                changed = true;
            }
        }

        let specialized = std::mem::take(&mut monomorphizer.specialized);
        if !specialized.is_empty() {
            progress.added_specializations += specialized.len();
            progress.changed_bindings += specialized.len();
            lowered.bindings.extend(specialized);
            changed = true;
        }

        if !changed {
            break;
        }
    }
    let module = if prune {
        let before_prune = lowered.clone();
        let pruned = prune_unreachable_bindings(lowered);
        progress.merge(MonoProgress::from_modules(&before_prune, &pruned));
        pruned
    } else {
        lowered
    };
    MonoStep { module, progress }
}

fn should_rewrite_binding(
    index: usize,
    original_len: usize,
    reachable_originals: &HashSet<core_ir::Path>,
    binding: &Binding,
) -> bool {
    if index >= original_len {
        return true;
    }
    if !reachable_originals.contains(&binding.name) {
        return false;
    }
    binding.type_params.is_empty() || is_specialized_path(&binding.name)
}
