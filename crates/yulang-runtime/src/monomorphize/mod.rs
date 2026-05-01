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
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::ResolveResidualRoleMethods,
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::ResolveResidualRoleMethods,
    MonoPass::RewriteUses,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::ResolveResidualRoleMethods,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
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
        module = apply_mono_pass(module, *pass)?;
        if let Some(before) = before {
            let after = MonoStats::from_module(&module);
            eprintln!(
                "mono pass {:>38}: bindings {} -> {}, roots {} -> {}",
                pass.name(),
                before.bindings,
                after.bindings,
                before.roots,
                after.roots
            );
        }
    }
    Ok(module)
}

fn apply_mono_pass(module: Module, pass: MonoPass) -> RuntimeResult<Module> {
    match pass {
        MonoPass::RewriteUses => Ok(rewrite_monomorphic_uses(module, false)),
        MonoPass::RefineTypes => refine_module_types(module),
        MonoPass::RefreshClosedSchemes => Ok(refresh_closed_specialized_schemes(module)),
        MonoPass::CanonicalizeSpecializations => {
            Ok(canonicalize_equivalent_specializations(module))
        }
        MonoPass::InlineNullaryConstructors => Ok(inline_polymorphic_nullary_constructors(module)),
        MonoPass::ResolveSpecializedResidualAssociated => {
            Ok(resolve_specialized_residual_associated_bindings(module))
        }
        MonoPass::ResolveResidualRoleMethods => Ok(resolve_residual_role_method_calls(module)),
        MonoPass::PruneUnreachable => Ok(prune_unreachable_bindings(module)),
        MonoPass::ResolveResidualAssociated => Ok(resolve_residual_associated_bindings(module)),
    }
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

fn rewrite_monomorphic_uses(module: Module, prune: bool) -> Module {
    let mut monomorphizer = Monomorphizer::new(&module);
    let original_len = module.bindings.len();
    let reachable_originals =
        reachable_binding_paths(&module.bindings, &module.root_exprs, &module.roots);
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
                changed = true;
            }
        }

        let specialized = std::mem::take(&mut monomorphizer.specialized);
        if !specialized.is_empty() {
            lowered.bindings.extend(specialized);
            changed = true;
        }

        if !changed {
            break;
        }
    }
    if prune {
        prune_unreachable_bindings(lowered)
    } else {
        lowered
    }
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
