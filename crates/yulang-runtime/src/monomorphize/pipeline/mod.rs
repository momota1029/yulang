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
use crate::monomorphize::demand_monomorphize_module;
use crate::refine::refine_module_types_with_report;
use crate::types::{
    collect_expr_type_vars, collect_hir_type_vars, collect_type_vars as collect_core_type_vars,
    core_type_has_vars, hir_type_has_vars, project_runtime_effect, should_thunk_effect,
    substitute_apply_evidence, substitute_join_evidence, substitute_scheme, substitute_type,
};
use crate::validate::validate_module;

mod canonicalize;
mod locals;
mod normalize;
mod paths;
mod reachability;
mod shape;
mod substitute;

use canonicalize::*;
use locals::*;
use normalize::*;
use paths::*;
use reachability::*;
use shape::*;
use substitute::*;

pub fn monomorphize_module(module: Module) -> RuntimeResult<Module> {
    let (lowered, _) = monomorphize_module_profiled(module)?;
    Ok(lowered)
}

pub fn monomorphize_module_profiled(
    module: Module,
) -> RuntimeResult<(Module, MonomorphizeProfile)> {
    let (lowered, profile) = run_mono_pipeline(module)?;
    ensure_monomorphic_bindings(&lowered)?;
    check_runtime_invariants(&lowered, RuntimeStage::Monomorphized)?;
    validate_module(&lowered)?;
    Ok((lowered, profile))
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct MonomorphizeProfile {
    pub passes: Vec<MonomorphizePassProfile>,
}

impl MonomorphizeProfile {
    pub fn pass_count(&self) -> usize {
        self.passes.len()
    }

    pub fn added_specializations(&self) -> usize {
        self.passes
            .iter()
            .map(|pass| pass.progress.added_specializations)
            .sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonomorphizePassProfile {
    pub name: &'static str,
    pub bindings_before: usize,
    pub bindings_after: usize,
    pub roots_before: usize,
    pub roots_after: usize,
    pub progress: MonomorphizeProgress,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct MonomorphizeProgress {
    pub changed_bindings: usize,
    pub changed_roots: usize,
    pub added_specializations: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MonoPass {
    DemandSpecialize,
    RefineTypes,
    RefreshClosedSchemes,
    CanonicalizeSpecializations,
    InlineNullaryConstructors,
    PruneUnreachableSpecializations,
    PruneUnreachable,
}

impl MonoPass {
    fn name(self) -> &'static str {
        match self {
            MonoPass::DemandSpecialize => "demand-specialize",
            MonoPass::RefineTypes => "refine-types",
            MonoPass::RefreshClosedSchemes => "refresh-closed-schemes",
            MonoPass::CanonicalizeSpecializations => "canonicalize-specializations",
            MonoPass::InlineNullaryConstructors => "inline-nullary-constructors",
            MonoPass::PruneUnreachableSpecializations => "prune-unreachable-specializations",
            MonoPass::PruneUnreachable => "prune-unreachable",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MonoStage {
    Pass(MonoPass),
    Repeat {
        name: &'static str,
        passes: &'static [MonoPass],
        times: usize,
    },
    Fixpoint {
        name: &'static str,
        passes: &'static [MonoPass],
        limit: usize,
    },
}

const INITIAL_FIXPOINT: &[MonoPass] = &[MonoPass::DemandSpecialize, MonoPass::RefineTypes];

const SPECIALIZATION_FIXPOINT: &[MonoPass] = &[
    MonoPass::DemandSpecialize,
    MonoPass::RefineTypes,
    MonoPass::RefreshClosedSchemes,
    MonoPass::PruneUnreachableSpecializations,
];

const MONO_PIPELINE: &[MonoStage] = &[
    MonoStage::Repeat {
        name: "initial-specialization",
        passes: INITIAL_FIXPOINT,
        times: 1,
    },
    MonoStage::Pass(MonoPass::CanonicalizeSpecializations),
    MonoStage::Pass(MonoPass::InlineNullaryConstructors),
    MonoStage::Fixpoint {
        name: "role-specialization",
        passes: SPECIALIZATION_FIXPOINT,
        limit: 8,
    },
    MonoStage::Pass(MonoPass::PruneUnreachable),
];

fn run_mono_pipeline(module: Module) -> RuntimeResult<(Module, MonomorphizeProfile)> {
    let debug = std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some();
    let mut module = module;
    let mut profile = MonomorphizeProfile::default();
    for stage in MONO_PIPELINE {
        match *stage {
            MonoStage::Pass(pass) => {
                let step = run_profiled_mono_pass(module, pass, &mut profile, debug)?;
                module = step.module;
            }
            MonoStage::Repeat {
                name,
                passes,
                times,
            } => {
                module = run_mono_repeat(module, name, passes, times, &mut profile, debug)?;
            }
            MonoStage::Fixpoint {
                name,
                passes,
                limit,
            } => {
                module = run_mono_fixpoint(module, name, passes, limit, &mut profile, debug)?;
            }
        }
    }
    Ok((module, profile))
}

fn run_mono_repeat(
    mut module: Module,
    name: &'static str,
    passes: &'static [MonoPass],
    times: usize,
    profile: &mut MonomorphizeProfile,
    debug: bool,
) -> RuntimeResult<Module> {
    for round in 0..times {
        let mut round_progress = MonoProgress::default();
        for pass in passes {
            let step = run_profiled_mono_pass(module, *pass, profile, debug)?;
            module = step.module;
            round_progress.merge(step.progress);
        }
        if debug {
            eprintln!(
                "mono repeat {name} round {round}: progress {}",
                round_progress.format()
            );
        }
        if !round_progress.changed() {
            break;
        }
    }
    Ok(module)
}

fn run_profiled_mono_pass(
    module: Module,
    pass: MonoPass,
    profile: &mut MonomorphizeProfile,
    debug: bool,
) -> RuntimeResult<MonoStep> {
    let before_for_changed_debug = std::env::var_os("YULANG_DEBUG_MONO_CHANGED")
        .is_some()
        .then(|| module.clone());
    let before = MonoStats::from_module(&module);
    let step = apply_mono_pass(module, pass)?;
    let after = MonoStats::from_module(&step.module);
    let progress = step.progress.to_public();
    profile.passes.push(MonomorphizePassProfile {
        name: pass.name(),
        bindings_before: before.bindings,
        bindings_after: after.bindings,
        roots_before: before.roots,
        roots_after: after.roots,
        progress,
    });
    if debug {
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
    if let Some(before) = before_for_changed_debug {
        debug_mono_changed_items(pass.name(), &before, &step.module);
    }
    Ok(step)
}

fn run_mono_fixpoint(
    mut module: Module,
    name: &'static str,
    passes: &'static [MonoPass],
    limit: usize,
    profile: &mut MonomorphizeProfile,
    debug: bool,
) -> RuntimeResult<Module> {
    for round in 0..limit {
        let round_start = module.clone();
        let mut round_progress = MonoProgress::default();
        for pass in passes {
            let step = run_profiled_mono_pass(module, *pass, profile, debug)?;
            module = step.module;
            round_progress.merge(step.progress);
        }
        if !round_progress.changed() || module == round_start {
            if debug {
                eprintln!("mono fixpoint {name} converged after {round} rounds");
            }
            return Ok(module);
        } else if debug {
            eprintln!(
                "mono fixpoint {name} round {round}: progress {}",
                round_progress.format()
            );
        }
    }
    if debug {
        eprintln!("mono fixpoint {name} reached round limit");
    }
    Ok(module)
}

fn apply_mono_pass(module: Module, pass: MonoPass) -> RuntimeResult<MonoStep> {
    match pass {
        MonoPass::DemandSpecialize => demand_specialize_module(module),
        MonoPass::RefineTypes => refine_module_types_for_mono(module),
        MonoPass::RefreshClosedSchemes => {
            run_tracked_infallible_pass(module, refresh_closed_specialized_schemes)
        }
        MonoPass::CanonicalizeSpecializations => {
            run_tracked_infallible_pass(module, canonicalize_equivalent_specializations)
        }
        MonoPass::InlineNullaryConstructors => {
            run_tracked_infallible_pass(module, inline_polymorphic_nullary_constructors)
        }
        MonoPass::PruneUnreachableSpecializations => {
            run_tracked_infallible_pass(module, prune_unreachable_specializations)
        }
        MonoPass::PruneUnreachable => {
            run_tracked_infallible_pass(module, prune_unreachable_bindings)
        }
    }
}

fn demand_specialize_module(module: Module) -> RuntimeResult<MonoStep> {
    let before = module.clone();
    let output =
        demand_monomorphize_module(module).map_err(|error| RuntimeError::InvariantViolation {
            stage: "monomorphization",
            context: format!("{error:?}"),
            message: "demand-driven specialization failed",
        })?;
    validate_module(&output.module)?;
    let progress = MonoProgress::from_modules(&before, &output.module);
    Ok(MonoStep {
        module: output.module,
        progress,
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

fn debug_mono_changed_items(pass: &str, before: &Module, after: &Module) {
    if std::env::var_os("YULANG_DEBUG_MONO_CHANGED").is_none() {
        return;
    }
    let changed_bindings = changed_binding_names(before, after);
    if !changed_bindings.is_empty() {
        eprintln!("mono changed {pass} bindings: {changed_bindings:?}");
    }
    let changed_roots = changed_root_indexes(before, after);
    if !changed_roots.is_empty() {
        eprintln!("mono changed {pass} roots: {changed_roots:?}");
    }
}

fn changed_binding_names(before: &Module, after: &Module) -> Vec<core_ir::Path> {
    let before_by_name = before
        .bindings
        .iter()
        .map(|binding| (&binding.name, binding))
        .collect::<HashMap<_, _>>();
    let mut names = Vec::new();
    for binding in &after.bindings {
        if before_by_name
            .get(&binding.name)
            .is_none_or(|before| *before != binding)
        {
            names.push(binding.name.clone());
        }
    }
    for binding in &before.bindings {
        if !after
            .bindings
            .iter()
            .any(|after| after.name == binding.name)
        {
            names.push(binding.name.clone());
        }
    }
    names
}

fn changed_root_indexes(before: &Module, after: &Module) -> Vec<usize> {
    let len = before.root_exprs.len().max(after.root_exprs.len());
    (0..len)
        .filter(|index| before.root_exprs.get(*index) != after.root_exprs.get(*index))
        .collect()
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

    fn to_public(self) -> MonomorphizeProgress {
        MonomorphizeProgress {
            changed_bindings: self.changed_bindings,
            changed_roots: self.changed_roots,
            added_specializations: self.added_specializations,
        }
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

fn refine_module_types_for_mono(module: Module) -> RuntimeResult<MonoStep> {
    let output = refine_module_types_with_report(module)?;
    let progress = MonoProgress {
        changed_bindings: output.report.changed_bindings,
        changed_roots: output.report.changed_roots,
        added_specializations: 0,
    };
    Ok(MonoStep {
        module: output.module,
        progress,
    })
}
