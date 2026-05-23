//! Specialize runtime IR until it is executable by the VM.
//!
//! This stage may clone bindings at concrete use sites, refine runtime types,
//! resolve residual role calls, and remove unreachable helpers.  It should not
//! invent new source semantics.  In particular, thunk shape and effect hygiene
//! introduced by runtime lowering must be preserved rather than reconstructed
//! from erased value types.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::time::Duration;

use yulang_typed_ir as typed_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult};
use crate::invariant::{
    RuntimeStage, check_runtime_invariants, check_strict_runtime_type_surfaces,
    check_strict_runtime_value_types,
};
use crate::ir::{
    Binding, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence, MatchArm, Module, Pattern,
    RecordExprField, RecordPatternField, RecordSpreadExpr, RecordSpreadPattern, ResumeBinding,
    Root, Stmt, Type as RuntimeType, TypeInstantiation,
};
use crate::monomorphize::{
    DemandEvidenceProfile, DemandQueueProfile, DemandSpecialization, demand_monomorphize_module,
    reset_demand_evidence_profile, snapshot_demand_evidence_profile,
};
use crate::refine::refine_module_types_with_report;
use crate::types::{
    collect_expr_type_vars, collect_hir_type_vars, collect_type_vars as collect_core_type_vars,
    core_type_has_vars, effect_is_empty, effect_paths_match, hir_type_has_vars,
    project_runtime_effect, project_runtime_type_with_vars, runtime_core_type, should_thunk_effect,
    substitute_type,
};
use crate::validate::validate_module;

mod audit;
mod canonicalize;
mod conflict_casts;
mod fill_holes;
mod handler_boundary;
mod local_refresh;
mod locals;
mod metadata;
mod never_effect_join;
mod normalize;
mod paths;
mod principal_elaborate;
mod principal_unify;
mod reachability;
mod shape;
mod substitute;
mod total_substitute;
mod type_graph;
mod type_projection_metrics;
mod type_surface;

use audit::*;
use canonicalize::*;
use conflict_casts::*;
use fill_holes::*;
use handler_boundary::*;
use local_refresh::*;
use locals::*;
use metadata::*;
use never_effect_join::*;
use normalize::*;
use paths::*;
use principal_elaborate::*;
use principal_unify::*;
use reachability::*;
use shape::*;
use substitute::*;
use total_substitute::*;
use type_surface::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MonomorphizeMode {
    PrincipalElaborate,
    LegacyDemandFixpoint,
}

impl MonomorphizeMode {
    fn detect() -> Self {
        if std::env::var_os("YULANG_LEGACY_MONO_FIXPOINT").is_some() {
            Self::LegacyDemandFixpoint
        } else {
            Self::PrincipalElaborate
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::PrincipalElaborate => "principal-elaborate",
            Self::LegacyDemandFixpoint => "legacy-demand-fixpoint",
        }
    }
}

impl Default for MonomorphizeMode {
    fn default() -> Self {
        Self::PrincipalElaborate
    }
}

pub fn monomorphize_module(module: Module) -> RuntimeResult<Module> {
    crate::monomorphize::effect_hole_metrics::reset();
    type_projection_metrics::reset();
    preview_type_graph_pipeline_if_requested("pre-monomorphize", &module);
    let lowered = run_mono_pipeline_unprofiled(module)?;
    let lowered = normalize_semantic_cast_coercions(lowered);
    let lowered = normalize_monomorphized_metadata(lowered);
    let lowered = normalize_parametric_primitive_intrinsics(lowered);
    preview_type_graph_pipeline_if_requested("post-monomorphize", &lowered);
    let (lowered, final_defaults) = fill_final_type_holes(lowered);
    report_final_type_holes_if_requested("final-defaults", &final_defaults);
    preview_type_graph_pipeline_if_requested("final-defaulted", &lowered);
    audit_monomorphized_module(&lowered)?;
    check_runtime_invariants(&lowered, RuntimeStage::Monomorphized)?;
    check_strict_monomorphized_runtime_types_if_requested(&lowered)?;
    validate_module(&lowered)?;
    crate::monomorphize::effect_hole_metrics::report_if_requested("monomorphize_module");
    type_projection_metrics::report_if_requested("monomorphize_module");
    Ok(lowered)
}

pub fn monomorphize_module_profiled(
    module: Module,
) -> RuntimeResult<(Module, MonomorphizeProfile)> {
    crate::monomorphize::effect_hole_metrics::reset();
    type_projection_metrics::reset();
    preview_type_graph_pipeline_if_requested("pre-monomorphize", &module);
    let (lowered, profile) = run_mono_pipeline(module)?;
    let lowered = normalize_semantic_cast_coercions(lowered);
    let lowered = normalize_monomorphized_metadata(lowered);
    let lowered = normalize_parametric_primitive_intrinsics(lowered);
    preview_type_graph_pipeline_if_requested("post-monomorphize", &lowered);
    let (lowered, final_defaults) = fill_final_type_holes(lowered);
    report_final_type_holes_if_requested("final-defaults", &final_defaults);
    preview_type_graph_pipeline_if_requested("final-defaulted", &lowered);
    audit_monomorphized_module(&lowered)?;
    check_runtime_invariants(&lowered, RuntimeStage::Monomorphized)?;
    check_strict_monomorphized_runtime_types_if_requested(&lowered)?;
    validate_module(&lowered)?;
    crate::monomorphize::effect_hole_metrics::report_if_requested("monomorphize_module_profiled");
    type_projection_metrics::report_if_requested("monomorphize_module_profiled");
    Ok((lowered, profile))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonomorphizeProfile {
    pub mode: MonomorphizeMode,
    pub passes: Vec<MonomorphizePassProfile>,
    pub demand_evidence: DemandEvidenceProfile,
}

impl Default for MonomorphizeProfile {
    fn default() -> Self {
        Self {
            mode: MonomorphizeMode::default(),
            passes: Vec::new(),
            demand_evidence: DemandEvidenceProfile::default(),
        }
    }
}

impl MonomorphizeProfile {
    pub fn pass_count(&self) -> usize {
        self.passes.len()
    }

    pub fn effective_pass_count(&self) -> usize {
        self.passes
            .iter()
            .filter(|pass| pass.progress.changed())
            .count()
    }

    pub fn added_specializations(&self) -> usize {
        self.passes
            .iter()
            .map(|pass| pass.progress.added_specializations)
            .sum()
    }

    pub fn demand_queue_profile(&self) -> DemandQueueProfile {
        self.passes
            .iter()
            .fold(DemandQueueProfile::default(), |mut profile, pass| {
                profile.merge(pass.demand_queue);
                profile
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MonomorphizePassProfile {
    pub name: &'static str,
    pub duration: Duration,
    pub bindings_before: usize,
    pub bindings_after: usize,
    pub roots_before: usize,
    pub roots_after: usize,
    pub progress: MonomorphizeProgress,
    pub demand_queue: DemandQueueProfile,
    pub principal_elaborate: SubstitutionSpecializeProfile,
    pub added_binding_paths: Vec<typed_ir::Path>,
    pub added_specializations: Vec<DemandSpecialization>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeProfile {
    pub stats: HashMap<&'static str, usize>,
    pub timings: HashMap<&'static str, Duration>,
    pub target_skips: Vec<SubstitutionSpecializeTargetSkips>,
    pub target_inferences: Vec<SubstitutionSpecializeTargetInferences>,
    pub target_rewrites: Vec<SubstitutionSpecializeTargetRewrites>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeTargetSkips {
    pub target: typed_ir::Path,
    pub survives_final_prune: Option<bool>,
    pub actionable: bool,
    pub reasons: Vec<SubstitutionSpecializeSkipCount>,
    pub missing_vars: Vec<SubstitutionSpecializeMissingVarCount>,
    pub no_complete_causes: Vec<SubstitutionSpecializeSkipCount>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeSkipCount {
    pub reason: &'static str,
    pub count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeMissingVarCount {
    pub var: typed_ir::TypeVar,
    pub count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeTargetRewrites {
    pub target: typed_ir::Path,
    pub total_apply_visits: usize,
    pub rewrites: usize,
    pub cached_incomplete: usize,
    pub incomplete: usize,
    pub max_specialization_depth: usize,
    pub contexts: Vec<SubstitutionSpecializeRewriteContextCount>,
    pub phases: Vec<SubstitutionSpecializeRewritePhaseTiming>,
    pub expr_kinds: Vec<SubstitutionSpecializeRewriteExprKindTiming>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeRewriteContextCount {
    pub context: &'static str,
    pub count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeRewritePhaseTiming {
    pub phase: &'static str,
    pub duration: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeRewriteExprKindTiming {
    pub kind: &'static str,
    pub count: usize,
    pub duration: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeTargetInferences {
    pub target: typed_ir::Path,
    pub sources: Vec<SubstitutionSpecializeInferenceCount>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubstitutionSpecializeInferenceCount {
    pub source: &'static str,
    pub count: usize,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct MonomorphizeProgress {
    pub changed_bindings: usize,
    pub changed_roots: usize,
    pub added_specializations: usize,
}

impl MonomorphizeProgress {
    pub fn changed(self) -> bool {
        self.changed_bindings > 0 || self.changed_roots > 0 || self.added_specializations > 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MonoPass {
    PrincipalElaborate,
    DemandSpecialize,
    RefineTypes,
    RefreshClosedSchemes,
    SemanticCastCoercions,
    CanonicalizeSpecializations,
    InlinePolymorphicWrappers,
    PruneUnreachableSpecializations,
    PruneUnreachable,
}

impl MonoPass {
    fn name(self) -> &'static str {
        match self {
            MonoPass::PrincipalElaborate => "principal-elaborate",
            MonoPass::DemandSpecialize => "demand-specialize",
            MonoPass::RefineTypes => "refine-types",
            MonoPass::RefreshClosedSchemes => "refresh-closed-schemes",
            MonoPass::SemanticCastCoercions => "semantic-cast-coercions",
            MonoPass::CanonicalizeSpecializations => "canonicalize-specializations",
            MonoPass::InlinePolymorphicWrappers => "inline-polymorphic-wrappers",
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
    MonoStage::Pass(MonoPass::InlinePolymorphicWrappers),
    MonoStage::Fixpoint {
        name: "role-specialization",
        passes: SPECIALIZATION_FIXPOINT,
        limit: 8,
    },
    MonoStage::Pass(MonoPass::SemanticCastCoercions),
    MonoStage::Pass(MonoPass::PruneUnreachable),
];

fn run_mono_pipeline(module: Module) -> RuntimeResult<(Module, MonomorphizeProfile)> {
    let mode = MonomorphizeMode::detect();
    reset_demand_evidence_profile();
    let (module, mut profile) = match mode {
        MonomorphizeMode::PrincipalElaborate => run_principal_elaborate_pipeline(module)?,
        MonomorphizeMode::LegacyDemandFixpoint => run_legacy_demand_fixpoint_pipeline(module)?,
    };
    profile.mode = mode;
    profile.demand_evidence = snapshot_demand_evidence_profile();
    annotate_substitution_skip_reachability(&mut profile, &module);
    Ok((module, profile))
}

fn run_principal_elaborate_pipeline(
    module: Module,
) -> RuntimeResult<(Module, MonomorphizeProfile)> {
    let debug = std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some();
    let mut module = module;
    let mut profile = MonomorphizeProfile::default();
    let step = run_profiled_mono_pass(
        module,
        MonoPass::InlinePolymorphicWrappers,
        &mut profile,
        debug,
    )?;
    module = step.module;
    module = run_principal_elaborate_fixpoint(module, 8, &mut profile, debug)?;
    let step =
        run_profiled_mono_pass(module, MonoPass::SemanticCastCoercions, &mut profile, debug)?;
    module = step.module;
    let step = run_profiled_mono_pass(module, MonoPass::PruneUnreachable, &mut profile, debug)?;
    module = step.module;
    module = remove_specialized_generic_original_bindings(module);
    module = remove_runtime_unreferenced_generic_bindings(module);
    if std::env::var_os("YULANG_PRINCIPAL_ELABORATE_STRICT").is_some()
        && let Some(context) = principal_elaborate_strict_failure(&module)
    {
        return Err(RuntimeError::InvariantViolation {
            stage: "principal-elaborate",
            context,
            message: "principal elaboration plan incomplete",
        });
    }
    Ok((module, profile))
}

fn check_strict_monomorphized_runtime_types_if_requested(module: &Module) -> RuntimeResult<()> {
    if std::env::var_os("YULANG_STRICT_MONO_RUNTIME_TYPES").is_some() {
        check_strict_runtime_value_types(module, RuntimeStage::Monomorphized)?;
    }
    if std::env::var_os("YULANG_STRICT_MONO_TYPE_SURFACES").is_some() {
        check_strict_runtime_type_surfaces(module, RuntimeStage::Monomorphized)?;
    }
    Ok(())
}

fn report_final_type_holes_if_requested(label: &'static str, report: &FillHolesReport) {
    if std::env::var_os("YULANG_DEBUG_TYPE_GRAPH_PIPELINE").is_none() {
        return;
    }
    eprintln!(
        "type graph {label}: applied_filled_value_holes={} applied_filled_effect_holes={}",
        report.filled_value_holes, report.filled_effect_holes,
    );
}

fn preview_type_graph_pipeline_if_requested(label: &'static str, module: &Module) {
    if std::env::var_os("YULANG_DEBUG_TYPE_GRAPH_PIPELINE").is_none() {
        return;
    }
    let total = total_substitute_module_preview(module);
    let casts = insert_conflict_casts_preview(module);
    eprintln!(
        "type graph preview[{label}]: slots={} edges={} conflicts={} binding_slots={} apply_edges={} direct_mismatches={} direct_mismatch_equal_edges={} direct_mismatch_apply_edges={} direct_mismatch_let_edges={} root_index_sum={} local_name_bytes={} self_edges={} bounds_evidence={} bounds_lower_candidates={} bounds_exact_candidates={} bounds_upper_requirements={} bounds_upper_only_dependencies={} bounds_bottom_like_exclusions={} bounds_empty={} bounds_lower_upper_diverged={} bounds_lower_visible_diverged={} apply_callee_bounds={} apply_arg_bounds={} apply_result_bounds={} handler_result_bounds={} slots_with_lower_evidence={} slots_with_closed_lower_evidence={} slots_with_multiple_lower_evidence={} slots_with_upper_requirements={} slots_with_only_upper_requirements={} role_bounds_evidence={} role_input_lower_candidates={} role_associated_lower_candidates={} role_upper_only_dependencies={} role_bottom_like_exclusions={} role_associated_resolution_attempts={} role_associated_resolution_missing_inputs={} role_associated_resolution_missing_impls={} role_associated_resolution_ambiguous_impls={} role_associated_resolution_resolved={} role_associated_resolution_projected_type_vars={} type_var_lower_evidence={} type_var_lower_derived_structural_evidence={} type_var_lower_vars={} type_var_lower_scoped_vars={} type_var_lower_vars_used_in_multiple_scopes={} type_var_lower_solved_vars={} type_var_lower_closed_solved_vars={} type_var_lower_recursive_substitution_vars={} type_var_lower_closed_after_recursive_substitution_vars={} type_var_lower_residual_open_vars_after_recursive_substitution={} type_var_lower_residual_open_recursive_cycle_vars_after_substitution={} type_var_lower_residual_open_missing_substitution_vars_after_substitution={} type_var_lower_residual_open_with_apply_substitution={} type_var_lower_residual_open_with_principal_candidate={} type_var_lower_residual_open_with_principal_elaboration={} type_var_lower_residual_open_with_type_instantiation={} type_var_lower_residual_open_with_role_associated_resolution={} type_var_lower_residual_open_with_structural_decomposition={} type_var_lower_residual_open_with_mixed_sources={} type_var_lower_structural_iterations={} type_var_lower_structural_candidate_visits={} type_var_lower_structural_addition_attempts={} type_var_lower_conflicting_vars={} type_var_lower_closed_conflicting_vars={} type_var_lower_conflicts_with_apply_substitution={} type_var_lower_conflicts_with_principal_candidate={} type_var_lower_conflicts_with_principal_elaboration={} type_var_lower_conflicts_with_type_instantiation={} type_var_lower_conflicts_with_role_associated_resolution={} type_var_lower_conflicts_with_structural_decomposition={} type_var_lower_conflicts_with_mixed_sources={} type_var_lower_bottom_like_exclusions={} type_var_lower_identity_exclusions={} lower_snapshot_solved_slots={} lower_snapshot_closed_solved_slots={} lower_snapshot_open_solved_slots={} lower_snapshot_conflicting_lower_slots={} lower_snapshot_closed_conflicting_lower_slots={} lower_snapshot_upper_only_slots={} lower_snapshot_slots_without_bounds={} lower_snapshot_solved_groups={} lower_snapshot_conflicting_lower_groups={} lower_snapshot_upper_only_groups={} lower_snapshot_groups_without_bounds={} lower_solution_checked_edges={} lower_solution_mismatched_edges={} lower_solution_unresolved_edges={} upper_supplement_requirements={} upper_supplement_checked_against_lower={} upper_supplement_satisfied_by_lower={} upper_supplement_mismatched_with_lower={} upper_supplemented_slots={} upper_supplement_closed_slots={} upper_supplement_open_slots={} upper_supplement_ambiguous_slots={} applied_slots={} inserted_casts={} unresolved_conflicts={} filled_value_holes={} filled_effect_holes={}",
        total.graph.slots,
        total.graph.edges,
        total.graph.conflicts,
        total.graph.binding_slots,
        total.graph.apply_edges,
        total.graph.direct_mismatches,
        total.graph.direct_mismatch_equal_edges,
        total.graph.direct_mismatch_apply_edges,
        total.graph.direct_mismatch_let_edges,
        total.graph.root_index_sum,
        total.graph.local_name_bytes,
        total.graph.self_edges,
        total.graph.bounds_evidence,
        total.graph.bounds_lower_candidates,
        total.graph.bounds_exact_candidates,
        total.graph.bounds_upper_requirements,
        total.graph.bounds_upper_only_dependencies,
        total.graph.bounds_bottom_like_exclusions,
        total.graph.bounds_empty,
        total.graph.bounds_lower_upper_diverged,
        total.graph.bounds_lower_visible_diverged,
        total.graph.apply_callee_bounds,
        total.graph.apply_arg_bounds,
        total.graph.apply_result_bounds,
        total.graph.handler_result_bounds,
        total.graph.slots_with_lower_evidence,
        total.graph.slots_with_closed_lower_evidence,
        total.graph.slots_with_multiple_lower_evidence,
        total.graph.slots_with_upper_requirements,
        total.graph.slots_with_only_upper_requirements,
        total.graph.role_bounds_evidence,
        total.graph.role_input_lower_candidates,
        total.graph.role_associated_lower_candidates,
        total.graph.role_upper_only_dependencies,
        total.graph.role_bottom_like_exclusions,
        total.graph.role_associated_resolution_attempts,
        total.graph.role_associated_resolution_missing_inputs,
        total.graph.role_associated_resolution_missing_impls,
        total.graph.role_associated_resolution_ambiguous_impls,
        total.graph.role_associated_resolution_resolved,
        total.graph.role_associated_resolution_projected_type_vars,
        total.type_vars.evidence,
        total.type_vars.derived_structural_lower_evidence,
        total.type_vars.vars,
        total.type_vars.scoped_vars,
        total.type_vars.vars_used_in_multiple_scopes,
        total.type_vars.solved_vars,
        total.type_vars.closed_solved_vars,
        total.type_vars.recursive_substitution_vars,
        total.type_vars.closed_after_recursive_substitution_vars,
        total
            .type_vars
            .residual_open_vars_after_recursive_substitution,
        total
            .type_vars
            .residual_open_recursive_cycle_vars_after_substitution,
        total
            .type_vars
            .residual_open_missing_substitution_vars_after_substitution,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_apply_substitution,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_principal_candidate,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_principal_elaboration,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_type_instantiation,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_role_associated_resolution,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_structural_decomposition,
        total
            .type_vars
            .residual_open_after_recursive_substitution_with_mixed_sources,
        total.type_vars.structural_decomposition_iterations,
        total.type_vars.structural_decomposition_candidate_visits,
        total.type_vars.structural_decomposition_addition_attempts,
        total.type_vars.conflicting_vars,
        total.type_vars.closed_conflicting_vars,
        total.type_vars.conflicting_vars_with_apply_substitution,
        total.type_vars.conflicting_vars_with_principal_candidate,
        total.type_vars.conflicting_vars_with_principal_elaboration,
        total.type_vars.conflicting_vars_with_type_instantiation,
        total
            .type_vars
            .conflicting_vars_with_role_associated_resolution,
        total
            .type_vars
            .conflicting_vars_with_structural_decomposition,
        total.type_vars.conflicting_vars_with_mixed_sources,
        total.type_vars.bottom_like_exclusions,
        total.type_vars.identity_lower_exclusions,
        total.lower_snapshot.solved_slots,
        total.lower_snapshot.closed_solved_slots,
        total.lower_snapshot.open_solved_slots,
        total.lower_snapshot.conflicting_lower_slots,
        total.lower_snapshot.closed_conflicting_lower_slots,
        total.lower_snapshot.upper_only_slots,
        total.lower_snapshot.slots_without_bounds,
        total.lower_snapshot.solved_groups,
        total.lower_snapshot.conflicting_lower_groups,
        total.lower_snapshot.upper_only_groups,
        total.lower_snapshot.groups_without_bounds,
        total.lower_snapshot.lower_solution_checked_edges,
        total.lower_snapshot.lower_solution_mismatched_edges,
        total.lower_snapshot.lower_solution_unresolved_edges,
        total.upper_supplement.upper_requirements,
        total.upper_supplement.checked_against_lower,
        total.upper_supplement.satisfied_by_lower,
        total.upper_supplement.mismatched_with_lower,
        total.upper_supplemented_slots,
        total.upper_supplement.closed_supplemented_slots,
        total.upper_supplement.open_supplemented_slots,
        total.upper_supplement.ambiguous_supplement_slots,
        total.applied_slots,
        casts.inserted_casts,
        casts.unresolved_conflicts,
        total.final_defaults.filled_value_holes,
        total.final_defaults.filled_effect_holes,
    );
    if std::env::var_os("YULANG_DEBUG_TYPE_GRAPH_PIPELINE_DETAILS").is_some() {
        for sample in &total.type_vars.residual_open_samples {
            eprintln!("type graph detail[{label}]: residual_open {sample}");
        }
    }
}

fn run_legacy_demand_fixpoint_pipeline(
    module: Module,
) -> RuntimeResult<(Module, MonomorphizeProfile)> {
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

fn run_mono_pipeline_unprofiled(module: Module) -> RuntimeResult<Module> {
    match MonomorphizeMode::detect() {
        MonomorphizeMode::PrincipalElaborate => run_principal_elaborate_pipeline_unprofiled(module),
        MonomorphizeMode::LegacyDemandFixpoint => {
            run_mono_pipeline(module).map(|(module, _profile)| module)
        }
    }
}

fn run_principal_elaborate_pipeline_unprofiled(module: Module) -> RuntimeResult<Module> {
    let mut module = inline_polymorphic_wrappers(module);
    for _ in 0..8 {
        module = principal_elaborate_module(module);
        module = refresh_closed_specialized_schemes(module);
        module = normalize_semantic_cast_coercions(module);
        module = prune_unreachable_bindings(module);
        if module
            .bindings
            .iter()
            .all(|binding| binding.type_params.is_empty())
        {
            break;
        }
    }
    module = normalize_semantic_cast_coercions(module);
    module = prune_unreachable_bindings(module);
    module = remove_specialized_generic_original_bindings(module);
    module = remove_runtime_unreferenced_generic_bindings(module);
    if std::env::var_os("YULANG_PRINCIPAL_ELABORATE_STRICT").is_some()
        && let Some(context) = principal_elaborate_strict_failure(&module)
    {
        return Err(RuntimeError::InvariantViolation {
            stage: "principal-elaborate",
            context,
            message: "principal elaboration plan incomplete",
        });
    }
    Ok(module)
}

fn run_principal_elaborate_fixpoint(
    mut module: Module,
    limit: usize,
    profile: &mut MonomorphizeProfile,
    debug: bool,
) -> RuntimeResult<Module> {
    for round in 0..limit {
        let mut round_progress = MonoProgress::default();
        let step = run_profiled_mono_pass(module, MonoPass::PrincipalElaborate, profile, debug)?;
        module = step.module;
        round_progress.merge(step.progress);

        let step = run_profiled_mono_pass(module, MonoPass::RefreshClosedSchemes, profile, debug)?;
        module = step.module;
        round_progress.merge(step.progress);

        let step = run_profiled_mono_pass(module, MonoPass::SemanticCastCoercions, profile, debug)?;
        module = step.module;
        round_progress.merge(step.progress);

        let step = run_profiled_mono_pass(module, MonoPass::PruneUnreachable, profile, debug)?;
        module = step.module;
        let monomorphic_after_prune = module
            .bindings
            .iter()
            .all(|binding| binding.type_params.is_empty());
        round_progress.merge(step.progress);

        if monomorphic_after_prune || !round_progress.changed() {
            if debug {
                eprintln!("mono fixpoint principal-elaborate converged after {round} rounds");
            }
            return Ok(module);
        } else if debug {
            eprintln!(
                "mono fixpoint principal-elaborate round {round}: progress {}",
                round_progress.format()
            );
        }
    }
    if debug {
        eprintln!("mono fixpoint principal-elaborate reached round limit");
    }
    Ok(module)
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
    let started = std::time::Instant::now();
    let step = apply_mono_pass(module, pass)?;
    let duration = started.elapsed();
    let after = MonoStats::from_module(&step.module);
    let progress = step.progress.to_public();
    profile.passes.push(MonomorphizePassProfile {
        name: pass.name(),
        duration,
        bindings_before: before.bindings,
        bindings_after: after.bindings,
        roots_before: before.roots,
        roots_after: after.roots,
        progress,
        demand_queue: step.demand_queue,
        principal_elaborate: step.principal_elaborate.clone(),
        added_binding_paths: step.added_binding_paths.clone(),
        added_specializations: step.added_specializations.clone(),
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
        let mut round_progress = MonoProgress::default();
        for pass in passes {
            let step = run_profiled_mono_pass(module, *pass, profile, debug)?;
            module = step.module;
            round_progress.merge(step.progress);
        }
        if !round_progress.changed() {
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
        MonoPass::PrincipalElaborate => {
            let bindings_before = module.bindings.len();
            let roots_before = module.root_exprs.len();
            let (module, principal_elaborate) = principal_elaborate_module_profiled(module);
            let added_binding_paths = module
                .bindings
                .iter()
                .skip(bindings_before)
                .map(|binding| binding.name.clone())
                .collect::<Vec<_>>();
            let changed_bindings = principal_elaborate
                .stats
                .get("principal-unify-rewrite")
                .copied()
                .unwrap_or_default()
                + principal_elaborate
                    .stats
                    .get("principal-unify-rewrite-surviving-template-binding")
                    .copied()
                    .unwrap_or_default();
            let progress = MonoProgress {
                changed_bindings,
                changed_roots: module.root_exprs.len().abs_diff(roots_before),
                added_specializations: module.bindings.len().saturating_sub(bindings_before),
            };
            Ok(MonoStep {
                module,
                progress,
                demand_queue: DemandQueueProfile::default(),
                principal_elaborate,
                added_binding_paths,
                added_specializations: Vec::new(),
            })
        }
        MonoPass::DemandSpecialize => demand_specialize_module(module),
        MonoPass::RefineTypes => refine_module_types_for_mono(module),
        MonoPass::RefreshClosedSchemes => {
            run_tracked_infallible_pass(module, refresh_closed_specialized_schemes)
        }
        MonoPass::SemanticCastCoercions => {
            run_tracked_infallible_pass(module, normalize_semantic_cast_coercions)
        }
        MonoPass::CanonicalizeSpecializations => {
            run_tracked_infallible_pass(module, canonicalize_equivalent_specializations)
        }
        MonoPass::InlinePolymorphicWrappers => {
            run_tracked_infallible_pass(module, inline_polymorphic_wrappers)
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
    let added_binding_paths = added_binding_paths(&before, &output.module);
    let added_specializations = output.profile.emitted_specializations;
    Ok(MonoStep {
        module: output.module,
        progress,
        demand_queue: output.profile.queue,
        principal_elaborate: SubstitutionSpecializeProfile::default(),
        added_binding_paths,
        added_specializations,
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

fn changed_binding_names(before: &Module, after: &Module) -> Vec<typed_ir::Path> {
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
    demand_queue: DemandQueueProfile,
    principal_elaborate: SubstitutionSpecializeProfile,
    added_binding_paths: Vec<typed_ir::Path>,
    added_specializations: Vec<DemandSpecialization>,
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

    fn from_stats(before: MonoStats, after: MonoStats) -> Self {
        Self {
            changed_bindings: before.bindings.abs_diff(after.bindings),
            changed_roots: before.roots.abs_diff(after.roots),
            added_specializations: after.bindings.saturating_sub(before.bindings),
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
    if std::env::var_os("YULANG_LEGACY_MONO_FIXPOINT").is_some()
        || std::env::var_os("YULANG_MONO_ACCURATE_PROGRESS").is_some()
    {
        let before = module.clone();
        let module = f(module)?;
        let progress = MonoProgress::from_modules(&before, &module);
        let added_binding_paths = added_binding_paths(&before, &module);
        return Ok(MonoStep {
            module,
            progress,
            demand_queue: DemandQueueProfile::default(),
            principal_elaborate: SubstitutionSpecializeProfile::default(),
            added_binding_paths,
            added_specializations: Vec::new(),
        });
    }

    let before = MonoStats::from_module(&module);
    let before_paths = module
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let module = f(module)?;
    let progress = MonoProgress::from_stats(before, MonoStats::from_module(&module));
    let added_binding_paths = module
        .bindings
        .iter()
        .filter(|binding| !before_paths.contains(&binding.name))
        .map(|binding| binding.name.clone())
        .collect();
    Ok(MonoStep {
        module,
        progress,
        demand_queue: DemandQueueProfile::default(),
        principal_elaborate: SubstitutionSpecializeProfile::default(),
        added_binding_paths,
        added_specializations: Vec::new(),
    })
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
        demand_queue: DemandQueueProfile::default(),
        principal_elaborate: SubstitutionSpecializeProfile::default(),
        added_binding_paths: Vec::new(),
        added_specializations: Vec::new(),
    })
}

fn added_binding_paths(before: &Module, after: &Module) -> Vec<typed_ir::Path> {
    let before_paths = before
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    after
        .bindings
        .iter()
        .filter(|binding| !before_paths.contains(&binding.name))
        .map(|binding| binding.name.clone())
        .collect()
}

fn annotate_substitution_skip_reachability(
    profile: &mut MonomorphizeProfile,
    final_module: &Module,
) {
    let surviving_bindings = final_reachable_binding_paths(final_module);
    for pass in &mut profile.passes {
        for target in &mut pass.principal_elaborate.target_skips {
            target.survives_final_prune = Some(surviving_bindings.contains(&target.target));
        }
    }
}
