//! Lower principal core IR into typed runtime IR.
//!
//! This stage consumes principal schemes and local evidence from `yulang-infer`
//! and introduces runtime constructs such as thunks, `bind_here`, effect id
//! administration, and runtime coercions.  Later stages may specialize and
//! preserve these constructs, but should not need to rediscover why they were
//! introduced.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use yulang_core_ir as core_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult, TypeSource};
use crate::invariant::{RuntimeStage, check_runtime_invariants};
use crate::ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    MatchArm, Module, Pattern, RecordExprField, RecordPatternField, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, Stmt, Type as RuntimeType, TypeInstantiation,
    TypeSubstitution,
};
use crate::types::{
    BoundsChoice, TypeChoice, choose_bounds_type, choose_core_type, choose_optional_core_type,
    collect_hir_type_vars, collect_type_vars, contains_non_runtime_effect_type,
    contains_non_runtime_type, core_type_has_vars, core_type_is_hole, core_types_compatible,
    diagnostic_core_type, effect_compatible, effect_is_empty, effect_path, effect_paths,
    effect_paths_match, effect_row_from_items, hir_type_hole_count, hir_type_is_hole,
    infer_type_substitutions, is_qualified_runtime_path, needs_runtime_coercion,
    project_runtime_bounds, project_runtime_effect, project_runtime_hir_type_with_vars,
    project_runtime_type_with_vars, runtime_core_type, should_thunk_effect,
    strict_core_type as core_type, substitute_hir_type, substitute_type, thunk_effect,
    type_compatible, wildcard_effect_type,
};
use crate::validate::validate_module;

mod diagnostics;
mod effects;
mod evidence;
mod expr;
mod function;
mod hints;
mod lowerer;
mod patterns;
mod std_types;
mod substitutions;
mod thunk;

use diagnostics::*;
use effects::*;
use evidence::*;
use expr::*;
use function::*;
use hints::*;
use patterns::*;
use std_types::*;
use substitutions::*;
use thunk::*;

pub struct RuntimeLowerOutput {
    pub module: Module,
    pub profile: RuntimeLowerProfile,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RuntimeLowerProfile {
    pub expected_arg_evidence: ExpectedArgEvidenceProfile,
    pub expected_adapter_evidence: ExpectedAdapterEvidenceProfile,
    pub runtime_adapters: RuntimeAdapterProfile,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ExpectedArgEvidenceProfile {
    pub present: usize,
    pub converted: usize,
    pub usable_by_table: usize,
    pub usable_by_bounds: usize,
    pub used_as_arg_type_hint: usize,
    pub used_as_lowering_expected: usize,
    pub ignored_no_expected_arg: usize,
    pub ignored_not_convertible: usize,
    pub ignored_table_open: usize,
    pub ignored_table_uninformative: usize,
    pub ignored_table_not_runtime_usable: usize,
    pub ignored_bounds_unusable: usize,
    pub ignored_unusable: usize,
    pub ignored_no_push: usize,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RuntimeAdapterProfile {
    pub value_to_thunk: usize,
    pub thunk_to_value: usize,
    pub bind_here: usize,
    pub apply_evidence_value_to_thunk: usize,
    pub apply_evidence_thunk_to_value: usize,
    pub apply_evidence_bind_here: usize,
    pub apply_evidence_adapter_with_evidence: usize,
    pub apply_evidence_adapter_with_source_edge: usize,
    pub apply_evidence_adapter_without_evidence: usize,
    pub apply_evidence_value_to_thunk_with_source_edge: usize,
    pub apply_evidence_thunk_to_value_with_source_edge: usize,
    pub apply_evidence_bind_here_with_source_edge: usize,
    pub apply_lower_callee_value_to_thunk: usize,
    pub apply_lower_callee_thunk_to_value: usize,
    pub apply_lower_callee_bind_here: usize,
    pub apply_lower_argument_value_to_thunk: usize,
    pub apply_lower_argument_thunk_to_value: usize,
    pub apply_lower_argument_bind_here: usize,
    pub apply_prepare_final_argument_value_to_thunk: usize,
    pub apply_prepare_final_argument_thunk_to_value: usize,
    pub apply_prepare_final_argument_bind_here: usize,
    pub apply_prepare_effect_operation_argument_value_to_thunk: usize,
    pub apply_prepare_effect_operation_argument_thunk_to_value: usize,
    pub apply_prepare_effect_operation_argument_bind_here: usize,
    pub reused_thunk: usize,
    pub forced_effect_thunk: usize,
    pub matched_expected_adapter: usize,
    pub unmatched_expected_adapter: usize,
    pub unmatched_value_to_thunk: usize,
    pub unmatched_thunk_to_value: usize,
    pub unmatched_bind_here: usize,
    pub events: Vec<RuntimeAdapterEvent>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeAdapterEvent {
    pub kind: RuntimeAdapterEventKind,
    pub phase: RuntimeApplyAdapterPhase,
    pub owner: Option<core_ir::Path>,
    pub apply_target: Option<core_ir::Path>,
    pub arg_source_edge: Option<u32>,
    pub actual: RuntimeType,
    pub expected: RuntimeType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuntimeAdapterEventKind {
    ValueToThunk,
    ThunkToValue,
    BindHere,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuntimeApplyAdapterPhase {
    LowerCallee,
    LowerArgument,
    PrepareFinalArgument,
    PrepareEffectOperationArgument,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct ExpectedAdapterEvidenceProfile {
    pub total: usize,
    pub runtime_usable: usize,
    pub closed: usize,
    pub informative: usize,
    pub effect_operation_argument: usize,
    pub value_to_thunk: usize,
    pub thunk_to_value: usize,
    pub bind_here: usize,
    pub handler_residual: usize,
    pub handler_return: usize,
    pub resume_argument: usize,
}

pub fn lower_core_program(program: core_ir::CoreProgram) -> RuntimeResult<Module> {
    lower_core_program_profiled(program).map(|output| output.module)
}

pub fn lower_core_program_profiled(
    program: core_ir::CoreProgram,
) -> RuntimeResult<RuntimeLowerOutput> {
    let graph = program.graph;
    let evidence = program.evidence;
    lower_principal_module_with_graph_and_evidence_profiled(program.program, &graph, &evidence)
}

pub fn lower_principal_module(module: core_ir::PrincipalModule) -> RuntimeResult<Module> {
    lower_principal_module_with_graph(module, &core_ir::CoreGraphView::default())
}

pub fn lower_principal_module_with_graph(
    module: core_ir::PrincipalModule,
    graph: &core_ir::CoreGraphView,
) -> RuntimeResult<Module> {
    let evidence = core_ir::PrincipalEvidence::default();
    lower_principal_module_with_graph_and_evidence(module, graph, &evidence)
}

fn lower_principal_module_with_graph_and_evidence(
    module: core_ir::PrincipalModule,
    graph: &core_ir::CoreGraphView,
    evidence: &core_ir::PrincipalEvidence,
) -> RuntimeResult<Module> {
    lower_principal_module_with_graph_and_evidence_profiled(module, graph, evidence)
        .map(|output| output.module)
}

fn lower_principal_module_with_graph_and_evidence_profiled(
    module: core_ir::PrincipalModule,
    graph: &core_ir::CoreGraphView,
    evidence: &core_ir::PrincipalEvidence,
) -> RuntimeResult<RuntimeLowerOutput> {
    let principal_vars = principal_module_type_vars(&module);
    let mut binding_infos = module
        .bindings
        .iter()
        .map(|binding| {
            let ty = project_runtime_hir_type_with_vars(&binding.scheme.body, &principal_vars);
            (
                binding.name.clone(),
                BindingInfo {
                    type_params: principal_hir_type_params(&ty),
                    ty,
                    requirements: binding.scheme.requirements.clone(),
                },
            )
        })
        .collect::<HashMap<_, _>>();
    let mut env = module
        .bindings
        .iter()
        .map(|binding| {
            (
                binding.name.clone(),
                binding_infos
                    .get(&binding.name)
                    .map(|info| info.ty.clone())
                    .unwrap_or_else(|| {
                        project_runtime_hir_type_with_vars(&binding.scheme.body, &principal_vars)
                    }),
            )
        })
        .collect::<HashMap<_, _>>();
    normalize_initial_alias_types(&module.bindings, &mut env, &mut binding_infos);
    let aliases = direct_aliases(&module.bindings);
    let expected_edges_by_id = evidence
        .expected_edges
        .iter()
        .map(|edge| (edge.id, edge))
        .collect();
    let mut lowerer = Lowerer {
        env,
        binding_infos,
        aliases,
        graph,
        runtime_symbols: graph
            .runtime_symbols
            .iter()
            .map(|symbol| (symbol.path.clone(), symbol.kind))
            .collect(),
        principal_vars,
        expected_edges_by_id,
        use_expected_arg_evidence: std::env::var_os("YULANG_USE_EXPECTED_ARG_EVIDENCE").is_some(),
        expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
        runtime_adapter_profile: RuntimeAdapterProfile::default(),
        current_binding: None,
        current_runtime_adapter_source: None,
        next_synthetic_type_var: 0,
        next_effect_id_var: 0,
    };
    let path = module.path;
    let bindings = module
        .bindings
        .into_iter()
        .map(|binding| lowerer.lower_binding(binding))
        .collect::<RuntimeResult<Vec<_>>>()?;
    let root_exprs = module
        .root_exprs
        .into_iter()
        .enumerate()
        .map(|(index, expr)| lowerer.lower_root_expr(index, expr))
        .collect::<RuntimeResult<Vec<_>>>()?;
    if std::env::var_os("YULANG_DEBUG_EXPECTED_ARG_EVIDENCE").is_some() {
        eprintln!(
            "expected-arg evidence: present={} converted={} usable-by-table={} usable-by-bounds={} used-as-arg-type-hint={} used-as-lowering-expected={} ignored-no-expected-arg={} ignored-not-convertible={} ignored-table-open={} ignored-table-uninformative={} ignored-table-not-runtime-usable={} ignored-bounds-unusable={} ignored-unusable={} ignored-no-push={}",
            lowerer.expected_arg_evidence_profile.present,
            lowerer.expected_arg_evidence_profile.converted,
            lowerer.expected_arg_evidence_profile.usable_by_table,
            lowerer.expected_arg_evidence_profile.usable_by_bounds,
            lowerer.expected_arg_evidence_profile.used_as_arg_type_hint,
            lowerer
                .expected_arg_evidence_profile
                .used_as_lowering_expected,
            lowerer
                .expected_arg_evidence_profile
                .ignored_no_expected_arg,
            lowerer
                .expected_arg_evidence_profile
                .ignored_not_convertible,
            lowerer.expected_arg_evidence_profile.ignored_table_open,
            lowerer
                .expected_arg_evidence_profile
                .ignored_table_uninformative,
            lowerer
                .expected_arg_evidence_profile
                .ignored_table_not_runtime_usable,
            lowerer
                .expected_arg_evidence_profile
                .ignored_bounds_unusable,
            lowerer.expected_arg_evidence_profile.ignored_unusable,
            lowerer.expected_arg_evidence_profile.ignored_no_push,
        );
    }
    if std::env::var_os("YULANG_DEBUG_RUNTIME_ADAPTERS").is_some() {
        eprintln!(
            "runtime adapters: value-to-thunk={} thunk-to-value={} bind-here={} apply-evidence-value-to-thunk={} apply-evidence-thunk-to-value={} apply-evidence-bind-here={} reused-thunk={} forced-effect-thunk={}",
            lowerer.runtime_adapter_profile.value_to_thunk,
            lowerer.runtime_adapter_profile.thunk_to_value,
            lowerer.runtime_adapter_profile.bind_here,
            lowerer
                .runtime_adapter_profile
                .apply_evidence_value_to_thunk,
            lowerer
                .runtime_adapter_profile
                .apply_evidence_thunk_to_value,
            lowerer.runtime_adapter_profile.apply_evidence_bind_here,
            lowerer.runtime_adapter_profile.reused_thunk,
            lowerer.runtime_adapter_profile.forced_effect_thunk,
        );
    }
    let roots = module
        .roots
        .into_iter()
        .map(|root| match root {
            core_ir::PrincipalRoot::Binding(path) => Root::Binding(path),
            core_ir::PrincipalRoot::Expr(index) => Root::Expr(index),
        })
        .collect();
    let module = Module {
        path,
        bindings,
        root_exprs,
        roots,
    };
    check_runtime_invariants(&module, RuntimeStage::Lowered)?;
    validate_module(&module)?;
    let mut runtime_adapters = lowerer.runtime_adapter_profile;
    profile_runtime_adapter_expected_matches(&mut runtime_adapters, evidence);
    Ok(RuntimeLowerOutput {
        module,
        profile: RuntimeLowerProfile {
            expected_arg_evidence: lowerer.expected_arg_evidence_profile,
            expected_adapter_evidence: expected_adapter_evidence_profile(evidence),
            runtime_adapters,
        },
    })
}

fn profile_runtime_adapter_expected_matches(
    profile: &mut RuntimeAdapterProfile,
    evidence: &core_ir::PrincipalEvidence,
) {
    for event in &profile.events {
        if expected_adapter_event_match(evidence, event) {
            profile.matched_expected_adapter += 1;
        } else {
            profile.unmatched_expected_adapter += 1;
            match event.kind {
                RuntimeAdapterEventKind::ValueToThunk => {
                    profile.unmatched_value_to_thunk += 1;
                }
                RuntimeAdapterEventKind::ThunkToValue => {
                    profile.unmatched_thunk_to_value += 1;
                }
                RuntimeAdapterEventKind::BindHere => {
                    profile.unmatched_bind_here += 1;
                }
            }
        }
    }
}

fn expected_adapter_event_match(
    evidence: &core_ir::PrincipalEvidence,
    event: &RuntimeAdapterEvent,
) -> bool {
    evidence
        .expected_adapter_edges
        .iter()
        .any(|edge| expected_adapter_edge_matches_event(edge, event))
}

fn expected_adapter_edge_matches_event(
    edge: &core_ir::ExpectedAdapterEdgeEvidence,
    event: &RuntimeAdapterEvent,
) -> bool {
    if expected_adapter_event_kind(edge.kind) != Some(event.kind) {
        return false;
    }
    if let Some(source_edge) = event.arg_source_edge
        && edge.source_expected_edge != Some(source_edge)
    {
        return false;
    }
    true
}

fn expected_adapter_event_kind(
    kind: core_ir::ExpectedAdapterEdgeKind,
) -> Option<RuntimeAdapterEventKind> {
    match kind {
        core_ir::ExpectedAdapterEdgeKind::ValueToThunk => {
            Some(RuntimeAdapterEventKind::ValueToThunk)
        }
        core_ir::ExpectedAdapterEdgeKind::ThunkToValue => {
            Some(RuntimeAdapterEventKind::ThunkToValue)
        }
        core_ir::ExpectedAdapterEdgeKind::BindHere => Some(RuntimeAdapterEventKind::BindHere),
        core_ir::ExpectedAdapterEdgeKind::EffectOperationArgument
        | core_ir::ExpectedAdapterEdgeKind::HandlerResidual
        | core_ir::ExpectedAdapterEdgeKind::HandlerReturn
        | core_ir::ExpectedAdapterEdgeKind::ResumeArgument => None,
    }
}

fn expected_adapter_evidence_profile(
    evidence: &core_ir::PrincipalEvidence,
) -> ExpectedAdapterEvidenceProfile {
    let mut profile = ExpectedAdapterEvidenceProfile::default();
    for edge in &evidence.expected_adapter_edges {
        profile.total += 1;
        if edge.runtime_usable {
            profile.runtime_usable += 1;
        }
        if edge.closed {
            profile.closed += 1;
        }
        if edge.informative {
            profile.informative += 1;
        }
        match edge.kind {
            core_ir::ExpectedAdapterEdgeKind::EffectOperationArgument => {
                profile.effect_operation_argument += 1;
            }
            core_ir::ExpectedAdapterEdgeKind::ValueToThunk => {
                profile.value_to_thunk += 1;
            }
            core_ir::ExpectedAdapterEdgeKind::ThunkToValue => {
                profile.thunk_to_value += 1;
            }
            core_ir::ExpectedAdapterEdgeKind::BindHere => {
                profile.bind_here += 1;
            }
            core_ir::ExpectedAdapterEdgeKind::HandlerResidual => {
                profile.handler_residual += 1;
            }
            core_ir::ExpectedAdapterEdgeKind::HandlerReturn => {
                profile.handler_return += 1;
            }
            core_ir::ExpectedAdapterEdgeKind::ResumeArgument => {
                profile.resume_argument += 1;
            }
        }
    }
    profile
}

fn normalize_initial_alias_types(
    bindings: &[core_ir::PrincipalBinding],
    env: &mut HashMap<core_ir::Path, RuntimeType>,
    binding_infos: &mut HashMap<core_ir::Path, BindingInfo>,
) {
    for _ in 0..bindings.len() {
        let mut changed = false;
        for binding in bindings {
            let core_ir::Expr::Var(target) = &binding.body else {
                continue;
            };
            let Some(current_ty) = env.get(&binding.name).cloned() else {
                continue;
            };
            let Some(target_ty) = env.get(target).cloned() else {
                continue;
            };
            if !prefer_alias_target_runtime_type(&current_ty, &target_ty) {
                continue;
            }
            if current_ty == target_ty {
                continue;
            }
            env.insert(binding.name.clone(), target_ty.clone());
            if let Some(info) = binding_infos.get_mut(&binding.name) {
                info.ty = target_ty.clone();
                info.type_params = principal_hir_type_params(&target_ty);
            }
            changed = true;
        }
        if !changed {
            break;
        }
    }
}

fn direct_aliases(bindings: &[core_ir::PrincipalBinding]) -> HashMap<core_ir::Path, core_ir::Path> {
    bindings
        .iter()
        .filter_map(|binding| match &binding.body {
            core_ir::Expr::Var(target) if target != &binding.name => {
                Some((binding.name.clone(), target.clone()))
            }
            _ => None,
        })
        .collect()
}

struct Lowerer<'a> {
    env: HashMap<core_ir::Path, RuntimeType>,
    binding_infos: HashMap<core_ir::Path, BindingInfo>,
    aliases: HashMap<core_ir::Path, core_ir::Path>,
    graph: &'a core_ir::CoreGraphView,
    runtime_symbols: HashMap<core_ir::Path, core_ir::RuntimeSymbolKind>,
    principal_vars: BTreeSet<core_ir::TypeVar>,
    expected_edges_by_id: HashMap<u32, &'a core_ir::ExpectedEdgeEvidence>,
    use_expected_arg_evidence: bool,
    expected_arg_evidence_profile: ExpectedArgEvidenceProfile,
    runtime_adapter_profile: RuntimeAdapterProfile,
    current_binding: Option<core_ir::Path>,
    current_runtime_adapter_source: Option<RuntimeAdapterSource>,
    next_synthetic_type_var: usize,
    next_effect_id_var: usize,
}

#[derive(Clone)]
struct BindingInfo {
    ty: RuntimeType,
    type_params: Vec<core_ir::TypeVar>,
    requirements: Vec<core_ir::RoleRequirement>,
}

#[cfg(test)]
mod tests;
