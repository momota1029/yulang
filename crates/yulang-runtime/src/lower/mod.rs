//! Lower principal core IR into typed runtime IR.
//!
//! This stage consumes principal schemes and local evidence from `yulang-infer`
//! and introduces runtime constructs such as thunks, `bind_here`, effect id
//! administration, and runtime coercions.  Later stages may specialize and
//! preserve these constructs, but should not need to rediscover why they were
//! introduced.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use yulang_typed_ir as typed_ir;

use crate::diagnostic::{
    RuntimeCalleeLabel, RuntimeError, RuntimeResult, TypeMismatchContext, TypeMismatchPhase,
    TypeSource,
};
use crate::invariant::{RuntimeStage, check_runtime_invariants};
use crate::ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, HandleArm, HandleEffect, JoinEvidence,
    LoweredModule, MatchArm, Module, Pattern, RecordExprField, RecordPatternField,
    RecordSpreadExpr, RecordSpreadPattern, ResumeBinding, Root, Stmt, Type as RuntimeType,
    TypeInstantiation, TypeSubstitution,
};
use crate::types::{
    BoundsChoice, TypeChoice, choose_bounds_type, choose_core_type, choose_optional_core_type,
    close_type_substitution_map_recursively, collect_hir_type_vars, collect_type_vars,
    contains_non_runtime_effect_type, contains_non_runtime_type, core_type_has_vars,
    core_type_is_imprecise_runtime_slot, core_types_compatible, diagnostic_core_type,
    effect_compatible, effect_is_empty, effect_path, effect_paths, effect_paths_match,
    effect_row_from_items, hir_type_imprecision_count, hir_type_is_hole, infer_type_substitutions,
    infer_type_substitutions_prefer_non_never,
    infer_type_substitutions_prefer_non_never_skip_empty_effects, is_qualified_runtime_path,
    needs_runtime_coercion, project_runtime_bounds, project_runtime_effect,
    project_runtime_hint_type_with_vars, project_runtime_hir_type_with_vars,
    project_runtime_type_with_vars, runtime_core_type, runtime_type_contains_unknown,
    runtime_type_is_imprecise_runtime_slot, should_thunk_effect, strict_core_type as core_type,
    substitute_bounds, substitute_hir_type, substitute_type, thunk_effect, type_compatible,
    wildcard_effect_type,
};
use crate::validate::validate_module;

mod core_shape;
mod diagnostics;
mod effects;
mod evidence;
mod expr;
mod function;
mod hints;
mod lowerer;
mod patterns;
mod primitive_types;
mod substitutions;
mod thunk;

pub use core_shape::CoreShapeProfile;
use core_shape::*;
use diagnostics::*;
use effects::*;
use evidence::*;
use expr::*;
use function::*;
use hints::*;
use patterns::*;
use primitive_types::*;
use substitutions::*;
use thunk::*;

pub struct RuntimeLowerOutput {
    pub module: LoweredModule,
    pub profile: RuntimeLowerProfile,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RuntimeLowerProfile {
    pub core_shape: CoreShapeProfile,
    pub expected_arg_evidence: ExpectedArgEvidenceProfile,
    pub expected_adapter_evidence: ExpectedAdapterEvidenceProfile,
    pub derived_expected_evidence: DerivedExpectedEvidenceProfile,
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
    pub collect_events: bool,
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
    pub matched_derived_expected_edge_parent: usize,
    pub unmatched_derived_expected_edge_parent: usize,
    pub observed_adapter_with_source_expected_edge: usize,
    pub observed_adapter_without_source_expected_edge: usize,
    pub observed_adapter_source_application_callee: usize,
    pub observed_adapter_source_application_argument: usize,
    pub observed_adapter_source_other_expected_edge: usize,
    pub observed_adapter_source_with_derived_parent: usize,
    pub observed_adapter_source_without_derived_parent: usize,
    pub events: Vec<RuntimeAdapterEvent>,
    pub observed_adapter_evidence: Vec<ObservedAdapterEvidence>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObservedAdapterEvidence {
    pub kind: ObservedAdapterEvidenceKind,
    pub phase: RuntimeApplyAdapterPhase,
    pub owner: Option<typed_ir::Path>,
    pub apply_target: Option<typed_ir::Path>,
    pub source_expected_edge: Option<u32>,
    pub actual: RuntimeType,
    pub expected: RuntimeType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ObservedAdapterEvidenceKind {
    ValueToThunk,
    ForceThunkToValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeAdapterEvent {
    pub kind: RuntimeAdapterEventKind,
    pub phase: RuntimeApplyAdapterPhase,
    pub owner: Option<typed_ir::Path>,
    pub apply_target: Option<typed_ir::Path>,
    pub callee_source_edge: Option<u32>,
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

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DerivedExpectedEvidenceProfile {
    pub total: usize,
    pub record_field: usize,
    pub tuple_item: usize,
    pub variant_payload: usize,
    pub function_param: usize,
    pub function_return: usize,
    pub covariant: usize,
    pub contravariant: usize,
    pub invariant: usize,
}

pub fn lower_core_program(program: typed_ir::CoreProgram) -> RuntimeResult<LoweredModule> {
    let graph = program.graph;
    let evidence = program.evidence;
    let effect_operations = program.effect_operations;
    lower_principal_module_with_graph_evidence_and_effects(
        program.program,
        &graph,
        &evidence,
        &effect_operations,
    )
}

pub fn lower_core_program_profiled(
    program: typed_ir::CoreProgram,
) -> RuntimeResult<RuntimeLowerOutput> {
    let core_shape = profile_core_program(&program);
    let graph = program.graph;
    let evidence = program.evidence;
    let effect_operations = program.effect_operations;
    lower_principal_module_with_graph_evidence_and_effects_profiled(
        program.program,
        &graph,
        &evidence,
        &effect_operations,
        core_shape,
    )
}

pub fn lower_principal_module(module: typed_ir::PrincipalModule) -> RuntimeResult<LoweredModule> {
    lower_principal_module_with_graph(module, &typed_ir::CoreGraphView::default())
}

pub fn lower_principal_module_with_graph(
    module: typed_ir::PrincipalModule,
    graph: &typed_ir::CoreGraphView,
) -> RuntimeResult<LoweredModule> {
    let evidence = typed_ir::PrincipalEvidence::default();
    lower_principal_module_with_graph_evidence_and_effects(module, graph, &evidence, &[])
}

fn lower_principal_module_with_graph_evidence_and_effects(
    module: typed_ir::PrincipalModule,
    graph: &typed_ir::CoreGraphView,
    evidence: &typed_ir::PrincipalEvidence,
    effect_operations: &[typed_ir::EffectOperationDecl],
) -> RuntimeResult<LoweredModule> {
    lower_principal_module_with_graph_and_evidence_inner(
        module,
        graph,
        evidence,
        effect_operations,
        CoreShapeProfile::default(),
        false,
    )
    .map(|output| output.module)
}

fn lower_principal_module_with_graph_evidence_and_effects_profiled(
    module: typed_ir::PrincipalModule,
    graph: &typed_ir::CoreGraphView,
    evidence: &typed_ir::PrincipalEvidence,
    effect_operations: &[typed_ir::EffectOperationDecl],
    core_shape: CoreShapeProfile,
) -> RuntimeResult<RuntimeLowerOutput> {
    lower_principal_module_with_graph_and_evidence_inner(
        module,
        graph,
        evidence,
        effect_operations,
        core_shape,
        true,
    )
}

fn lower_principal_module_with_graph_and_evidence_inner(
    module: typed_ir::PrincipalModule,
    graph: &typed_ir::CoreGraphView,
    evidence: &typed_ir::PrincipalEvidence,
    effect_operations: &[typed_ir::EffectOperationDecl],
    core_shape: CoreShapeProfile,
    collect_profile: bool,
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
                    type_params: {
                        if is_constructor_variant_expr(&binding.body) {
                            principal_runtime_type_params(&binding.scheme.body, &ty, true)
                        } else {
                            principal_runtime_type_params(&binding.scheme.body, &ty, false)
                        }
                    },
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
    let effect_op_signatures = effect_operations
        .iter()
        .map(|decl| (decl.path.clone(), decl.scheme.clone()))
        .collect::<HashMap<_, _>>();
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
        effect_op_signatures,
        primitive_paths: RuntimePrimitivePathTable::from_graph(graph),
        principal_vars,
        expected_edges_by_id,
        use_expected_arg_evidence: std::env::var_os("YULANG_USE_EXPECTED_ARG_EVIDENCE").is_some(),
        use_principal_elaboration: std::env::var_os("YULANG_DISABLE_PRINCIPAL_ELABORATE").is_none(),
        expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
        runtime_adapter_profile: RuntimeAdapterProfile::default(),
        local_param_boundaries: HashMap::new(),
        handler_body_depth: 0,
        current_function_boundary: None,
        current_binding: None,
        current_runtime_adapter_source: None,
        next_synthetic_type_var: 0,
        next_effect_id_var: 0,
    };
    lowerer.runtime_adapter_profile.collect_events = collect_profile;
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
            typed_ir::PrincipalRoot::Binding(path) => Root::Binding(path),
            typed_ir::PrincipalRoot::Expr(index) => Root::Expr(index),
        })
        .collect();
    let module = Module {
        path,
        bindings,
        root_exprs,
        roots,
        role_impls: graph.role_impls.clone(),
    };
    check_runtime_invariants(&module, RuntimeStage::Lowered)?;
    validate_module(&module)?;
    let module = lower_runtime_typed_module(module);
    let mut runtime_adapters = lowerer.runtime_adapter_profile;
    if collect_profile {
        profile_runtime_adapter_expected_matches(&mut runtime_adapters, evidence);
        profile_runtime_adapter_derived_parent_matches(&mut runtime_adapters, evidence);
        collect_observed_adapter_evidence(&mut runtime_adapters, evidence);
    }
    Ok(RuntimeLowerOutput {
        module,
        profile: RuntimeLowerProfile {
            core_shape,
            expected_arg_evidence: lowerer.expected_arg_evidence_profile,
            expected_adapter_evidence: collect_profile
                .then(|| expected_adapter_evidence_profile(evidence))
                .unwrap_or_default(),
            derived_expected_evidence: collect_profile
                .then(|| derived_expected_evidence_profile(evidence))
                .unwrap_or_default(),
            runtime_adapters,
        },
    })
}

fn lower_runtime_typed_module(module: Module) -> LoweredModule {
    yulang_runtime_ir::Module {
        path: module.path,
        bindings: module
            .bindings
            .into_iter()
            .map(lower_runtime_typed_binding)
            .collect(),
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(lower_runtime_typed_expr)
            .collect(),
        roots: module.roots,
        role_impls: module.role_impls,
    }
}

fn lower_runtime_typed_binding(binding: Binding) -> yulang_runtime_ir::LoweredBinding {
    yulang_runtime_ir::Binding {
        name: binding.name,
        type_params: binding.type_params,
        scheme: binding.scheme,
        body: lower_runtime_typed_expr(binding.body),
    }
}

fn lower_runtime_typed_expr(expr: Expr) -> yulang_runtime_ir::LoweredExpr {
    let ty = runtime_type_to_lowered_type(expr.ty);
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
            body: Box::new(lower_runtime_typed_expr(*body)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => yulang_runtime_ir::ExprKind::Apply {
            callee: Box::new(lower_runtime_typed_expr(*callee)),
            arg: Box::new(lower_runtime_typed_expr(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => yulang_runtime_ir::ExprKind::If {
            cond: Box::new(lower_runtime_typed_expr(*cond)),
            then_branch: Box::new(lower_runtime_typed_expr(*then_branch)),
            else_branch: Box::new(lower_runtime_typed_expr(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => yulang_runtime_ir::ExprKind::Tuple(
            items.into_iter().map(lower_runtime_typed_expr).collect(),
        ),
        ExprKind::Record { fields, spread } => yulang_runtime_ir::ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordExprField {
                    name: field.name,
                    value: lower_runtime_typed_expr(field.value),
                })
                .collect(),
            spread: spread.map(lower_runtime_typed_record_spread_expr),
        },
        ExprKind::Variant { tag, value } => yulang_runtime_ir::ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(lower_runtime_typed_expr(*value))),
        },
        ExprKind::Select { base, field } => yulang_runtime_ir::ExprKind::Select {
            base: Box::new(lower_runtime_typed_expr(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => yulang_runtime_ir::ExprKind::Match {
            scrutinee: Box::new(lower_runtime_typed_expr(*scrutinee)),
            arms: arms
                .into_iter()
                .map(lower_runtime_typed_match_arm)
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => yulang_runtime_ir::ExprKind::Block {
            stmts: stmts.into_iter().map(lower_runtime_typed_stmt).collect(),
            tail: tail.map(|tail| Box::new(lower_runtime_typed_expr(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => yulang_runtime_ir::ExprKind::Handle {
            body: Box::new(lower_runtime_typed_expr(*body)),
            arms: arms
                .into_iter()
                .map(lower_runtime_typed_handle_arm)
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => yulang_runtime_ir::ExprKind::BindHere {
            expr: Box::new(lower_runtime_typed_expr(*expr)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => yulang_runtime_ir::ExprKind::Thunk {
            effect,
            value: runtime_type_to_lowered_type(value),
            expr: Box::new(lower_runtime_typed_expr(*expr)),
        },
        ExprKind::LocalPushId { id, body } => yulang_runtime_ir::ExprKind::LocalPushId {
            id,
            body: Box::new(lower_runtime_typed_expr(*body)),
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
            thunk: Box::new(lower_runtime_typed_expr(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => yulang_runtime_ir::ExprKind::Coerce {
            from,
            to,
            expr: Box::new(lower_runtime_typed_expr(*expr)),
        },
        ExprKind::Pack { var, expr } => yulang_runtime_ir::ExprKind::Pack {
            var,
            expr: Box::new(lower_runtime_typed_expr(*expr)),
        },
    };
    yulang_runtime_ir::Expr::typed(kind, ty)
}

fn lower_runtime_typed_stmt(stmt: Stmt) -> yulang_runtime_ir::LoweredStmt {
    match stmt {
        Stmt::Let { pattern, value } => yulang_runtime_ir::Stmt::Let {
            pattern: lower_runtime_typed_pattern(pattern),
            value: lower_runtime_typed_expr(value),
        },
        Stmt::Expr(expr) => yulang_runtime_ir::Stmt::Expr(lower_runtime_typed_expr(expr)),
        Stmt::Module { def, body } => yulang_runtime_ir::Stmt::Module {
            def,
            body: lower_runtime_typed_expr(body),
        },
    }
}

fn lower_runtime_typed_pattern(pattern: Pattern) -> yulang_runtime_ir::LoweredPattern {
    match pattern {
        Pattern::Wildcard { ty } => yulang_runtime_ir::Pattern::Wildcard {
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::Bind { name, ty } => yulang_runtime_ir::Pattern::Bind {
            name,
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::Lit { lit, ty } => yulang_runtime_ir::Pattern::Lit {
            lit,
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::Tuple { items, ty } => yulang_runtime_ir::Pattern::Tuple {
            items: items.into_iter().map(lower_runtime_typed_pattern).collect(),
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => yulang_runtime_ir::Pattern::List {
            prefix: prefix
                .into_iter()
                .map(lower_runtime_typed_pattern)
                .collect(),
            spread: spread.map(|spread| Box::new(lower_runtime_typed_pattern(*spread))),
            suffix: suffix
                .into_iter()
                .map(lower_runtime_typed_pattern)
                .collect(),
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::Record { fields, spread, ty } => yulang_runtime_ir::Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::RecordPatternField {
                    name: field.name,
                    pattern: lower_runtime_typed_pattern(field.pattern),
                    default: field.default.map(lower_runtime_typed_expr),
                })
                .collect(),
            spread: spread.map(lower_runtime_typed_record_spread_pattern),
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::Variant { tag, value, ty } => yulang_runtime_ir::Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(lower_runtime_typed_pattern(*value))),
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::Or { left, right, ty } => yulang_runtime_ir::Pattern::Or {
            left: Box::new(lower_runtime_typed_pattern(*left)),
            right: Box::new(lower_runtime_typed_pattern(*right)),
            ty: runtime_type_to_lowered_type(ty),
        },
        Pattern::As { pattern, name, ty } => yulang_runtime_ir::Pattern::As {
            pattern: Box::new(lower_runtime_typed_pattern(*pattern)),
            name,
            ty: runtime_type_to_lowered_type(ty),
        },
    }
}

fn lower_runtime_typed_record_spread_expr(
    spread: RecordSpreadExpr,
) -> yulang_runtime_ir::LoweredRecordSpreadExpr {
    match spread {
        RecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Head(Box::new(lower_runtime_typed_expr(*expr)))
        }
        RecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::RecordSpreadExpr::Tail(Box::new(lower_runtime_typed_expr(*expr)))
        }
    }
}

fn lower_runtime_typed_record_spread_pattern(
    spread: RecordSpreadPattern,
) -> yulang_runtime_ir::LoweredRecordSpreadPattern {
    match spread {
        RecordSpreadPattern::Head(pattern) => yulang_runtime_ir::RecordSpreadPattern::Head(
            Box::new(lower_runtime_typed_pattern(*pattern)),
        ),
        RecordSpreadPattern::Tail(pattern) => yulang_runtime_ir::RecordSpreadPattern::Tail(
            Box::new(lower_runtime_typed_pattern(*pattern)),
        ),
    }
}

fn lower_runtime_typed_match_arm(arm: MatchArm) -> yulang_runtime_ir::LoweredMatchArm {
    yulang_runtime_ir::MatchArm {
        pattern: lower_runtime_typed_pattern(arm.pattern),
        guard: arm.guard.map(lower_runtime_typed_expr),
        body: lower_runtime_typed_expr(arm.body),
    }
}

fn lower_runtime_typed_handle_arm(arm: HandleArm) -> yulang_runtime_ir::LoweredHandleArm {
    yulang_runtime_ir::HandleArm {
        effect: arm.effect,
        payload: lower_runtime_typed_pattern(arm.payload),
        resume: arm.resume.map(|resume| yulang_runtime_ir::ResumeBinding {
            name: resume.name,
            ty: runtime_type_to_lowered_type(resume.ty),
        }),
        guard: arm.guard.map(lower_runtime_typed_expr),
        body: lower_runtime_typed_expr(arm.body),
    }
}

fn runtime_type_to_lowered_type(ty: RuntimeType) -> typed_ir::Type {
    match ty {
        RuntimeType::Unknown => typed_ir::Type::Unknown,
        RuntimeType::Value(ty) => ty,
        RuntimeType::Fun { param, ret } => {
            let (param, param_effect) = runtime_type_to_effected_lowered_type(*param);
            let (ret, ret_effect) = runtime_type_to_effected_lowered_type(*ret);
            typed_ir::Type::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret: Box::new(ret),
                ret_effect: Box::new(ret_effect),
            }
        }
        RuntimeType::Thunk { value, .. } => runtime_type_to_lowered_type(*value),
    }
}

fn runtime_type_to_effected_lowered_type(ty: RuntimeType) -> (typed_ir::Type, typed_ir::Type) {
    match ty {
        RuntimeType::Thunk { effect, value } => (runtime_type_to_lowered_type(*value), effect),
        other => (runtime_type_to_lowered_type(other), typed_ir::Type::Never),
    }
}

fn is_constructor_variant_expr(expr: &typed_ir::Expr) -> bool {
    matches!(
        expr,
        typed_ir::Expr::Variant {
            source: typed_ir::VariantExprSource::Constructor,
            ..
        }
    )
}

fn collect_observed_adapter_evidence(
    profile: &mut RuntimeAdapterProfile,
    evidence: &typed_ir::PrincipalEvidence,
) {
    profile.observed_adapter_evidence = profile
        .events
        .iter()
        .filter_map(observed_adapter_evidence_from_event)
        .collect();
    profile_observed_adapter_source_coverage(profile, evidence);
}

fn profile_observed_adapter_source_coverage(
    profile: &mut RuntimeAdapterProfile,
    evidence: &typed_ir::PrincipalEvidence,
) {
    let observed = profile.observed_adapter_evidence.clone();
    for observed in observed {
        let Some(source_expected_edge) = observed.source_expected_edge else {
            profile.observed_adapter_without_source_expected_edge += 1;
            continue;
        };
        profile.observed_adapter_with_source_expected_edge += 1;
        match evidence
            .expected_edge(source_expected_edge)
            .map(|edge| edge.kind)
        {
            Some(typed_ir::ExpectedEdgeKind::ApplicationCallee) => {
                profile.observed_adapter_source_application_callee += 1;
            }
            Some(typed_ir::ExpectedEdgeKind::ApplicationArgument) => {
                profile.observed_adapter_source_application_argument += 1;
            }
            Some(_) | None => {
                profile.observed_adapter_source_other_expected_edge += 1;
            }
        }
        if evidence
            .derived_expected_edges_for_parent(source_expected_edge)
            .next()
            .is_some()
        {
            profile.observed_adapter_source_with_derived_parent += 1;
        } else {
            profile.observed_adapter_source_without_derived_parent += 1;
        }
    }
}

fn observed_adapter_evidence_from_event(
    event: &RuntimeAdapterEvent,
) -> Option<ObservedAdapterEvidence> {
    let kind = match event.kind {
        RuntimeAdapterEventKind::ValueToThunk => ObservedAdapterEvidenceKind::ValueToThunk,
        RuntimeAdapterEventKind::ThunkToValue => ObservedAdapterEvidenceKind::ForceThunkToValue,
        RuntimeAdapterEventKind::BindHere => return None,
    };
    Some(ObservedAdapterEvidence {
        kind,
        phase: event.phase,
        owner: event.owner.clone(),
        apply_target: event.apply_target.clone(),
        source_expected_edge: runtime_adapter_event_source_edge(event),
        actual: event.actual.clone(),
        expected: event.expected.clone(),
    })
}

fn profile_runtime_adapter_expected_matches(
    profile: &mut RuntimeAdapterProfile,
    evidence: &typed_ir::PrincipalEvidence,
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

fn profile_runtime_adapter_derived_parent_matches(
    profile: &mut RuntimeAdapterProfile,
    evidence: &typed_ir::PrincipalEvidence,
) {
    for event in &profile.events {
        let Some(source_edge) = runtime_adapter_event_source_edge(event) else {
            continue;
        };
        if evidence
            .derived_expected_edges_for_parent(source_edge)
            .next()
            .is_some()
        {
            profile.matched_derived_expected_edge_parent += 1;
        } else {
            profile.unmatched_derived_expected_edge_parent += 1;
        }
    }
}

fn expected_adapter_event_match(
    evidence: &typed_ir::PrincipalEvidence,
    event: &RuntimeAdapterEvent,
) -> bool {
    evidence
        .expected_adapter_edges
        .iter()
        .any(|edge| expected_adapter_edge_matches_event(edge, event))
}

fn expected_adapter_edge_matches_event(
    edge: &typed_ir::ExpectedAdapterEdgeEvidence,
    event: &RuntimeAdapterEvent,
) -> bool {
    if expected_adapter_event_kind(edge.kind) != Some(event.kind) {
        return false;
    }
    if let Some(source_edge) = runtime_adapter_event_source_edge(event)
        && edge.source_expected_edge != Some(source_edge)
    {
        return false;
    }
    true
}

fn runtime_adapter_event_source_edge(event: &RuntimeAdapterEvent) -> Option<u32> {
    match event.phase {
        RuntimeApplyAdapterPhase::LowerCallee => event.callee_source_edge,
        RuntimeApplyAdapterPhase::LowerArgument
        | RuntimeApplyAdapterPhase::PrepareFinalArgument
        | RuntimeApplyAdapterPhase::PrepareEffectOperationArgument => event.arg_source_edge,
    }
}

fn expected_adapter_event_kind(
    kind: typed_ir::ExpectedAdapterEdgeKind,
) -> Option<RuntimeAdapterEventKind> {
    match kind {
        typed_ir::ExpectedAdapterEdgeKind::ValueToThunk => {
            Some(RuntimeAdapterEventKind::ValueToThunk)
        }
        typed_ir::ExpectedAdapterEdgeKind::ThunkToValue => {
            Some(RuntimeAdapterEventKind::ThunkToValue)
        }
        typed_ir::ExpectedAdapterEdgeKind::BindHere => Some(RuntimeAdapterEventKind::BindHere),
        typed_ir::ExpectedAdapterEdgeKind::EffectOperationArgument
        | typed_ir::ExpectedAdapterEdgeKind::HandlerResidual
        | typed_ir::ExpectedAdapterEdgeKind::HandlerReturn
        | typed_ir::ExpectedAdapterEdgeKind::ResumeArgument => None,
    }
}

fn expected_adapter_evidence_profile(
    evidence: &typed_ir::PrincipalEvidence,
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
            typed_ir::ExpectedAdapterEdgeKind::EffectOperationArgument => {
                profile.effect_operation_argument += 1;
            }
            typed_ir::ExpectedAdapterEdgeKind::ValueToThunk => {
                profile.value_to_thunk += 1;
            }
            typed_ir::ExpectedAdapterEdgeKind::ThunkToValue => {
                profile.thunk_to_value += 1;
            }
            typed_ir::ExpectedAdapterEdgeKind::BindHere => {
                profile.bind_here += 1;
            }
            typed_ir::ExpectedAdapterEdgeKind::HandlerResidual => {
                profile.handler_residual += 1;
            }
            typed_ir::ExpectedAdapterEdgeKind::HandlerReturn => {
                profile.handler_return += 1;
            }
            typed_ir::ExpectedAdapterEdgeKind::ResumeArgument => {
                profile.resume_argument += 1;
            }
        }
    }
    profile
}

fn derived_expected_evidence_profile(
    evidence: &typed_ir::PrincipalEvidence,
) -> DerivedExpectedEvidenceProfile {
    let mut profile = DerivedExpectedEvidenceProfile::default();
    for edge in &evidence.derived_expected_edges {
        profile.total += 1;
        match edge.kind {
            typed_ir::DerivedExpectedEdgeKind::RecordField => profile.record_field += 1,
            typed_ir::DerivedExpectedEdgeKind::TupleItem => profile.tuple_item += 1,
            typed_ir::DerivedExpectedEdgeKind::VariantPayload => profile.variant_payload += 1,
            typed_ir::DerivedExpectedEdgeKind::FunctionParam => profile.function_param += 1,
            typed_ir::DerivedExpectedEdgeKind::FunctionReturn => profile.function_return += 1,
        }
        match edge.polarity {
            typed_ir::EdgePolarity::Covariant => profile.covariant += 1,
            typed_ir::EdgePolarity::Contravariant => profile.contravariant += 1,
            typed_ir::EdgePolarity::Invariant => profile.invariant += 1,
        }
    }
    profile
}

fn normalize_initial_alias_types(
    bindings: &[typed_ir::PrincipalBinding],
    env: &mut HashMap<typed_ir::Path, RuntimeType>,
    binding_infos: &mut HashMap<typed_ir::Path, BindingInfo>,
) {
    for _ in 0..bindings.len() {
        let mut changed = false;
        for binding in bindings {
            let typed_ir::Expr::Var(target) = &binding.body else {
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

fn direct_aliases(
    bindings: &[typed_ir::PrincipalBinding],
) -> HashMap<typed_ir::Path, typed_ir::Path> {
    bindings
        .iter()
        .filter_map(|binding| match &binding.body {
            typed_ir::Expr::Var(target) if target != &binding.name => {
                Some((binding.name.clone(), target.clone()))
            }
            _ => None,
        })
        .collect()
}

struct Lowerer<'a> {
    env: HashMap<typed_ir::Path, RuntimeType>,
    binding_infos: HashMap<typed_ir::Path, BindingInfo>,
    aliases: HashMap<typed_ir::Path, typed_ir::Path>,
    graph: &'a typed_ir::CoreGraphView,
    runtime_symbols: HashMap<typed_ir::Path, typed_ir::RuntimeSymbolKind>,
    /// Operation path -> signature scheme exported by `infer`. Used as a
    /// fallback when an `EffectOp` Var has no surrounding `expected` type, so
    /// that the `.ty` we record is the operation's actual signature template
    /// (with `Type::Var(..)` for the act's type parameters) instead of
    /// `RuntimeType::Unknown`. Monomorphizing substitutions downstream then
    /// resolve those vars to concrete types.
    effect_op_signatures: HashMap<typed_ir::Path, typed_ir::Scheme>,
    primitive_paths: RuntimePrimitivePathTable,
    principal_vars: BTreeSet<typed_ir::TypeVar>,
    expected_edges_by_id: HashMap<u32, &'a typed_ir::ExpectedEdgeEvidence>,
    use_expected_arg_evidence: bool,
    use_principal_elaboration: bool,
    expected_arg_evidence_profile: ExpectedArgEvidenceProfile,
    runtime_adapter_profile: RuntimeAdapterProfile,
    local_param_boundaries: HashMap<typed_ir::Path, LocalParamBoundary>,
    handler_body_depth: usize,
    current_function_boundary: Option<EffectIdVar>,
    current_binding: Option<typed_ir::Path>,
    current_runtime_adapter_source: Option<RuntimeAdapterSource>,
    next_synthetic_type_var: usize,
    next_effect_id_var: usize,
}

#[derive(Clone)]
struct BindingInfo {
    ty: RuntimeType,
    type_params: Vec<typed_ir::TypeVar>,
    requirements: Vec<typed_ir::RoleRequirement>,
}

#[derive(Debug, Clone)]
struct LocalParamBoundary {
    id: EffectIdVar,
    effect: typed_ir::Type,
    applies_to_thunk_var: bool,
    applies_to_call_outside_handler: bool,
}

#[cfg(test)]
mod tests;
