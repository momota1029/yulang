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
    contains_non_runtime_type, core_type_is_hole, core_types_compatible, diagnostic_core_type,
    effect_compatible, effect_is_empty, effect_path, effect_paths, effect_paths_match,
    effect_row_from_items, hir_type_hole_count, hir_type_is_hole, infer_type_substitutions,
    is_qualified_runtime_path, needs_runtime_coercion, project_runtime_bounds,
    project_runtime_effect, project_runtime_hir_type_with_vars, project_runtime_type_with_vars,
    runtime_core_type, should_thunk_effect, strict_core_type as core_type, substitute_hir_type,
    substitute_type, thunk_effect, type_compatible, wildcard_effect_type,
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

pub fn lower_core_program(program: core_ir::CoreProgram) -> RuntimeResult<Module> {
    let graph = program.graph;
    lower_principal_module_with_graph(program.program, &graph)
}

pub fn lower_principal_module(module: core_ir::PrincipalModule) -> RuntimeResult<Module> {
    lower_principal_module_with_graph(module, &core_ir::CoreGraphView::default())
}

pub fn lower_principal_module_with_graph(
    module: core_ir::PrincipalModule,
    graph: &core_ir::CoreGraphView,
) -> RuntimeResult<Module> {
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
        use_expected_arg_evidence: std::env::var_os("YULANG_USE_EXPECTED_ARG_EVIDENCE").is_some(),
        expected_arg_evidence_profile: ExpectedArgEvidenceProfile::default(),
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
            "expected-arg evidence: available={} used={} ignored-unusable={}",
            lowerer.expected_arg_evidence_profile.available,
            lowerer.expected_arg_evidence_profile.used,
            lowerer.expected_arg_evidence_profile.ignored_unusable,
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
    Ok(module)
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
    use_expected_arg_evidence: bool,
    expected_arg_evidence_profile: ExpectedArgEvidenceProfile,
    next_synthetic_type_var: usize,
    next_effect_id_var: usize,
}

#[derive(Clone)]
struct BindingInfo {
    ty: RuntimeType,
    type_params: Vec<core_ir::TypeVar>,
    requirements: Vec<core_ir::RoleRequirement>,
}

#[derive(Default)]
struct ExpectedArgEvidenceProfile {
    available: usize,
    used: usize,
    ignored_unusable: usize,
}

#[cfg(test)]
mod tests;
