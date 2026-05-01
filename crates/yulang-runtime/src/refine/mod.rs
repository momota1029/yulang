//! Refine runtime IR types from already-lowered expressions.
//!
//! This stage propagates concrete information through runtime IR after
//! specialization or rewriting.  It is allowed to make existing runtime types
//! more precise, but it should not add new control-flow constructs or erase
//! semantic thunk/effect boundaries.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use yulang_core_ir as core_ir;

use crate::diagnostic::RuntimeResult;
use crate::ir::{
    Binding, Expr, ExprKind, HandleArm, MatchArm, Module, Pattern, RecordExprField,
    RecordPatternField, RecordSpreadExpr, RecordSpreadPattern, ResumeBinding, Stmt,
    Type as RuntimeType,
};
use crate::types::{
    TypeChoice, choose_core_type, collect_hir_type_vars, collect_type_vars, effect_is_empty,
    effect_paths, effect_paths_match, effect_row, hir_type_has_vars,
    is_nullary_constructor_path_for_type, needs_runtime_coercion, project_runtime_bounds,
    project_runtime_effect, project_runtime_hir_type_with_vars, same_effect_head,
    should_thunk_effect, substitute_apply_evidence, substitute_hir_type, substitute_join_evidence,
    substitute_scheme, substitute_type, thunk_effect, type_compatible,
};

mod cast;
mod constraints;
mod effects;
mod locals;
mod pattern;
mod rewrite;
mod shape;
mod stmt;
mod thunk_force;
mod type_context;

use constraints::*;
use effects::*;
use locals::*;
use rewrite::*;
use shape::*;

pub fn refine_module_types(module: Module) -> RuntimeResult<Module> {
    Ok(refine_module_types_with_report(module)?.module)
}

pub(crate) fn refine_module_types_with_report(module: Module) -> RuntimeResult<RefineModuleOutput> {
    let mut constraints = TypeConstraints::new(&module);
    for binding in &module.bindings {
        if is_principal_polymorphic_binding(binding) {
            continue;
        }
        let expected = constraints
            .binding_types
            .get(&binding.name)
            .cloned()
            .unwrap_or_else(|| binding.body.ty.clone());
        constraints.collect_expr(&binding.body, Some(&expected));
    }
    for expr in &module.root_exprs {
        constraints.collect_expr(expr, Some(&expr.ty));
    }

    let substitutions = constraints.into_substitutions();
    let mut rewriter = RefineRewriter {
        substitutions,
        binding_types: HashMap::new(),
        locals: HashMap::new(),
        pure_handler_bindings: pure_handler_bindings(&module),
    };
    Ok(rewriter.module(module))
}

pub(crate) struct RefineModuleOutput {
    pub(crate) module: Module,
    pub(crate) report: RefineReport,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RefineReport {
    pub(crate) changed_bindings: usize,
    pub(crate) changed_roots: usize,
}

pub(super) fn is_principal_polymorphic_binding(binding: &Binding) -> bool {
    !binding.type_params.is_empty() && !is_monomorphized_path(&binding.name)
}

pub(super) fn is_monomorphized_path(path: &core_ir::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|name| name.0.contains("__mono"))
}
