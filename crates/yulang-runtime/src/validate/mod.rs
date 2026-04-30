use std::collections::{BTreeMap, BTreeSet, HashMap};

use yulang_core_ir as core_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult, TypeSource};
use crate::ir::{
    Binding, Expr, ExprKind, HandleArm, HandleEffect, MatchArm, Module, Pattern, RecordSpreadExpr,
    RecordSpreadPattern, ResumeBinding, Root, Stmt, Type as RuntimeType, TypeInstantiation,
};
use crate::types::{
    BoundsChoice, choose_bounds_type, collect_type_vars, contains_non_runtime_effect_type,
    contains_non_runtime_type, core_types_compatible, diagnostic_core_type, effect_compatible,
    is_qualified_runtime_path, project_runtime_hir_type_with_vars, strict_core_type as core_type,
};

mod expr;
mod helpers;
mod pattern;
mod types;

use expr::*;
use helpers::*;
use pattern::*;
use types::*;

#[derive(Debug, Clone)]
pub(super) struct BindingInfo {
    pub(super) ty: RuntimeType,
    pub(super) type_params: Vec<core_ir::TypeVar>,
}

pub fn validate_module(module: &Module) -> RuntimeResult<()> {
    let mut bindings = HashMap::new();
    for binding in &module.bindings {
        let info = BindingInfo {
            ty: binding.body.ty.clone(),
            type_params: binding.type_params.clone(),
        };
        match bindings.get_mut(&binding.name) {
            Some(current) if binding_info_generality(&info) > binding_info_generality(current) => {
                *current = info;
            }
            Some(_) => {}
            None => {
                bindings.insert(binding.name.clone(), info);
            }
        }
    }
    for root in &module.roots {
        match root {
            Root::Binding(path) if !bindings.contains_key(path) => {
                return Err(RuntimeError::UnboundVariable { path: path.clone() });
            }
            Root::Expr(index) if *index >= module.root_exprs.len() => {
                return Err(RuntimeError::MissingRootType { index: *index });
            }
            Root::Binding(_) | Root::Expr(_) => {}
        }
    }
    for binding in &module.bindings {
        validate_binding(binding, &bindings)?;
    }
    for expr in &module.root_exprs {
        validate_expr(expr, &bindings, &mut HashMap::new())?;
    }
    Ok(())
}

fn validate_binding(
    binding: &Binding,
    bindings: &HashMap<core_ir::Path, BindingInfo>,
) -> RuntimeResult<()> {
    validate_hir_type_no_any(&binding.body.ty, TypeSource::Validation)?;
    validate_expr(&binding.body, bindings, &mut HashMap::new())?;
    let mut vars = BTreeSet::new();
    collect_type_vars(&binding.scheme.body, &mut vars);
    require_same_hir_type(
        &project_runtime_hir_type_with_vars(&binding.scheme.body, &vars),
        &binding.body.ty,
        TypeSource::BindingScheme,
    )
}
