//! Build fully-principal export evidence for runtime specialization.
//!
//! This module owns the infer-side algorithm that should eventually make
//! runtime monomorphization a direct type-substitution step.  The key rule is
//! that co-occurrence and polar elimination are applied at the export slot that
//! owns the evidence, not as one global type-variable union.

use std::collections::{BTreeMap, BTreeSet};

use yulang_core_ir as core_ir;

use crate::ids::TypeVar;
use crate::solve::Infer;

use super::types::{
    collect_core_type_vars, export_type_bounds_for_tv, project_core_value_type_or_any,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CompleteApplyPrincipalEvidence {
    pub(super) principal_callee: core_ir::Type,
    pub(super) substitutions: Vec<core_ir::TypeSubstitution>,
}

pub(super) fn complete_apply_principal_evidence(
    infer: &Infer,
    principal_callee: core_ir::Type,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Option<CompleteApplyPrincipalEvidence> {
    let substitutions = apply_principal_substitutions(infer, &principal_callee, arg_tv, result_tv);
    (!substitutions.is_empty()).then_some(CompleteApplyPrincipalEvidence {
        principal_callee,
        substitutions,
    })
}

pub(super) fn apply_principal_substitutions(
    infer: &Infer,
    principal_callee: &core_ir::Type,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Vec<core_ir::TypeSubstitution> {
    let Some((param, ret)) = principal_fun_param_ret(principal_callee) else {
        return Vec::new();
    };
    let mut params = BTreeSet::new();
    collect_core_type_vars(principal_callee, &mut params);
    if params.is_empty() {
        return Vec::new();
    }

    let mut substitutions = BTreeMap::new();
    if let Some(arg_ty) = export_monomorphic_type_for_tv(infer, arg_tv) {
        infer_core_type_substitutions(param, &arg_ty, &params, &mut substitutions);
    }
    if let Some(result_ty) = export_monomorphic_type_for_tv(infer, result_tv) {
        infer_core_type_substitutions(ret, &result_ty, &params, &mut substitutions);
    }

    substitutions
        .into_iter()
        .filter(|(_, ty)| !matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_)))
        .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
        .collect()
}

fn principal_fun_param_ret(ty: &core_ir::Type) -> Option<(&core_ir::Type, &core_ir::Type)> {
    match ty {
        core_ir::Type::Fun { param, ret, .. } => Some((param, ret)),
        core_ir::Type::Recursive { body, .. } => principal_fun_param_ret(body),
        core_ir::Type::Inter(items) | core_ir::Type::Union(items) => {
            items.iter().find_map(principal_fun_param_ret)
        }
        _ => None,
    }
}

fn export_monomorphic_type_for_tv(infer: &Infer, tv: TypeVar) -> Option<core_ir::Type> {
    let bounds = export_type_bounds_for_tv(infer, tv);
    bounds
        .lower
        .as_deref()
        .or(bounds.upper.as_deref())
        .cloned()
        .map(|ty| project_core_value_type_or_any(ty, &BTreeSet::new()))
        .filter(|ty| !matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_)))
}

fn infer_core_type_substitutions(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    match (template, actual) {
        (core_ir::Type::Var(var), actual) if params.contains(var) => {
            substitutions
                .entry(var.clone())
                .or_insert_with(|| actual.clone());
        }
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                infer_core_type_arg_substitutions(template_arg, actual_arg, params, substitutions);
            }
        }
        (
            core_ir::Type::Fun { param, ret, .. },
            core_ir::Type::Fun {
                param: actual_param,
                ret: actual_ret,
                ..
            },
        ) => {
            infer_core_type_substitutions(param, actual_param, params, substitutions);
            infer_core_type_substitutions(ret, actual_ret, params, substitutions);
        }
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                infer_core_type_substitutions(item, actual_item, params, substitutions);
            }
        }
        (core_ir::Type::Record(record), core_ir::Type::Record(actual_record)) => {
            for field in &record.fields {
                if let Some(actual_field) = actual_record
                    .fields
                    .iter()
                    .find(|actual| actual.name == field.name)
                {
                    infer_core_type_substitutions(
                        &field.value,
                        &actual_field.value,
                        params,
                        substitutions,
                    );
                }
            }
        }
        (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual) => {
            for item in items {
                infer_core_type_substitutions(item, actual, params, substitutions);
            }
        }
        (core_ir::Type::Recursive { var, body }, actual) => {
            let mut params = params.clone();
            params.remove(var);
            infer_core_type_substitutions(body, actual, &params, substitutions);
        }
        _ => {}
    }
}

fn infer_core_type_arg_substitutions(
    template: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
    params: &BTreeSet<core_ir::TypeVar>,
    substitutions: &mut BTreeMap<core_ir::TypeVar, core_ir::Type>,
) {
    match (template, actual) {
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
            infer_core_type_substitutions(template, actual, params, substitutions);
        }
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
            if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                infer_core_type_substitutions(template, actual, params, substitutions);
            }
            if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                infer_core_type_substitutions(template, actual, params, substitutions);
            }
        }
        _ => {}
    }
}
