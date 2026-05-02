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
    collect_core_type_vars, export_coalesced_apply_evidence_bounds, export_type_bounds_for_tv,
    project_core_value_type_or_any,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CompleteApplyPrincipalEvidence {
    pub(super) principal_callee: core_ir::Type,
    pub(super) substitutions: Vec<core_ir::TypeSubstitution>,
}

pub(super) fn complete_apply_principal_evidence(
    infer: &Infer,
    principal_callee: core_ir::Type,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Option<CompleteApplyPrincipalEvidence> {
    let substitutions =
        apply_principal_substitutions(infer, &principal_callee, callee_tv, arg_tv, result_tv);
    (!substitutions.is_empty()).then_some(CompleteApplyPrincipalEvidence {
        principal_callee,
        substitutions,
    })
}

pub(super) fn apply_principal_substitutions(
    infer: &Infer,
    principal_callee: &core_ir::Type,
    callee_tv: TypeVar,
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

    let mut unifier = PrincipalSubstitutionUnifier::new(&params);
    let slot_types = apply_slot_monomorphic_types(infer, callee_tv, arg_tv, result_tv);
    if let Some(arg_ty) = slot_types.arg {
        unifier.infer(param, &arg_ty);
    }
    if let Some(result_ty) = slot_types.result {
        unifier.infer(ret, &result_ty);
    }
    if unifier.is_empty() {
        if let Some(arg_ty) = export_monomorphic_type_for_tv(infer, arg_tv) {
            unifier.infer(param, &arg_ty);
        }
        if let Some(result_ty) = export_monomorphic_type_for_tv(infer, result_tv) {
            unifier.infer(ret, &result_ty);
        }
    }

    unifier
        .into_substitutions()
        .filter(|(_, ty)| !matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_)))
        .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
        .collect()
}

struct ApplySlotTypes {
    arg: Option<core_ir::Type>,
    result: Option<core_ir::Type>,
}

fn apply_slot_monomorphic_types(
    infer: &Infer,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> ApplySlotTypes {
    let relevant_vars = BTreeSet::new();
    let (_, arg, result) =
        export_coalesced_apply_evidence_bounds(infer, callee_tv, arg_tv, result_tv, &relevant_vars);
    ApplySlotTypes {
        arg: monomorphic_type_from_bounds(arg),
        result: monomorphic_type_from_bounds(result),
    }
}

fn monomorphic_type_from_bounds(bounds: core_ir::TypeBounds) -> Option<core_ir::Type> {
    bounds
        .lower
        .as_deref()
        .or(bounds.upper.as_deref())
        .cloned()
        .filter(|ty| !matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_)))
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

struct PrincipalSubstitutionUnifier<'a> {
    params: &'a BTreeSet<core_ir::TypeVar>,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: BTreeSet<core_ir::TypeVar>,
}

impl<'a> PrincipalSubstitutionUnifier<'a> {
    fn new(params: &'a BTreeSet<core_ir::TypeVar>) -> Self {
        Self {
            params,
            substitutions: BTreeMap::new(),
            conflicts: BTreeSet::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.substitutions.is_empty()
    }

    fn into_substitutions(self) -> impl Iterator<Item = (core_ir::TypeVar, core_ir::Type)> {
        let conflicts = self.conflicts;
        self.substitutions
            .into_iter()
            .filter(move |(var, _)| !conflicts.contains(var))
    }

    fn infer(&mut self, template: &core_ir::Type, actual: &core_ir::Type) {
        match (template, actual) {
            (core_ir::Type::Var(var), actual) if self.params.contains(var) => {
                self.bind(var, actual);
            }
            (
                core_ir::Type::Named { path, args },
                core_ir::Type::Named {
                    path: actual_path,
                    args: actual_args,
                },
            ) if path == actual_path && args.len() == actual_args.len() => {
                for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                    self.infer_arg(template_arg, actual_arg);
                }
            }
            (
                core_ir::Type::Fun {
                    param,
                    param_effect,
                    ret_effect,
                    ret,
                },
                core_ir::Type::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                },
            ) => {
                self.infer(param, actual_param);
                self.infer(param_effect, actual_param_effect);
                self.infer(ret_effect, actual_ret_effect);
                self.infer(ret, actual_ret);
            }
            (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
                if items.len() == actual_items.len() =>
            {
                for (item, actual_item) in items.iter().zip(actual_items) {
                    self.infer(item, actual_item);
                }
            }
            (core_ir::Type::Record(record), core_ir::Type::Record(actual_record)) => {
                for field in &record.fields {
                    if let Some(actual_field) = actual_record
                        .fields
                        .iter()
                        .find(|actual| actual.name == field.name)
                    {
                        self.infer(&field.value, &actual_field.value);
                    }
                }
            }
            (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual) => {
                for item in items {
                    self.infer(item, actual);
                }
            }
            (core_ir::Type::Recursive { var, body }, actual) => {
                if !self.params.contains(var) {
                    self.infer(body, actual);
                }
            }
            _ => {}
        }
    }

    fn infer_arg(&mut self, template: &core_ir::TypeArg, actual: &core_ir::TypeArg) {
        match (template, actual) {
            (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
                self.infer(template, actual);
            }
            (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
                if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                    self.infer(template, actual);
                }
                if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                    self.infer(template, actual);
                }
            }
            _ => {}
        }
    }

    fn bind(&mut self, var: &core_ir::TypeVar, actual: &core_ir::Type) {
        if matches!(actual, core_ir::Type::Any | core_ir::Type::Var(_)) {
            return;
        }
        if self.conflicts.contains(var) {
            return;
        }
        match self.substitutions.get(var) {
            Some(existing) if existing == actual => {}
            Some(_) => {
                self.substitutions.remove(var);
                self.conflicts.insert(var.clone());
            }
            None => {
                self.substitutions.insert(var.clone(), actual.clone());
            }
        }
    }
}
