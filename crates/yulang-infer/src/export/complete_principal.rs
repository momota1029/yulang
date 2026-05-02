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
        unifier.infer_value(param, &arg_ty);
    }
    if let Some(result_ty) = slot_types.result {
        unifier.infer_value(ret, &result_ty);
    }
    if unifier.is_empty() {
        if let Some(arg_ty) = export_monomorphic_type_for_tv(infer, arg_tv) {
            unifier.infer_value(param, &arg_ty);
        }
        if let Some(result_ty) = export_monomorphic_type_for_tv(infer, result_tv) {
            unifier.infer_value(ret, &result_ty);
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

    fn infer_value(&mut self, template: &core_ir::Type, actual: &core_ir::Type) {
        self.infer(template, actual, false);
    }

    fn infer_effect(&mut self, template: &core_ir::Type, actual: &core_ir::Type) {
        self.infer(template, actual, true);
    }

    fn infer(&mut self, template: &core_ir::Type, actual: &core_ir::Type, allow_never: bool) {
        match (template, actual) {
            (core_ir::Type::Var(var), actual) if self.params.contains(var) => {
                self.bind(var, actual, allow_never);
            }
            (
                core_ir::Type::Named { path, args },
                core_ir::Type::Named {
                    path: actual_path,
                    args: actual_args,
                },
            ) if path == actual_path && args.len() == actual_args.len() => {
                for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                    self.infer_arg(template_arg, actual_arg, allow_never);
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
                self.infer_value(param, actual_param);
                self.infer_effect(param_effect, actual_param_effect);
                self.infer_effect(ret_effect, actual_ret_effect);
                self.infer_value(ret, actual_ret);
            }
            (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
                if items.len() == actual_items.len() =>
            {
                for (item, actual_item) in items.iter().zip(actual_items) {
                    self.infer(item, actual_item, allow_never);
                }
            }
            (core_ir::Type::Record(record), core_ir::Type::Record(actual_record)) => {
                for field in &record.fields {
                    if let Some(actual_field) = actual_record
                        .fields
                        .iter()
                        .find(|actual| actual.name == field.name)
                    {
                        self.infer(&field.value, &actual_field.value, allow_never);
                    }
                }
            }
            (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual) => {
                for item in items {
                    self.infer(item, actual, allow_never);
                }
            }
            (core_ir::Type::Recursive { var, body }, actual) => {
                if !self.params.contains(var) {
                    self.infer(body, actual, allow_never);
                }
            }
            _ => {}
        }
    }

    fn infer_arg(
        &mut self,
        template: &core_ir::TypeArg,
        actual: &core_ir::TypeArg,
        allow_never: bool,
    ) {
        match (template, actual) {
            (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
                self.infer(template, actual, allow_never);
            }
            (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
                if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                    self.infer(template, actual, allow_never);
                }
                if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                    self.infer(template, actual, allow_never);
                }
            }
            _ => {}
        }
    }

    fn bind(&mut self, var: &core_ir::TypeVar, actual: &core_ir::Type, allow_never: bool) {
        if matches!(actual, core_ir::Type::Any | core_ir::Type::Var(_))
            || (!allow_never && matches!(actual, core_ir::Type::Never))
        {
            return;
        }
        if self.conflicts.contains(var) {
            return;
        }
        match self.substitutions.get(var) {
            Some(existing) if existing == actual => {}
            Some(existing) => {
                if let Some(merged) = merge_substitution_type(existing, actual) {
                    self.substitutions.insert(var.clone(), merged);
                } else {
                    self.substitutions.remove(var);
                    self.conflicts.insert(var.clone());
                }
            }
            None => {
                self.substitutions.insert(var.clone(), actual.clone());
            }
        }
    }
}

fn merge_substitution_type(left: &core_ir::Type, right: &core_ir::Type) -> Option<core_ir::Type> {
    if left == right {
        return Some(left.clone());
    }
    if type_has_vars(left) && !type_has_vars(right) {
        return Some(right.clone());
    }
    if !type_has_vars(left) && type_has_vars(right) {
        return Some(left.clone());
    }
    match (left, right) {
        (
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: right_path,
                args: right_args,
            },
        ) if path == right_path && args.len() == right_args.len() => {
            let args = args
                .iter()
                .zip(right_args)
                .map(|(left, right)| merge_type_arg(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Named {
                path: path.clone(),
                args,
            })
        }
        (
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            core_ir::Type::Fun {
                param: right_param,
                param_effect: right_param_effect,
                ret_effect: right_ret_effect,
                ret: right_ret,
            },
        ) => Some(core_ir::Type::Fun {
            param: Box::new(merge_substitution_type(param, right_param)?),
            param_effect: Box::new(merge_substitution_type(param_effect, right_param_effect)?),
            ret_effect: Box::new(merge_substitution_type(ret_effect, right_ret_effect)?),
            ret: Box::new(merge_substitution_type(ret, right_ret)?),
        }),
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(right_items))
            if items.len() == right_items.len() =>
        {
            let items = items
                .iter()
                .zip(right_items)
                .map(|(left, right)| merge_substitution_type(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Tuple(items))
        }
        _ => None,
    }
}

fn merge_type_arg(left: &core_ir::TypeArg, right: &core_ir::TypeArg) -> Option<core_ir::TypeArg> {
    match (left, right) {
        (core_ir::TypeArg::Type(left), core_ir::TypeArg::Type(right)) => {
            merge_substitution_type(left, right).map(core_ir::TypeArg::Type)
        }
        (core_ir::TypeArg::Type(ty), core_ir::TypeArg::Bounds(bounds))
        | (core_ir::TypeArg::Bounds(bounds), core_ir::TypeArg::Type(ty)) => {
            type_fits_bounds(ty, bounds).then(|| core_ir::TypeArg::Type(ty.clone()))
        }
        (core_ir::TypeArg::Bounds(left), core_ir::TypeArg::Bounds(right)) => {
            Some(core_ir::TypeArg::Bounds(merge_type_bounds(left, right)?))
        }
    }
}

fn merge_type_bounds(
    left: &core_ir::TypeBounds,
    right: &core_ir::TypeBounds,
) -> Option<core_ir::TypeBounds> {
    let lower = merge_optional_bound(left.lower.as_deref(), right.lower.as_deref())?;
    let upper = merge_optional_bound(left.upper.as_deref(), right.upper.as_deref())?;
    Some(core_ir::TypeBounds {
        lower: lower.map(Box::new),
        upper: upper.map(Box::new),
    })
}

fn merge_optional_bound(
    left: Option<&core_ir::Type>,
    right: Option<&core_ir::Type>,
) -> Option<Option<core_ir::Type>> {
    match (left, right) {
        (Some(left), Some(right)) => merge_substitution_type(left, right).map(Some),
        (Some(ty), None) | (None, Some(ty)) => Some(Some(ty.clone())),
        (None, None) => Some(None),
    }
}

fn type_fits_bounds(ty: &core_ir::Type, bounds: &core_ir::TypeBounds) -> bool {
    bounds
        .lower
        .as_deref()
        .is_none_or(|lower| merge_substitution_type(lower, ty).is_some())
        && bounds
            .upper
            .as_deref()
            .is_none_or(|upper| merge_substitution_type(upper, ty).is_some())
}

fn type_has_vars(ty: &core_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    !vars.is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tv(name: &str) -> core_ir::TypeVar {
        core_ir::TypeVar(name.to_string())
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn list(arg: core_ir::TypeArg) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path {
                segments: vec![
                    core_ir::Name("std".to_string()),
                    core_ir::Name("list".to_string()),
                    core_ir::Name("list".to_string()),
                ],
            },
            args: vec![arg],
        }
    }

    fn one_param_unifier() -> PrincipalSubstitutionUnifier<'static> {
        let params = Box::leak(Box::new(BTreeSet::from([tv("t")])));
        PrincipalSubstitutionUnifier::new(params)
    }

    #[test]
    fn merges_bounds_arg_to_concrete_type_arg() {
        let concrete = list(core_ir::TypeArg::Type(named("int")));
        let bounded = list(core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: Some(Box::new(named("int"))),
            upper: None,
        }));

        assert_eq!(merge_substitution_type(&bounded, &concrete), Some(concrete));
    }

    #[test]
    fn value_position_does_not_bind_never() {
        let mut unifier = one_param_unifier();
        unifier.infer_value(&core_ir::Type::Var(tv("t")), &core_ir::Type::Never);

        assert!(unifier.into_substitutions().next().is_none());
    }

    #[test]
    fn effect_position_can_bind_never() {
        let mut unifier = one_param_unifier();
        unifier.infer_effect(&core_ir::Type::Var(tv("t")), &core_ir::Type::Never);

        assert_eq!(
            unifier.into_substitutions().collect::<Vec<_>>(),
            vec![(tv("t"), core_ir::Type::Never)]
        );
    }

    #[test]
    fn conflicting_candidates_drop_the_substitution() {
        let mut unifier = one_param_unifier();
        unifier.infer_value(&core_ir::Type::Var(tv("t")), &named("int"));
        unifier.infer_value(&core_ir::Type::Var(tv("t")), &named("bool"));

        assert!(unifier.into_substitutions().next().is_none());
    }
}
