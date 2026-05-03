//! Build fully-principal export evidence for runtime specialization.
//!
//! This module owns the infer-side algorithm that should eventually make
//! runtime monomorphization a direct type-substitution step.  The key rule is
//! that co-occurrence and polar elimination are applied at the export slot that
//! owns the evidence, not as one global type-variable union.
//!
//! The longer-term target is principal elaboration evidence, not just a
//! substitution table.  A call site should expose the type it naturally
//! synthesizes, the contextual type required by the parent expression, and the
//! coercion/adapter holes needed to cross that boundary.  Runtime lowering can
//! then fill those holes with `Coerce`, thunk wrappers, `BindHere`, or handler
//! adapters instead of rediscovering the same subtyping facts through demand
//! monomorphization.

use std::collections::{BTreeMap, BTreeSet};

use yulang_core_ir as core_ir;

use crate::diagnostic::{ExpectedEdge, ExpectedEdgeId, ExpectedEdgeKind};
use crate::ids::TypeVar;
use crate::lower::LowerState;
use crate::solve::Infer;

use super::types::{
    collect_core_type_vars, export_coalesced_apply_evidence_bounds,
    export_coalesced_coerce_evidence_bounds, export_coalesced_type_bounds_for_tv,
    export_type_bounds_for_tv, project_core_value_type_or_any,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CompleteApplyPrincipalEvidence {
    pub(super) principal_callee: core_ir::Type,
    pub(super) substitutions: Vec<core_ir::TypeSubstitution>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedEdgeEvidence {
    pub id: ExpectedEdgeId,
    pub kind: ExpectedEdgeKind,
    pub actual: core_ir::TypeBounds,
    pub expected: core_ir::TypeBounds,
    pub actual_effect: Option<core_ir::TypeBounds>,
    pub expected_effect: Option<core_ir::TypeBounds>,
    pub closed: bool,
}

pub(super) fn complete_coerce_principal_evidence(
    infer: &Infer,
    source_edge: Option<ExpectedEdgeId>,
    actual_tv: TypeVar,
    expected_tv: TypeVar,
) -> core_ir::CoerceEvidence {
    let relevant_vars = BTreeSet::new();
    let (actual, expected) =
        export_coalesced_coerce_evidence_bounds(infer, actual_tv, expected_tv, &relevant_vars);
    core_ir::CoerceEvidence {
        source_edge: source_edge.map(|id| id.0),
        actual,
        expected,
    }
}

pub(super) fn complete_apply_principal_evidence(
    infer: &Infer,
    principal_scheme: core_ir::Scheme,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Option<CompleteApplyPrincipalEvidence> {
    let substitutions =
        apply_principal_substitutions(infer, &principal_scheme, callee_tv, arg_tv, result_tv);
    (!substitutions.is_empty()).then_some(CompleteApplyPrincipalEvidence {
        principal_callee: principal_scheme.body,
        substitutions,
    })
}

pub fn collect_expected_edge_evidence(state: &LowerState) -> Vec<ExpectedEdgeEvidence> {
    state
        .expected_edges
        .iter()
        .map(|edge| complete_expected_edge_evidence(&state.infer, edge))
        .collect()
}

pub(super) fn complete_expected_edge_evidence(
    infer: &Infer,
    edge: &ExpectedEdge,
) -> ExpectedEdgeEvidence {
    let actual = export_coalesced_type_bounds_for_tv(infer, edge.actual_tv);
    let expected = export_coalesced_type_bounds_for_tv(infer, edge.expected_tv);
    let actual_effect = edge
        .actual_eff
        .map(|tv| export_coalesced_type_bounds_for_tv(infer, tv));
    let expected_effect = edge
        .expected_eff
        .map(|tv| export_coalesced_type_bounds_for_tv(infer, tv));
    let closed = type_bounds_closed(&actual)
        && type_bounds_closed(&expected)
        && actual_effect.as_ref().is_none_or(type_bounds_closed)
        && expected_effect.as_ref().is_none_or(type_bounds_closed);
    ExpectedEdgeEvidence {
        id: edge.id,
        kind: edge.kind,
        actual,
        expected,
        actual_effect,
        expected_effect,
        closed,
    }
}

pub(super) fn apply_principal_substitutions(
    infer: &Infer,
    principal_scheme: &core_ir::Scheme,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Vec<core_ir::TypeSubstitution> {
    let principal_callee = &principal_scheme.body;
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
    unifier.infer_role_associated_requirements(&principal_scheme.requirements);

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

    fn infer_role_associated_requirements(&mut self, requirements: &[core_ir::RoleRequirement]) {
        for requirement in requirements {
            let Some(input) = first_requirement_input(requirement)
                .and_then(|bounds| self.substitute_bounds(bounds))
                .and_then(monomorphic_type_from_bounds)
            else {
                continue;
            };
            for associated in requirement.args.iter().filter_map(requirement_associated) {
                self.infer_list_item_associated(&input, associated);
            }
        }
    }

    fn infer_list_item_associated(
        &mut self,
        input: &core_ir::Type,
        associated: (&core_ir::Name, &core_ir::TypeBounds),
    ) {
        let (name, bounds) = associated;
        if name.0 != "item" {
            return;
        }
        let Some(item) = list_item_type(input) else {
            return;
        };
        if let Some(lower) = &bounds.lower {
            self.infer_value(lower, &item);
        }
        if let Some(upper) = &bounds.upper {
            self.infer_value(upper, &item);
        }
    }

    fn substitute_bounds(&self, bounds: &core_ir::TypeBounds) -> Option<core_ir::TypeBounds> {
        Some(core_ir::TypeBounds {
            lower: substitute_optional_box(bounds.lower.as_deref(), |ty| self.substitute_type(ty))?,
            upper: substitute_optional_box(bounds.upper.as_deref(), |ty| self.substitute_type(ty))?,
        })
    }

    fn substitute_type(&self, ty: &core_ir::Type) -> Option<core_ir::Type> {
        match ty {
            core_ir::Type::Var(var) if self.conflicts.contains(var) => None,
            core_ir::Type::Var(var) => self
                .substitutions
                .get(var)
                .cloned()
                .or_else(|| Some(core_ir::Type::Var(var.clone()))),
            core_ir::Type::Named { path, args } => Some(core_ir::Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.substitute_arg(arg))
                    .collect::<Option<Vec<_>>>()?,
            }),
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Some(core_ir::Type::Fun {
                param: Box::new(self.substitute_type(param)?),
                param_effect: Box::new(self.substitute_type(param_effect)?),
                ret_effect: Box::new(self.substitute_type(ret_effect)?),
                ret: Box::new(self.substitute_type(ret)?),
            }),
            core_ir::Type::Tuple(items) => Some(core_ir::Type::Tuple(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            core_ir::Type::Record(record) => Some(core_ir::Type::Record(core_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| {
                        Some(core_ir::RecordField {
                            name: field.name.clone(),
                            value: self.substitute_type(&field.value)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                spread: match &record.spread {
                    Some(core_ir::RecordSpread::Head(ty)) => Some(core_ir::RecordSpread::Head(
                        Box::new(self.substitute_type(ty)?),
                    )),
                    Some(core_ir::RecordSpread::Tail(ty)) => Some(core_ir::RecordSpread::Tail(
                        Box::new(self.substitute_type(ty)?),
                    )),
                    None => None,
                },
            })),
            core_ir::Type::Variant(variant) => Some(core_ir::Type::Variant(core_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| {
                        Some(core_ir::VariantCase {
                            name: case.name.clone(),
                            payloads: case
                                .payloads
                                .iter()
                                .map(|payload| self.substitute_type(payload))
                                .collect::<Option<Vec<_>>>()?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                tail: substitute_optional_box(variant.tail.as_deref(), |tail| {
                    self.substitute_type(tail)
                })?,
            })),
            core_ir::Type::Row { items, tail } => Some(core_ir::Type::Row {
                items: items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
                tail: Box::new(self.substitute_type(tail)?),
            }),
            core_ir::Type::Union(items) => Some(core_ir::Type::Union(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            core_ir::Type::Inter(items) => Some(core_ir::Type::Inter(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            core_ir::Type::Recursive { var, body } => Some(core_ir::Type::Recursive {
                var: var.clone(),
                body: Box::new(self.substitute_type(body)?),
            }),
            core_ir::Type::Never | core_ir::Type::Any => Some(ty.clone()),
        }
    }

    fn substitute_arg(&self, arg: &core_ir::TypeArg) -> Option<core_ir::TypeArg> {
        match arg {
            core_ir::TypeArg::Type(ty) => Some(core_ir::TypeArg::Type(self.substitute_type(ty)?)),
            core_ir::TypeArg::Bounds(bounds) => {
                Some(core_ir::TypeArg::Bounds(self.substitute_bounds(bounds)?))
            }
        }
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

fn first_requirement_input(requirement: &core_ir::RoleRequirement) -> Option<&core_ir::TypeBounds> {
    requirement.args.iter().find_map(|arg| match arg {
        core_ir::RoleRequirementArg::Input(bounds) => Some(bounds),
        core_ir::RoleRequirementArg::Associated { .. } => None,
    })
}

fn requirement_associated(
    arg: &core_ir::RoleRequirementArg,
) -> Option<(&core_ir::Name, &core_ir::TypeBounds)> {
    match arg {
        core_ir::RoleRequirementArg::Associated { name, bounds } => Some((name, bounds)),
        core_ir::RoleRequirementArg::Input(_) => None,
    }
}

fn list_item_type(ty: &core_ir::Type) -> Option<core_ir::Type> {
    let core_ir::Type::Named { path, args } = ty else {
        return None;
    };
    if !path.segments.last().is_some_and(|name| name.0 == "list") || args.len() != 1 {
        return None;
    }
    match &args[0] {
        core_ir::TypeArg::Type(ty) => Some(ty.clone()),
        core_ir::TypeArg::Bounds(bounds) => monomorphic_type_from_bounds(bounds.clone()),
    }
}

fn substitute_optional_box<T>(
    value: Option<&core_ir::Type>,
    mut substitute: impl FnMut(&core_ir::Type) -> Option<T>,
) -> Option<Option<Box<T>>> {
    match value {
        Some(ty) => substitute(ty).map(Box::new).map(Some),
        None => Some(None),
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

fn type_bounds_closed(bounds: &core_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds.lower.as_deref().is_none_or(|ty| !type_has_vars(ty))
        && bounds.upper.as_deref().is_none_or(|ty| !type_has_vars(ty))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowan::SyntaxNode;
    use yulang_parser::sink::YulangLanguage;

    use crate::{LowerState, diagnostic, lower_root};

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

    fn fold_path() -> core_ir::Path {
        core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("fold".to_string()),
                core_ir::Name("Fold".to_string()),
            ],
        }
    }

    fn parse_and_lower(src: &str) -> LowerState {
        let green = yulang_parser::parse_module_to_green(src);
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);
        state
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

    #[test]
    fn infers_fold_item_associated_from_list_input() {
        let params = Box::leak(Box::new(BTreeSet::from([tv("xs"), tv("item")])));
        let mut unifier = PrincipalSubstitutionUnifier::new(params);
        unifier.infer_value(
            &core_ir::Type::Var(tv("xs")),
            &list(core_ir::TypeArg::Type(named("int"))),
        );
        unifier.infer_role_associated_requirements(&[core_ir::RoleRequirement {
            role: fold_path(),
            args: vec![
                core_ir::RoleRequirementArg::Input(core_ir::TypeBounds::exact(core_ir::Type::Var(
                    tv("xs"),
                ))),
                core_ir::RoleRequirementArg::Associated {
                    name: core_ir::Name("item".to_string()),
                    bounds: core_ir::TypeBounds::exact(core_ir::Type::Var(tv("item"))),
                },
            ],
        }]);

        assert_eq!(
            unifier.into_substitutions().collect::<Vec<_>>(),
            vec![
                (tv("item"), named("int")),
                (tv("xs"), list(core_ir::TypeArg::Type(named("int")))),
            ]
        );
    }

    #[test]
    fn completes_expected_edge_evidence_with_exported_bounds() {
        let state = parse_and_lower("my f(x: int) = x\nf 1\n");
        let edge = state
            .expected_edges
            .iter()
            .find(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
            .expect("application argument edge");

        let evidence = complete_expected_edge_evidence(&state.infer, edge);

        assert_eq!(evidence.id, edge.id,);
        assert_eq!(
            evidence.kind,
            diagnostic::ExpectedEdgeKind::ApplicationArgument
        );
        assert_eq!(evidence.actual.lower.as_deref(), Some(&named("int")));
        assert_eq!(evidence.expected, core_ir::TypeBounds::exact(named("int")));
        assert!(evidence.actual_effect.is_none());
        assert!(evidence.expected_effect.is_none());
        assert!(!evidence.closed);
    }
}
