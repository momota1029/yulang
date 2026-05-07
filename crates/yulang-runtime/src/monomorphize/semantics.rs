use std::collections::{BTreeMap, HashMap, HashSet};

use yulang_core_ir as core_ir;

use super::{DemandCoreType, DemandEffect, DemandRecordField, DemandTypeArg, DemandVariantCase};
use crate::ir::{Binding, Expr, ExprKind, Module, Stmt};
use crate::types::effect_paths;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct DemandSemantics {
    associated_signature_kinds: HashMap<core_ir::Path, AssociatedSignatureKind>,
    associated_type_projections: Vec<AssociatedTypeProjection>,
    fold_members: HashSet<core_ir::Path>,
    fold_find_methods: HashSet<core_ir::Path>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AssociatedTypeProjection {
    role: core_ir::Path,
    inputs: Vec<core_ir::TypeBounds>,
    name: core_ir::Name,
    value: core_ir::TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum AssociatedSignatureKind {
    ForIn { loop_effects: Vec<core_ir::Path> },
    SubHandler { effect: core_ir::Path },
    LocalVarRef { effect: core_ir::Path },
    LocalVarRun { effect: core_ir::Path },
    ListViewRaw { result: Option<core_ir::Path> },
    ListIndexRaw,
    ListIndexRangeRaw,
    ListBinary,
    HandlerCollection { consumes: Vec<core_ir::Path> },
    FoldFind,
    Fold { thunk_callback: bool },
}

impl DemandSemantics {
    pub(super) fn from_module(module: &Module) -> Self {
        let associated_signature_kinds = module
            .bindings
            .iter()
            .filter_map(|binding| {
                structural_associated_signature_kind(binding)
                    .map(|kind| (binding.name.clone(), kind))
            })
            .collect();
        let mut associated_type_projections = Vec::new();
        let mut fold_members = HashSet::new();
        let mut fold_find_methods = HashSet::new();
        for role_impl in &module.role_impls {
            for associated in &role_impl.associated_types {
                associated_type_projections.push(AssociatedTypeProjection {
                    role: role_impl.role.clone(),
                    inputs: role_impl.inputs.clone(),
                    name: associated.name.clone(),
                    value: associated.value.clone(),
                });
            }
            if !role_impl
                .associated_types
                .iter()
                .any(|associated| associated.name.0 == "item")
            {
                continue;
            }
            let mut find_method = role_impl.role.clone();
            find_method.segments.push(core_ir::Name("find".to_string()));
            fold_find_methods.insert(find_method);
            for member in &role_impl.members {
                if member.name.0 == "fold" {
                    fold_members.insert(member.value.clone());
                }
            }
        }
        Self {
            associated_signature_kinds,
            associated_type_projections,
            fold_members,
            fold_find_methods,
        }
    }

    pub(super) fn is_fold_member(&self, target: &core_ir::Path) -> bool {
        self.fold_members.contains(target)
    }

    pub(super) fn is_fold_find_method(&self, target: &core_ir::Path) -> bool {
        self.fold_find_methods.contains(target)
    }

    pub(super) fn associated_signature_kind(
        &self,
        target: &core_ir::Path,
    ) -> Option<AssociatedSignatureKind> {
        if let Some(effect) = local_ref_effect_path(target) {
            return Some(AssociatedSignatureKind::LocalVarRef { effect });
        }
        if let Some(effect) = local_ref_run_effect_path(target) {
            return Some(AssociatedSignatureKind::LocalVarRun { effect });
        }
        if let Some(kind) = self.associated_signature_kinds.get(target) {
            return Some(kind.clone());
        }
        if self.is_fold_find_method(target) {
            return Some(AssociatedSignatureKind::FoldFind);
        }
        if self.is_fold_member(target) {
            return Some(AssociatedSignatureKind::Fold {
                thunk_callback: false,
            });
        }
        None
    }

    pub(super) fn is_effect_polymorphic_higher_order_target(&self, target: &core_ir::Path) -> bool {
        matches!(
            self.associated_signature_kind(target),
            Some(AssociatedSignatureKind::ForIn { .. } | AssociatedSignatureKind::Fold { .. })
        )
    }

    pub(super) fn project_unique_associated_type(
        &self,
        name: &core_ir::Name,
        inputs: &[DemandCoreType],
    ) -> Option<DemandCoreType> {
        let mut resolved = None;
        for projection in self
            .associated_type_projections
            .iter()
            .filter(|projection| {
                projection.name == *name && projection.inputs.len() == inputs.len()
            })
        {
            let mut substitutions = BTreeMap::new();
            if !projection
                .inputs
                .iter()
                .zip(inputs)
                .all(|(template, actual)| {
                    match_bounds_template(template, actual, &mut substitutions)
                })
            {
                continue;
            }
            let Some(value) = demand_core_from_bounds(&projection.value, &substitutions) else {
                continue;
            };
            match &resolved {
                Some(existing) if existing != &value => return None,
                Some(_) => {}
                None => resolved = Some(value),
            }
        }
        resolved
    }
}

pub(super) fn pure_handler_bindings(module: &Module) -> HashMap<core_ir::Path, Vec<core_ir::Path>> {
    module
        .bindings
        .iter()
        .filter_map(|binding| {
            expr_pure_handler_consumes(&binding.body)
                .map(|consumes| (binding.name.clone(), consumes))
        })
        .collect()
}

pub(super) fn consumed_effects_for_target(
    semantics: &DemandSemantics,
    pure_handlers: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
    target: &core_ir::Path,
) -> Vec<core_ir::Path> {
    let mut out = pure_handlers.get(target).cloned().unwrap_or_default();
    for effect in known_consumed_effects_for_target(semantics, target) {
        if !out.iter().any(|known| effect_paths_match(known, &effect)) {
            out.push(effect);
        }
    }
    out
}

pub(super) fn known_consumed_effects_for_target(
    semantics: &DemandSemantics,
    target: &core_ir::Path,
) -> Vec<core_ir::Path> {
    if let Some(effect) = local_ref_run_effect_path(target) {
        return vec![effect];
    }

    match semantics.associated_signature_kind(target) {
        Some(AssociatedSignatureKind::HandlerCollection { consumes }) => {
            return consumes;
        }
        Some(AssociatedSignatureKind::SubHandler { effect }) => {
            return vec![effect];
        }
        Some(AssociatedSignatureKind::FoldFind) => {}
        _ => {}
    }

    Vec::new()
}

fn expr_pure_handler_consumes(expr: &Expr) -> Option<Vec<core_ir::Path>> {
    match &expr.kind {
        ExprKind::Handle { handler, .. }
            if handler
                .residual_after
                .as_ref()
                .is_some_and(core_effect_is_empty) =>
        {
            Some(handler.consumes.clone())
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_pure_handler_consumes(body),
        ExprKind::Block {
            tail: Some(tail), ..
        } => expr_pure_handler_consumes(tail),
        ExprKind::Block { stmts, tail: None } => match stmts.last() {
            Some(Stmt::Expr(expr)) => expr_pure_handler_consumes(expr),
            _ => None,
        },
        _ => None,
    }
}

fn core_effect_is_empty(effect: &core_ir::Type) -> bool {
    matches!(effect, core_ir::Type::Never)
        || matches!(
            effect,
            core_ir::Type::Row { items, tail }
                if items.is_empty() && core_effect_is_empty(tail)
        )
}

fn match_bounds_template(
    template: &core_ir::TypeBounds,
    actual: &DemandCoreType,
    substitutions: &mut BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> bool {
    let lower_matches = template
        .lower
        .as_deref()
        .is_none_or(|lower| match_core_template(lower, actual, substitutions));
    let upper_matches = template
        .upper
        .as_deref()
        .is_none_or(|upper| match_core_template(upper, actual, substitutions));
    lower_matches && upper_matches
}

fn match_core_template(
    template: &core_ir::Type,
    actual: &DemandCoreType,
    substitutions: &mut BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> bool {
    match template {
        core_ir::Type::Var(var) => bind_associated_projection_var(var, actual, substitutions),
        core_ir::Type::Named { path, args } => {
            let DemandCoreType::Named {
                path: actual_path,
                args: actual_args,
            } = actual
            else {
                return false;
            };
            path == actual_path
                && args.len() == actual_args.len()
                && args.iter().zip(actual_args).all(|(template, actual)| {
                    match_type_arg_template(template, actual, substitutions)
                })
        }
        core_ir::Type::Tuple(items) => {
            let DemandCoreType::Tuple(actual_items) = actual else {
                return false;
            };
            items.len() == actual_items.len()
                && items
                    .iter()
                    .zip(actual_items)
                    .all(|(template, actual)| match_core_template(template, actual, substitutions))
        }
        core_ir::Type::Any => true,
        core_ir::Type::Never => matches!(actual, DemandCoreType::Never),
        core_ir::Type::Unknown => matches!(actual, DemandCoreType::Any | DemandCoreType::Hole(_)),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            let DemandCoreType::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            } = actual
            else {
                return false;
            };
            match_core_template(param, actual_param, substitutions)
                && match_effect_template(param_effect, actual_param_effect, substitutions)
                && match_effect_template(ret_effect, actual_ret_effect, substitutions)
                && match_core_template(ret, actual_ret, substitutions)
        }
        core_ir::Type::Union(items) => items
            .iter()
            .any(|item| match_core_template(item, actual, &mut substitutions.clone())),
        core_ir::Type::Inter(items) => items
            .iter()
            .all(|item| match_core_template(item, actual, substitutions)),
        core_ir::Type::Record(_) | core_ir::Type::Variant(_) | core_ir::Type::Row { .. } => false,
        core_ir::Type::Recursive { body, .. } => match_core_template(body, actual, substitutions),
    }
}

fn match_type_arg_template(
    template: &core_ir::TypeArg,
    actual: &DemandTypeArg,
    substitutions: &mut BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> bool {
    match (template, actual) {
        (core_ir::TypeArg::Type(template), DemandTypeArg::Type(actual)) => {
            match_core_template(template, actual, substitutions)
        }
        (core_ir::TypeArg::Type(template), DemandTypeArg::Bounds { lower, upper }) => lower
            .iter()
            .chain(upper)
            .any(|actual| match_core_template(template, actual, &mut substitutions.clone())),
        (core_ir::TypeArg::Bounds(template), DemandTypeArg::Type(actual)) => {
            match_bounds_template(template, actual, substitutions)
        }
        (core_ir::TypeArg::Bounds(template), DemandTypeArg::Bounds { lower, upper }) => lower
            .iter()
            .chain(upper)
            .any(|actual| match_bounds_template(template, actual, &mut substitutions.clone())),
    }
}

fn match_effect_template(
    template: &core_ir::Type,
    actual: &DemandEffect,
    substitutions: &mut BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> bool {
    match (template, actual) {
        (core_ir::Type::Never, DemandEffect::Empty) => true,
        (core_ir::Type::Var(var), effect) => {
            bind_associated_projection_var(var, &effect_arg_core(effect.clone()), substitutions)
        }
        (template, DemandEffect::Atom(actual)) => {
            match_core_template(template, actual, substitutions)
        }
        (core_ir::Type::Row { items, tail }, DemandEffect::Row(actual_items))
            if matches!(tail.as_ref(), core_ir::Type::Never) =>
        {
            items.len() == actual_items.len()
                && items.iter().zip(actual_items).all(|(template, actual)| {
                    match_effect_template(template, actual, substitutions)
                })
        }
        _ => false,
    }
}

fn bind_associated_projection_var(
    var: &core_ir::TypeVar,
    actual: &DemandCoreType,
    substitutions: &mut BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> bool {
    if !actual.is_closed() {
        return false;
    }
    match substitutions.get(var) {
        Some(existing) => existing == actual,
        None => {
            substitutions.insert(var.clone(), actual.clone());
            true
        }
    }
}

fn demand_core_from_bounds(
    bounds: &core_ir::TypeBounds,
    substitutions: &BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> Option<DemandCoreType> {
    let lower = bounds
        .lower
        .as_deref()
        .and_then(|lower| demand_core_from_type(lower, substitutions));
    let upper = bounds
        .upper
        .as_deref()
        .and_then(|upper| demand_core_from_type(upper, substitutions));
    match (lower, upper) {
        (Some(lower), Some(upper)) if lower == upper => Some(lower),
        (Some(_), Some(_)) => None,
        (Some(value), None) | (None, Some(value)) => Some(value),
        (None, None) => None,
    }
}

fn demand_core_from_type(
    ty: &core_ir::Type,
    substitutions: &BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> Option<DemandCoreType> {
    match ty {
        core_ir::Type::Unknown => Some(DemandCoreType::Any),
        core_ir::Type::Never => Some(DemandCoreType::Never),
        core_ir::Type::Any => Some(DemandCoreType::Any),
        core_ir::Type::Var(var) => substitutions.get(var).cloned(),
        core_ir::Type::Named { path, args } => Some(DemandCoreType::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| demand_type_arg_from_core(arg, substitutions))
                .collect::<Option<Vec<_>>>()?,
        }),
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Some(DemandCoreType::Fun {
            param: Box::new(demand_core_from_type(param, substitutions)?),
            param_effect: Box::new(demand_effect_from_type(param_effect, substitutions)?),
            ret_effect: Box::new(demand_effect_from_type(ret_effect, substitutions)?),
            ret: Box::new(demand_core_from_type(ret, substitutions)?),
        }),
        core_ir::Type::Tuple(items) => Some(DemandCoreType::Tuple(
            items
                .iter()
                .map(|item| demand_core_from_type(item, substitutions))
                .collect::<Option<Vec<_>>>()?,
        )),
        core_ir::Type::Record(record) if record.spread.is_none() => Some(DemandCoreType::Record(
            record
                .fields
                .iter()
                .map(|field| {
                    Some(DemandRecordField {
                        name: field.name.clone(),
                        value: demand_core_from_type(&field.value, substitutions)?,
                        optional: field.optional,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
        )),
        core_ir::Type::Variant(variant) if variant.tail.is_none() => Some(DemandCoreType::Variant(
            variant
                .cases
                .iter()
                .map(|case| {
                    Some(DemandVariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| demand_core_from_type(payload, substitutions))
                            .collect::<Option<Vec<_>>>()?,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
        )),
        core_ir::Type::Row { items, tail } if matches!(tail.as_ref(), core_ir::Type::Never) => {
            Some(DemandCoreType::RowAsValue(
                items
                    .iter()
                    .map(|item| demand_effect_from_type(item, substitutions))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        core_ir::Type::Union(items) => Some(DemandCoreType::Union(
            items
                .iter()
                .map(|item| demand_core_from_type(item, substitutions))
                .collect::<Option<Vec<_>>>()?,
        )),
        core_ir::Type::Inter(items) => Some(DemandCoreType::Inter(
            items
                .iter()
                .map(|item| demand_core_from_type(item, substitutions))
                .collect::<Option<Vec<_>>>()?,
        )),
        core_ir::Type::Recursive { var, body } => Some(DemandCoreType::Recursive {
            var: var.clone(),
            body: Box::new(demand_core_from_type(body, substitutions)?),
        }),
        core_ir::Type::Record(_) | core_ir::Type::Variant(_) | core_ir::Type::Row { .. } => None,
    }
}

fn demand_type_arg_from_core(
    arg: &core_ir::TypeArg,
    substitutions: &BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> Option<DemandTypeArg> {
    match arg {
        core_ir::TypeArg::Type(ty) => Some(DemandTypeArg::Type(demand_core_from_type(
            ty,
            substitutions,
        )?)),
        core_ir::TypeArg::Bounds(bounds) => Some(DemandTypeArg::Bounds {
            lower: bounds
                .lower
                .as_deref()
                .and_then(|lower| demand_core_from_type(lower, substitutions)),
            upper: bounds
                .upper
                .as_deref()
                .and_then(|upper| demand_core_from_type(upper, substitutions)),
        }),
    }
}

fn demand_effect_from_type(
    ty: &core_ir::Type,
    substitutions: &BTreeMap<core_ir::TypeVar, DemandCoreType>,
) -> Option<DemandEffect> {
    match ty {
        core_ir::Type::Never => Some(DemandEffect::Empty),
        core_ir::Type::Row { items, tail } if matches!(tail.as_ref(), core_ir::Type::Never) => {
            Some(DemandEffect::Row(
                items
                    .iter()
                    .map(|item| demand_effect_from_type(item, substitutions))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        ty => Some(DemandEffect::Atom(demand_core_from_type(
            ty,
            substitutions,
        )?)),
    }
}

fn effect_arg_core(effect: DemandEffect) -> DemandCoreType {
    match effect {
        DemandEffect::Empty => DemandCoreType::Never,
        DemandEffect::Row(items) => DemandCoreType::RowAsValue(items),
        effect => DemandCoreType::RowAsValue(vec![effect]),
    }
}

fn local_ref_run_effect_path(target: &core_ir::Path) -> Option<core_ir::Path> {
    let [namespace, name] = target.segments.as_slice() else {
        return None;
    };
    (name.0 == "run" && namespace.0.starts_with('&')).then(|| core_ir::Path {
        segments: vec![namespace.clone()],
    })
}

fn structural_associated_signature_kind(binding: &Binding) -> Option<AssociatedSignatureKind> {
    if runtime_fun_args(&binding.body.ty).len() >= 3
        && expr_contains_primitive(&binding.body, core_ir::PrimitiveOp::ListViewRaw)
    {
        return Some(AssociatedSignatureKind::Fold {
            thunk_callback: true,
        });
    }
    if let Some(kind) = primitive_associated_signature_kind(&binding.body) {
        return Some(kind);
    }
    if let Some(loop_effects) = for_in_callback_loop_effects(&binding.body.ty) {
        return Some(AssociatedSignatureKind::ForIn { loop_effects });
    }
    if let Some(consumes) = handler_collection_consumes(binding) {
        return Some(AssociatedSignatureKind::HandlerCollection { consumes });
    }
    if let Some(effect) = sub_handler_effect(binding) {
        return Some(AssociatedSignatureKind::SubHandler { effect });
    }
    None
}

fn sub_handler_effect(binding: &Binding) -> Option<core_ir::Path> {
    if binding
        .name
        .segments
        .last()
        .is_none_or(|name| name.0 != "sub")
    {
        return None;
    }
    let consumes = expr_pure_handler_consumes(&binding.body)
        .or_else(|| runtime_first_thunk_param_effects(&binding.body.ty))?;
    match consumes.as_slice() {
        [effect] => Some(effect.clone()),
        _ => None,
    }
}

fn handler_collection_consumes(binding: &Binding) -> Option<Vec<core_ir::Path>> {
    let consumes = expr_pure_handler_consumes(&binding.body)
        .or_else(|| runtime_first_thunk_param_effects(&binding.body.ty))?;
    if consumes.is_empty() {
        return None;
    }
    (function_result_named_single_type_arg(&binding.scheme.body)
        || runtime_result_named_single_type_arg(&binding.body.ty)
        || expr_result_named_single_type_arg(&binding.body))
    .then_some(consumes)
}

fn primitive_associated_signature_kind(expr: &Expr) -> Option<AssociatedSignatureKind> {
    match direct_primitive_head(expr)? {
        core_ir::PrimitiveOp::ListViewRaw => Some(AssociatedSignatureKind::ListViewRaw {
            result: runtime_result_named_path(&expr.ty),
        }),
        core_ir::PrimitiveOp::ListIndex => Some(AssociatedSignatureKind::ListIndexRaw),
        core_ir::PrimitiveOp::ListIndexRangeRaw => Some(AssociatedSignatureKind::ListIndexRangeRaw),
        core_ir::PrimitiveOp::ListMerge => Some(AssociatedSignatureKind::ListBinary),
        _ => None,
    }
}

fn direct_primitive_head(expr: &Expr) -> Option<core_ir::PrimitiveOp> {
    match &expr.kind {
        ExprKind::PrimitiveOp(op) => Some(*op),
        ExprKind::Lambda { body, .. }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => direct_primitive_head(body),
        ExprKind::Apply { callee, .. } => direct_primitive_head(callee),
        _ => None,
    }
}

fn expr_contains_primitive(expr: &Expr, op: core_ir::PrimitiveOp) -> bool {
    match &expr.kind {
        ExprKind::PrimitiveOp(candidate) => *candidate == op,
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_contains_primitive(body, op),
        ExprKind::Apply { callee, arg, .. } => {
            expr_contains_primitive(callee, op) || expr_contains_primitive(arg, op)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_contains_primitive(cond, op)
                || expr_contains_primitive(then_branch, op)
                || expr_contains_primitive(else_branch, op)
        }
        ExprKind::Tuple(items) => items.iter().any(|item| expr_contains_primitive(item, op)),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_contains_primitive(&field.value, op))
                || spread.as_ref().is_some_and(|spread| match spread {
                    crate::ir::RecordSpreadExpr::Head(value)
                    | crate::ir::RecordSpreadExpr::Tail(value) => {
                        expr_contains_primitive(value, op)
                    }
                })
        }
        ExprKind::Variant { value, .. } => value
            .as_deref()
            .is_some_and(|value| expr_contains_primitive(value, op)),
        ExprKind::Select { base, .. } => expr_contains_primitive(base, op),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_contains_primitive(scrutinee, op)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_contains_primitive(guard, op))
                        || expr_contains_primitive(&arm.body, op)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
                    expr_contains_primitive(value, op)
                }
            }) || tail
                .as_deref()
                .is_some_and(|tail| expr_contains_primitive(tail, op))
        }
        ExprKind::Handle { body, arms, .. } => {
            expr_contains_primitive(body, op)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_contains_primitive(guard, op))
                        || expr_contains_primitive(&arm.body, op)
                })
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}

fn local_ref_effect_path(target: &core_ir::Path) -> Option<core_ir::Path> {
    let [namespace, name] = target.segments.as_slice() else {
        return None;
    };
    (name.0 == "var_ref" && namespace.0.starts_with('&')).then(|| core_ir::Path {
        segments: vec![namespace.clone()],
    })
}

fn function_result_named_single_type_arg(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Fun { ret, .. } => function_result_named_single_type_arg(ret),
        core_ir::Type::Named { args, .. } => {
            matches!(args.as_slice(), [core_ir::TypeArg::Type(_)])
        }
        _ => false,
    }
}

fn runtime_first_thunk_param_effects(ty: &crate::ir::Type) -> Option<Vec<core_ir::Path>> {
    let crate::ir::Type::Fun { param, .. } = ty else {
        return None;
    };
    let crate::ir::Type::Thunk { effect, .. } = param.as_ref() else {
        return None;
    };
    Some(effect_paths(effect))
}

fn for_in_callback_loop_effects(ty: &crate::ir::Type) -> Option<Vec<core_ir::Path>> {
    let args = runtime_fun_args(ty);
    let callback = args.get(1)?;
    let effects = runtime_result_effect_paths(callback);
    (!effects.is_empty()).then_some(effects)
}

fn runtime_fun_args(mut ty: &crate::ir::Type) -> Vec<&crate::ir::Type> {
    let mut args = Vec::new();
    while let crate::ir::Type::Fun { param, ret } = ty {
        args.push(param.as_ref());
        ty = ret;
    }
    args
}

fn runtime_result_effect_paths(ty: &crate::ir::Type) -> Vec<core_ir::Path> {
    match ty {
        crate::ir::Type::Fun { ret, .. } => runtime_result_effect_paths(ret),
        crate::ir::Type::Thunk { effect, .. } => effect_paths(effect),
        _ => Vec::new(),
    }
}

fn runtime_result_named_single_type_arg(ty: &crate::ir::Type) -> bool {
    match ty {
        crate::ir::Type::Fun { ret, .. } => runtime_result_named_single_type_arg(ret),
        crate::ir::Type::Thunk { value, .. } => runtime_result_named_single_type_arg(value),
        crate::ir::Type::Core(core_ir::Type::Named { args, .. }) => {
            matches!(args.as_slice(), [core_ir::TypeArg::Type(_)])
        }
        _ => false,
    }
}

fn runtime_result_named_path(ty: &crate::ir::Type) -> Option<core_ir::Path> {
    match ty {
        crate::ir::Type::Fun { ret, .. } => runtime_result_named_path(ret),
        crate::ir::Type::Thunk { value, .. } => runtime_result_named_path(value),
        crate::ir::Type::Core(core_ir::Type::Named { path, .. }) => Some(path.clone()),
        _ => None,
    }
}

fn expr_result_named_single_type_arg(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_result_named_single_type_arg(body),
        ExprKind::Block {
            tail: Some(tail), ..
        } => expr_result_named_single_type_arg(tail),
        ExprKind::Block { stmts, tail: None } => match stmts.last() {
            Some(Stmt::Expr(expr)) => expr_result_named_single_type_arg(expr),
            _ => false,
        },
        _ => runtime_result_named_single_type_arg(&expr.ty),
    }
}

fn effect_paths_match(left: &core_ir::Path, right: &core_ir::Path) -> bool {
    left == right
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Binding, HandleEffect, JoinEvidence, Type as RuntimeType};

    #[test]
    fn consumed_effects_include_user_defined_pure_handlers() {
        let handler = path(&["user", "handler"]);
        let effect = path(&["user", "effect"]);
        let module = Module {
            path: path(&["user"]),
            bindings: vec![Binding {
                name: handler.clone(),
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Any,
                },
                body: Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Unit),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        arms: Vec::new(),
                        evidence: JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: HandleEffect {
                            consumes: vec![effect.clone()],
                            residual_before: Some(core_ir::Type::Named {
                                path: effect.clone(),
                                args: Vec::new(),
                            }),
                            residual_after: Some(core_ir::Type::Never),
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                ),
            }],
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
        };

        let pure_handlers = pure_handler_bindings(&module);

        assert_eq!(
            consumed_effects_for_target(&DemandSemantics::default(), &pure_handlers, &handler),
            vec![effect]
        );
    }

    fn path(segments: &[&str]) -> core_ir::Path {
        core_ir::Path {
            segments: segments
                .iter()
                .map(|segment| core_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
