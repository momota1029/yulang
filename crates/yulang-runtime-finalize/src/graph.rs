use std::collections::{BTreeMap, BTreeSet};

use yulang_runtime_ir::{Binding, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{FinalizeDiagnostic, FinalizeResult};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeGraph {
    next_fresh: usize,
    slots: BTreeMap<typed_ir::TypeVar, TypeVarBounds>,
    constraints: Vec<SubtypeConstraint>,
}

impl TypeGraph {
    pub fn instantiate_principal(&mut self, binding: &Binding) -> PrincipalInstance {
        let mut renames = BTreeMap::new();
        for param in &binding.type_params {
            let fresh = self.fresh_var(param);
            self.slots.entry(fresh.clone()).or_default();
            renames.insert(param.clone(), fresh);
        }
        PrincipalInstance {
            original_binding: binding.name.clone(),
            principal_type: rename_type(&binding.scheme.body, &renames),
            type_params: renames
                .into_iter()
                .map(|(original, fresh)| PrincipalTypeParam { original, fresh })
                .collect(),
        }
    }

    pub fn collect_runtime_bounds(
        &mut self,
        template: &typed_ir::Type,
        bounds: &RuntimeBounds,
    ) -> FinalizeResult<()> {
        if let Some(lower) = &bounds.lower {
            self.collect_runtime(template, lower, BoundSide::Lower)?;
        }
        if let Some(upper) = &bounds.upper {
            self.collect_runtime(template, upper, BoundSide::Upper)?;
        }
        self.propagate_constraints()
    }

    pub fn collect_runtime_lower(
        &mut self,
        template: &typed_ir::Type,
        lower: &RuntimeType,
    ) -> FinalizeResult<()> {
        self.collect_runtime(template, lower, BoundSide::Lower)?;
        self.propagate_constraints()
    }

    pub fn collect_runtime_upper(
        &mut self,
        template: &typed_ir::Type,
        upper: &RuntimeType,
    ) -> FinalizeResult<()> {
        self.collect_runtime(template, upper, BoundSide::Upper)?;
        self.propagate_constraints()
    }

    pub fn fresh_hole(&mut self, prefix: &str) -> typed_ir::Type {
        let var = self.fresh_var(&typed_ir::TypeVar(prefix.into()));
        self.slots.entry(var.clone()).or_default();
        typed_ir::Type::Var(var)
    }

    pub fn constrain_subtype(
        &mut self,
        lower: typed_ir::Type,
        upper: typed_ir::Type,
    ) -> FinalizeResult<()> {
        let constraint = SubtypeConstraint { lower, upper };
        if !self.constraints.contains(&constraint) {
            self.constraints.push(constraint);
        }
        self.propagate_constraints()
    }

    pub fn default_unbound_lower(
        &mut self,
        vars: BTreeSet<typed_ir::TypeVar>,
        lower: typed_ir::Type,
    ) -> FinalizeResult<()> {
        for var in vars {
            let Some(slot) = self.slots.get_mut(&var) else {
                continue;
            };
            if slot.lower.is_none() && slot.upper.is_none() {
                slot.push_lower(var, lower.clone())?;
            }
        }
        self.propagate_constraints()
    }

    pub fn solve(self) -> GraphSolution {
        let type_vars = self
            .slots
            .into_iter()
            .map(|(var, bounds)| {
                let solution = bounds.solution_ref().cloned();
                ResolvedTypeVar {
                    var,
                    bounds,
                    solution,
                }
            })
            .collect();
        GraphSolution { type_vars }
    }

    pub fn slot(&self, var: &typed_ir::TypeVar) -> Option<&TypeVarBounds> {
        self.slots.get(var)
    }

    fn fresh_var(&mut self, source: &typed_ir::TypeVar) -> typed_ir::TypeVar {
        let fresh = typed_ir::TypeVar(format!("{}#{}", source.0, self.next_fresh));
        self.next_fresh += 1;
        fresh
    }

    fn collect_runtime(
        &mut self,
        template: &typed_ir::Type,
        actual: &RuntimeType,
        side: BoundSide,
    ) -> FinalizeResult<()> {
        match actual {
            RuntimeType::Core(actual) => self.collect_core(template, actual, side),
            RuntimeType::Fun { param, ret } => {
                let typed_ir::Type::Fun {
                    param: template_param,
                    param_effect: template_param_effect,
                    ret_effect: template_ret_effect,
                    ret: template_ret,
                } = template
                else {
                    return Ok(());
                };
                let RuntimeEffectedType {
                    value: actual_param,
                    effect: actual_param_effect,
                } = split_runtime_effected_type(param);
                let RuntimeEffectedType {
                    value: actual_ret,
                    effect: actual_ret_effect,
                } = split_runtime_effected_type(ret);
                self.collect_runtime(template_param, actual_param, side)?;
                self.collect_runtime_effect(template_param_effect, actual_param_effect, side)?;
                self.collect_runtime_effect(template_ret_effect, actual_ret_effect, side)?;
                self.collect_runtime(template_ret, actual_ret, side)
            }
            RuntimeType::Thunk { value, .. } => self.collect_runtime(template, value, side),
            RuntimeType::Unknown => Ok(()),
        }
    }

    fn collect_core(
        &mut self,
        template: &typed_ir::Type,
        actual: &typed_ir::Type,
        side: BoundSide,
    ) -> FinalizeResult<()> {
        match template {
            typed_ir::Type::Var(var) => self.record(var.clone(), actual.clone(), side).map(|_| ()),
            typed_ir::Type::Named { path, args } => {
                let typed_ir::Type::Named {
                    path: actual_path,
                    args: actual_args,
                } = actual
                else {
                    return Ok(());
                };
                if path != actual_path || args.len() != actual_args.len() {
                    return Ok(());
                }
                for (template, actual) in args.iter().zip(actual_args) {
                    self.collect_type_arg(template, actual, side)?;
                }
                Ok(())
            }
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                let typed_ir::Type::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                } = actual
                else {
                    return Ok(());
                };
                self.collect_core(param, actual_param, side)?;
                self.collect_core(param_effect, actual_param_effect, side)?;
                self.collect_core(ret_effect, actual_ret_effect, side)?;
                self.collect_core(ret, actual_ret, side)
            }
            typed_ir::Type::Tuple(items) => {
                let typed_ir::Type::Tuple(actual_items) = actual else {
                    return Ok(());
                };
                if items.len() != actual_items.len() {
                    return Ok(());
                }
                for (template, actual) in items.iter().zip(actual_items) {
                    self.collect_core(template, actual, side)?;
                }
                Ok(())
            }
            typed_ir::Type::Row { items, tail } => {
                let typed_ir::Type::Row {
                    items: actual_items,
                    tail: actual_tail,
                } = actual
                else {
                    return Ok(());
                };
                self.collect_row(items, tail, actual_items, actual_tail, side)
            }
            typed_ir::Type::Unknown
            | typed_ir::Type::Never
            | typed_ir::Type::Any
            | typed_ir::Type::Union(_)
            | typed_ir::Type::Inter(_)
            | typed_ir::Type::Record(_)
            | typed_ir::Type::Variant(_)
            | typed_ir::Type::Recursive { .. } => Ok(()),
        }
    }

    fn collect_runtime_effect(
        &mut self,
        template: &typed_ir::Type,
        actual: RuntimeEffectRef<'_>,
        side: BoundSide,
    ) -> FinalizeResult<()> {
        match actual {
            RuntimeEffectRef::Known(actual) => self.collect_core(template, actual, side),
            RuntimeEffectRef::Pure | RuntimeEffectRef::Unknown => Ok(()),
        }
    }

    fn propagate_constraints(&mut self) -> FinalizeResult<()> {
        loop {
            let mut changed = false;
            for constraint in self.constraints.clone() {
                changed |= self.apply_subtype_constraint(constraint.lower, constraint.upper)?;
            }
            if !changed {
                return Ok(());
            }
        }
    }

    fn apply_subtype_constraint(
        &mut self,
        lower: typed_ir::Type,
        upper: typed_ir::Type,
    ) -> FinalizeResult<bool> {
        if lower == upper || matches!(upper, typed_ir::Type::Any) {
            return Ok(false);
        }
        match (lower, upper) {
            (typed_ir::Type::Unknown, _) | (_, typed_ir::Type::Unknown) => Ok(false),
            (typed_ir::Type::Var(lower), upper) => {
                let mut changed = false;
                if let Some(bound) = self
                    .slots
                    .get(&lower)
                    .and_then(|slot| slot.lower.as_ref())
                    .cloned()
                {
                    changed |= self.apply_subtype_constraint(bound, upper.clone())?;
                }
                changed |= self.record(lower, upper, BoundSide::Upper)?;
                Ok(changed)
            }
            (lower, typed_ir::Type::Var(upper)) => {
                let mut changed = false;
                let lower = self.known_lower_or_self(lower);
                if let Some(bound) = self
                    .slots
                    .get(&upper)
                    .and_then(|slot| slot.upper.as_ref())
                    .cloned()
                {
                    changed |= self.apply_subtype_constraint(lower.clone(), bound)?;
                }
                changed |= self.record(upper, lower, BoundSide::Lower)?;
                Ok(changed)
            }
            (
                typed_ir::Type::Fun {
                    param: lower_param,
                    param_effect: lower_param_effect,
                    ret_effect: lower_ret_effect,
                    ret: lower_ret,
                },
                typed_ir::Type::Fun {
                    param: upper_param,
                    param_effect: upper_param_effect,
                    ret_effect: upper_ret_effect,
                    ret: upper_ret,
                },
            ) => {
                let mut changed = false;
                changed |= self.apply_subtype_constraint(*upper_param, *lower_param)?;
                changed |=
                    self.apply_subtype_constraint(*lower_param_effect, *upper_param_effect)?;
                changed |= self.apply_subtype_constraint(*lower_ret_effect, *upper_ret_effect)?;
                changed |= self.apply_subtype_constraint(*lower_ret, *upper_ret)?;
                Ok(changed)
            }
            (
                typed_ir::Type::Named {
                    path: lower_path,
                    args: lower_args,
                },
                typed_ir::Type::Named {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                let mut changed = false;
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    changed |= self.constrain_type_arg(lower, upper)?;
                }
                Ok(changed)
            }
            (typed_ir::Type::Tuple(lower), typed_ir::Type::Tuple(upper))
                if lower.len() == upper.len() =>
            {
                let mut changed = false;
                for (lower, upper) in lower.into_iter().zip(upper) {
                    changed |= self.apply_subtype_constraint(lower, upper)?;
                }
                Ok(changed)
            }
            (
                typed_ir::Type::Row {
                    items: lower_items,
                    tail: lower_tail,
                },
                typed_ir::Type::Row {
                    items: upper_items,
                    tail: upper_tail,
                },
            ) => self.constrain_row(lower_items, *lower_tail, upper_items, *upper_tail),
            _ => Ok(false),
        }
    }

    fn constrain_type_arg(
        &mut self,
        lower: typed_ir::TypeArg,
        upper: typed_ir::TypeArg,
    ) -> FinalizeResult<bool> {
        match (lower, upper) {
            (typed_ir::TypeArg::Type(lower), typed_ir::TypeArg::Type(upper)) => {
                self.apply_subtype_constraint(lower, upper)
            }
            (typed_ir::TypeArg::Bounds(lower), typed_ir::TypeArg::Bounds(upper)) => {
                let mut changed = false;
                if let (Some(lower), Some(upper)) = (lower.lower, upper.lower) {
                    changed |= self.apply_subtype_constraint(*lower, *upper)?;
                }
                if let (Some(lower), Some(upper)) = (lower.upper, upper.upper) {
                    changed |= self.apply_subtype_constraint(*lower, *upper)?;
                }
                Ok(changed)
            }
            _ => Ok(false),
        }
    }

    fn known_lower_or_self(&self, ty: typed_ir::Type) -> typed_ir::Type {
        let typed_ir::Type::Var(var) = &ty else {
            return ty;
        };
        self.slots
            .get(var)
            .and_then(|slot| slot.lower.as_ref())
            .cloned()
            .unwrap_or(ty)
    }

    fn known_upper_or_self(&self, ty: typed_ir::Type) -> typed_ir::Type {
        let typed_ir::Type::Var(var) = &ty else {
            return ty;
        };
        self.slots
            .get(var)
            .and_then(|slot| slot.upper.as_ref())
            .cloned()
            .unwrap_or(ty)
    }

    fn collect_type_arg(
        &mut self,
        template: &typed_ir::TypeArg,
        actual: &typed_ir::TypeArg,
        side: BoundSide,
    ) -> FinalizeResult<()> {
        match (template, actual) {
            (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
                self.collect_core(template, actual, side)
            }
            (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
                if let Some(lower) = actual.lower.as_deref() {
                    self.collect_core(template, lower, BoundSide::Lower)?;
                }
                if let Some(upper) = actual.upper.as_deref() {
                    self.collect_core(template, upper, BoundSide::Upper)?;
                }
                Ok(())
            }
            (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
                if let Some(lower) = template.lower.as_deref() {
                    self.collect_core(lower, actual, side)?;
                }
                if let Some(upper) = template.upper.as_deref() {
                    self.collect_core(upper, actual, BoundSide::Upper)?;
                }
                Ok(())
            }
            (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
                if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                    self.collect_core(template, actual, BoundSide::Lower)?;
                }
                if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                    self.collect_core(template, actual, BoundSide::Upper)?;
                }
                Ok(())
            }
        }
    }

    fn collect_row(
        &mut self,
        template_items: &[typed_ir::Type],
        template_tail: &typed_ir::Type,
        actual_items: &[typed_ir::Type],
        actual_tail: &typed_ir::Type,
        side: BoundSide,
    ) -> FinalizeResult<()> {
        let RowResidual {
            matched,
            unmatched_left,
            unmatched_right,
        } = split_row_items(template_items, actual_items);
        if matched.is_empty() && !template_items.is_empty() && !actual_items.is_empty() {
            return Ok(());
        }
        for (template, actual) in matched {
            self.collect_core(template, actual, side)?;
        }
        if !unmatched_left.is_empty() {
            return Ok(());
        }
        let residual = effect_row_from_items_and_tail(unmatched_right, actual_tail.clone());
        self.collect_core(template_tail, &residual, side)
    }

    fn constrain_row(
        &mut self,
        lower_items: Vec<typed_ir::Type>,
        lower_tail: typed_ir::Type,
        upper_items: Vec<typed_ir::Type>,
        upper_tail: typed_ir::Type,
    ) -> FinalizeResult<bool> {
        let RowResidual {
            matched,
            unmatched_left,
            unmatched_right,
        } = split_row_items(&lower_items, &upper_items);
        if matched.is_empty() && !lower_items.is_empty() && !upper_items.is_empty() {
            return Ok(false);
        }
        let mut changed = false;
        for (lower, upper) in matched {
            changed |= self.apply_subtype_constraint(lower.clone(), upper.clone())?;
        }
        let lower_residual = effect_row_from_items_and_tail(unmatched_left, lower_tail);
        let upper_residual = effect_row_from_items_and_tail(unmatched_right, upper_tail);
        changed |= self.apply_subtype_constraint(lower_residual, upper_residual)?;
        Ok(changed)
    }

    fn record(
        &mut self,
        var: typed_ir::TypeVar,
        mut ty: typed_ir::Type,
        side: BoundSide,
    ) -> FinalizeResult<bool> {
        ty = match side {
            BoundSide::Lower => self.known_lower_or_self(ty),
            BoundSide::Upper => self.known_upper_or_self(ty),
        };
        if matches!(ty, typed_ir::Type::Unknown) || is_vacuous_bound(&ty, side) {
            return Ok(false);
        }
        let slot = self.slots.entry(var.clone()).or_default();
        match side {
            BoundSide::Lower => slot.push_lower(var, ty),
            BoundSide::Upper => slot.push_upper(var, ty),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubtypeConstraint {
    lower: typed_ir::Type,
    upper: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalInstance {
    pub original_binding: typed_ir::Path,
    pub principal_type: typed_ir::Type,
    pub type_params: Vec<PrincipalTypeParam>,
}

impl PrincipalInstance {
    pub fn original_substitutions(
        &self,
        solution: &GraphSolution,
    ) -> Vec<typed_ir::TypeSubstitution> {
        self.type_params
            .iter()
            .filter_map(|param| {
                solution
                    .solution_for(&param.fresh)
                    .cloned()
                    .map(|ty| typed_ir::TypeSubstitution {
                        var: param.original.clone(),
                        ty,
                    })
            })
            .collect()
    }

    pub fn effect_only_type_params(&self) -> BTreeSet<typed_ir::TypeVar> {
        let params = self
            .type_params
            .iter()
            .map(|param| param.fresh.clone())
            .collect::<BTreeSet<_>>();
        let mut vars = TypePositionVars::default();
        collect_type_position_vars(
            &self.principal_type,
            TypePosition::Value,
            &params,
            &mut vars,
        );
        vars.effect
            .difference(&vars.value)
            .cloned()
            .collect::<BTreeSet<_>>()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalTypeParam {
    pub original: typed_ir::TypeVar,
    pub fresh: typed_ir::TypeVar,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RuntimeBounds {
    pub lower: Option<RuntimeType>,
    pub upper: Option<RuntimeType>,
}

impl RuntimeBounds {
    pub fn lower(ty: RuntimeType) -> Self {
        Self {
            lower: Some(ty),
            upper: None,
        }
    }

    pub fn upper(ty: RuntimeType) -> Self {
        Self {
            lower: None,
            upper: Some(ty),
        }
    }

    pub fn exact(ty: RuntimeType) -> Self {
        Self {
            lower: Some(ty.clone()),
            upper: Some(ty),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeVarBounds {
    pub lower: Option<typed_ir::Type>,
    pub upper: Option<typed_ir::Type>,
}

impl TypeVarBounds {
    pub fn solution(self) -> Option<typed_ir::Type> {
        self.lower.or(self.upper)
    }

    pub fn solution_ref(&self) -> Option<&typed_ir::Type> {
        self.lower.as_ref().or(self.upper.as_ref())
    }

    fn push_lower(&mut self, var: typed_ir::TypeVar, ty: typed_ir::Type) -> FinalizeResult<bool> {
        push_bound(&mut self.lower, var, ty)
    }

    fn push_upper(&mut self, var: typed_ir::TypeVar, ty: typed_ir::Type) -> FinalizeResult<bool> {
        push_bound(&mut self.upper, var, ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphSolution {
    pub type_vars: Vec<ResolvedTypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedTypeVar {
    pub var: typed_ir::TypeVar,
    pub bounds: TypeVarBounds,
    pub solution: Option<typed_ir::Type>,
}

impl GraphSolution {
    pub fn is_complete(&self) -> bool {
        self.type_vars.iter().all(|var| var.solution.is_some())
    }

    pub fn substitutions(&self) -> Vec<typed_ir::TypeSubstitution> {
        self.type_vars
            .iter()
            .filter_map(|var| {
                var.solution.clone().map(|ty| typed_ir::TypeSubstitution {
                    var: var.var.clone(),
                    ty,
                })
            })
            .collect()
    }

    pub fn solution_for(&self, var: &typed_ir::TypeVar) -> Option<&typed_ir::Type> {
        self.type_vars
            .iter()
            .find(|resolved| &resolved.var == var)
            .and_then(|resolved| resolved.solution.as_ref())
    }

    pub fn materialize_core(&self, ty: typed_ir::Type) -> typed_ir::Type {
        materialize_type(ty, &self.substitutions())
    }
}

pub fn materialize_core_type(
    ty: typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::Type {
    materialize_type(ty, substitutions)
}

pub fn materialize_runtime_type(
    ty: RuntimeType,
    substitutions: &[typed_ir::TypeSubstitution],
) -> RuntimeType {
    match ty {
        RuntimeType::Unknown => RuntimeType::Unknown,
        RuntimeType::Core(ty) => RuntimeType::Core(materialize_type(ty, substitutions)),
        RuntimeType::Fun { param, ret } => RuntimeType::Fun {
            param: Box::new(materialize_runtime_type(*param, substitutions)),
            ret: Box::new(materialize_runtime_type(*ret, substitutions)),
        },
        RuntimeType::Thunk { effect, value } => RuntimeType::Thunk {
            effect: materialize_type(effect, substitutions),
            value: Box::new(materialize_runtime_type(*value, substitutions)),
        },
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundSide {
    Lower,
    Upper,
}

struct RuntimeEffectedType<'a> {
    value: &'a RuntimeType,
    effect: RuntimeEffectRef<'a>,
}

#[derive(Clone, Copy)]
enum RuntimeEffectRef<'a> {
    Known(&'a typed_ir::Type),
    Pure,
    Unknown,
}

fn split_runtime_effected_type(ty: &RuntimeType) -> RuntimeEffectedType<'_> {
    match ty {
        RuntimeType::Thunk { effect, value } => RuntimeEffectedType {
            value,
            effect: RuntimeEffectRef::Known(effect),
        },
        RuntimeType::Unknown => RuntimeEffectedType {
            value: ty,
            effect: RuntimeEffectRef::Unknown,
        },
        RuntimeType::Core(_) | RuntimeType::Fun { .. } => RuntimeEffectedType {
            value: ty,
            effect: RuntimeEffectRef::Pure,
        },
    }
}

fn push_bound(
    slot: &mut Option<typed_ir::Type>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
) -> FinalizeResult<bool> {
    if let Some(previous) = slot {
        if bounds_are_equivalent(previous, &ty) {
            return Ok(false);
        }
        if matches!(
            (&*previous, &ty),
            (typed_ir::Type::Var(_), typed_ir::Type::Var(_))
        ) {
            return Ok(false);
        }
        if matches!(ty, typed_ir::Type::Var(_)) && !matches!(previous, typed_ir::Type::Var(_)) {
            return Ok(false);
        }
        if matches!(previous, typed_ir::Type::Var(_)) && !matches!(ty, typed_ir::Type::Var(_)) {
            *previous = ty;
            return Ok(true);
        }
        if type_contains_var(previous) || type_contains_var(&ty) {
            return Ok(false);
        }
        return Err(FinalizeDiagnostic::ConflictingBounds {
            var,
            previous: previous.clone(),
            next: ty,
        });
    }
    *slot = Some(ty);
    Ok(true)
}

fn type_contains_var(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Var(_) => true,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_contains_var(param)
                || type_contains_var(param_effect)
                || type_contains_var(ret_effect)
                || type_contains_var(ret)
        }
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_var),
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_contains_var),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_contains_var) || type_contains_var(tail)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_contains_var(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_contains_var(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_contains_var))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| type_contains_var(tail))
        }
        typed_ir::Type::Recursive { body, .. } => type_contains_var(body),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn type_arg_contains_var(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_contains_var(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_contains_var(ty))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_contains_var(ty))
        }
    }
}

fn bounds_are_equivalent(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    left == right
        || closed_singleton_row_item(left).is_some_and(|item| item == right)
        || closed_singleton_row_item(right).is_some_and(|item| item == left)
        || normalize_bound_form(left) == normalize_bound_form(right)
}

fn normalize_bound_form(ty: &typed_ir::Type) -> typed_ir::Type {
    normalize_bound_form_inner(ty, false)
}

fn normalize_bound_form_inner(ty: &typed_ir::Type, effect_atom: bool) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: if effect_atom && args.iter().any(type_arg_contains_unknown) {
                Vec::new()
            } else {
                args.iter()
                    .map(|arg| normalize_bound_arg_form(arg, effect_atom))
                    .collect()
            },
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(normalize_bound_form_inner(param, false)),
            param_effect: Box::new(normalize_bound_form_inner(param_effect, false)),
            ret_effect: Box::new(normalize_bound_form_inner(ret_effect, false)),
            ret: Box::new(normalize_bound_form_inner(ret, false)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| normalize_bound_form_inner(item, false))
                .collect(),
        ),
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| normalize_bound_form_inner(item, false))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| normalize_bound_form_inner(item, false))
                .collect(),
        ),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| normalize_bound_form_inner(item, true))
                .collect(),
            tail: Box::new(normalize_bound_form_inner(tail, false)),
        },
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: normalize_bound_form_inner(&field.value, false),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(normalize_bound_form_inner(ty, false)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(normalize_bound_form_inner(ty, false)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| normalize_bound_form_inner(payload, false))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(normalize_bound_form_inner(tail, false))),
        }),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(normalize_bound_form_inner(body, effect_atom)),
        },
        typed_ir::Type::Var(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => ty.clone(),
    }
}

fn normalize_bound_arg_form(arg: &typed_ir::TypeArg, effect_atom: bool) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(normalize_bound_form_inner(ty, effect_atom))
        }
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds
                .lower
                .as_deref()
                .filter(|lower| !matches!(lower, typed_ir::Type::Never))
            {
                return typed_ir::TypeArg::Type(normalize_bound_form_inner(lower, effect_atom));
            }
            if let Some(upper) = bounds
                .upper
                .as_deref()
                .filter(|upper| !matches!(upper, typed_ir::Type::Any))
            {
                return typed_ir::TypeArg::Type(normalize_bound_form_inner(upper, effect_atom));
            }
            typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: bounds
                    .lower
                    .as_ref()
                    .map(|lower| Box::new(normalize_bound_form_inner(lower, effect_atom))),
                upper: bounds
                    .upper
                    .as_ref()
                    .map(|upper| Box::new(normalize_bound_form_inner(upper, effect_atom))),
            })
        }
    }
}

fn type_arg_contains_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_contains_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_contains_unknown(ty))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_contains_unknown(ty))
        }
    }
}

fn type_contains_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_contains_unknown(param)
                || type_contains_unknown(param_effect)
                || type_contains_unknown(ret_effect)
                || type_contains_unknown(ret)
        }
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_unknown),
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_contains_unknown),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_contains_unknown) || type_contains_unknown(tail)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_contains_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_contains_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_contains_unknown))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| type_contains_unknown(tail))
        }
        typed_ir::Type::Recursive { body, .. } => type_contains_unknown(body),
        typed_ir::Type::Var(_) | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn closed_singleton_row_item(ty: &typed_ir::Type) -> Option<&typed_ir::Type> {
    let typed_ir::Type::Row { items, tail } = ty else {
        return None;
    };
    if items.len() == 1 && matches!(tail.as_ref(), typed_ir::Type::Never) {
        items.first()
    } else {
        None
    }
}

fn is_vacuous_bound(ty: &typed_ir::Type, side: BoundSide) -> bool {
    matches!(
        (side, ty),
        (BoundSide::Lower, typed_ir::Type::Never) | (BoundSide::Upper, typed_ir::Type::Any)
    )
}

struct RowResidual<'a> {
    matched: Vec<(&'a typed_ir::Type, &'a typed_ir::Type)>,
    unmatched_left: Vec<typed_ir::Type>,
    unmatched_right: Vec<typed_ir::Type>,
}

#[derive(Default)]
struct TypePositionVars {
    value: BTreeSet<typed_ir::TypeVar>,
    effect: BTreeSet<typed_ir::TypeVar>,
}

#[derive(Clone, Copy)]
enum TypePosition {
    Value,
    Effect,
}

fn collect_type_position_vars(
    ty: &typed_ir::Type,
    position: TypePosition,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match ty {
        typed_ir::Type::Var(var) if params.contains(var) => match position {
            TypePosition::Value => {
                vars.value.insert(var.clone());
            }
            TypePosition::Effect => {
                vars.effect.insert(var.clone());
            }
        },
        typed_ir::Type::Var(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => {}
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_position_vars(param, TypePosition::Value, params, vars);
            collect_type_position_vars(param_effect, TypePosition::Effect, params, vars);
            collect_type_position_vars(ret_effect, TypePosition::Effect, params, vars);
            collect_type_position_vars(ret, TypePosition::Value, params, vars);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_position_vars(arg, params, vars);
            }
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_type_position_vars(item, position, params, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_item_position_vars(item, params, vars);
            }
            collect_type_position_vars(tail, TypePosition::Effect, params, vars);
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_position_vars(&field.value, TypePosition::Value, params, vars);
            }
            if let Some(spread) = &record.spread {
                collect_record_spread_position_vars(spread, params, vars);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_position_vars(payload, TypePosition::Value, params, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_position_vars(tail, TypePosition::Value, params, vars);
            }
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_type_position_vars(body, position, params, vars);
        }
    }
}

fn collect_effect_item_position_vars(
    ty: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match ty {
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_position_vars(arg, params, vars);
            }
        }
        other => collect_type_position_vars(other, TypePosition::Effect, params, vars),
    }
}

fn collect_type_arg_position_vars(
    arg: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            collect_type_position_vars(ty, TypePosition::Value, params, vars);
        }
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_type_position_vars(lower, TypePosition::Value, params, vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_type_position_vars(upper, TypePosition::Value, params, vars);
            }
        }
    }
}

fn collect_record_spread_position_vars(
    spread: &typed_ir::RecordSpread,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match spread {
        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
            collect_type_position_vars(ty, TypePosition::Value, params, vars);
        }
    }
}

fn split_row_items<'a>(
    left_items: &'a [typed_ir::Type],
    right_items: &'a [typed_ir::Type],
) -> RowResidual<'a> {
    let mut matched_right = vec![false; right_items.len()];
    let mut matched = Vec::new();
    let mut unmatched_left = Vec::new();

    for left in left_items {
        let Some((index, right)) = right_items
            .iter()
            .enumerate()
            .find(|(index, right)| !matched_right[*index] && same_effect_head(left, right))
        else {
            unmatched_left.push(left.clone());
            continue;
        };
        matched_right[index] = true;
        matched.push((left, right));
    }

    let unmatched_right = right_items
        .iter()
        .enumerate()
        .filter_map(|(index, right)| (!matched_right[index]).then_some(right.clone()))
        .collect();

    RowResidual {
        matched,
        unmatched_left,
        unmatched_right,
    }
}

fn same_effect_head(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    match (left, right) {
        (
            typed_ir::Type::Named { path, .. },
            typed_ir::Type::Named {
                path: actual_path, ..
            },
        ) => effect_paths_match(path, actual_path),
        _ => false,
    }
}

fn effect_paths_match(left: &typed_ir::Path, right: &typed_ir::Path) -> bool {
    left == right
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

fn qualified_prefix_effect_paths_match(parent: &typed_ir::Path, child: &typed_ir::Path) -> bool {
    effect_path_can_match_child_prefix(parent)
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}

fn effect_path_can_match_child_prefix(path: &typed_ir::Path) -> bool {
    path.segments.len() > 1
        || path.segments.first().is_some_and(|name| {
            name.0.starts_with('#') || name.0.starts_with('&') && name.0.contains('#')
        })
}

fn effect_row_from_items_and_tail(
    items: Vec<typed_ir::Type>,
    tail: typed_ir::Type,
) -> typed_ir::Type {
    if items.is_empty() {
        return tail;
    }
    typed_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

fn rename_type(
    ty: &typed_ir::Type,
    renames: &BTreeMap<typed_ir::TypeVar, typed_ir::TypeVar>,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => renames
            .get(var)
            .cloned()
            .map(typed_ir::Type::Var)
            .unwrap_or_else(|| typed_ir::Type::Var(var.clone())),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(rename_type(param, renames)),
            param_effect: Box::new(rename_type(param_effect, renames)),
            ret_effect: Box::new(rename_type(ret_effect, renames)),
            ret: Box::new(rename_type(ret, renames)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
        ),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| rename_type_arg(arg, renames))
                .collect(),
        },
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
            tail: Box::new(rename_type(tail, renames)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: rename_type(&field.value, renames),
                    optional: field.optional,
                })
                .collect(),
            spread: record
                .spread
                .as_ref()
                .map(|spread| rename_record_spread(spread, renames)),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| rename_type(payload, renames))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(rename_type(tail, renames))),
        }),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: renames.get(var).cloned().unwrap_or_else(|| var.clone()),
            body: Box::new(rename_type(body, renames)),
        },
        typed_ir::Type::Unknown => typed_ir::Type::Unknown,
        typed_ir::Type::Never => typed_ir::Type::Never,
        typed_ir::Type::Any => typed_ir::Type::Any,
    }
}

fn rename_type_arg(
    arg: &typed_ir::TypeArg,
    renames: &BTreeMap<typed_ir::TypeVar, typed_ir::TypeVar>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(rename_type(ty, renames)),
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(rename_type(ty, renames))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(rename_type(ty, renames))),
        }),
    }
}

fn rename_record_spread(
    spread: &typed_ir::RecordSpread,
    renames: &BTreeMap<typed_ir::TypeVar, typed_ir::TypeVar>,
) -> typed_ir::RecordSpread {
    match spread {
        typed_ir::RecordSpread::Head(ty) => {
            typed_ir::RecordSpread::Head(Box::new(rename_type(ty, renames)))
        }
        typed_ir::RecordSpread::Tail(ty) => {
            typed_ir::RecordSpread::Tail(Box::new(rename_type(ty, renames)))
        }
    }
}

fn materialize_type(
    ty: typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => substitutions
            .iter()
            .find(|substitution| substitution.var == var)
            .map(|substitution| substitution.ty.clone())
            .unwrap_or(typed_ir::Type::Var(var)),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(materialize_type(*param, substitutions)),
            param_effect: Box::new(materialize_type(*param_effect, substitutions)),
            ret_effect: Box::new(materialize_type(*ret_effect, substitutions)),
            ret: Box::new(materialize_type(*ret, substitutions)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(|item| materialize_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(|arg| materialize_type_arg(arg, substitutions))
                .collect(),
        },
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .into_iter()
                .map(|item| materialize_type(item, substitutions))
                .collect(),
            tail: Box::new(materialize_type(*tail, substitutions)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .into_iter()
                .map(|item| materialize_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .into_iter()
                .map(|item| materialize_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: materialize_type(field.value, substitutions),
                    optional: field.optional,
                })
                .collect(),
            spread: record
                .spread
                .map(|spread| materialize_record_spread(spread, substitutions)),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name,
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(|payload| materialize_type(payload, substitutions))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(materialize_type(*tail, substitutions))),
        }),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(materialize_type(*body, substitutions)),
        },
        ty => ty,
    }
}

fn materialize_record_spread(
    spread: typed_ir::RecordSpread,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::RecordSpread {
    match spread {
        typed_ir::RecordSpread::Head(ty) => {
            typed_ir::RecordSpread::Head(Box::new(materialize_type(*ty, substitutions)))
        }
        typed_ir::RecordSpread::Tail(ty) => {
            typed_ir::RecordSpread::Tail(Box::new(materialize_type(*ty, substitutions)))
        }
    }
}

fn materialize_type_arg(
    arg: typed_ir::TypeArg,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(materialize_type(ty, substitutions)),
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .map(|ty| Box::new(materialize_type(*ty, substitutions))),
            upper: bounds
                .upper
                .map(|ty| Box::new(materialize_type(*ty, substitutions))),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_runtime_ir::{Expr, ExprKind};

    #[test]
    fn principal_type_is_freshened_into_graph() {
        let mut graph = TypeGraph::default();
        let instance = graph.instantiate_principal(&id_binding());

        assert_eq!(instance.original_binding, path(&["id"]));
        assert!(matches!(
            instance.principal_type,
            typed_ir::Type::Fun { .. }
        ));
        assert_eq!(
            instance.type_params,
            vec![PrincipalTypeParam {
                original: typed_ir::TypeVar("a".into()),
                fresh: typed_ir::TypeVar("a#0".into()),
            }]
        );
        assert!(graph.slot(&typed_ir::TypeVar("a#0".into())).is_some());
    }

    #[test]
    fn graph_solves_fresh_principal_var_from_lower_bound() {
        let mut graph = TypeGraph::default();
        let instance = graph.instantiate_principal(&id_binding());
        let typed_ir::Type::Fun { param, ret, .. } = &instance.principal_type else {
            panic!("expected function principal");
        };

        graph
            .collect_runtime_lower(param, &RuntimeType::Core(int_type()))
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.materialize_core(ret.as_ref().clone()), int_type());
        assert_eq!(
            instance.original_substitutions(&solution),
            vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }]
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn lower_solution_wins_over_upper_solution() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(int_type())),
                    upper: Some(RuntimeType::Core(number_type())),
                },
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(
            solution.substitutions(),
            vec![typed_ir::TypeSubstitution {
                var,
                ty: int_type(),
            }]
        );
    }

    #[test]
    fn top_and_bottom_are_extremes_not_holes() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(any_type())),
                    upper: Some(RuntimeType::Core(never_type())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&any_type())
        );
    }

    #[test]
    fn bottom_lower_and_top_upper_are_vacuous_bounds() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(never_type())),
                    upper: Some(RuntimeType::Core(any_type())),
                },
            )
            .unwrap();

        assert_eq!(graph.slot(&var).and_then(TypeVarBounds::solution_ref), None);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(int_type())),
                    upper: Some(RuntimeType::Core(any_type())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&int_type())
        );
    }

    #[test]
    fn symbolic_bounds_do_not_conflict_before_concrete_bounds_arrive() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());
        let first = typed_ir::Type::Var(typed_ir::TypeVar("b".into()));
        let second = typed_ir::Type::Var(typed_ir::TypeVar("c".into()));

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(first.clone())),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(second)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&first)
        );
    }

    #[test]
    fn graph_solution_keeps_lower_and_upper_after_solving() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Core(int_type())),
                    upper: Some(RuntimeType::Core(number_type())),
                },
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(
            solution.type_vars,
            vec![ResolvedTypeVar {
                var,
                bounds: TypeVarBounds {
                    lower: Some(int_type()),
                    upper: Some(number_type()),
                },
                solution: Some(int_type()),
            }]
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn subtype_constraints_solve_curried_first_application() {
        let mut graph = TypeGraph::default();
        let a_var = typed_ir::TypeVar("a".into());
        let b_var = typed_ir::TypeVar("b".into());
        let a = typed_ir::Type::Var(a_var.clone());
        let b = typed_ir::Type::Var(b_var.clone());
        graph.slots.entry(a_var.clone()).or_default();
        graph.slots.entry(b_var.clone()).or_default();
        let r0 = graph.fresh_hole("apply");
        let r1 = graph.fresh_hole("apply");

        graph
            .constrain_subtype(
                fun_type(a.clone(), fun_type(b.clone(), a.clone())),
                fun_type(int_type(), r0.clone()),
            )
            .unwrap();
        graph
            .constrain_subtype(r0, fun_type(bool_type(), r1.clone()))
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&a_var), Some(&int_type()));
        assert_eq!(solution.solution_for(&b_var), Some(&bool_type()));
        assert_eq!(solution.materialize_core(r1), int_type());
        assert!(solution.is_complete());
    }

    #[test]
    fn subtype_constraints_propagate_after_later_bounds_arrive() {
        let mut graph = TypeGraph::default();
        let a_var = typed_ir::TypeVar("a".into());
        let b_var = typed_ir::TypeVar("b".into());
        graph.slots.entry(a_var.clone()).or_default();
        graph.slots.entry(b_var.clone()).or_default();

        graph
            .constrain_subtype(
                typed_ir::Type::Var(a_var.clone()),
                typed_ir::Type::Var(b_var.clone()),
            )
            .unwrap();
        graph
            .collect_runtime_lower(
                &typed_ir::Type::Var(a_var.clone()),
                &RuntimeType::Core(int_type()),
            )
            .unwrap();

        let solution = graph.solve();

        assert_eq!(solution.solution_for(&a_var), Some(&int_type()));
        assert_eq!(solution.solution_for(&b_var), Some(&int_type()));
    }

    #[test]
    fn runtime_function_thunks_feed_function_effect_slots() {
        let mut graph = TypeGraph::default();
        let a_var = typed_ir::TypeVar("a".into());
        let b_var = typed_ir::TypeVar("b".into());
        let param_effect_var = typed_ir::TypeVar("pe".into());
        let ret_effect_var = typed_ir::TypeVar("re".into());
        let template = fun_type_with_effects(
            typed_ir::Type::Var(a_var.clone()),
            typed_ir::Type::Var(param_effect_var.clone()),
            typed_ir::Type::Var(ret_effect_var.clone()),
            typed_ir::Type::Var(b_var.clone()),
        );

        graph
            .collect_runtime_bounds(
                &template,
                &RuntimeBounds::exact(RuntimeType::Fun {
                    param: Box::new(RuntimeType::Thunk {
                        effect: effect_type("arg"),
                        value: Box::new(RuntimeType::Core(int_type())),
                    }),
                    ret: Box::new(RuntimeType::Thunk {
                        effect: effect_type("ret"),
                        value: Box::new(RuntimeType::Core(bool_type())),
                    }),
                }),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&a_var), Some(&int_type()));
        assert_eq!(solution.solution_for(&b_var), Some(&bool_type()));
        assert_eq!(
            solution.solution_for(&param_effect_var),
            Some(&effect_type("arg"))
        );
        assert_eq!(
            solution.solution_for(&ret_effect_var),
            Some(&effect_type("ret"))
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn singleton_closed_effect_row_bound_matches_its_atom() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let atom = effect_type("io");
        let row = typed_ir::Type::Row {
            items: vec![atom.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Core(row.clone())),
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Core(atom)),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&row)
        );
    }

    #[test]
    fn graph_solution_reports_open_type_vars() {
        let mut graph = TypeGraph::default();
        graph.instantiate_principal(&id_binding());
        let solution = graph.solve();

        assert!(!solution.is_complete());
    }

    fn id_binding() -> Binding {
        Binding {
            name: path(&["id"]),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        }
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["Int"]),
            args: Vec::new(),
        }
    }

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["Bool"]),
            args: Vec::new(),
        }
    }

    fn any_type() -> typed_ir::Type {
        typed_ir::Type::Any
    }

    fn number_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["Number"]),
            args: Vec::new(),
        }
    }

    fn never_type() -> typed_ir::Type {
        typed_ir::Type::Never
    }

    fn fun_type(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        fun_type_with_effects(param, typed_ir::Type::Never, typed_ir::Type::Never, ret)
    }

    fn fun_type_with_effects(
        param: typed_ir::Type,
        param_effect: typed_ir::Type,
        ret_effect: typed_ir::Type,
        ret: typed_ir::Type,
    ) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(param_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        }
    }

    fn effect_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&[name]),
            args: Vec::new(),
        }
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
