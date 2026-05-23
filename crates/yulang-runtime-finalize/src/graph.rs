use std::collections::BTreeMap;

use yulang_runtime_ir::{Binding, Type as RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{FinalizeDiagnostic, FinalizeResult};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeGraph {
    next_fresh: usize,
    slots: BTreeMap<typed_ir::TypeVar, TypeVarBounds>,
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
        Ok(())
    }

    pub fn collect_runtime_lower(
        &mut self,
        template: &typed_ir::Type,
        lower: &RuntimeType,
    ) -> FinalizeResult<()> {
        self.collect_runtime(template, lower, BoundSide::Lower)
    }

    pub fn collect_runtime_upper(
        &mut self,
        template: &typed_ir::Type,
        upper: &RuntimeType,
    ) -> FinalizeResult<()> {
        self.collect_runtime(template, upper, BoundSide::Upper)
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
        self.constrain_core(lower, upper)
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
                    ret: template_ret,
                    ..
                } = template
                else {
                    return Ok(());
                };
                self.collect_runtime(template_param, param, side)?;
                self.collect_runtime(template_ret, ret, side)
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
            typed_ir::Type::Var(var) => self.record(var.clone(), actual.clone(), side),
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
            typed_ir::Type::Fun { param, ret, .. } => {
                let typed_ir::Type::Fun {
                    param: actual_param,
                    ret: actual_ret,
                    ..
                } = actual
                else {
                    return Ok(());
                };
                self.collect_core(param, actual_param, side)?;
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
                if items.len() != actual_items.len() {
                    return Ok(());
                }
                for (template, actual) in items.iter().zip(actual_items) {
                    self.collect_core(template, actual, side)?;
                }
                self.collect_core(tail, actual_tail, side)
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

    fn constrain_core(
        &mut self,
        lower: typed_ir::Type,
        upper: typed_ir::Type,
    ) -> FinalizeResult<()> {
        if lower == upper
            || matches!(lower, typed_ir::Type::Never)
            || matches!(upper, typed_ir::Type::Any)
        {
            return Ok(());
        }
        match (lower, upper) {
            (typed_ir::Type::Unknown, _) | (_, typed_ir::Type::Unknown) => Ok(()),
            (typed_ir::Type::Var(lower), upper) => {
                if let Some(bound) = self
                    .slots
                    .get(&lower)
                    .and_then(|slot| slot.lower.as_ref())
                    .cloned()
                {
                    self.constrain_core(bound, upper.clone())?;
                }
                self.record(lower, upper, BoundSide::Upper)
            }
            (lower, typed_ir::Type::Var(upper)) => {
                let lower = self.known_lower_or_self(lower);
                if let Some(bound) = self
                    .slots
                    .get(&upper)
                    .and_then(|slot| slot.upper.as_ref())
                    .cloned()
                {
                    self.constrain_core(lower.clone(), bound)?;
                }
                self.record(upper, lower, BoundSide::Lower)
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
                self.constrain_core(*upper_param, *lower_param)?;
                self.constrain_core(*lower_param_effect, *upper_param_effect)?;
                self.constrain_core(*lower_ret_effect, *upper_ret_effect)?;
                self.constrain_core(*lower_ret, *upper_ret)
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
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    self.constrain_type_arg(lower, upper)?;
                }
                Ok(())
            }
            (typed_ir::Type::Tuple(lower), typed_ir::Type::Tuple(upper))
                if lower.len() == upper.len() =>
            {
                for (lower, upper) in lower.into_iter().zip(upper) {
                    self.constrain_core(lower, upper)?;
                }
                Ok(())
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
            ) if lower_items.len() == upper_items.len() => {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_core(lower, upper)?;
                }
                self.constrain_core(*lower_tail, *upper_tail)
            }
            _ => Ok(()),
        }
    }

    fn constrain_type_arg(
        &mut self,
        lower: typed_ir::TypeArg,
        upper: typed_ir::TypeArg,
    ) -> FinalizeResult<()> {
        match (lower, upper) {
            (typed_ir::TypeArg::Type(lower), typed_ir::TypeArg::Type(upper)) => {
                self.constrain_core(lower, upper)
            }
            (typed_ir::TypeArg::Bounds(lower), typed_ir::TypeArg::Bounds(upper)) => {
                if let (Some(lower), Some(upper)) = (lower.lower, upper.lower) {
                    self.constrain_core(*lower, *upper)?;
                }
                if let (Some(lower), Some(upper)) = (lower.upper, upper.upper) {
                    self.constrain_core(*lower, *upper)?;
                }
                Ok(())
            }
            _ => Ok(()),
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

    fn record(
        &mut self,
        var: typed_ir::TypeVar,
        ty: typed_ir::Type,
        side: BoundSide,
    ) -> FinalizeResult<()> {
        if matches!(ty, typed_ir::Type::Unknown) || is_vacuous_bound(&ty, side) {
            return Ok(());
        }
        let slot = self.slots.entry(var.clone()).or_default();
        match side {
            BoundSide::Lower => slot.push_lower(var, ty),
            BoundSide::Upper => slot.push_upper(var, ty),
        }
    }
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

    fn push_lower(&mut self, var: typed_ir::TypeVar, ty: typed_ir::Type) -> FinalizeResult<()> {
        push_bound(&mut self.lower, var, ty)
    }

    fn push_upper(&mut self, var: typed_ir::TypeVar, ty: typed_ir::Type) -> FinalizeResult<()> {
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

fn push_bound(
    slot: &mut Option<typed_ir::Type>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
) -> FinalizeResult<()> {
    if let Some(previous) = slot {
        if previous == &ty {
            return Ok(());
        }
        return Err(FinalizeDiagnostic::ConflictingBounds {
            var,
            previous: previous.clone(),
            next: ty,
        });
    }
    *slot = Some(ty);
    Ok(())
}

fn is_vacuous_bound(ty: &typed_ir::Type, side: BoundSide) -> bool {
    matches!(
        (side, ty),
        (BoundSide::Lower, typed_ir::Type::Never) | (BoundSide::Upper, typed_ir::Type::Any)
    )
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
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
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
