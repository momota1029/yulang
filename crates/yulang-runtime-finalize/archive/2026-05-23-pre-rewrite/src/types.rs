use std::collections::BTreeMap;

use yulang_runtime_ir::Type as RuntimeType;
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{FinalizeDiagnostic, FinalizeError, FinalizeResult};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct LowerSubstitutions {
    by_var: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
}

impl LowerSubstitutions {
    pub(crate) fn insert(
        &mut self,
        var: typed_ir::TypeVar,
        ty: typed_ir::Type,
    ) -> FinalizeResult<()> {
        if let Some(previous) = self.by_var.get(&var) {
            if previous == &ty {
                return Ok(());
            }
            return Err(FinalizeError::Diagnostic(
                FinalizeDiagnostic::ConflictingLower {
                    var,
                    previous: previous.clone(),
                    next: ty,
                },
            ));
        }
        self.by_var.insert(var, ty);
        Ok(())
    }

    pub(crate) fn get(&self, var: &typed_ir::TypeVar) -> Option<&typed_ir::Type> {
        self.by_var.get(var)
    }

    pub(crate) fn from_type_substitutions(
        substitutions: &[typed_ir::TypeSubstitution],
    ) -> FinalizeResult<Self> {
        let mut lower = Self::default();
        for substitution in substitutions {
            lower.insert(substitution.var.clone(), substitution.ty.clone())?;
        }
        Ok(lower)
    }

    pub(crate) fn into_vec(self) -> Vec<typed_ir::TypeSubstitution> {
        self.by_var
            .into_iter()
            .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
            .collect()
    }
}

pub(crate) fn unify_runtime_with_core(
    substitutions: &mut LowerSubstitutions,
    expected: &typed_ir::Type,
    actual: &RuntimeType,
) -> FinalizeResult<()> {
    match (expected, actual) {
        (typed_ir::Type::Var(var), RuntimeType::Core(actual)) => {
            substitutions.insert(var.clone(), actual.clone())
        }
        (expected, RuntimeType::Core(actual)) => unify_core_types(substitutions, expected, actual),
        (
            typed_ir::Type::Fun {
                param,
                param_effect: _,
                ret_effect,
                ret,
            },
            RuntimeType::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => {
            unify_runtime_with_core(substitutions, param, actual_param)?;
            unify_runtime_with_core(substitutions, ret, actual_ret)?;
            collect_core_type_lowers(substitutions, ret_effect, &typed_ir::Type::Never)
        }
        (
            typed_ir::Type::Fun {
                param: _,
                param_effect: _,
                ret_effect,
                ret,
            },
            RuntimeType::Thunk {
                effect,
                value: actual_value,
            },
        ) => {
            collect_core_type_lowers(substitutions, ret_effect, effect)?;
            unify_runtime_with_core(substitutions, ret, actual_value)
        }
        _ => Err(FinalizeError::Diagnostic(
            FinalizeDiagnostic::ShapeMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            },
        )),
    }
}

pub(crate) fn unify_core_types(
    substitutions: &mut LowerSubstitutions,
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> FinalizeResult<()> {
    match (expected, actual) {
        (typed_ir::Type::Var(var), actual) => substitutions.insert(var.clone(), actual.clone()),
        (typed_ir::Type::Tuple(expected), typed_ir::Type::Tuple(actual))
            if expected.len() == actual.len() =>
        {
            for (expected, actual) in expected.iter().zip(actual) {
                unify_core_types(substitutions, expected, actual)?;
            }
            Ok(())
        }
        (
            typed_ir::Type::Fun {
                param: expected_param,
                param_effect: expected_param_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => {
            unify_core_types(substitutions, expected_param, actual_param)?;
            unify_core_types(substitutions, expected_param_effect, actual_param_effect)?;
            unify_core_types(substitutions, expected_ret_effect, actual_ret_effect)?;
            unify_core_types(substitutions, expected_ret, actual_ret)
        }
        (
            typed_ir::Type::Named {
                path: expected_path,
                args: expected_args,
            },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if expected_path == actual_path && expected_args.len() == actual_args.len() => {
            for (expected, actual) in expected_args.iter().zip(actual_args) {
                unify_type_arg(substitutions, expected, actual)?;
            }
            Ok(())
        }
        (expected, actual) if expected == actual => Ok(()),
        (expected, actual) => Err(FinalizeError::Diagnostic(
            FinalizeDiagnostic::ShapeMismatch {
                expected: expected.clone(),
                actual: RuntimeType::Core(actual.clone()),
            },
        )),
    }
}

pub(crate) fn materialize_runtime_type(
    ty: RuntimeType,
    substitutions: &LowerSubstitutions,
) -> RuntimeType {
    match ty {
        RuntimeType::Unknown => RuntimeType::Unknown,
        RuntimeType::Core(ty) => RuntimeType::Core(materialize_core_type(ty, substitutions)),
        RuntimeType::Fun { param, ret } => RuntimeType::Fun {
            param: Box::new(materialize_runtime_type(*param, substitutions)),
            ret: Box::new(materialize_runtime_type(*ret, substitutions)),
        },
        RuntimeType::Thunk { effect, value } => RuntimeType::Thunk {
            effect: materialize_core_type(effect, substitutions),
            value: Box::new(materialize_runtime_type(*value, substitutions)),
        },
    }
}

pub(crate) fn materialize_expr_type(
    ty: RuntimeType,
    substitutions: &LowerSubstitutions,
) -> RuntimeType {
    materialize_runtime_type(ty, substitutions)
}

pub(crate) fn materialize_core_type(
    ty: typed_ir::Type,
    substitutions: &LowerSubstitutions,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => substitutions
            .get(&var)
            .cloned()
            .unwrap_or(typed_ir::Type::Var(var)),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(materialize_core_type(*param, substitutions)),
            param_effect: Box::new(materialize_core_type(*param_effect, substitutions)),
            ret_effect: Box::new(materialize_core_type(*ret_effect, substitutions)),
            ret: Box::new(materialize_core_type(*ret, substitutions)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(|item| materialize_core_type(item, substitutions))
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
                .map(|item| materialize_core_type(item, substitutions))
                .collect(),
            tail: Box::new(materialize_core_type(*tail, substitutions)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .into_iter()
                .map(|item| materialize_core_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .into_iter()
                .map(|item| materialize_core_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: materialize_core_type(field.value, substitutions),
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
                        .map(|payload| materialize_core_type(payload, substitutions))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(materialize_core_type(*tail, substitutions))),
        }),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(materialize_core_type(*body, substitutions)),
        },
        typed_ir::Type::Unknown => typed_ir::Type::Unknown,
        typed_ir::Type::Never => typed_ir::Type::Never,
        typed_ir::Type::Any => typed_ir::Type::Any,
    }
}

pub(crate) fn runtime_type_is_closed(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Core(ty) => core_type_is_closed(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_is_closed(param) && runtime_type_is_closed(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_is_closed(effect) && runtime_type_is_closed(value)
        }
    }
}

pub(crate) fn runtime_types_match(left: &RuntimeType, right: &RuntimeType) -> bool {
    left == right
}

pub(crate) fn path_as_local_name(path: &typed_ir::Path) -> Option<&typed_ir::Name> {
    match path.segments.as_slice() {
        [name] => Some(name),
        _ => None,
    }
}

fn unify_type_arg(
    substitutions: &mut LowerSubstitutions,
    expected: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
) -> FinalizeResult<()> {
    match (expected, actual) {
        (typed_ir::TypeArg::Type(expected), typed_ir::TypeArg::Type(actual)) => {
            unify_core_types(substitutions, expected, actual)
        }
        (typed_ir::TypeArg::Bounds(expected), typed_ir::TypeArg::Bounds(actual)) => {
            if let (Some(expected_lower), Some(actual_lower)) = (&expected.lower, &actual.lower) {
                unify_core_types(substitutions, expected_lower, actual_lower)?;
            }
            if let (Some(expected_upper), Some(actual_upper)) = (&expected.upper, &actual.upper) {
                unify_core_types(substitutions, expected_upper, actual_upper)?;
            }
            Ok(())
        }
        _ => Err(FinalizeError::Diagnostic(
            FinalizeDiagnostic::ShapeMismatch {
                expected: typed_ir::Type::Unknown,
                actual: RuntimeType::Core(typed_ir::Type::Unknown),
            },
        )),
    }
}

fn collect_core_type_lowers(
    substitutions: &mut LowerSubstitutions,
    expected: &typed_ir::Type,
    actual: &typed_ir::Type,
) -> FinalizeResult<()> {
    unify_core_types(substitutions, expected, actual)
}

fn materialize_type_arg(
    arg: typed_ir::TypeArg,
    substitutions: &LowerSubstitutions,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(materialize_core_type(ty, substitutions))
        }
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .map(|ty| Box::new(materialize_core_type(*ty, substitutions))),
            upper: bounds
                .upper
                .map(|ty| Box::new(materialize_core_type(*ty, substitutions))),
        }),
    }
}

fn materialize_record_spread(
    spread: typed_ir::RecordSpread,
    substitutions: &LowerSubstitutions,
) -> typed_ir::RecordSpread {
    match spread {
        typed_ir::RecordSpread::Head(ty) => {
            typed_ir::RecordSpread::Head(Box::new(materialize_core_type(*ty, substitutions)))
        }
        typed_ir::RecordSpread::Tail(ty) => {
            typed_ir::RecordSpread::Tail(Box::new(materialize_core_type(*ty, substitutions)))
        }
    }
}

fn core_type_is_closed(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Never | typed_ir::Type::Any => true,
        typed_ir::Type::Named { args, .. } => args.iter().all(type_arg_is_closed),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_is_closed(param)
                && core_type_is_closed(param_effect)
                && core_type_is_closed(ret_effect)
                && core_type_is_closed(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().all(core_type_is_closed),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| core_type_is_closed(&field.value))
                && record.spread.as_ref().is_none_or(record_spread_is_closed)
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(core_type_is_closed))
                && variant
                    .tail
                    .as_ref()
                    .is_none_or(|tail| core_type_is_closed(tail))
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(core_type_is_closed) && core_type_is_closed(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_is_closed(body),
    }
}

fn type_arg_is_closed(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_is_closed(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_none_or(|ty| core_type_is_closed(ty))
                && bounds
                    .upper
                    .as_ref()
                    .is_none_or(|ty| core_type_is_closed(ty))
        }
    }
}

fn record_spread_is_closed(spread: &typed_ir::RecordSpread) -> bool {
    match spread {
        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
            core_type_is_closed(ty)
        }
    }
}
