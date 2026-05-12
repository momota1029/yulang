use super::*;

/// Classifies the special core types that used to be conflated in runtime code.
///
/// `Any` is a real top type. It is not an unknown type.
///
/// `Unknown` is an internal evidence/projection hole. It must not be accepted
/// as a completed principal substitution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CoreTypeMeaning {
    Unknown,
    Top,
    InferenceVar,
    Other,
}

pub(crate) fn core_type_meaning(ty: &typed_ir::Type) -> CoreTypeMeaning {
    match ty {
        typed_ir::Type::Unknown => CoreTypeMeaning::Unknown,
        typed_ir::Type::Any => CoreTypeMeaning::Top,
        typed_ir::Type::Var(_) => CoreTypeMeaning::InferenceVar,
        _ => CoreTypeMeaning::Other,
    }
}

pub(crate) fn core_type_is_inference_hole(ty: &typed_ir::Type) -> bool {
    matches!(
        core_type_meaning(ty),
        CoreTypeMeaning::Unknown | CoreTypeMeaning::InferenceVar
    )
}

pub(crate) fn runtime_type_is_inference_hole(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Unknown | RuntimeType::Core(typed_ir::Type::Unknown | typed_ir::Type::Var(_))
    )
}

pub(crate) fn core_type_is_imprecise_runtime_slot(ty: &typed_ir::Type) -> bool {
    matches!(
        core_type_meaning(ty),
        CoreTypeMeaning::Unknown | CoreTypeMeaning::Top | CoreTypeMeaning::InferenceVar
    )
}

pub(crate) fn runtime_type_is_imprecise_runtime_slot(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Unknown
            | RuntimeType::Core(
                typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
            )
    )
}

pub(crate) fn core_type_is_runtime_projection_fallback(ty: &typed_ir::Type) -> bool {
    matches!(core_type_meaning(ty), CoreTypeMeaning::Unknown)
}

pub(crate) fn wildcard_effect_type() -> typed_ir::Type {
    typed_ir::Type::Any
}

pub(crate) fn runtime_projection_fallback_type() -> typed_ir::Type {
    typed_ir::Type::Unknown
}

pub(crate) fn runtime_type_contains_unknown(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_contains_unknown(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_contains_unknown(param) || runtime_type_contains_unknown(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_contains_unknown(effect) || runtime_type_contains_unknown(value)
        }
    }
}

pub(crate) fn core_type_contains_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_unknown),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_unknown(param)
                || core_type_contains_unknown(param_effect)
                || core_type_contains_unknown(ret_effect)
                || core_type_contains_unknown(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_unknown),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_unknown))
                || variant
                    .tail
                    .as_deref()
                    .is_some_and(core_type_contains_unknown)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_unknown) || core_type_contains_unknown(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_contains_unknown(body),
    }
}

fn type_arg_contains_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_contains_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .is_some_and(core_type_contains_unknown)
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(core_type_contains_unknown)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inference_holes_are_unknown_or_type_vars() {
        assert!(core_type_is_inference_hole(&typed_ir::Type::Unknown));
        assert!(!core_type_is_inference_hole(&typed_ir::Type::Any));
        assert!(core_type_is_inference_hole(&typed_ir::Type::Var(
            typed_ir::TypeVar("a".to_string())
        )));
        assert!(!core_type_is_inference_hole(&typed_ir::Type::Never));
    }

    #[test]
    fn imprecise_runtime_slots_include_top_and_vars() {
        assert!(runtime_type_is_imprecise_runtime_slot(
            &RuntimeType::Unknown
        ));
        assert!(core_type_is_imprecise_runtime_slot(&typed_ir::Type::Any));
        assert!(core_type_is_imprecise_runtime_slot(&typed_ir::Type::Var(
            typed_ir::TypeVar("a".to_string())
        )));
        assert!(!core_type_is_imprecise_runtime_slot(&typed_ir::Type::Never));
    }

    #[test]
    fn runtime_projection_fallback_is_unknown() {
        assert!(core_type_is_runtime_projection_fallback(
            &runtime_projection_fallback_type()
        ));
        assert!(!core_type_is_runtime_projection_fallback(
            &typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()))
        ));
    }

    #[test]
    fn wildcard_effect_still_uses_any_representation() {
        assert_eq!(wildcard_effect_type(), typed_ir::Type::Any);
    }
}
