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

pub(crate) fn core_type_meaning(ty: &core_ir::Type) -> CoreTypeMeaning {
    match ty {
        core_ir::Type::Unknown => CoreTypeMeaning::Unknown,
        core_ir::Type::Any => CoreTypeMeaning::Top,
        core_ir::Type::Var(_) => CoreTypeMeaning::InferenceVar,
        _ => CoreTypeMeaning::Other,
    }
}

pub(crate) fn core_type_is_inference_hole(ty: &core_ir::Type) -> bool {
    matches!(
        core_type_meaning(ty),
        CoreTypeMeaning::Unknown | CoreTypeMeaning::InferenceVar
    )
}

pub(crate) fn runtime_type_is_inference_hole(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Unknown | RuntimeType::Core(core_ir::Type::Unknown | core_ir::Type::Var(_))
    )
}

pub(crate) fn core_type_is_imprecise_runtime_slot(ty: &core_ir::Type) -> bool {
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
                core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_)
            )
    )
}

pub(crate) fn core_type_is_runtime_projection_fallback(ty: &core_ir::Type) -> bool {
    matches!(core_type_meaning(ty), CoreTypeMeaning::Unknown)
}

pub(crate) fn wildcard_effect_type() -> core_ir::Type {
    core_ir::Type::Any
}

pub(crate) fn runtime_projection_fallback_type() -> core_ir::Type {
    core_ir::Type::Unknown
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

pub(crate) fn core_type_contains_unknown(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Unknown => true,
        core_ir::Type::Never | core_ir::Type::Any | core_ir::Type::Var(_) => false,
        core_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_unknown),
        core_ir::Type::Fun {
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
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(core_type_contains_unknown)
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_unknown(ty)
                    }
                })
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_unknown))
                || variant
                    .tail
                    .as_deref()
                    .is_some_and(core_type_contains_unknown)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_unknown) || core_type_contains_unknown(tail)
        }
        core_ir::Type::Recursive { body, .. } => core_type_contains_unknown(body),
    }
}

fn type_arg_contains_unknown(arg: &core_ir::TypeArg) -> bool {
    match arg {
        core_ir::TypeArg::Type(ty) => core_type_contains_unknown(ty),
        core_ir::TypeArg::Bounds(bounds) => {
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
        assert!(core_type_is_inference_hole(&core_ir::Type::Unknown));
        assert!(!core_type_is_inference_hole(&core_ir::Type::Any));
        assert!(core_type_is_inference_hole(&core_ir::Type::Var(
            core_ir::TypeVar("a".to_string())
        )));
        assert!(!core_type_is_inference_hole(&core_ir::Type::Never));
    }

    #[test]
    fn imprecise_runtime_slots_include_top_and_vars() {
        assert!(runtime_type_is_imprecise_runtime_slot(
            &RuntimeType::Unknown
        ));
        assert!(core_type_is_imprecise_runtime_slot(&core_ir::Type::Any));
        assert!(core_type_is_imprecise_runtime_slot(&core_ir::Type::Var(
            core_ir::TypeVar("a".to_string())
        )));
        assert!(!core_type_is_imprecise_runtime_slot(&core_ir::Type::Never));
    }

    #[test]
    fn runtime_projection_fallback_is_unknown() {
        assert!(core_type_is_runtime_projection_fallback(
            &runtime_projection_fallback_type()
        ));
        assert!(!core_type_is_runtime_projection_fallback(
            &core_ir::Type::Var(core_ir::TypeVar("a".to_string()))
        ));
    }

    #[test]
    fn wildcard_effect_still_uses_any_representation() {
        assert_eq!(wildcard_effect_type(), core_ir::Type::Any);
    }
}
