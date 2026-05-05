use super::*;

/// Classifies the special core types that used to be conflated in runtime code.
///
/// `Any` is a real top type.  It is not an unknown type.  Some runtime
/// projections still use `Any` as an erased fallback because core IR has no
/// separate unknown marker yet; those sites should opt into the fallback helpers
/// below instead of calling it an inference hole.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CoreTypeMeaning {
    Top,
    InferenceVar,
    Other,
}

pub(crate) fn core_type_meaning(ty: &core_ir::Type) -> CoreTypeMeaning {
    match ty {
        core_ir::Type::Any => CoreTypeMeaning::Top,
        core_ir::Type::Var(_) => CoreTypeMeaning::InferenceVar,
        _ => CoreTypeMeaning::Other,
    }
}

pub(crate) fn core_type_is_inference_hole(ty: &core_ir::Type) -> bool {
    matches!(core_type_meaning(ty), CoreTypeMeaning::InferenceVar)
}

pub(crate) fn runtime_type_is_inference_hole(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Core(core_ir::Type::Var(_)))
}

pub(crate) fn core_type_is_imprecise_runtime_slot(ty: &core_ir::Type) -> bool {
    matches!(
        core_type_meaning(ty),
        CoreTypeMeaning::Top | CoreTypeMeaning::InferenceVar
    )
}

pub(crate) fn runtime_type_is_imprecise_runtime_slot(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Unknown | RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))
    )
}

pub(crate) fn core_type_is_runtime_projection_fallback(ty: &core_ir::Type) -> bool {
    matches!(core_type_meaning(ty), CoreTypeMeaning::Top)
}

pub(crate) fn wildcard_effect_type() -> core_ir::Type {
    core_ir::Type::Any
}

pub(crate) fn runtime_projection_fallback_type() -> core_ir::Type {
    core_ir::Type::Any
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inference_holes_are_only_type_vars() {
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
    fn runtime_projection_fallback_is_only_any() {
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
