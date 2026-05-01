use super::*;

/// Names the places where `core_ir::Type::Any` is still used as an unknown.
///
/// These helpers do not change the representation.  They keep call sites honest
/// about whether `_` means an inference hole, an effect wildcard, or an erased
/// fallback produced by runtime projection.
pub(crate) fn core_type_is_inference_hole(ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Any | core_ir::Type::Var(_))
}

pub(crate) fn runtime_type_is_inference_hole(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))
    )
}

pub(crate) fn core_type_is_runtime_projection_fallback(ty: &core_ir::Type) -> bool {
    matches!(ty, core_ir::Type::Any)
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
    fn inference_holes_include_principal_vars() {
        assert!(core_type_is_inference_hole(&core_ir::Type::Any));
        assert!(core_type_is_inference_hole(&core_ir::Type::Var(
            core_ir::TypeVar("a".to_string())
        )));
        assert!(!core_type_is_inference_hole(&core_ir::Type::Never));
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
