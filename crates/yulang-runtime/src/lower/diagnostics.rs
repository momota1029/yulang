use super::*;

pub(super) fn reject_non_runtime_type(ty: &core_ir::Type, source: TypeSource) -> RuntimeResult<()> {
    if contains_non_runtime_type(ty) {
        return Err(RuntimeError::NonRuntimeType {
            ty: ty.clone(),
            source,
        });
    }
    Ok(())
}

pub(super) fn reject_non_runtime_hir_type(
    ty: &RuntimeType,
    source: TypeSource,
) -> RuntimeResult<()> {
    match ty {
        RuntimeType::Core(ty) => reject_non_runtime_type(ty, source),
        RuntimeType::Fun { param, ret } => {
            reject_non_runtime_hir_type(param, source)?;
            reject_non_runtime_hir_type(ret, source)
        }
        RuntimeType::Thunk { effect, value } => {
            if contains_non_runtime_effect_type(effect) {
                return Err(RuntimeError::NonRuntimeType {
                    ty: effect.clone(),
                    source,
                });
            }
            reject_non_runtime_hir_type(value, source)
        }
    }
}
