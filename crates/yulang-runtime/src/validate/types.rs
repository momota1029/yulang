use super::*;

pub(super) fn require_same_type(
    expected: &core_ir::Type,
    actual: &core_ir::Type,
    source: TypeSource,
) -> RuntimeResult<()> {
    if core_types_compatible(expected, actual) || effect_compatible(expected, actual) {
        return Ok(());
    }
    Err(RuntimeError::TypeMismatch {
        expected: expected.clone(),
        actual: actual.clone(),
        source,
    })
}
