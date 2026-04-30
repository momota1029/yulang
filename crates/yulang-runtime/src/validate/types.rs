use super::*;

pub(super) fn require_same_type(
    expected: &core_ir::Type,
    actual: &core_ir::Type,
    source: TypeSource,
) -> RuntimeResult<()> {
    if core_types_compatible(expected, actual)
        || effect_compatible(expected, actual)
        || effect_compatible(actual, expected)
    {
        return Ok(());
    }
    if std::env::var_os("YULANG_DEBUG_RUNTIME_TYPE").is_some() {
        eprintln!("validate same type {source:?}: {expected:?} / {actual:?}");
    }
    Err(RuntimeError::TypeMismatch {
        expected: expected.clone(),
        actual: actual.clone(),
        source,
    })
}
