//! Pattern-local runtime type selection.
//!
//! Pattern binders appear in multiple finalize phases: graph collection needs
//! local types while building apply-spine evidence, and materialization refreshes
//! local variable types after a specialization has changed enclosing params.
//! Keep the scrutinee-vs-pattern fallback rule in one place so both phases make
//! the same choice.

use yulang_runtime_ir::RuntimeType;
use yulang_typed_ir as typed_ir;

pub(crate) fn choose_pattern_ty(
    pattern_ty: &RuntimeType,
    scrutinee_ty: Option<&RuntimeType>,
) -> RuntimeType {
    if let Some(scrutinee_ty) = scrutinee_ty
        && !super::runtime_type_has_unknown(scrutinee_ty)
    {
        return scrutinee_ty.clone();
    }
    if !super::runtime_type_has_unknown(pattern_ty) {
        return pattern_ty.clone();
    }
    pattern_ty.clone()
}

pub(crate) fn tuple_component_runtime_types(
    scrutinee_ty: Option<&RuntimeType>,
    pattern_ty: &RuntimeType,
    arity: usize,
) -> Vec<Option<RuntimeType>> {
    let preferred = scrutinee_ty
        .filter(|ty| !super::runtime_type_has_unknown(ty))
        .cloned();
    let chosen = preferred.unwrap_or_else(|| pattern_ty.clone());
    if let RuntimeType::Value(typed_ir::Type::Tuple(items)) = &chosen
        && items.len() == arity
    {
        return items
            .iter()
            .map(|item| Some(RuntimeType::Value(item.clone())))
            .collect();
    }
    vec![None; arity]
}

pub(crate) fn record_field_runtime_type(
    scrutinee_ty: Option<&RuntimeType>,
    pattern_ty: &RuntimeType,
    name: &typed_ir::Name,
) -> Option<RuntimeType> {
    let preferred = scrutinee_ty
        .filter(|ty| !super::runtime_type_has_unknown(ty))
        .or_else(|| (!super::runtime_type_has_unknown(pattern_ty)).then_some(pattern_ty))?;
    let RuntimeType::Value(typed_ir::Type::Record(record)) = preferred else {
        return None;
    };
    record
        .fields
        .iter()
        .find(|field| field.name == *name)
        .map(|field| RuntimeType::Value(field.value.clone()))
}
