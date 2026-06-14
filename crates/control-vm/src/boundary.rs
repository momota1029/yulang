//! Runtime boundary checks shared by validation and execution.

use mono::Type;

pub(crate) fn function_parts(ty: &Type) -> Option<(&Type, &Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg, ret))
}

pub(crate) fn thunk_value_type(ty: &Type) -> Option<&Type> {
    let Type::Thunk { value, .. } = ty else {
        return None;
    };
    Some(value)
}

pub(crate) fn equivalent_runtime_types(source: &Type, target: &Type) -> bool {
    if source == target || source.is_pure_effect() && target.is_pure_effect() {
        return true;
    }
    match (source, target) {
        (source, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            equivalent_runtime_types(source, value)
        }
        (Type::Thunk { effect, value }, target) if effect.is_pure_effect() => {
            equivalent_runtime_types(value, target)
        }
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            target_fields.iter().all(|target| {
                record_field_type(source_fields, &target.name).map_or(target.optional, |source| {
                    equivalent_runtime_types(&source.value, &target.value)
                })
            })
        }
        (Type::PolyVariant(source_variants), Type::PolyVariant(target_variants)) => {
            source_variants.iter().all(|source| {
                target_variants
                    .iter()
                    .find(|target| {
                        target.name == source.name && target.payloads.len() == source.payloads.len()
                    })
                    .is_some_and(|target| {
                        source
                            .payloads
                            .iter()
                            .zip(&target.payloads)
                            .all(|(source, target)| equivalent_runtime_types(source, target))
                    })
            })
        }
        (source, Type::Union(left, right)) => {
            equivalent_runtime_types(source, left) || equivalent_runtime_types(source, right)
        }
        (Type::Union(left, right), target) => {
            equivalent_runtime_types(left, target) && equivalent_runtime_types(right, target)
        }
        (source, Type::Intersection(left, right)) => {
            equivalent_runtime_types(source, left) && equivalent_runtime_types(source, right)
        }
        (Type::Intersection(left, right), target) => {
            equivalent_runtime_types(left, target) || equivalent_runtime_types(right, target)
        }
        _ => false,
    }
}

fn record_field_type<'a>(fields: &'a [mono::TypeField], name: &str) -> Option<&'a mono::TypeField> {
    fields.iter().find(|field| field.name == name)
}

pub(crate) fn value_boundary_supported(source: &Type, target: &Type) -> bool {
    if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
        return true;
    }
    if matches!(source, Type::Never) {
        return true;
    }
    match (source, target) {
        (Type::Thunk { value: source, .. }, Type::Thunk { value: target, .. }) => {
            value_boundary_supported(source, target)
        }
        (Type::Thunk { value: source, .. }, target) => value_boundary_supported(source, target),
        (source, Type::Thunk { value: target, .. }) => value_boundary_supported(source, target),
        _ => false,
    }
}

pub(crate) fn function_boundary_supported(source: &Type, target: &Type) -> bool {
    let Some((source_arg, source_ret)) = function_parts(source) else {
        return false;
    };
    let Some((target_arg, target_ret)) = function_parts(target) else {
        return false;
    };
    value_boundary_supported(target_arg, source_arg)
        && value_boundary_supported(source_ret, target_ret)
}
