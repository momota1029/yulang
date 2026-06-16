use super::*;

pub(super) fn final_return_type(mut ty: &Type) -> &Type {
    while let Type::Fun { ret, .. } = ty {
        ty = ret;
    }
    ty
}

pub(super) fn runtime_value_shape(ty: &Type) -> &Type {
    match ty {
        Type::Thunk { value, .. } => value,
        _ => ty,
    }
}

pub(super) fn runtime_value_is_never(ty: &Type) -> bool {
    matches!(runtime_value_shape(ty), Type::Never)
}

pub(super) fn value_argument_narrows_polyvariant(declared: &Type, actual: &Type) -> bool {
    let Type::PolyVariant(declared_variants) = runtime_value_shape(declared) else {
        return false;
    };
    let Type::PolyVariant(actual_variants) = runtime_value_shape(actual) else {
        return false;
    };
    actual_variants.len() < declared_variants.len()
        && actual_variants.iter().all(|actual| {
            declared_variants.iter().any(|declared| {
                declared.name == actual.name && declared.payloads.len() == actual.payloads.len()
            })
        })
}

pub(super) fn function_runtime_parts(ty: &Type) -> Option<(Type, Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg.as_ref().clone(), ret.as_ref().clone()))
}

pub(super) fn split_function_spine(mut ty: Type, arity: usize) -> Option<(Vec<Type>, Type)> {
    let mut args = Vec::with_capacity(arity);
    for _ in 0..arity {
        let Type::Fun { arg, ret, .. } = ty else {
            return None;
        };
        args.push(*arg);
        ty = *ret;
    }
    Some((args, ty))
}

pub(super) fn split_runtime_computation_shape(shape: Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (*value, *effect),
        value => (value, Type::pure_effect()),
    }
}

pub(super) fn catch_residual_effect(scrutinee_effect: Type, handled_effects: &[Type]) -> Type {
    if handled_effects.is_empty() || scrutinee_effect.is_pure_effect() {
        return scrutinee_effect;
    }
    let handled_items = handled_effects
        .iter()
        .flat_map(effect_row_items)
        .cloned()
        .collect::<Vec<_>>();
    residual_effect_after_handling(scrutinee_effect, &handled_items)
}

pub(super) fn effect_row_items(effect: &Type) -> &[Type] {
    match effect {
        Type::EffectRow(items) => items,
        _ => std::slice::from_ref(effect),
    }
}

pub(super) fn residual_effect_after_handling(effect: Type, handled_items: &[Type]) -> Type {
    if effect.is_pure_effect() {
        return Type::pure_effect();
    }
    match effect {
        Type::EffectRow(items) => residual_effect_row_after_handling(items, handled_items),
        Type::Con { .. } if effect_item_is_handled(&effect, handled_items) => Type::pure_effect(),
        Type::Con { .. } => Type::EffectRow(vec![effect]),
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(residual_effect_after_handling(*left, handled_items)),
            Box::new(residual_effect_after_handling(*right, handled_items)),
        )),
        Type::Intersection(left, right) => {
            residual_intersection_after_handling(*left, *right, handled_items)
        }
        Type::Stack { .. } | Type::OpenVar(_) => symbolic_residual_effect(effect, handled_items),
        Type::Any | Type::Never => effect,
        Type::Fun { .. }
        | Type::Thunk { .. }
        | Type::Record(_)
        | Type::PolyVariant(_)
        | Type::Tuple(_) => symbolic_residual_effect(effect, handled_items),
    }
}

pub(super) fn residual_intersection_after_handling(
    left: Type,
    right: Type,
    handled_items: &[Type],
) -> Type {
    if let Some(residual) = residual_row_tail_from_intersection(&left, &right, handled_items) {
        return residual;
    }
    if let Some(residual) = residual_row_tail_from_intersection(&right, &left, handled_items) {
        return residual;
    }
    symbolic_residual_effect(
        Type::Intersection(Box::new(left), Box::new(right)),
        handled_items,
    )
}

pub(super) fn residual_row_tail_from_intersection(
    row_side: &Type,
    other_side: &Type,
    handled_items: &[Type],
) -> Option<Type> {
    let Type::EffectRow(items) = row_side else {
        return None;
    };
    let tail = items.last()?;
    if !effect_row_mentions_handled(items, handled_items) || !type_contains_type(other_side, tail) {
        return None;
    }
    Some(symbolic_residual_effect(tail.clone(), handled_items))
}

pub(super) fn residual_effect_row_after_handling(items: Vec<Type>, handled_items: &[Type]) -> Type {
    let mut residual = Vec::new();
    for item in items {
        if effect_item_is_handled(&item, handled_items) {
            continue;
        }
        if effect_item_needs_symbolic_residual(&item) {
            residual.push(symbolic_residual_effect(item, handled_items));
        } else {
            residual.push(item);
        }
    }
    types::simplify_type(Type::EffectRow(residual))
}

pub(super) fn effect_row_mentions_handled(items: &[Type], handled_items: &[Type]) -> bool {
    items
        .iter()
        .any(|item| effect_item_is_handled(item, handled_items))
}

pub(super) fn effect_item_is_handled(item: &Type, handled_items: &[Type]) -> bool {
    handled_items
        .iter()
        .any(|handled| same_effect_row_family(item, handled))
}

pub(super) fn effect_item_needs_symbolic_residual(item: &Type) -> bool {
    matches!(
        item,
        Type::OpenVar(_)
            | Type::Stack { .. }
            | Type::Union(_, _)
            | Type::Intersection(_, _)
            | Type::Any
    )
}

pub(super) fn symbolic_residual_effect(effect: Type, handled_items: &[Type]) -> Type {
    let Some(weight) = residual_stack_weight(handled_items) else {
        return effect;
    };
    types::simplify_type(Type::Stack {
        inner: Box::new(effect),
        weight,
    })
}

pub(super) fn residual_stack_weight(handled_items: &[Type]) -> Option<StackWeight> {
    let families = handled_items
        .iter()
        .filter_map(effect_family_from_item)
        .collect::<Vec<_>>();
    (!families.is_empty()).then_some(StackWeight {
        entries: vec![StackWeightEntry {
            id: 0,
            pops: 0,
            floor: vec![EffectFamilies::AllExcept(families)],
            stack: Vec::new(),
        }],
    })
}

pub(super) fn effect_family_from_item(item: &Type) -> Option<EffectFamily> {
    let Type::Con { path, args } = item else {
        return None;
    };
    Some(EffectFamily {
        path: path.clone(),
        args: args.clone(),
    })
}

pub(super) fn type_contains_type(ty: &Type, needle: &Type) -> bool {
    if ty == needle {
        return true;
    }
    match ty {
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_type(arg, needle)
                || type_contains_type(arg_effect, needle)
                || type_contains_type(ret_effect, needle)
                || type_contains_type(ret, needle)
        }
        Type::Thunk { effect, value } => {
            type_contains_type(effect, needle) || type_contains_type(value, needle)
        }
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(|arg| type_contains_type(arg, needle))
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_type(&field.value, needle)),
        Type::PolyVariant(variants) => variants.iter().any(|variant| {
            variant
                .payloads
                .iter()
                .any(|payload| type_contains_type(payload, needle))
        }),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_type(left, needle) || type_contains_type(right, needle)
        }
        Type::Stack { inner, .. } => type_contains_type(inner, needle),
        Type::Any | Type::Never | Type::OpenVar(_) => false,
    }
}

pub(super) fn matching_effect_row_item(item: &Type, candidates: &[Type]) -> Option<Type> {
    candidates
        .iter()
        .find(|candidate| same_effect_row_family(item, candidate))
        .cloned()
}

pub(super) fn same_effect_row_family(left: &Type, right: &Type) -> bool {
    matches!(
        (left, right),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len()
    )
}

pub(super) fn is_self_stack_bound(slot: u32, ty: &Type) -> bool {
    let Type::Stack { inner, .. } = ty else {
        return false;
    };
    matches!(inner.as_ref(), Type::OpenVar(candidate) if *candidate == slot)
}
