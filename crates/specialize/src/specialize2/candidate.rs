use super::*;

mod surface;
pub(in crate::specialize2) use surface::*;

pub(super) fn join_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return join_record_type_candidates(graph, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return join_poly_variant_type_candidates(graph, left, right);
        }
        (Type::EffectRow(_), Type::EffectRow(_)) => {
            let (Type::EffectRow(left), Type::EffectRow(right)) = (left, right) else {
                unreachable!("effect row candidates checked by caller");
            };
            return merge_effect_row_candidates(graph, left, right, CandidateMerge::Join);
        }
        (Type::EffectRow(_), _) | (_, Type::EffectRow(_)) => {
            let left_items = effect_candidate_items(left.clone());
            let right_items = effect_candidate_items(right.clone());
            if let (Some(left), Some(right)) = (left_items, right_items) {
                return merge_effect_row_candidates(graph, left, right, CandidateMerge::Join);
            }
        }
        _ => {}
    }
    if left == right || type_candidate_subtype(graph, &right, &left) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &left, &right) {
        return Ok(right);
    }
    match (left, right) {
        (Type::OpenVar(_), right) => Ok(right),
        (left, Type::OpenVar(_)) => Ok(left),
        (Type::Never, right) => Ok(right),
        (left, Type::Never) => Ok(left),
        (left, right) if left.is_pure_effect() && right.is_pure_effect() => Ok(Type::pure_effect()),
        (
            Type::Thunk {
                effect: left_effect,
                value: left_value,
            },
            Type::Thunk {
                effect: right_effect,
                value: right_value,
            },
        ) => Ok(types::runtime_shape(
            join_type_candidates(graph, *left_effect, *right_effect)?,
            join_type_candidates(graph, *left_value, *right_value)?,
        )),
        (Type::Thunk { effect, value }, right) => Ok(types::runtime_shape(
            *effect,
            join_type_candidates(graph, *value, right)?,
        )),
        (left, Type::Thunk { effect, value }) => Ok(types::runtime_shape(
            *effect,
            join_type_candidates(graph, left, *value)?,
        )),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            merge_same_head_con_candidate(
                graph,
                left_path,
                left_args,
                right_args,
                CandidateMerge::Join,
            )
        }
        (Type::Tuple(left_items), Type::Tuple(right_items))
            if left_items.len() == right_items.len() =>
        {
            merge_tuple_type_candidates(graph, left_items, right_items, CandidateMerge::Join)
        }
        (left @ Type::Fun { .. }, right @ Type::Fun { .. }) => {
            merge_function_type_candidates(graph, left, right, CandidateMerge::Join)
        }
        (Type::EffectRow(left), Type::EffectRow(right)) => {
            merge_effect_row_candidates(graph, left, right, CandidateMerge::Join)
        }
        (
            Type::Stack {
                inner: left,
                weight,
            },
            Type::Stack {
                inner: right,
                weight: right_weight,
            },
        ) if weight == right_weight => Ok(types::simplify_stack_type(
            join_type_candidates(graph, *left, *right)?,
            weight,
        )),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot: 0,
            existing: left,
            incoming: right,
        }),
    }
}

pub(super) fn meet_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return meet_record_type_candidates(graph, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return meet_poly_variant_type_candidates(graph, left, right);
        }
        (Type::EffectRow(_), Type::EffectRow(_)) => {
            let (Type::EffectRow(left), Type::EffectRow(right)) = (left, right) else {
                unreachable!("effect row candidates checked by caller");
            };
            return merge_effect_row_candidates(graph, left, right, CandidateMerge::Meet);
        }
        (Type::EffectRow(_), _) | (_, Type::EffectRow(_)) => {
            let left_items = effect_candidate_items(left.clone());
            let right_items = effect_candidate_items(right.clone());
            if let (Some(left), Some(right)) = (left_items, right_items) {
                return merge_effect_row_candidates(graph, left, right, CandidateMerge::Meet);
            }
        }
        _ => {}
    }
    if left == right || type_candidate_subtype(graph, &left, &right) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &right, &left) {
        return Ok(right);
    }
    match (left, right) {
        (Type::OpenVar(_), right) => Ok(right),
        (left, Type::OpenVar(_)) => Ok(left),
        (Type::Any, right) => Ok(right),
        (left, Type::Any) => Ok(left),
        (left, right) if left.is_pure_effect() && right.is_pure_effect() => Ok(Type::pure_effect()),
        (
            Type::Thunk {
                effect: left_effect,
                value: left_value,
            },
            Type::Thunk {
                effect: right_effect,
                value: right_value,
            },
        ) => Ok(types::runtime_shape(
            meet_type_candidates(graph, *left_effect, *right_effect)?,
            meet_type_candidates(graph, *left_value, *right_value)?,
        )),
        (Type::Thunk { value, .. }, right) => meet_type_candidates(graph, *value, right),
        (left, Type::Thunk { value, .. }) => meet_type_candidates(graph, left, *value),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            merge_same_head_con_candidate(
                graph,
                left_path,
                left_args,
                right_args,
                CandidateMerge::Meet,
            )
        }
        (Type::Tuple(left_items), Type::Tuple(right_items))
            if left_items.len() == right_items.len() =>
        {
            merge_tuple_type_candidates(graph, left_items, right_items, CandidateMerge::Meet)
        }
        (left @ Type::Fun { .. }, right @ Type::Fun { .. }) => {
            merge_function_type_candidates(graph, left, right, CandidateMerge::Meet)
        }
        (Type::EffectRow(left), Type::EffectRow(right)) => {
            merge_effect_row_candidates(graph, left, right, CandidateMerge::Meet)
        }
        (
            Type::Stack {
                inner: left,
                weight,
            },
            Type::Stack {
                inner: right,
                weight: right_weight,
            },
        ) if weight == right_weight => Ok(types::simplify_stack_type(
            meet_type_candidates(graph, *left, *right)?,
            weight,
        )),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot: 0,
            existing: left,
            incoming: right,
        }),
    }
}

pub(super) fn join_record_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, left_fields, right_fields, RecordMerge::Join)
        .map(Type::Record)
}

pub(super) fn meet_record_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, left_fields, right_fields, RecordMerge::Meet)
        .map(Type::Record)
}

pub(super) fn merge_record_type_candidates(
    graph: &TypeGraph<'_>,
    left_fields: Vec<TypeField>,
    right_fields: Vec<TypeField>,
    merge: RecordMerge,
) -> Result<Vec<TypeField>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_fields {
        match record_field_type(&right_fields, &left.name) {
            Some(right) => {
                let value = match merge {
                    RecordMerge::Join => {
                        join_type_candidates(graph, left.value.clone(), right.value.clone())?
                    }
                    RecordMerge::Meet => {
                        meet_type_candidates(graph, left.value.clone(), right.value.clone())?
                    }
                };
                out.push(TypeField {
                    name: left.name.clone(),
                    value,
                    optional: match merge {
                        RecordMerge::Join => left.optional || right.optional,
                        RecordMerge::Meet => left.optional && right.optional,
                    },
                });
            }
            None => out.push(TypeField {
                name: left.name.clone(),
                value: left.value.clone(),
                optional: match merge {
                    RecordMerge::Join => true,
                    RecordMerge::Meet => left.optional,
                },
            }),
        }
    }
    for right in right_fields {
        if left_fields.iter().any(|left| left.name == right.name) {
            continue;
        }
        out.push(TypeField {
            name: right.name,
            value: right.value,
            optional: match merge {
                RecordMerge::Join => true,
                RecordMerge::Meet => right.optional,
            },
        });
    }
    Ok(out)
}

pub(super) fn join_poly_variant_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    merge_poly_variant_type_candidates(graph, left_variants, right_variants, VariantMerge::Join)
        .map(Type::PolyVariant)
}

pub(super) fn meet_poly_variant_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    let variants = merge_poly_variant_type_candidates(
        graph,
        left_variants,
        right_variants,
        VariantMerge::Meet,
    )?;
    if variants.is_empty() {
        return Ok(Type::Never);
    }
    Ok(Type::PolyVariant(variants))
}

pub(super) fn merge_poly_variant_type_candidates(
    graph: &TypeGraph<'_>,
    left_variants: Vec<TypeVariant>,
    right_variants: Vec<TypeVariant>,
    merge: VariantMerge,
) -> Result<Vec<TypeVariant>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_variants {
        match matching_variant(&right_variants, left) {
            Some(right) => {
                let payloads = left
                    .payloads
                    .iter()
                    .cloned()
                    .zip(right.payloads.iter().cloned())
                    .map(|(left, right)| match merge {
                        VariantMerge::Join => join_type_candidates(graph, left, right),
                        VariantMerge::Meet => meet_type_candidates(graph, left, right),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                out.push(TypeVariant {
                    name: left.name.clone(),
                    payloads,
                });
            }
            None if merge == VariantMerge::Join => out.push(left.clone()),
            None => {}
        }
    }
    if merge == VariantMerge::Join {
        for right in right_variants {
            if left_variants
                .iter()
                .any(|left| variants_match(left, &right))
            {
                continue;
            }
            out.push(right);
        }
    }
    Ok(out)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RecordMerge {
    Join,
    Meet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VariantMerge {
    Join,
    Meet,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum CandidateMerge {
    Join,
    Meet,
}

pub(super) fn merge_same_head_con_candidate(
    graph: &TypeGraph<'_>,
    path: Vec<String>,
    left_args: Vec<Type>,
    right_args: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let args = left_args
        .into_iter()
        .zip(right_args)
        .map(|(left, right)| merge_candidate_component(graph, left, right, merge))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Con { path, args })
}

pub(super) fn merge_tuple_type_candidates(
    graph: &TypeGraph<'_>,
    left_items: Vec<Type>,
    right_items: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let items = left_items
        .into_iter()
        .zip(right_items)
        .map(|(left, right)| merge_candidate_component(graph, left, right, merge))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Tuple(items))
}

pub(super) fn merge_function_type_candidates(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let Some(left) = function_computation_parts(&left) else {
        unreachable!("function candidates checked by caller");
    };
    let Some(right) = function_computation_parts(&right) else {
        unreachable!("function candidates checked by caller");
    };
    let contravariant = match merge {
        CandidateMerge::Join => CandidateMerge::Meet,
        CandidateMerge::Meet => CandidateMerge::Join,
    };
    Ok(Type::Fun {
        arg: Box::new(merge_candidate_component(
            graph,
            left.arg,
            right.arg,
            contravariant,
        )?),
        arg_effect: Box::new(merge_candidate_component(
            graph,
            left.arg_effect,
            right.arg_effect,
            contravariant,
        )?),
        ret_effect: Box::new(merge_candidate_component(
            graph,
            left.ret_effect,
            right.ret_effect,
            merge,
        )?),
        ret: Box::new(merge_candidate_component(
            graph, left.ret, right.ret, merge,
        )?),
    })
}

pub(super) fn merge_effect_row_candidates(
    graph: &TypeGraph<'_>,
    left: Vec<Type>,
    right: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let (left_items, left_tail) = split_effect_candidate_tail_owned(graph, left);
    let (right_items, right_tail) = split_effect_candidate_tail_owned(graph, right);
    let left_has_tail = left_tail.is_some();
    let right_has_tail = right_tail.is_some();
    let mut out = Vec::new();
    let mut right_used = vec![false; right_items.len()];
    for left_item in left_items {
        match right_items
            .iter()
            .enumerate()
            .find_map(|(index, right_item)| {
                (!right_used[index] && same_effect_row_family(&left_item, right_item))
                    .then_some(index)
            }) {
            Some(index) => {
                right_used[index] = true;
                out.push(merge_effect_row_item_candidate(
                    graph,
                    left_item,
                    right_items[index].clone(),
                    merge,
                )?);
            }
            None if merge == CandidateMerge::Join || right_has_tail => out.push(left_item),
            None => {}
        }
    }
    for (index, right_item) in right_items.into_iter().enumerate() {
        if right_used[index] {
            continue;
        }
        if merge == CandidateMerge::Join || left_has_tail {
            out.push(right_item);
        }
    }
    match (merge, left_tail, right_tail) {
        (CandidateMerge::Join, Some(left), Some(right)) => {
            out.push(join_type_candidates(graph, left, right)?);
        }
        (CandidateMerge::Meet, Some(left), Some(right)) => {
            out.push(meet_type_candidates(graph, left, right)?);
        }
        (CandidateMerge::Join, Some(tail), None) | (CandidateMerge::Join, None, Some(tail)) => {
            out.push(tail);
        }
        _ => {}
    }
    Ok(types::simplify_type(Type::EffectRow(out)))
}

pub(super) fn merge_effect_row_item_candidate(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    if left == right {
        return Ok(left);
    }
    match (left, right) {
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            merge_same_family_effect_item_candidate(graph, left_path, left_args, right_args, merge)
        }
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if effect_path_contains_family(&left_path, &right_path) => Ok(match merge {
            CandidateMerge::Join => Type::Con {
                path: left_path,
                args: left_args,
            },
            CandidateMerge::Meet => Type::Con {
                path: right_path,
                args: right_args,
            },
        }),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if effect_path_contains_family(&right_path, &left_path) => Ok(match merge {
            CandidateMerge::Join => Type::Con {
                path: right_path,
                args: right_args,
            },
            CandidateMerge::Meet => Type::Con {
                path: left_path,
                args: left_args,
            },
        }),
        (left, right) => merge_candidate_component(graph, left, right, merge),
    }
}

pub(super) fn merge_same_family_effect_item_candidate(
    graph: &TypeGraph<'_>,
    path: Vec<String>,
    left_args: Vec<Type>,
    right_args: Vec<Type>,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    let args = left_args
        .into_iter()
        .zip(right_args)
        .map(|(left, right)| merge_effect_payload_candidate(graph, left, right, merge))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Type::Con { path, args })
}

pub(super) fn merge_effect_payload_candidate(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    match merge_candidate_component(graph, left.clone(), right.clone(), merge) {
        Ok(merged) => Ok(merged),
        Err(SpecializeError::ConflictingTypeCandidates { .. }) => Ok(match merge {
            CandidateMerge::Join => {
                types::simplify_type(Type::Union(Box::new(left), Box::new(right)))
            }
            CandidateMerge::Meet => {
                types::simplify_type(Type::Intersection(Box::new(left), Box::new(right)))
            }
        }),
        Err(error) => Err(error),
    }
}

pub(super) fn merge_candidate_component(
    graph: &TypeGraph<'_>,
    left: Type,
    right: Type,
    merge: CandidateMerge,
) -> Result<Type, SpecializeError> {
    match merge {
        CandidateMerge::Join => join_type_candidates(graph, left, right),
        CandidateMerge::Meet => meet_type_candidates(graph, left, right),
    }
}

pub(super) fn same_candidate_head(left: &Type, right: &Type) -> bool {
    match (left, right) {
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) => left_path == right_path && left_args.len() == right_args.len(),
        (Type::Fun { .. }, Type::Fun { .. }) => true,
        (Type::Thunk { .. }, Type::Thunk { .. }) => true,
        (Type::Tuple(left), Type::Tuple(right)) => left.len() == right.len(),
        _ => false,
    }
}
