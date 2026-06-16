use super::*;

pub(super) fn type_candidate_subtype(graph: &TypeGraph<'_>, lower: &Type, upper: &Type) -> bool {
    if lower == upper || matches!(lower, Type::Never) || matches!(upper, Type::Any) {
        return true;
    }
    match (lower, upper) {
        (Type::Con { path: lower, .. }, Type::Con { path: upper, .. }) if lower != upper => graph
            .arena
            .cast_rules
            .iter()
            .any(|rule| rule.source == *lower && rule.target == *upper),
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
            lower_args.iter().zip(upper_args).all(|(lower, upper)| {
                type_candidate_subtype(graph, lower, upper)
                    && type_candidate_subtype(graph, upper, lower)
            })
        }
        (
            Type::Fun {
                arg: lower_arg,
                ret: lower_ret,
                ..
            },
            Type::Fun {
                arg: upper_arg,
                ret: upper_ret,
                ..
            },
        ) => {
            type_candidate_subtype(graph, upper_arg, lower_arg)
                && type_candidate_subtype(graph, lower_ret, upper_ret)
        }
        (Type::Tuple(lower), Type::Tuple(upper)) if lower.len() == upper.len() => lower
            .iter()
            .zip(upper)
            .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper)),
        (Type::Record(lower), Type::Record(upper)) => upper.iter().all(|upper| {
            upper.optional
                || record_field_type(lower, &upper.name)
                    .is_some_and(|lower| type_candidate_subtype(graph, &lower.value, &upper.value))
        }),
        (Type::PolyVariant(lower), Type::PolyVariant(upper)) => lower.iter().all(|lower| {
            matching_variant(upper, lower).is_some_and(|upper| {
                lower
                    .payloads
                    .iter()
                    .zip(&upper.payloads)
                    .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
            })
        }),
        (Type::EffectRow(lower), Type::EffectRow(upper)) => {
            effect_row_candidate_subtype(graph, lower, upper)
        }
        (Type::Union(left, right), upper) => {
            type_candidate_subtype(graph, left, upper)
                && type_candidate_subtype(graph, right, upper)
        }
        (lower, Type::Intersection(left, right)) => {
            type_candidate_subtype(graph, lower, left)
                && type_candidate_subtype(graph, lower, right)
        }
        _ => false,
    }
}

pub(super) fn effect_row_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower_items: &[Type],
    upper_items: &[Type],
) -> bool {
    let (lower_items, lower_has_top_tail) = split_effect_candidate_tail(graph, lower_items);
    let (upper_items, upper_has_top_tail) = split_effect_candidate_tail(graph, upper_items);
    if lower_items.is_empty() && !lower_has_top_tail {
        return true;
    }
    let mut matched_upper = vec![false; upper_items.len()];
    for lower in lower_items {
        let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
            (!matched_upper[index] && effect_row_item_candidate_subtype(graph, lower, upper))
                .then_some(index)
        }) else {
            if upper_has_top_tail {
                continue;
            }
            return false;
        };
        matched_upper[upper_index] = true;
    }
    !lower_has_top_tail || upper_has_top_tail
}

pub(super) fn effect_rows_have_same_families(
    graph: &TypeGraph<'_>,
    left: &Type,
    right: &Type,
) -> bool {
    let (Type::EffectRow(left), Type::EffectRow(right)) = (left, right) else {
        return false;
    };
    let (left, left_has_tail) = split_effect_candidate_tail(graph, left);
    let (right, right_has_tail) = split_effect_candidate_tail(graph, right);
    !left_has_tail
        && !right_has_tail
        && left.len() == right.len()
        && left.iter().all(|left| {
            right
                .iter()
                .any(|right| same_effect_row_family(left, right))
        })
}

pub(super) fn refine_effect_lower_with_upper(
    graph: &TypeGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> Result<Option<Type>, SpecializeError> {
    let (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) = (lower, upper) else {
        return Ok(None);
    };
    let (lower_items, lower_has_tail) = split_effect_candidate_tail(graph, lower_items);
    let (upper_items, upper_has_tail) = split_effect_candidate_tail(graph, upper_items);
    if lower_has_tail {
        if upper_has_tail
            || !lower_items.iter().all(|lower_item| {
                upper_items
                    .iter()
                    .any(|upper_item| same_effect_row_family(lower_item, upper_item))
            })
        {
            return Ok(None);
        }
        return meet_type_candidates(graph, lower.clone(), upper.clone()).map(Some);
    }
    let mut refined = Vec::with_capacity(lower_items.len());
    for lower_item in lower_items {
        match upper_items
            .iter()
            .find(|upper_item| same_effect_row_family(lower_item, upper_item))
        {
            Some(upper_item) => refined.push(merge_effect_row_item_candidate(
                graph,
                lower_item.clone(),
                upper_item.clone(),
                CandidateMerge::Meet,
            )?),
            None if upper_has_tail => refined.push(lower_item.clone()),
            None => return Ok(None),
        }
    }
    Ok(Some(types::simplify_type(Type::EffectRow(refined))))
}

pub(super) fn effect_row_item_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> bool {
    match (lower, upper) {
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) if lower_path == upper_path && lower_args.len() == upper_args.len() => lower_args
            .iter()
            .zip(upper_args)
            .all(|(lower, upper)| effect_payload_candidate_subtype(graph, lower, upper)),
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) if effect_path_contains_family(upper_path, lower_path) => {
            effect_payloads_candidate_subtype(graph, lower_args, upper_args)
        }
        _ => same_effect_row_family(lower, upper) && type_candidate_subtype(graph, lower, upper),
    }
}

pub(super) fn effect_payloads_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower_args: &[Type],
    upper_args: &[Type],
) -> bool {
    upper_args.is_empty()
        || (lower_args.len() == upper_args.len()
            && lower_args
                .iter()
                .zip(upper_args)
                .all(|(lower, upper)| effect_payload_candidate_subtype(graph, lower, upper)))
}

pub(super) fn effect_payload_candidate_subtype(
    graph: &TypeGraph<'_>,
    lower: &Type,
    upper: &Type,
) -> bool {
    if lower == upper || matches!(upper, Type::OpenVar(_)) {
        return true;
    }
    if matches!(lower, Type::OpenVar(_)) {
        return false;
    }
    type_candidate_subtype(graph, lower, upper)
}

pub(super) fn split_effect_candidate_tail<'a>(
    graph: &TypeGraph<'_>,
    items: &'a [Type],
) -> (&'a [Type], bool) {
    match items.last() {
        Some(tail) if type_is_effect_tail_candidate(graph, tail) => {
            (&items[..items.len() - 1], true)
        }
        _ => (items, false),
    }
}

pub(super) fn split_effect_candidate_tail_owned(
    graph: &TypeGraph<'_>,
    mut items: Vec<Type>,
) -> (Vec<Type>, Option<Type>) {
    let Some(tail) = items.last().cloned() else {
        return (items, None);
    };
    if type_is_effect_tail_candidate(graph, &tail) {
        items.pop();
        return (items, Some(tail));
    }
    (items, None)
}

pub(super) fn type_is_effect_tail_candidate(graph: &TypeGraph<'_>, ty: &Type) -> bool {
    match ty {
        Type::OpenVar(slot) => graph
            .slots
            .get(*slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Effect),
        Type::EffectRow(items) => items
            .last()
            .is_some_and(|tail| type_is_effect_tail_candidate(graph, tail)),
        Type::Intersection(left, right) => {
            type_is_effect_tail_candidate(graph, left)
                && type_is_effect_tail_candidate(graph, right)
        }
        Type::Stack { inner, .. } => type_is_effect_tail_candidate(graph, inner),
        _ => false,
    }
}

pub(super) fn effect_consumption_demand(expected: &Type) -> Option<EffectSubtractionDemand> {
    effect_intersection_consumption_demand(expected)
        .or_else(|| effect_row_consumption_demand(expected))
}

pub(super) fn effect_intersection_consumption_demand(
    expected: &Type,
) -> Option<EffectSubtractionDemand> {
    let Type::Intersection(left, right) = expected else {
        return None;
    };
    effect_intersection_consumption_demand_pair(left, right)
        .or_else(|| effect_intersection_consumption_demand_pair(right, left))
}

pub(super) fn effect_intersection_consumption_demand_pair(
    tail: &Type,
    row: &Type,
) -> Option<EffectSubtractionDemand> {
    let Type::EffectRow(items) = row else {
        return None;
    };
    let Some(last) = items.last() else {
        return None;
    };
    if last != tail {
        return None;
    }
    let handled_items = items[..items.len() - 1].to_vec();
    if handled_items.is_empty() {
        return None;
    }
    Some(EffectSubtractionDemand {
        tail: tail.clone(),
        runtime_effect: row.clone(),
        handled_items,
    })
}

pub(super) fn effect_row_consumption_demand(expected: &Type) -> Option<EffectSubtractionDemand> {
    let Type::EffectRow(items) = expected else {
        return None;
    };
    let Some(Type::OpenVar(_)) = items.last() else {
        return None;
    };
    let handled_items = items[..items.len() - 1].to_vec();
    if handled_items.is_empty() {
        return None;
    }
    Some(EffectSubtractionDemand {
        tail: items[items.len() - 1].clone(),
        runtime_effect: expected.clone(),
        handled_items,
    })
}

pub(super) fn effect_row_from_parts(mut items: Vec<Type>, tail: Option<Type>) -> Type {
    if items.is_empty() && tail.is_some() {
        return tail.expect("tail is present");
    }
    match tail {
        Some(Type::EffectRow(tail_items)) => items.extend(tail_items),
        Some(tail) if tail.is_pure_effect() => {}
        Some(tail) => items.push(tail),
        None => {}
    }
    if items.is_empty() {
        Type::pure_effect()
    } else {
        types::simplify_type(Type::EffectRow(items))
    }
}

pub(super) fn residual_effect_after_consuming_handled_candidate(
    actual_items: Vec<Type>,
    actual_tail: Option<Type>,
    handled_items: &[Type],
) -> Type {
    let mut matched_handled = vec![false; handled_items.len()];
    let mut residual_items = Vec::new();
    for actual in actual_items {
        let Some(index) = handled_items
            .iter()
            .enumerate()
            .find_map(|(index, handled)| {
                (!matched_handled[index] && same_effect_row_family(&actual, handled))
                    .then_some(index)
            })
        else {
            residual_items.push(actual);
            continue;
        };
        matched_handled[index] = true;
    }
    effect_row_from_parts(residual_items, actual_tail)
}

pub(super) fn effect_lower_candidates_overlap(left: &Type, right: &Type) -> bool {
    let Some(left_items) = effect_candidate_items(left.clone()) else {
        return left == right;
    };
    let Some(right_items) = effect_candidate_items(right.clone()) else {
        return left == right;
    };
    left_items.iter().any(|left| {
        right_items
            .iter()
            .any(|right| same_effect_row_family(left, right))
    })
}

pub(super) fn empty_stack_weight() -> StackWeight {
    StackWeight {
        entries: Vec::new(),
    }
}

pub(super) fn stack_weight_is_empty(weight: &StackWeight) -> bool {
    weight.entries.is_empty()
}

pub(super) fn peel_stack_weight(mut ty: Type, mut weight: StackWeight) -> (Type, StackWeight) {
    while let Type::Stack {
        inner,
        weight: stack_weight,
    } = ty
    {
        weight = compose_stack_weights(stack_weight, weight);
        ty = *inner;
    }
    (ty, weight)
}

pub(super) fn compose_stack_weights(left: StackWeight, right: StackWeight) -> StackWeight {
    if left.entries.is_empty() {
        return right;
    }
    if right.entries.is_empty() {
        return left;
    }
    let mut out = left;
    for entry in right.entries {
        for families in entry.floor {
            push_stack_floor(&mut out, entry.id, families);
        }
        push_stack_pops(&mut out, entry.id, entry.pops);
        for families in entry.stack {
            push_stack_item(&mut out, entry.id, families);
        }
    }
    out
}

pub(super) fn compose_replay_stack_weights(left: StackWeight, right: StackWeight) -> StackWeight {
    saturate_unmatched_pops(compose_stack_weights(left, right))
}

pub(super) fn saturate_unmatched_pops(mut weight: StackWeight) -> StackWeight {
    for entry in &mut weight.entries {
        if entry.pops > 0 {
            entry.pops = u32::MAX;
        }
    }
    weight
}

pub(super) fn push_stack_floor(weight: &mut StackWeight, id: u32, families: EffectFamilies) {
    let entry = stack_weight_entry_mut(weight, id);
    let combined = entry
        .floor
        .drain(..)
        .fold(families, intersect_effect_families);
    if !matches!(combined, EffectFamilies::All) {
        entry.floor.push(normalize_effect_families(combined));
    }
    remove_empty_stack_weight_entry(weight, id);
}

pub(super) fn push_stack_item(weight: &mut StackWeight, id: u32, families: EffectFamilies) {
    let entry = stack_weight_entry_mut(weight, id);
    entry.stack.push(normalize_effect_families(families));
}

pub(super) fn push_stack_pops(weight: &mut StackWeight, id: u32, count: u32) {
    if count == 0 {
        return;
    }
    let entry = stack_weight_entry_mut(weight, id);
    if count == u32::MAX {
        entry.stack.clear();
        entry.pops = u32::MAX;
        return;
    }
    let removable = entry.stack.len().min(count as usize);
    if removable > 0 {
        entry.stack.truncate(entry.stack.len() - removable);
    }
    let remaining = count.saturating_sub(removable as u32);
    if remaining > 0 {
        entry.pops = entry.pops.saturating_add(remaining);
        if entry.pops == u32::MAX {
            entry.stack.clear();
        }
    }
    remove_empty_stack_weight_entry(weight, id);
}

pub(super) fn stack_weight_entry_mut(weight: &mut StackWeight, id: u32) -> &mut StackWeightEntry {
    match weight.entries.binary_search_by_key(&id, |entry| entry.id) {
        Ok(index) => &mut weight.entries[index],
        Err(index) => {
            weight.entries.insert(
                index,
                StackWeightEntry {
                    id,
                    pops: 0,
                    floor: Vec::new(),
                    stack: Vec::new(),
                },
            );
            &mut weight.entries[index]
        }
    }
}

pub(super) fn remove_empty_stack_weight_entry(weight: &mut StackWeight, id: u32) {
    if let Ok(index) = weight.entries.binary_search_by_key(&id, |entry| entry.id)
        && weight.entries[index].pops == 0
        && weight.entries[index].floor.is_empty()
        && weight.entries[index].stack.is_empty()
    {
        weight.entries.remove(index);
    }
}

pub(super) fn subtract_stack_weight(weight: StackWeight, removed: &[EffectFamily]) -> StackWeight {
    if removed.is_empty() {
        return weight;
    }

    let mut out = StackWeight {
        entries: Vec::new(),
    };
    for entry in weight.entries {
        let mut residual_parts = Vec::new();
        if entry.floor.is_empty() && entry.stack.is_empty() {
            residual_parts.push(subtract_effect_families(EffectFamilies::All, removed));
        } else {
            for families in &entry.floor {
                residual_parts.push(subtract_effect_families(families.clone(), removed));
            }
            for families in &entry.stack {
                residual_parts.push(subtract_effect_families(families.clone(), removed));
            }
        }
        if let Some(floor) = residual_parts.into_iter().reduce(intersect_effect_families) {
            push_stack_floor(&mut out, entry.id, floor);
        }
        push_stack_pops(&mut out, entry.id, entry.pops);
        for families in entry.stack {
            push_stack_item(
                &mut out,
                entry.id,
                subtract_effect_families(families, removed),
            );
        }
    }
    out
}

pub(super) fn subtract_effect_families(
    families: EffectFamilies,
    removed: &[EffectFamily],
) -> EffectFamilies {
    match families {
        EffectFamilies::Empty => EffectFamilies::Empty,
        EffectFamilies::All => all_except_effect_families(removed.iter().cloned()),
        EffectFamilies::Set(items) => set_effect_families(
            items
                .into_iter()
                .filter(|family| !effect_family_path_is_in(family, removed)),
        ),
        EffectFamilies::AllExcept(items) => {
            all_except_effect_families(items.into_iter().chain(removed.iter().cloned()))
        }
    }
}

pub(super) fn intersect_effect_families(
    left: EffectFamilies,
    right: EffectFamilies,
) -> EffectFamilies {
    match (left, right) {
        (EffectFamilies::Empty, _) | (_, EffectFamilies::Empty) => EffectFamilies::Empty,
        (EffectFamilies::All, right) | (right, EffectFamilies::All) => {
            normalize_effect_families(right)
        }
        (EffectFamilies::Set(left), EffectFamilies::Set(right)) => set_effect_families(
            left.into_iter()
                .filter(|family| effect_family_path_is_in(family, &right)),
        ),
        (EffectFamilies::Set(set), EffectFamilies::AllExcept(excluded))
        | (EffectFamilies::AllExcept(excluded), EffectFamilies::Set(set)) => set_effect_families(
            set.into_iter()
                .filter(|family| !effect_family_path_is_in(family, &excluded)),
        ),
        (EffectFamilies::AllExcept(left), EffectFamilies::AllExcept(right)) => {
            all_except_effect_families(left.into_iter().chain(right))
        }
    }
}

pub(super) fn normalize_effect_families(families: EffectFamilies) -> EffectFamilies {
    match families {
        EffectFamilies::Empty => EffectFamilies::Empty,
        EffectFamilies::All => EffectFamilies::All,
        EffectFamilies::Set(items) => set_effect_families(items),
        EffectFamilies::AllExcept(items) => all_except_effect_families(items),
    }
}

pub(super) fn stack_weight_allows_effect_item(weight: &StackWeight, item: &Type) -> bool {
    weight
        .entries
        .iter()
        .flat_map(|entry| entry.floor.iter().chain(&entry.stack))
        .all(|families| effect_families_allow_item(families, item))
}

pub(super) fn effect_families_allow_item(families: &EffectFamilies, item: &Type) -> bool {
    match families {
        EffectFamilies::Empty => false,
        EffectFamilies::All => true,
        EffectFamilies::Set(allowed) => allowed
            .iter()
            .any(|family| effect_family_matches_item(family, item)),
        EffectFamilies::AllExcept(excluded) => !excluded
            .iter()
            .any(|family| effect_family_matches_item(family, item)),
    }
}

pub(super) fn effect_family_matches_item(family: &EffectFamily, item: &Type) -> bool {
    let Type::Con { path, args } = item else {
        return false;
    };
    effect_path_contains_family(&family.path, path)
        && (family.args.is_empty() || args.len() == family.args.len())
}

pub(super) fn effect_families_from_items(items: &[Type]) -> Vec<EffectFamily> {
    let mut out = Vec::new();
    for item in items {
        if let Some(family) = effect_family_from_item(item)
            && !out
                .iter()
                .any(|existing: &EffectFamily| existing.path == family.path)
        {
            out.push(family);
        }
    }
    out
}

pub(super) fn sorted_effect_families(mut families: Vec<EffectFamily>) -> Vec<EffectFamily> {
    families.sort_by(|left, right| left.path.cmp(&right.path));
    families
}

pub(super) fn set_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> EffectFamilies {
    let items = collect_effect_families(items);
    match items.as_slice() {
        [] => EffectFamilies::Empty,
        _ => EffectFamilies::Set(items),
    }
}

pub(super) fn all_except_effect_families(
    items: impl IntoIterator<Item = EffectFamily>,
) -> EffectFamilies {
    let items = collect_effect_families(items);
    match items.as_slice() {
        [] => EffectFamilies::All,
        _ => EffectFamilies::AllExcept(items),
    }
}

pub(super) fn collect_effect_families(
    items: impl IntoIterator<Item = EffectFamily>,
) -> Vec<EffectFamily> {
    let mut out = Vec::new();
    for family in items {
        if !out
            .iter()
            .any(|existing: &EffectFamily| existing.path == family.path)
        {
            out.push(family);
        }
    }
    out.sort_by(|left, right| left.path.cmp(&right.path));
    out
}

pub(super) fn effect_family_path_is_in(family: &EffectFamily, items: &[EffectFamily]) -> bool {
    items
        .iter()
        .any(|item| effect_paths_same_family(&item.path, &family.path))
}
