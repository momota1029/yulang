use super::*;

pub(super) fn merge_effect_substitution(existing: Type, incoming: Type) -> Type {
    if existing.is_pure_effect() {
        return incoming;
    }
    if incoming.is_pure_effect() {
        return existing;
    }
    match (existing, incoming) {
        (Type::EffectRow(mut existing), Type::EffectRow(incoming)) => {
            for item in incoming {
                if !existing.contains(&item) {
                    existing.push(item);
                }
            }
            Type::EffectRow(existing)
        }
        (existing, incoming) => simplify_type(Type::Union(Box::new(existing), Box::new(incoming))),
    }
}

pub(super) fn stack_type(inner: Type, weight: mono::StackWeight) -> Type {
    if weight.entries.is_empty() {
        return inner;
    }
    simplify_stack_type(inner, weight)
}

pub(crate) fn simplify_stack_type(inner: Type, weight: mono::StackWeight) -> Type {
    if weight.entries.is_empty() {
        return inner;
    }
    if !type_may_contain_effects(&inner) {
        return inner;
    }
    if let Some(effect) = apply_stack_to_effect(inner.clone(), &weight) {
        return effect;
    }
    Type::Stack {
        inner: Box::new(inner),
        weight,
    }
}

pub(super) fn apply_stack_to_effect(effect: Type, weight: &mono::StackWeight) -> Option<Type> {
    match effect {
        Type::EffectRow(items) => Some(Type::EffectRow(filter_effect_row(items, weight))),
        Type::Intersection(left, right) => {
            let left = apply_stack_to_effect(*left, weight)?;
            let right = apply_stack_to_effect(*right, weight)?;
            Some(simplify_effect_intersection(left, right))
        }
        Type::Union(left, right) => {
            let left = apply_stack_to_effect(*left, weight)?;
            let right = apply_stack_to_effect(*right, weight)?;
            Some(simplify_effect_union(left, right))
        }
        Type::Any | Type::Never => Some(effect),
        Type::Stack {
            inner,
            weight: inner_weight,
        } => Some(stack_type(
            *inner,
            compose_runtime_stack_weights(inner_weight, weight.clone()),
        )),
        Type::Con { .. }
        | Type::Fun { .. }
        | Type::Thunk { .. }
        | Type::Record(_)
        | Type::PolyVariant(_)
        | Type::Tuple(_)
        | Type::OpenVar(_) => None,
    }
}

pub(super) fn filter_effect_row(items: Vec<Type>, weight: &mono::StackWeight) -> Vec<Type> {
    let mut out = Vec::new();
    for item in flatten_effect_row_items(items) {
        if effect_item_survives_stack(&item, weight) && !out.contains(&item) {
            out.push(item);
        }
    }
    out
}

pub(super) fn flatten_effect_row_items(items: Vec<Type>) -> Vec<Type> {
    let mut out = Vec::new();
    for item in items {
        match item {
            Type::EffectRow(nested) => out.extend(flatten_effect_row_items(nested)),
            other => out.push(other),
        }
    }
    out
}

pub(super) fn effect_item_survives_stack(item: &Type, weight: &mono::StackWeight) -> bool {
    weight
        .entries
        .iter()
        .all(|entry| stack_entry_allows_effect_item(entry, item))
}

pub(super) fn stack_entry_allows_effect_item(entry: &mono::StackWeightEntry, item: &Type) -> bool {
    if entry.floor.is_empty() && entry.stack.is_empty() {
        return entry.pops == 0;
    }
    entry
        .floor
        .iter()
        .chain(&entry.stack)
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

pub(super) fn effect_path_contains_family(family: &[String], item: &[String]) -> bool {
    !family.is_empty() && item.starts_with(family)
}

fn compose_runtime_stack_weights(
    left: mono::StackWeight,
    right: mono::StackWeight,
) -> mono::StackWeight {
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

fn push_stack_floor(weight: &mut mono::StackWeight, id: u32, families: EffectFamilies) {
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

fn push_stack_item(weight: &mut mono::StackWeight, id: u32, families: EffectFamilies) {
    let entry = stack_weight_entry_mut(weight, id);
    entry.stack.push(normalize_effect_families(families));
}

fn push_stack_pops(weight: &mut mono::StackWeight, id: u32, count: u32) {
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

fn stack_weight_entry_mut(weight: &mut mono::StackWeight, id: u32) -> &mut mono::StackWeightEntry {
    match weight.entries.binary_search_by_key(&id, |entry| entry.id) {
        Ok(index) => &mut weight.entries[index],
        Err(index) => {
            weight.entries.insert(
                index,
                mono::StackWeightEntry {
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

fn remove_empty_stack_weight_entry(weight: &mut mono::StackWeight, id: u32) {
    if let Ok(index) = weight.entries.binary_search_by_key(&id, |entry| entry.id)
        && weight.entries[index].pops == 0
        && weight.entries[index].floor.is_empty()
        && weight.entries[index].stack.is_empty()
    {
        weight.entries.remove(index);
    }
}

fn intersect_effect_families(left: EffectFamilies, right: EffectFamilies) -> EffectFamilies {
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

fn normalize_effect_families(families: EffectFamilies) -> EffectFamilies {
    match families {
        EffectFamilies::Empty => EffectFamilies::Empty,
        EffectFamilies::All => EffectFamilies::All,
        EffectFamilies::Set(items) => set_effect_families(items),
        EffectFamilies::AllExcept(items) => all_except_effect_families(items),
    }
}

fn set_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> EffectFamilies {
    let items = collect_effect_families(items);
    match items.as_slice() {
        [] => EffectFamilies::Empty,
        _ => EffectFamilies::Set(items),
    }
}

fn all_except_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> EffectFamilies {
    let items = collect_effect_families(items);
    match items.as_slice() {
        [] => EffectFamilies::All,
        _ => EffectFamilies::AllExcept(items),
    }
}

fn collect_effect_families(items: impl IntoIterator<Item = EffectFamily>) -> Vec<EffectFamily> {
    let mut out = Vec::new();
    for family in items {
        if !out
            .iter()
            .any(|existing: &EffectFamily| effect_paths_same_family(&existing.path, &family.path))
        {
            out.push(family);
        }
    }
    out.sort_by(|left, right| left.path.cmp(&right.path));
    out
}

fn effect_family_path_is_in(family: &EffectFamily, items: &[EffectFamily]) -> bool {
    items
        .iter()
        .any(|item| effect_paths_same_family(&item.path, &family.path))
}

fn effect_paths_same_family(left: &[String], right: &[String]) -> bool {
    effect_path_contains_family(left, right) || effect_path_contains_family(right, left)
}

pub(super) fn simplify_effect_intersection(left: Type, right: Type) -> Type {
    let simplified = simplify_intersection_type(left, right);
    if matches!(simplified, Type::Intersection(_, _)) {
        return simplified;
    }
    if simplified.is_pure_effect() {
        return Type::pure_effect();
    }
    simplified
}

pub(super) fn simplify_intersection_type(left: Type, right: Type) -> Type {
    let mut parts = Vec::new();
    collect_intersection_parts(left, &mut parts);
    collect_intersection_parts(right, &mut parts);
    if parts.iter().any(|part| matches!(part, Type::Never)) {
        return Type::Never;
    }
    let mut unique = Vec::new();
    for part in parts {
        if matches!(part, Type::Any) || unique.contains(&part) {
            continue;
        }
        unique.push(part);
    }
    match unique.as_slice() {
        [] => Type::Any,
        [single] => single.clone(),
        _ if let Some(candidate) = single_intersection_concrete_candidate(&unique) => candidate,
        _ if unique.iter().all(|part| matches!(part, Type::EffectRow(_))) => {
            intersect_effect_rows(unique)
        }
        _ if unique.iter().all(Type::is_pure_effect) => Type::pure_effect(),
        _ => unique
            .into_iter()
            .reduce(|left, right| Type::Intersection(Box::new(left), Box::new(right)))
            .expect("non-empty intersection parts"),
    }
}

pub(crate) fn simplify_type(ty: Type) -> Type {
    match ty {
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            arg: Box::new(simplify_type(*arg)),
            arg_effect: Box::new(simplify_type(*arg_effect)),
            ret_effect: Box::new(simplify_type(*ret_effect)),
            ret: Box::new(simplify_type(*ret)),
        },
        Type::Thunk { effect, value } => Type::Thunk {
            effect: Box::new(simplify_type(*effect)),
            value: Box::new(simplify_type(*value)),
        },
        Type::Con { path, args } => Type::Con {
            path,
            args: args.into_iter().map(simplify_type).collect(),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| TypeField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::PolyVariant(variants) => Type::PolyVariant(
            variants
                .into_iter()
                .map(|variant| TypeVariant {
                    name: variant.name,
                    payloads: variant.payloads.into_iter().map(simplify_type).collect(),
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(items.into_iter().map(simplify_type).collect()),
        Type::EffectRow(items) => simplify_effect_row(items),
        Type::Stack { inner, weight } => simplify_stack_type(simplify_type(*inner), weight),
        Type::Union(left, right) => {
            simplify_union_type(simplify_type(*left), simplify_type(*right))
        }
        Type::Intersection(left, right) => {
            simplify_intersection_type(simplify_type(*left), simplify_type(*right))
        }
        Type::Any | Type::Never | Type::OpenVar(_) => ty,
    }
}

pub(super) fn type_may_contain_effects(ty: &Type) -> bool {
    match ty {
        Type::Any
        | Type::OpenVar(_)
        | Type::EffectRow(_)
        | Type::Thunk { .. }
        | Type::Fun { .. } => true,
        Type::Con { args, .. } | Type::Tuple(args) => args.iter().any(type_may_contain_effects),
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_may_contain_effects(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_may_contain_effects)),
        Type::Stack { .. } => true,
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_may_contain_effects(left) || type_may_contain_effects(right)
        }
        Type::Never => false,
    }
}

pub(super) fn collect_intersection_parts(ty: Type, out: &mut Vec<Type>) {
    match ty {
        Type::Intersection(left, right) => {
            collect_intersection_parts(*left, out);
            collect_intersection_parts(*right, out);
        }
        ty => out.push(ty),
    }
}

pub(super) fn simplify_effect_union(left: Type, right: Type) -> Type {
    let simplified = simplify_union_type(left, right);
    if matches!(simplified, Type::Union(_, _)) {
        return simplified;
    }
    if simplified.is_pure_effect() {
        return Type::pure_effect();
    }
    simplified
}

pub(super) fn simplify_union_type(left: Type, right: Type) -> Type {
    if left == right {
        return left;
    }
    if matches!(left, Type::Never) {
        return right;
    }
    if matches!(right, Type::Never) {
        return left;
    }
    if matches!(left, Type::Any) || matches!(right, Type::Any) {
        return Type::Any;
    }
    if let (Type::EffectRow(left), Type::EffectRow(right)) = (left.clone(), right.clone()) {
        return union_effect_rows(left, right);
    }
    if left.is_pure_effect() && right.is_pure_effect() {
        return Type::pure_effect();
    }
    let mut parts = Vec::new();
    collect_union_parts(left, &mut parts);
    collect_union_parts(right, &mut parts);
    if let Some(candidate) = single_union_concrete_candidate(&parts) {
        return candidate;
    }
    parts
        .into_iter()
        .reduce(|left, right| Type::Union(Box::new(left), Box::new(right)))
        .expect("union parts should be non-empty")
}

pub(super) fn single_intersection_concrete_candidate(parts: &[Type]) -> Option<Type> {
    let candidate = single_concrete_candidate(parts)?;
    parts
        .iter()
        .all(|part| intersection_part_allows_candidate(part, &candidate))
        .then_some(candidate)
}

pub(super) fn single_union_concrete_candidate(parts: &[Type]) -> Option<Type> {
    let candidate = single_concrete_candidate(parts)?;
    parts
        .iter()
        .all(|part| matches!(part, Type::OpenVar(_)) || part == &candidate)
        .then_some(candidate)
}

pub(super) fn single_concrete_candidate(parts: &[Type]) -> Option<Type> {
    let mut candidate = None;
    for part in parts {
        if matches!(part, Type::OpenVar(_)) || type_contains_open_var(part) {
            continue;
        }
        if matches!(part, Type::Any | Type::Never | Type::EffectRow(_)) || part.is_pure_effect() {
            continue;
        }
        match &candidate {
            Some(existing) if existing != part => return None,
            Some(_) => {}
            None => candidate = Some(part.clone()),
        }
    }
    candidate
}

pub(super) fn intersection_part_allows_candidate(part: &Type, candidate: &Type) -> bool {
    if part == candidate || matches!(part, Type::OpenVar(_)) {
        return true;
    }
    let mut union_parts = Vec::new();
    collect_union_parts(part.clone(), &mut union_parts);
    union_parts.len() > 1
        && union_parts
            .iter()
            .all(|part| matches!(part, Type::OpenVar(_)) || part == candidate)
}

pub(super) fn collect_union_parts(ty: Type, out: &mut Vec<Type>) {
    match ty {
        Type::Union(left, right) => {
            collect_union_parts(*left, out);
            collect_union_parts(*right, out);
        }
        ty if out.contains(&ty) => {}
        ty => out.push(ty),
    }
}

pub(super) fn type_contains_open_var(ty: &Type) -> bool {
    match ty {
        Type::OpenVar(_) => true,
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_open_var(arg)
                || type_contains_open_var(arg_effect)
                || type_contains_open_var(ret_effect)
                || type_contains_open_var(ret)
        }
        Type::Thunk { effect, value } => {
            type_contains_open_var(effect) || type_contains_open_var(value)
        }
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_open_var)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_open_var(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_open_var)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_open_var(left) || type_contains_open_var(right)
        }
        Type::Stack { inner, .. } => type_contains_open_var(inner),
        Type::Any | Type::Never => false,
    }
}

pub(super) fn simplify_effect_row(items: Vec<Type>) -> Type {
    let mut out = Vec::new();
    push_effect_row_items(&mut out, items);
    Type::EffectRow(out)
}

pub(super) fn push_effect_row_items(out: &mut Vec<Type>, items: Vec<Type>) {
    for item in items {
        match simplify_type(item) {
            item if item.is_pure_effect() => {}
            Type::EffectRow(items) => push_effect_row_items(out, items),
            item if out.contains(&item) => {}
            item => {
                if let Some(existing) = out
                    .iter_mut()
                    .find(|existing| same_effect_item_path(existing, &item))
                {
                    *existing = merge_effect_row_item(existing.clone(), item);
                    continue;
                }
                out.push(item);
            }
        }
    }
}

pub(super) fn same_effect_item_path(left: &Type, right: &Type) -> bool {
    matches!(
        (left, right),
        (
            Type::Con {
                path: left_path,
                ..
            },
            Type::Con {
                path: right_path,
                ..
            },
        ) if left_path == right_path
    )
}

pub(super) fn merge_effect_row_item(existing: Type, incoming: Type) -> Type {
    let Type::Con {
        path,
        args: existing_args,
    } = existing
    else {
        return incoming;
    };
    let Type::Con {
        args: incoming_args,
        ..
    } = incoming
    else {
        return Type::Con {
            path,
            args: existing_args,
        };
    };
    if existing_args.len() != incoming_args.len() {
        return Type::Con {
            path,
            args: existing_args,
        };
    }
    let unit = Type::unit();
    let args = existing_args
        .into_iter()
        .zip(incoming_args)
        .map(|(existing, incoming)| {
            if existing == incoming || incoming == unit {
                existing
            } else if existing == unit {
                incoming
            } else {
                existing
            }
        })
        .collect();
    Type::Con { path, args }
}

pub(super) fn union_effect_rows(left: Vec<Type>, right: Vec<Type>) -> Type {
    let mut out = Vec::new();
    push_effect_row_items(&mut out, left);
    push_effect_row_items(&mut out, right);
    Type::EffectRow(out)
}

pub(super) fn intersect_effect_rows(rows: Vec<Type>) -> Type {
    let mut rows = rows.into_iter().map(effect_row_items);
    let Some(first) = rows.next() else {
        return Type::pure_effect();
    };
    let mut out = first;
    for row in rows {
        out.retain(|item| row.contains(item));
    }
    Type::EffectRow(out)
}

pub(super) fn effect_row_items(row: Type) -> Vec<Type> {
    let Type::EffectRow(items) = row else {
        return Vec::new();
    };
    let mut out = Vec::new();
    push_effect_row_items(&mut out, items);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn con(path: &[&str]) -> Type {
        Type::Con {
            path: path.iter().map(|segment| (*segment).to_string()).collect(),
            args: Vec::new(),
        }
    }

    fn family(path: &[&str]) -> EffectFamily {
        EffectFamily {
            path: path.iter().map(|segment| (*segment).to_string()).collect(),
            args: Vec::new(),
        }
    }

    fn stack_weight_entry(
        pops: u32,
        floor: Vec<EffectFamilies>,
        stack: Vec<EffectFamilies>,
    ) -> mono::StackWeight {
        mono::StackWeight {
            entries: vec![mono::StackWeightEntry {
                id: 0,
                pops,
                floor,
                stack,
            }],
        }
    }

    #[test]
    fn concrete_effect_row_does_not_survive_pop_only_stack_entry() {
        let signal = con(&["signal"]);
        let weight = stack_weight_entry(1, Vec::new(), Vec::new());

        assert_eq!(
            simplify_stack_type(Type::EffectRow(vec![signal]), weight),
            Type::pure_effect()
        );
    }

    #[test]
    fn concrete_effect_row_respects_floor_below_unmatched_pop() {
        let signal = con(&["signal"]);
        let other = con(&["other"]);
        let weight = stack_weight_entry(
            u32::MAX,
            vec![EffectFamilies::AllExcept(vec![family(&["signal"])])],
            Vec::new(),
        );

        assert_eq!(
            simplify_stack_type(Type::EffectRow(vec![signal, other.clone()]), weight),
            Type::EffectRow(vec![other])
        );
    }

    #[test]
    fn nested_stack_weights_compose_before_filtering_effect_rows() {
        let signal = con(&["signal"]);
        let push_signal = stack_weight_entry(
            0,
            Vec::new(),
            vec![EffectFamilies::Set(vec![family(&["signal"])])],
        );
        let pop = stack_weight_entry(1, Vec::new(), Vec::new());
        let nested = Type::Stack {
            inner: Box::new(Type::EffectRow(vec![signal.clone()])),
            weight: push_signal,
        };

        assert_eq!(
            simplify_stack_type(nested, pop),
            Type::EffectRow(vec![signal])
        );
    }
}
