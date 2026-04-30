use std::collections::{HashMap, HashSet};

use crate::ids::TypeVar;
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactRow, CompactType, merge_compact_types,
};
use crate::symbols::Path;

pub(crate) fn normalize_rewritten_bounds(mut bounds: CompactBounds) -> CompactBounds {
    normalize_rewritten_compact_type_in_place(&mut bounds.lower, true);
    normalize_rewritten_compact_type_in_place(&mut bounds.upper, false);
    cancel_shared_vars_with_variable_extras(&mut bounds);
    absorb_upper_vars_from_row_lower(&mut bounds);
    collapse_root_self_alias_if_shaped(&mut bounds);
    bounds
}

fn normalize_rewritten_compact_type_in_place(ty: &mut CompactType, positive: bool) {
    coalesce_effect_atom_interval_args_in_type(ty);
    for con in &mut ty.cons {
        for arg in &mut con.args {
            normalize_rewritten_bounds_in_place(arg);
        }
    }
    for fun in &mut ty.funs {
        normalize_rewritten_compact_type_in_place(&mut fun.arg, !positive);
        normalize_rewritten_compact_type_in_place(&mut fun.arg_eff, !positive);
        normalize_rewritten_compact_type_in_place(&mut fun.ret_eff, positive);
        normalize_rewritten_compact_type_in_place(&mut fun.ret, positive);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            normalize_rewritten_compact_type_in_place(&mut field.value, positive);
        }
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                normalize_rewritten_compact_type_in_place(payload, positive);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            normalize_rewritten_compact_type_in_place(item, positive);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            normalize_rewritten_compact_type_in_place(item, positive);
        }
        normalize_rewritten_compact_type_in_place(&mut row.tail, positive);
    }
    merge_same_effect_rows_in_type(ty, positive);
    simplify_row_tail_absorption_in_type(ty);
    simplify_same_items_rows_in_type(ty, positive);
    simplify_same_tail_rows_in_type(ty, positive);
}

fn normalize_rewritten_bounds_in_place(bounds: &mut CompactBounds) {
    normalize_rewritten_compact_type_in_place(&mut bounds.lower, true);
    normalize_rewritten_compact_type_in_place(&mut bounds.upper, false);
    cancel_shared_vars_with_variable_extras(bounds);
    absorb_upper_vars_from_row_lower(bounds);
}

fn cancel_shared_vars_with_variable_extras(bounds: &mut CompactBounds) {
    let (Some(lower), Some(upper)) = (var_only_set(&bounds.lower), var_only_set(&bounds.upper))
    else {
        return;
    };
    let common = lower.intersection(&upper).copied().collect::<Vec<_>>();
    if common.is_empty() || lower.len() == common.len() || upper.len() == common.len() {
        return;
    }

    for tv in common {
        if bounds.self_var == Some(tv) {
            continue;
        }
        bounds.lower.vars.remove(&tv);
        bounds.upper.vars.remove(&tv);
    }
}

fn absorb_upper_vars_from_row_lower(bounds: &mut CompactBounds) {
    let Some(upper) = var_only_set(&bounds.upper) else {
        return;
    };
    if upper.is_empty()
        || bounds.lower.rows.is_empty()
        || !bounds.lower.prims.is_empty()
        || !bounds.lower.cons.is_empty()
        || !bounds.lower.funs.is_empty()
        || !bounds.lower.records.is_empty()
        || !bounds.lower.variants.is_empty()
        || !bounds.lower.tuples.is_empty()
        || !upper.is_subset(&bounds.lower.vars)
    {
        return;
    }

    for tv in upper {
        if bounds.self_var == Some(tv) {
            continue;
        }
        bounds.lower.vars.remove(&tv);
        bounds.upper.vars.remove(&tv);
    }
}

fn collapse_root_self_alias_if_shaped(bounds: &mut CompactBounds) {
    let Some(self_var) = bounds.self_var else {
        return;
    };
    if !bounds.lower.vars.contains(&self_var) || !bounds.upper.vars.contains(&self_var) {
        return;
    }
    if !is_var_only_type(&bounds.upper) {
        return;
    }
    if !has_non_var_shape(&bounds.lower) && !has_non_var_shape(&bounds.upper) {
        return;
    }

    bounds.lower.vars.remove(&self_var);
    bounds.upper.vars.remove(&self_var);
    if bounds.lower.vars.is_empty() && bounds.upper.vars.is_empty() {
        bounds.self_var = None;
    }
}

fn coalesce_effect_atom_interval_args_in_type(ty: &mut CompactType) {
    for con in &mut ty.cons {
        coalesce_effect_atom_interval_args_in_con(con);
    }
}

fn coalesce_effect_atom_interval_args_in_con(con: &mut CompactCon) {
    let mut effect_pairs = HashSet::new();
    let mut effect_equal_sets = Vec::new();
    let mut direct_pairs = HashSet::new();
    for arg in &con.args {
        collect_effect_atom_interval_pairs(&arg.lower, &mut effect_pairs, &mut effect_equal_sets);
        collect_effect_atom_interval_pairs(&arg.upper, &mut effect_pairs, &mut effect_equal_sets);
        if let Some(pair) = single_var_interval_pair(arg) {
            direct_pairs.insert(pair);
        }
    }

    let mut subst = HashMap::new();
    for &(lower, upper) in direct_pairs.intersection(&effect_pairs) {
        if lower != upper {
            subst.insert(upper, lower);
        }
    }
    for (lower, upper) in direct_pairs {
        if lower == upper {
            continue;
        }
        if effect_equal_sets
            .iter()
            .any(|set| set.contains(&lower) && set.contains(&upper))
        {
            subst.insert(upper, lower);
        }
    }
    if !subst.is_empty() {
        for arg in &mut con.args {
            rewrite_compact_bounds_vars_in_place(arg, &subst);
        }
    }
}

fn collect_effect_atom_interval_pairs(
    ty: &CompactType,
    pairs: &mut HashSet<(TypeVar, TypeVar)>,
    equal_sets: &mut Vec<HashSet<TypeVar>>,
) {
    for row in &ty.rows {
        for item in &row.items {
            collect_effect_item_interval_pairs(item, pairs, equal_sets);
        }
    }
    for fun in &ty.funs {
        collect_effect_atom_interval_pairs(&fun.arg_eff, pairs, equal_sets);
        collect_effect_atom_interval_pairs(&fun.ret_eff, pairs, equal_sets);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_effect_atom_interval_pairs(&field.value, pairs, equal_sets);
        }
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_effect_atom_interval_pairs(payload, pairs, equal_sets);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_effect_atom_interval_pairs(item, pairs, equal_sets);
        }
    }
}

fn collect_effect_item_interval_pairs(
    item: &CompactType,
    pairs: &mut HashSet<(TypeVar, TypeVar)>,
    equal_sets: &mut Vec<HashSet<TypeVar>>,
) {
    for con in &item.cons {
        for arg in &con.args {
            if let Some(pair) = single_var_interval_pair(arg) {
                pairs.insert(pair);
            } else if let Some(vars) = same_var_interval_set(arg) {
                equal_sets.push(vars);
            }
        }
    }
}

fn single_var_interval_pair(bounds: &CompactBounds) -> Option<(TypeVar, TypeVar)> {
    Some((
        single_var_compact_type(&bounds.lower)?,
        single_var_compact_type(&bounds.upper)?,
    ))
}

fn same_var_interval_set(bounds: &CompactBounds) -> Option<HashSet<TypeVar>> {
    let lower = var_only_set(&bounds.lower)?;
    let upper = var_only_set(&bounds.upper)?;
    (lower.len() > 1 && lower == upper).then_some(lower)
}

fn single_var_compact_type(ty: &CompactType) -> Option<TypeVar> {
    (ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.iter().copied().next())
    .flatten()
}

fn is_var_only_type(ty: &CompactType) -> bool {
    ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn has_non_var_shape(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn rewrite_compact_bounds_vars_in_place(
    bounds: &mut CompactBounds,
    subst: &HashMap<TypeVar, TypeVar>,
) {
    if let Some(self_var) = bounds.self_var {
        bounds.self_var = Some(rewrite_compact_var(self_var, subst));
    }
    rewrite_compact_type_vars_in_place(&mut bounds.lower, subst);
    rewrite_compact_type_vars_in_place(&mut bounds.upper, subst);
}

fn rewrite_compact_type_vars_in_place(ty: &mut CompactType, subst: &HashMap<TypeVar, TypeVar>) {
    ty.vars = ty
        .vars
        .iter()
        .map(|&tv| rewrite_compact_var(tv, subst))
        .collect();
    for con in &mut ty.cons {
        for arg in &mut con.args {
            rewrite_compact_bounds_vars_in_place(arg, subst);
        }
    }
    for fun in &mut ty.funs {
        rewrite_compact_type_vars_in_place(&mut fun.arg, subst);
        rewrite_compact_type_vars_in_place(&mut fun.arg_eff, subst);
        rewrite_compact_type_vars_in_place(&mut fun.ret_eff, subst);
        rewrite_compact_type_vars_in_place(&mut fun.ret, subst);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            rewrite_compact_type_vars_in_place(&mut field.value, subst);
        }
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                rewrite_compact_type_vars_in_place(payload, subst);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            rewrite_compact_type_vars_in_place(item, subst);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            rewrite_compact_type_vars_in_place(item, subst);
        }
        rewrite_compact_type_vars_in_place(&mut row.tail, subst);
    }
}

fn rewrite_compact_var(tv: TypeVar, subst: &HashMap<TypeVar, TypeVar>) -> TypeVar {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(&next) = subst.get(&cur) {
        if next == cur || !seen.insert(cur) {
            break;
        }
        cur = next;
    }
    cur
}

fn merge_same_effect_rows_in_type(ty: &mut CompactType, positive: bool) {
    for row in &mut ty.rows {
        row.items = merge_same_effect_items(positive, std::mem::take(&mut row.items));
    }
}

fn merge_same_effect_items(positive: bool, items: Vec<CompactType>) -> Vec<CompactType> {
    let mut out = Vec::new();
    let mut keyed = HashMap::new();
    for item in items {
        if let Some(key) = single_effect_item_key(&item) {
            if let Some(&index) = keyed.get(&key) {
                let existing = std::mem::take(&mut out[index]);
                out[index] = merge_compact_types(positive, existing, item);
                continue;
            }
            keyed.insert(key, out.len());
        }
        if !out.contains(&item) {
            out.push(item);
        }
    }
    out
}

fn single_effect_item_key(item: &CompactType) -> Option<(Path, usize)> {
    if !item.vars.is_empty()
        || !item.funs.is_empty()
        || !item.records.is_empty()
        || !item.variants.is_empty()
        || !item.tuples.is_empty()
        || !item.rows.is_empty()
    {
        return None;
    }
    if item.prims.len() == 1 && item.cons.is_empty() {
        return item.prims.iter().next().cloned().map(|path| (path, 0));
    }
    if item.cons.len() == 1 && item.prims.is_empty() {
        let con = &item.cons[0];
        return Some((con.path.clone(), con.args.len()));
    }
    None
}

fn simplify_row_tail_absorption_in_type(ty: &mut CompactType) {
    ty.vars
        .retain(|tv| !ty.rows.iter().any(|row| row_tail_is_exact_var(row, *tv)));
}

fn simplify_same_tail_rows_in_type(ty: &mut CompactType, positive: bool) {
    let mut keep = vec![true; ty.rows.len()];
    for i in 0..ty.rows.len() {
        for j in 0..ty.rows.len() {
            if i == j || !keep[j] {
                continue;
            }
            let lhs = &ty.rows[i];
            let rhs = &ty.rows[j];
            if lhs.tail != rhs.tail {
                continue;
            }
            let lhs_contains_rhs = rhs.items.iter().all(|item| lhs.items.contains(item));
            let rhs_contains_lhs = lhs.items.iter().all(|item| rhs.items.contains(item));
            if positive {
                if lhs_contains_rhs && lhs.items.len() > rhs.items.len() {
                    keep[j] = false;
                } else if rhs_contains_lhs && rhs.items.len() > lhs.items.len() {
                    keep[i] = false;
                }
            } else if lhs_contains_rhs && lhs.items.len() < rhs.items.len() {
                keep[j] = false;
            } else if rhs_contains_lhs && rhs.items.len() < lhs.items.len() {
                keep[i] = false;
            }
        }
    }
    let mut idx = 0usize;
    ty.rows.retain(|_| {
        let keep_row = keep[idx];
        idx += 1;
        keep_row
    });
}

fn simplify_same_items_rows_in_type(ty: &mut CompactType, positive: bool) {
    let mut keep = vec![true; ty.rows.len()];
    for i in 0..ty.rows.len() {
        for j in 0..ty.rows.len() {
            if i == j || !keep[j] {
                continue;
            }
            let lhs = &ty.rows[i];
            let rhs = &ty.rows[j];
            if !same_row_items(lhs, rhs) {
                continue;
            }

            let lhs_closed = is_empty_compact_type(&lhs.tail);
            let rhs_closed = is_empty_compact_type(&rhs.tail);
            if lhs_closed == rhs_closed {
                continue;
            }

            if positive {
                if lhs_closed {
                    keep[i] = false;
                } else {
                    keep[j] = false;
                }
            } else if lhs_closed {
                keep[j] = false;
            } else {
                keep[i] = false;
            }
        }
    }

    let mut idx = 0usize;
    ty.rows.retain(|_| {
        let keep_row = keep[idx];
        idx += 1;
        keep_row
    });
}

fn same_row_items(lhs: &CompactRow, rhs: &CompactRow) -> bool {
    lhs.items.len() == rhs.items.len() && lhs.items.iter().all(|item| rhs.items.contains(item))
}

fn row_tail_is_exact_var(row: &CompactRow, tv: TypeVar) -> bool {
    single_var_tail(row).is_some_and(|tail_tv| tail_tv == tv)
}

fn single_var_tail(row: &CompactRow) -> Option<TypeVar> {
    let tail = row.tail.as_ref();
    (tail.vars.len() == 1
        && tail.prims.is_empty()
        && tail.cons.is_empty()
        && tail.funs.is_empty()
        && tail.records.is_empty()
        && tail.variants.is_empty()
        && tail.tuples.is_empty()
        && tail.rows.is_empty())
    .then(|| tail.vars.iter().copied().next())
    .flatten()
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn var_only_set(ty: &CompactType) -> Option<HashSet<TypeVar>> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.clone())
}
