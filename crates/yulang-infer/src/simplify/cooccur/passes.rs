use std::collections::{HashMap, HashSet};

use crate::ids::TypeVar;
use crate::symbols::Path;

use super::group::{GroupCoOccurrences, indistinguishable_group_replacements};
use super::{
    AlongItem, CoOccurrences, CompactBounds, CompactRoleConstraint, CompactType, CompactTypeScheme,
    ExactInfo, has_matching_polar_signature, is_effectively_recursive, merge_compact_bounds,
    merge_compact_types, rewrite_bounds,
};

pub(super) fn apply_group_co_occurrence_substitutions(
    analysis: &GroupCoOccurrences,
    cooccurs: &mut CoOccurrences,
    rec_vars: &mut HashMap<TypeVar, CompactBounds>,
    protected_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    for (replacements, require_matching_polar_exact) in [
        (
            indistinguishable_group_replacements(&analysis.types, true),
            false,
        ),
        (
            indistinguishable_group_replacements(&analysis.effect_types, true),
            false,
        ),
        (
            indistinguishable_group_replacements(&analysis.effects, true),
            true,
        ),
    ] {
        let accepted = collect_group_replacements(
            replacements,
            cooccurs,
            rec_vars,
            protected_vars,
            subst,
            require_matching_polar_exact,
        );
        if accepted.is_empty() {
            continue;
        }
        subst.extend(accepted.iter().map(|(&from, &to)| (from, Some(to))));
        rewrite_occurrence_info(cooccurs, &accepted);
        rewrite_recursive_bounds(rec_vars, &accepted);
    }
}

pub(super) fn apply_row_residual_unifications(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    rec_vars: &mut HashMap<TypeVar, CompactBounds>,
    cooccurs: &mut CoOccurrences,
    protected_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) -> HashSet<TypeVar> {
    let mut classes = HashMap::<RowResidualKey, Vec<RowResidualOccurrence>>::new();
    collect_row_residuals_in_bounds(&scheme.cty, true, subst, &mut classes);
    let mut rec_var_items = rec_vars.iter().collect::<Vec<_>>();
    rec_var_items.sort_by_key(|(tv, _)| tv.0);
    for (_, bounds) in rec_var_items {
        collect_row_residuals_in_bounds(bounds, true, subst, &mut classes);
    }
    for constraint in constraints {
        for arg in &constraint.args {
            collect_row_residuals_in_bounds(arg, true, subst, &mut classes);
        }
    }

    let mut accepted = HashMap::<TypeVar, TypeVar>::new();
    let mut residual_representatives = HashSet::<TypeVar>::new();
    for occurrences in classes.values() {
        let has_positive = occurrences.iter().any(|occurrence| occurrence.positive);
        let has_negative = occurrences.iter().any(|occurrence| !occurrence.positive);
        if !has_positive || !has_negative {
            continue;
        }

        if let Some(representative) = accept_var_class(
            occurrences.iter().map(|occurrence| occurrence.tv),
            protected_vars,
            subst,
            &mut accepted,
        ) {
            residual_representatives.insert(representative);
        }
        if let Some(first) = occurrences.first() {
            for arg_index in 0..first.arg_vars.len() {
                accept_var_class(
                    occurrences
                        .iter()
                        .flat_map(|occurrence| occurrence.arg_vars[arg_index].iter().copied()),
                    protected_vars,
                    subst,
                    &mut accepted,
                );
            }
        }
    }

    if accepted.is_empty() {
        return HashSet::new();
    }

    residual_representatives = residual_representatives
        .into_iter()
        .map(|tv| rewrite_group_var(tv, &accepted))
        .collect();
    subst.extend(accepted.iter().map(|(&from, &to)| (from, Some(to))));
    rewrite_occurrence_info(cooccurs, &accepted);
    rewrite_recursive_bounds(rec_vars, &accepted);
    residual_representatives
}

pub(super) fn expose_positive_row_residual_tails(
    scheme: &mut CompactTypeScheme,
    residual_vars: &HashSet<TypeVar>,
) {
    if residual_vars.is_empty() {
        return;
    }
    expose_positive_row_residual_tails_in_bounds(&mut scheme.cty, residual_vars);
    for bounds in scheme.rec_vars.values_mut() {
        expose_positive_row_residual_tails_in_bounds(bounds, residual_vars);
    }
}

fn expose_positive_row_residual_tails_in_bounds(
    bounds: &mut CompactBounds,
    residual_vars: &HashSet<TypeVar>,
) {
    expose_positive_row_residual_tails_in_type(&mut bounds.lower, true, false, residual_vars);
    expose_positive_row_residual_tails_in_type(&mut bounds.upper, false, false, residual_vars);
}

fn expose_positive_row_residual_tails_in_type(
    ty: &mut CompactType,
    positive: bool,
    expose_current_row: bool,
    residual_vars: &HashSet<TypeVar>,
) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            expose_positive_row_residual_tails_in_bounds(arg, residual_vars);
        }
    }
    for fun in &mut ty.funs {
        expose_positive_row_residual_tails_in_type(&mut fun.arg, !positive, false, residual_vars);
        expose_positive_row_residual_tails_in_type(
            &mut fun.arg_eff,
            !positive,
            false,
            residual_vars,
        );
        expose_positive_row_residual_tails_in_type(&mut fun.ret_eff, positive, true, residual_vars);
        expose_positive_row_residual_tails_in_type(&mut fun.ret, positive, false, residual_vars);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            expose_positive_row_residual_tails_in_type(
                &mut field.value,
                positive,
                false,
                residual_vars,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            expose_positive_row_residual_tails_in_type(
                &mut field.value,
                positive,
                false,
                residual_vars,
            );
        }
        expose_positive_row_residual_tails_in_type(
            &mut spread.tail,
            positive,
            false,
            residual_vars,
        );
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                expose_positive_row_residual_tails_in_type(payload, positive, false, residual_vars);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            expose_positive_row_residual_tails_in_type(item, positive, false, residual_vars);
        }
    }

    let mut exposed_tail_types = Vec::new();
    for row in &mut ty.rows {
        for item in &mut row.items {
            expose_positive_row_residual_tails_in_type(item, positive, false, residual_vars);
        }
        expose_positive_row_residual_tails_in_type(&mut row.tail, positive, false, residual_vars);
        if expose_current_row
            && positive
            && !row.items.is_empty()
            && is_row_residual_tail_for_vars(&row.tail, residual_vars)
        {
            exposed_tail_types.push(std::mem::take(&mut *row.tail));
        }
    }
    for tail in exposed_tail_types {
        let current = std::mem::take(ty);
        *ty = merge_compact_types(true, current, tail);
    }
}

fn is_row_residual_tail_for_vars(tail: &CompactType, residual_vars: &HashSet<TypeVar>) -> bool {
    !tail.vars.is_empty()
        && tail.vars.iter().all(|tv| residual_vars.contains(tv))
        && tail.prims.is_empty()
        && tail.cons.is_empty()
        && tail.funs.is_empty()
        && tail.records.is_empty()
        && tail.record_spreads.is_empty()
        && tail.variants.is_empty()
        && tail.tuples.is_empty()
        && tail.rows.is_empty()
}

pub(super) fn apply_exact_row_unifications(
    all_vars: &[TypeVar],
    exact_info: &ExactInfo,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    protected_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    let mut representatives = HashMap::new();
    for &var in all_vars {
        if subst.contains_key(&var) || !exact_info.has_concrete_row(var) {
            continue;
        }
        if protected_vars.contains(&var) {
            continue;
        }
        let key = (
            is_effectively_recursive(var, rec_vars),
            exact_info.signature(var),
        );
        if let Some(&representative) = representatives.get(&key) {
            subst.insert(var, Some(representative));
        } else {
            representatives.insert(key, var);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowResidualKey(Vec<RowItemShape>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RowItemShape {
    path: Path,
    arity: usize,
}

#[derive(Debug, Clone)]
struct RowResidualOccurrence {
    tv: TypeVar,
    positive: bool,
    arg_vars: Vec<Vec<TypeVar>>,
}

fn collect_row_residuals_in_bounds(
    bounds: &CompactBounds,
    positive: bool,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    classes: &mut HashMap<RowResidualKey, Vec<RowResidualOccurrence>>,
) {
    collect_row_residuals_in_type(&bounds.lower, positive, subst, classes);
    collect_row_residuals_in_type(&bounds.upper, !positive, subst, classes);
}

fn collect_row_residuals_in_type(
    ty: &CompactType,
    positive: bool,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    classes: &mut HashMap<RowResidualKey, Vec<RowResidualOccurrence>>,
) {
    for con in &ty.cons {
        for arg in &con.args {
            collect_row_residuals_in_bounds(arg, true, subst, classes);
        }
    }
    for fun in &ty.funs {
        collect_row_residuals_in_type(&fun.arg, !positive, subst, classes);
        collect_row_residuals_in_type(&fun.arg_eff, !positive, subst, classes);
        collect_row_residuals_in_type(&fun.ret_eff, positive, subst, classes);
        collect_row_residuals_in_type(&fun.ret, positive, subst, classes);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_row_residuals_in_type(&field.value, positive, subst, classes);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_row_residuals_in_type(&field.value, positive, subst, classes);
        }
        collect_row_residuals_in_type(&spread.tail, positive, subst, classes);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_row_residuals_in_type(payload, positive, subst, classes);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_row_residuals_in_type(item, positive, subst, classes);
        }
    }
    for row in &ty.rows {
        if let Some((key, arg_vars)) = row_residual_key_and_args(&row.items, subst) {
            for tv in row_tail_vars(&row.tail, subst) {
                classes
                    .entry(key.clone())
                    .or_default()
                    .push(RowResidualOccurrence {
                        tv,
                        positive,
                        arg_vars: arg_vars.clone(),
                    });
            }
        }
        for item in &row.items {
            collect_row_residuals_in_type(item, positive, subst, classes);
        }
        collect_row_residuals_in_type(&row.tail, positive, subst, classes);
    }
}

fn row_residual_key_and_args(
    items: &[CompactType],
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> Option<(RowResidualKey, Vec<Vec<TypeVar>>)> {
    if items.is_empty() {
        return None;
    }
    let mut entries = Vec::new();
    for item in items {
        if is_generated_local_effect_item(item) {
            continue;
        }
        entries.push(row_item_shape_and_args(item, subst)?);
    }
    if entries.is_empty() {
        return None;
    }
    entries.sort_by(|(lhs, _), (rhs, _)| {
        row_item_shape_sort_key(lhs).cmp(&row_item_shape_sort_key(rhs))
    });
    let mut shapes = Vec::new();
    let mut arg_vars = Vec::new();
    for (shape, args) in entries {
        shapes.push(shape);
        arg_vars.extend(args);
    }
    Some((RowResidualKey(shapes), arg_vars))
}

fn is_generated_local_effect_item(item: &CompactType) -> bool {
    item.vars.is_empty()
        && item.prims.is_empty()
        && item.cons.len() == 1
        && item
            .cons
            .first()
            .is_some_and(|con| is_generated_local_effect_path(&con.path))
        && item.funs.is_empty()
        && item.records.is_empty()
        && item.record_spreads.is_empty()
        && item.variants.is_empty()
        && item.tuples.is_empty()
        && item.rows.is_empty()
}

fn is_generated_local_effect_path(path: &Path) -> bool {
    path.segments
        .first()
        .is_some_and(|segment| segment.0.starts_with('&'))
}

fn row_item_shape_sort_key(shape: &RowItemShape) -> (String, usize) {
    (
        shape
            .path
            .segments
            .iter()
            .map(|segment| segment.0.as_str())
            .collect::<Vec<_>>()
            .join("::"),
        shape.arity,
    )
}

fn row_item_shape_and_args(
    item: &CompactType,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> Option<(RowItemShape, Vec<Vec<TypeVar>>)> {
    if !item.vars.is_empty()
        || !item.funs.is_empty()
        || !item.records.is_empty()
        || !item.record_spreads.is_empty()
        || !item.variants.is_empty()
        || !item.tuples.is_empty()
        || !item.rows.is_empty()
    {
        return None;
    }
    if item.prims.len() == 1 && item.cons.is_empty() {
        let path = item.prims.iter().next().cloned()?;
        return Some((RowItemShape { path, arity: 0 }, Vec::new()));
    }
    if item.cons.len() == 1 && item.prims.is_empty() {
        let con = &item.cons[0];
        let args = con
            .args
            .iter()
            .map(|arg| row_item_arg_vars(arg, subst))
            .collect::<Option<Vec<_>>>()?;
        return Some((
            RowItemShape {
                path: con.path.clone(),
                arity: con.args.len(),
            },
            args,
        ));
    }
    None
}

fn row_item_arg_vars(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> Option<Vec<TypeVar>> {
    let lower = row_arg_side_vars(&bounds.lower, subst)?;
    let upper = row_arg_side_vars(&bounds.upper, subst)?;
    let mut vars = lower.into_iter().chain(upper).collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    vars.dedup();
    (!vars.is_empty()).then_some(vars)
}

fn row_arg_side_vars(
    ty: &CompactType,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> Option<Vec<TypeVar>> {
    if !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    let mut vars = ty
        .vars
        .iter()
        .filter_map(|&tv| rewrite_optional_var(tv, subst))
        .collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    vars.dedup();
    Some(vars)
}

fn row_tail_vars(tail: &CompactType, subst: &HashMap<TypeVar, Option<TypeVar>>) -> Vec<TypeVar> {
    if !tail.prims.is_empty()
        || !tail.cons.is_empty()
        || !tail.funs.is_empty()
        || !tail.records.is_empty()
        || !tail.record_spreads.is_empty()
        || !tail.variants.is_empty()
        || !tail.tuples.is_empty()
        || !tail.rows.is_empty()
    {
        return Vec::new();
    }

    let mut vars = tail
        .vars
        .iter()
        .filter_map(|&tv| rewrite_optional_var(tv, subst))
        .collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    vars.dedup();
    vars
}

fn rewrite_optional_var(tv: TypeVar, subst: &HashMap<TypeVar, Option<TypeVar>>) -> Option<TypeVar> {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(next) = subst.get(&cur) {
        if !seen.insert(cur) {
            break;
        }
        match *next {
            Some(next) if next != cur => cur = next,
            Some(_) => break,
            None => return None,
        }
    }
    Some(cur)
}

fn accept_var_class(
    vars: impl Iterator<Item = TypeVar>,
    protected_vars: &HashSet<TypeVar>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    accepted: &mut HashMap<TypeVar, TypeVar>,
) -> Option<TypeVar> {
    let mut vars = vars
        .filter_map(|tv| rewrite_optional_var(tv, subst))
        .collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    vars.dedup();
    if vars.is_empty() {
        return None;
    }
    let representative = vars
        .iter()
        .copied()
        .find(|tv| protected_vars.contains(tv))
        .unwrap_or(vars[0]);
    if vars.len() < 2 {
        return Some(representative);
    }
    for var in vars {
        if var == representative
            || protected_vars.contains(&var)
            || subst.contains_key(&var)
            || accepted.contains_key(&var)
        {
            continue;
        }
        accepted.insert(var, representative);
    }
    Some(representative)
}

pub(super) fn apply_exact_sandwich_removal(
    all_vars: &[TypeVar],
    exact_info: &ExactInfo,
    protected_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    for &var in all_vars {
        if subst.contains_key(&var) {
            continue;
        }
        if protected_vars.contains(&var) {
            continue;
        }
        for positive in [true, false] {
            let Some(exacts) = exact_info.exact_occurrences(positive, var) else {
                continue;
            };
            let Some(opposite) = exact_info.exact_occurrences(!positive, var) else {
                continue;
            };
            if exacts.iter().any(|exact| opposite.contains(exact)) {
                subst.insert(var, None);
                break;
            }
        }
    }
}

pub(super) fn apply_shadow_var_collapse(
    all_vars: &[TypeVar],
    analysis: &CoOccurrences,
    protected_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    for &var in all_vars {
        if subst.contains_key(&var) {
            continue;
        }
        if protected_vars.contains(&var) {
            continue;
        }
        let Some(positive) = analysis.positive.get(&var) else {
            continue;
        };
        let Some(negative) = analysis.negative.get(&var) else {
            continue;
        };
        if positive != negative || positive.len() != 2 {
            continue;
        }

        let mut vars = positive
            .iter()
            .filter_map(|item| match item {
                AlongItem::Var(tv) => Some(*tv),
                AlongItem::Exact(_) => None,
            })
            .collect::<Vec<_>>();
        vars.sort_by_key(|tv| tv.0);
        vars.dedup();
        if vars.len() != 2 || !vars.contains(&var) {
            continue;
        }

        let other = vars.into_iter().find(|tv| *tv != var).unwrap();
        let other_only = HashSet::from([AlongItem::Var(other)]);
        if analysis.positive.get(&other) == Some(&other_only)
            && analysis.negative.get(&other) == Some(&other_only)
        {
            subst.insert(var, Some(other));
        }
    }
}

pub(super) fn apply_one_sided_exact_alias_collapse(
    all_vars: &[TypeVar],
    analysis: &CoOccurrences,
    protected_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    for &var in all_vars {
        if subst.contains_key(&var) {
            continue;
        }
        if protected_vars.contains(&var) {
            continue;
        }
        let Some(positive) = analysis.positive.get(&var) else {
            continue;
        };
        let Some(negative) = analysis.negative.get(&var) else {
            continue;
        };
        if is_one_sided_exact_alias(var, positive, negative)
            || is_one_sided_exact_alias(var, negative, positive)
        {
            subst.insert(var, None);
        }
    }
}

fn is_one_sided_exact_alias(
    var: TypeVar,
    plain_side: &HashSet<AlongItem>,
    exact_side: &HashSet<AlongItem>,
) -> bool {
    plain_side == &HashSet::from([AlongItem::Var(var)])
        && exact_side.len() == 2
        && exact_side.contains(&AlongItem::Var(var))
        && exact_side
            .iter()
            .any(|item| matches!(item, AlongItem::Exact(_)))
}

fn collect_group_replacements(
    replacements: HashMap<TypeVar, TypeVar>,
    cooccurs: &CoOccurrences,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    protected_vars: &HashSet<TypeVar>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    require_matching_polar_exact: bool,
) -> HashMap<TypeVar, TypeVar> {
    let mut accepted = HashMap::new();
    for (from, to) in replacements {
        if from == to || subst.contains_key(&from) {
            continue;
        }
        if protected_vars.contains(&from) {
            continue;
        }
        if require_matching_polar_exact && !has_matching_polar_signature(cooccurs, from, to) {
            continue;
        }
        if is_effectively_recursive(from, rec_vars) != is_effectively_recursive(to, rec_vars) {
            continue;
        }
        accepted.insert(from, to);
    }
    accepted
}

fn rewrite_occurrence_info(analysis: &mut CoOccurrences, accepted: &HashMap<TypeVar, TypeVar>) {
    rewrite_occurrence_side(&mut analysis.positive, accepted);
    rewrite_occurrence_side(&mut analysis.negative, accepted);
}

fn rewrite_occurrence_side(
    map: &mut HashMap<TypeVar, HashSet<AlongItem>>,
    accepted: &HashMap<TypeVar, TypeVar>,
) {
    let old = std::mem::take(map);
    let mut rewritten = HashMap::<TypeVar, HashSet<AlongItem>>::new();
    for (from, items) in old {
        let to = rewrite_group_var(from, accepted);
        let entry = rewritten.entry(to).or_default();
        for item in items {
            entry.insert(rewrite_along_item(item, accepted));
        }
    }
    *map = rewritten;
}

fn rewrite_recursive_bounds(
    rec_vars: &mut HashMap<TypeVar, CompactBounds>,
    accepted: &HashMap<TypeVar, TypeVar>,
) {
    let subst = accepted
        .iter()
        .map(|(&from, &to)| (from, Some(to)))
        .collect::<HashMap<_, _>>();
    let old = std::mem::take(rec_vars);
    let mut rewritten = HashMap::<TypeVar, CompactBounds>::new();
    let mut old = old.into_iter().collect::<Vec<_>>();
    old.sort_by_key(|(tv, _)| tv.0);
    for (from, bounds) in old {
        let to = rewrite_group_var(from, accepted);
        let bounds = rewrite_bounds(&bounds, &subst);
        rewritten
            .entry(to)
            .and_modify(|to_bounds| {
                *to_bounds = merge_compact_bounds(true, to_bounds.clone(), bounds.clone());
            })
            .or_insert(bounds);
    }
    *rec_vars = rewritten;
}

fn rewrite_group_var(tv: TypeVar, accepted: &HashMap<TypeVar, TypeVar>) -> TypeVar {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(&next) = accepted.get(&cur) {
        if !seen.insert(cur) || next == cur {
            break;
        }
        cur = next;
    }
    cur
}

fn rewrite_along_item(item: AlongItem, accepted: &HashMap<TypeVar, TypeVar>) -> AlongItem {
    match item {
        AlongItem::Var(tv) => AlongItem::Var(rewrite_group_var(tv, accepted)),
        AlongItem::Exact(exact) => AlongItem::Exact(exact),
    }
}
