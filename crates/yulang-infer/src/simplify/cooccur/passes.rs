use std::collections::{HashMap, HashSet};

use crate::ids::TypeVar;

use super::group::{GroupCoOccurrences, indistinguishable_group_replacements};
use super::{
    AlongItem, CoOccurrences, CompactBounds, ExactInfo, ExactKeyKind, has_matching_polar_signature,
    is_effectively_recursive, merge_compact_bounds, rewrite_bounds,
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
        && exact_side.iter().any(|item| {
            matches!(
                item, AlongItem::Exact(exact) if exact.kind == ExactKeyKind::Fun
            )
        })
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
