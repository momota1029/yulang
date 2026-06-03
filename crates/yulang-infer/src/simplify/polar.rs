use std::collections::{HashMap, HashSet};

use crate::ids::TypeVar;

use super::compact::CompactBounds;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PolarOccurrences {
    pub(crate) positive: HashSet<TypeVar>,
    pub(crate) negative: HashSet<TypeVar>,
}

impl PolarOccurrences {
    pub(crate) fn insert(&mut self, tv: TypeVar, positive: bool) {
        if positive {
            self.positive.insert(tv);
        } else {
            self.negative.insert(tv);
        }
    }
}

pub(crate) fn apply_polar_variable_removal(
    all_vars: &[TypeVar],
    analysis: &PolarOccurrences,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    for &var in all_vars {
        if subst.contains_key(&var) {
            continue;
        }
        match (
            analysis.positive.contains(&var),
            analysis.negative.contains(&var),
        ) {
            (true, false) => {
                subst.insert(var, None);
            }
            (false, true) if !super::cooccur::is_effectively_recursive(var, rec_vars) => {
                subst.insert(var, None);
            }
            (false, false) => {
                subst.insert(var, None);
            }
            _ => {}
        }
    }
}

pub(crate) fn rewrite_polar_occurrences(
    occurrences: &mut PolarOccurrences,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) {
    occurrences.positive = rewrite_occurrence_set(&occurrences.positive, subst);
    occurrences.negative = rewrite_occurrence_set(&occurrences.negative, subst);
}

fn rewrite_occurrence_set(
    vars: &HashSet<TypeVar>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> HashSet<TypeVar> {
    vars.iter()
        .filter_map(|tv| match subst.get(tv) {
            Some(Some(replacement)) => Some(*replacement),
            Some(None) => None,
            None => Some(*tv),
        })
        .collect()
}
