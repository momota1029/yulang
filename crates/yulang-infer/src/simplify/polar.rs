use std::collections::HashMap;
use std::collections::HashSet;

use crate::ids::TypeVar;

use super::compact::CompactBounds;
use super::cooccur::CoOccurrences;

pub(crate) fn apply_polar_variable_removal(
    all_vars: &[TypeVar],
    analysis: &CoOccurrences,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
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
        if super::cooccur::is_effectively_recursive(var, rec_vars) {
            continue;
        }
        match (analysis.positive.get(&var), analysis.negative.get(&var)) {
            (Some(_), None) | (None, Some(_)) => {
                subst.insert(var, None);
            }
            _ => {}
        }
    }
}
