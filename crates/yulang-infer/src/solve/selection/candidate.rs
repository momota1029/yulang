use std::collections::HashMap;

use crate::ids::TypeVar;
use crate::simplify::compact::CompactType;

use super::compact_match::match_compact_type_pattern;

pub(crate) fn role_candidate_input_subst(
    candidate: &crate::solve::RoleImplCandidate,
    input_indices: &[usize],
    concrete_inputs: &[CompactType],
) -> Option<HashMap<TypeVar, CompactType>> {
    let mut subst = HashMap::new();
    for (index, concrete) in input_indices.iter().zip(concrete_inputs) {
        let pattern = candidate.compact_args.get(*index)?;
        if !match_compact_type_pattern(pattern, concrete, &mut subst) {
            return None;
        }
    }
    Some(subst)
}

pub(crate) fn select_most_specific_role_candidates<'a>(
    candidates: Vec<&'a crate::solve::RoleImplCandidate>,
    input_indices: &[usize],
) -> Vec<&'a crate::solve::RoleImplCandidate> {
    candidates
        .iter()
        .copied()
        .filter(|candidate| {
            !candidates.iter().copied().any(|other| {
                !std::ptr::eq(*candidate, other)
                    && role_candidate_is_more_specific(other, candidate, input_indices)
            })
        })
        .collect()
}

fn role_candidate_is_more_specific(
    lhs: &crate::solve::RoleImplCandidate,
    rhs: &crate::solve::RoleImplCandidate,
    input_indices: &[usize],
) -> bool {
    role_candidate_pattern_matches(rhs, lhs, input_indices)
        && !role_candidate_pattern_matches(lhs, rhs, input_indices)
}

fn role_candidate_pattern_matches(
    pattern_candidate: &crate::solve::RoleImplCandidate,
    concrete_candidate: &crate::solve::RoleImplCandidate,
    input_indices: &[usize],
) -> bool {
    let mut subst = HashMap::new();
    input_indices.iter().all(|index| {
        let Some(pattern) = pattern_candidate.compact_args.get(*index) else {
            return false;
        };
        let Some(concrete) = concrete_candidate.compact_args.get(*index) else {
            return false;
        };
        match_compact_type_pattern(pattern, concrete, &mut subst)
    })
}
