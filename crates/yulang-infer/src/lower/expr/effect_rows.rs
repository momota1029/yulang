use std::collections::HashSet;

use crate::ids::TypeVar;
use crate::lower::LowerState;
use crate::types::{Neg, Pos};

pub(crate) fn neg_id_is_pure_row(
    state: &LowerState,
    neg: crate::ids::NegId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_neg(neg) {
        Neg::Row(items, tail) => {
            items.is_empty() && matches!(state.infer.arena.get_neg(tail), Neg::Top)
        }
        Neg::Var(tv) => {
            if !seen.insert(tv) {
                return false;
            }
            let lowers = state.infer.lower_refs_of(tv);
            let uppers = state.infer.upper_refs_of(tv);
            !lowers.is_empty()
                && lowers
                    .iter()
                    .all(|lower| pos_id_is_empty_row(state, *lower, &mut seen.clone()))
                && uppers
                    .iter()
                    .all(|upper| neg_id_is_pure_row(state, *upper, &mut seen.clone()))
        }
        Neg::Intersection(a, b) => {
            neg_id_is_pure_row(state, a, &mut seen.clone())
                && neg_id_is_pure_row(state, b, &mut seen.clone())
        }
        _ => false,
    }
}

pub(crate) fn pos_id_is_empty_row(
    state: &LowerState,
    pos: crate::ids::PosId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_pos(pos) {
        Pos::Bot => true,
        Pos::Row(items, tail) => {
            items.is_empty() && matches!(state.infer.arena.get_pos(tail), Pos::Bot)
        }
        Pos::Var(tv) | Pos::Raw(tv) => {
            if !seen.insert(tv) {
                return false;
            }
            let lowers = state.infer.lower_refs_of(tv);
            let uppers = state.infer.upper_refs_of(tv);
            !lowers.is_empty()
                && lowers
                    .iter()
                    .all(|lower| pos_id_is_empty_row(state, *lower, &mut seen.clone()))
                && uppers
                    .iter()
                    .all(|upper| neg_id_is_pure_row(state, *upper, &mut seen.clone()))
        }
        Pos::Union(a, b) => {
            pos_id_is_empty_row(state, a, &mut seen.clone())
                && pos_id_is_empty_row(state, b, &mut seen.clone())
        }
        _ => false,
    }
}
