use rustc_hash::FxHashSet;

use super::Infer;
use crate::ids::{NegId, PosId, TypeVar};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

pub(super) fn is_builtin_numeric_widening(
    actual: &crate::symbols::Path,
    expected: &crate::symbols::Path,
) -> bool {
    let Some(actual_leaf) = actual.segments.last().map(|name| name.0.as_str()) else {
        return false;
    };
    let Some(expected_leaf) = expected.segments.last().map(|name| name.0.as_str()) else {
        return false;
    };
    yulang_core_ir::can_widen_named_leaves(actual_leaf, expected_leaf)
}

pub(super) fn same_row_tail_var_nodes(pos: &Pos, neg: &Neg) -> bool {
    match (pos, neg) {
        (Pos::Var(lhs), Neg::Var(rhs)) | (Pos::Raw(lhs), Neg::Var(rhs)) => lhs == rhs,
        _ => false,
    }
}

pub(super) fn pos_id_direct_var(pos: &Pos) -> Option<TypeVar> {
    match pos {
        Pos::Var(tv) | Pos::Raw(tv) => Some(*tv),
        _ => None,
    }
}

pub(super) fn optionalized_neg_field(
    field: crate::types::RecordField<NegId>,
) -> crate::types::RecordField<NegId> {
    crate::types::RecordField {
        name: field.name,
        value: field.value,
        optional: true,
    }
}

pub(super) fn singleton_neg_record(
    infer: &Infer,
    field: crate::types::RecordField<NegId>,
) -> NegId {
    infer.alloc_neg(Neg::Record(vec![field]))
}

pub(super) fn neg_id_direct_var(neg: &Neg) -> Option<TypeVar> {
    match neg {
        Neg::Var(tv) => Some(*tv),
        _ => None,
    }
}

pub(super) fn live_neg_is_empty_row(
    infer: &Infer,
    neg: NegId,
    seen: &mut FxHashSet<TypeVar>,
) -> bool {
    match infer.arena.get_neg(neg) {
        Neg::Row(items, tail) => items.is_empty() && matches!(infer.arena.get_neg(tail), Neg::Top),
        Neg::Var(tv) => live_neg_var_is_empty_row(infer, tv, seen),
        _ => false,
    }
}

pub(super) fn live_pos_is_empty_row(
    infer: &Infer,
    pos: PosId,
    seen: &mut FxHashSet<TypeVar>,
) -> bool {
    match infer.arena.get_pos(pos) {
        Pos::Row(items, tail) => items.is_empty() && matches!(infer.arena.get_pos(tail), Pos::Bot),
        Pos::Var(tv) => live_pos_var_is_empty_row(infer, tv, seen),
        _ => false,
    }
}

pub(super) fn live_neg_var_is_empty_row(
    infer: &Infer,
    tv: TypeVar,
    seen: &mut FxHashSet<TypeVar>,
) -> bool {
    if !seen.insert(tv) {
        return false;
    }
    let lowers = infer.lower_refs_of(tv);
    let uppers = infer.upper_refs_of(tv);
    !lowers.is_empty()
        && lowers
            .iter()
            .all(|lower| live_pos_is_empty_row(infer, *lower, seen))
        && uppers
            .iter()
            .all(|upper| matches!(infer.arena.get_neg(*upper), Neg::Top))
}

pub(super) fn live_pos_var_is_empty_row(
    infer: &Infer,
    tv: TypeVar,
    seen: &mut FxHashSet<TypeVar>,
) -> bool {
    if !seen.insert(tv) {
        return false;
    }
    let lowers = infer.lower_refs_of(tv);
    let uppers = infer.upper_refs_of(tv);
    !lowers.is_empty()
        && lowers
            .iter()
            .all(|lower| live_pos_is_empty_row(infer, *lower, seen))
        && uppers
            .iter()
            .all(|upper| live_neg_is_empty_row(infer, *upper, seen))
}

pub(super) fn find_record_field<T: Copy>(
    fields: &[crate::types::RecordField<T>],
    name: &Name,
) -> Option<crate::types::RecordField<T>> {
    fields.iter().find(|field| field.name == *name).cloned()
}
