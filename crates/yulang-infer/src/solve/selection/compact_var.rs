use crate::ids::TypeVar;
use crate::simplify::compact::CompactType;

pub(super) fn common_compact_var(lhs: &CompactType, rhs: &CompactType) -> Option<TypeVar> {
    lhs.vars.iter().copied().find(|tv| rhs.vars.contains(tv))
}

pub(super) fn single_compact_var(ty: &CompactType) -> Option<TypeVar> {
    let vars = ty.vars.iter().copied().collect::<Vec<_>>();
    let [tv] = vars.as_slice() else {
        return None;
    };
    if ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(*tv)
    } else {
        None
    }
}
