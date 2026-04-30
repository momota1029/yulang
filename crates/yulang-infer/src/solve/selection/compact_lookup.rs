use std::collections::HashSet;

use crate::ids::{DefId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::simplify::compact::CompactType;
use crate::symbols::Name;

use super::Infer;

pub(super) fn resolve_selection_def_from_compact_instance(
    infer: &Infer,
    instance: &OwnedSchemeInstance,
    name: &Name,
    seen: &mut HashSet<TypeVar>,
) -> Option<DefId> {
    resolve_selection_def_from_compact_type(
        infer,
        &instance.scheme.compact.cty.lower,
        instance.subst.as_slice(),
        name,
        seen,
    )
}

fn resolve_selection_def_from_compact_type(
    infer: &Infer,
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
    name: &Name,
    seen: &mut HashSet<TypeVar>,
) -> Option<DefId> {
    for con in &ty.cons {
        if let Some(methods) = infer.type_methods.get(&con.path) {
            if let Some(&def) = methods.get(name) {
                return Some(def);
            }
        }
    }
    for tv in &ty.vars {
        let mapped = lookup_small_subst(subst, *tv);
        if let Some(def) = infer.resolve_selection_def_inner(mapped, name, seen) {
            return Some(def);
        }
    }
    None
}

fn lookup_small_subst(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}
