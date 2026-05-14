use std::collections::HashSet;

use crate::ids::{DefId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::simplify::compact::CompactType;
use crate::solve::Infer;
use crate::symbols::Name;
use crate::types::Pos;

impl Infer {
    pub(in crate::solve::selection) fn resolve_ref_selection_def(
        &self,
        recv_tv: TypeVar,
        name: &Name,
    ) -> Option<DefId> {
        let mut seen = HashSet::new();
        self.resolve_ref_selection_def_inner(recv_tv, name, &mut seen, true)
    }

    pub(in crate::solve::selection) fn resolve_ref_selection_def_precise(
        &self,
        recv_tv: TypeVar,
        name: &Name,
    ) -> Option<DefId> {
        let mut seen = HashSet::new();
        self.resolve_ref_selection_def_inner(recv_tv, name, &mut seen, false)
    }

    fn resolve_ref_selection_def_inner(
        &self,
        recv_tv: TypeVar,
        name: &Name,
        seen: &mut HashSet<TypeVar>,
        allow_global_unique: bool,
    ) -> Option<DefId> {
        if !seen.insert(recv_tv) {
            return None;
        }

        for lower in self.lower_refs_of(recv_tv) {
            if let Some(def) =
                self.resolve_ref_selection_def_from_pos(lower, name, seen, allow_global_unique)
            {
                return Some(def);
            }
        }

        for instance in self.compact_lower_instances_of(recv_tv) {
            if let Some(def) = self.resolve_ref_selection_def_from_compact_instance(
                &instance,
                name,
                seen,
                allow_global_unique,
            ) {
                return Some(def);
            }
        }

        if let Some(concrete) = super::concrete_tv_repr(self, recv_tv, true) {
            if let Some(def) = self.resolve_ref_selection_def_from_compact_type(
                &concrete,
                &[],
                name,
                seen,
                allow_global_unique,
            ) {
                return Some(def);
            }
        }

        if allow_global_unique && self.recv_has_ref_type_lower(recv_tv, &mut HashSet::new()) {
            self.unique_ref_type_method_named(name)
        } else {
            None
        }
    }

    fn unique_ref_type_method_named(&self, name: &Name) -> Option<DefId> {
        let mut found = None;
        for methods in self.ref_type_methods.values() {
            let Some(&def) = methods.get(name) else {
                continue;
            };
            if found.replace(def).is_some() {
                return None;
            }
        }
        found
    }

    fn resolve_ref_selection_def_from_compact_instance(
        &self,
        instance: &OwnedSchemeInstance,
        name: &Name,
        seen: &mut HashSet<TypeVar>,
        allow_global_unique: bool,
    ) -> Option<DefId> {
        self.resolve_ref_selection_def_from_compact_type(
            &instance.scheme.compact.cty.lower,
            instance.subst.as_slice(),
            name,
            seen,
            allow_global_unique,
        )
    }

    fn resolve_ref_selection_def_from_compact_type(
        &self,
        ty: &CompactType,
        subst: &[(TypeVar, TypeVar)],
        name: &Name,
        seen: &mut HashSet<TypeVar>,
        allow_global_unique: bool,
    ) -> Option<DefId> {
        for con in &ty.cons {
            if self.is_ref_type_path(&con.path) && con.args.len() >= 2 {
                if let Some(def) = self.resolve_ref_inner_selection_def_from_compact_type(
                    &con.args[1].lower,
                    subst,
                    name,
                    seen,
                ) {
                    return Some(def);
                }
                if let Some(def) = self.resolve_ref_inner_selection_def_from_compact_type(
                    &con.args[1].upper,
                    subst,
                    name,
                    seen,
                ) {
                    return Some(def);
                }
            }
        }
        for tv in &ty.vars {
            let mapped = lookup_small_subst(subst, *tv);
            if let Some(def) =
                self.resolve_ref_selection_def_inner(mapped, name, seen, allow_global_unique)
            {
                return Some(def);
            }
        }
        None
    }

    fn recv_has_ref_type_lower(&self, recv_tv: TypeVar, seen: &mut HashSet<TypeVar>) -> bool {
        if !seen.insert(recv_tv) {
            return false;
        }
        self.lower_refs_of(recv_tv)
            .into_iter()
            .any(|lower| self.pos_has_ref_type_lower(lower, seen))
            || self
                .compact_lower_instances_of(recv_tv)
                .into_iter()
                .any(|instance| self.compact_type_has_ref_type(&instance.scheme.compact.cty.lower))
    }

    fn pos_has_ref_type_lower(&self, pos: crate::ids::PosId, seen: &mut HashSet<TypeVar>) -> bool {
        match self.arena.get_pos(pos) {
            Pos::Con(path, _) => self.is_ref_type_path(&path),
            Pos::Var(inner) | Pos::Raw(inner) => self.recv_has_ref_type_lower(inner, seen),
            Pos::Union(left, right) => {
                self.pos_has_ref_type_lower(left, seen) || self.pos_has_ref_type_lower(right, seen)
            }
            _ => false,
        }
    }

    fn resolve_ref_selection_def_from_pos(
        &self,
        pos: crate::ids::PosId,
        name: &Name,
        seen: &mut HashSet<TypeVar>,
        allow_global_unique: bool,
    ) -> Option<DefId> {
        match self.arena.get_pos(pos) {
            Pos::Con(path, args) if self.is_ref_type_path(&path) && args.len() >= 2 => {
                self.resolve_ref_inner_selection_def_from_pos(args[1].0, name, seen)
            }
            Pos::Var(inner) | Pos::Raw(inner) => {
                self.resolve_ref_selection_def_inner(inner, name, seen, allow_global_unique)
            }
            Pos::Union(left, right) => merge_unique_ref_selection_def(
                self.resolve_ref_selection_def_from_pos(
                    left,
                    name,
                    &mut seen.clone(),
                    allow_global_unique,
                ),
                self.resolve_ref_selection_def_from_pos(right, name, seen, allow_global_unique),
            ),
            _ => None,
        }
    }

    fn resolve_ref_inner_selection_def_from_pos(
        &self,
        pos: crate::ids::PosId,
        name: &Name,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<DefId> {
        match self.arena.get_pos(pos) {
            Pos::Con(path, _) => self
                .ref_type_methods
                .get(&path)
                .and_then(|methods| methods.get(name).copied()),
            Pos::Var(inner) | Pos::Raw(inner) => {
                if !seen.insert(inner) {
                    return None;
                }
                for lower in self.lower_refs_of(inner) {
                    if let Some(def) =
                        self.resolve_ref_inner_selection_def_from_pos(lower, name, seen)
                    {
                        return Some(def);
                    }
                }
                None
            }
            Pos::Union(left, right) => merge_unique_ref_selection_def(
                self.resolve_ref_inner_selection_def_from_pos(left, name, &mut seen.clone()),
                self.resolve_ref_inner_selection_def_from_pos(right, name, seen),
            ),
            _ => None,
        }
    }

    fn resolve_ref_inner_selection_def_from_compact_type(
        &self,
        ty: &CompactType,
        subst: &[(TypeVar, TypeVar)],
        name: &Name,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<DefId> {
        for con in &ty.cons {
            if let Some(def) = self
                .ref_type_methods
                .get(&con.path)
                .and_then(|methods| methods.get(name).copied())
            {
                return Some(def);
            }
        }
        for tv in &ty.vars {
            let mapped = lookup_small_subst(subst, *tv);
            if !seen.insert(mapped) {
                continue;
            }
            for lower in self.lower_refs_of(mapped) {
                if let Some(def) = self.resolve_ref_inner_selection_def_from_pos(lower, name, seen)
                {
                    return Some(def);
                }
            }
            for instance in self.compact_lower_instances_of(mapped) {
                if let Some(def) = self.resolve_ref_inner_selection_def_from_compact_type(
                    &instance.scheme.compact.cty.lower,
                    instance.subst.as_slice(),
                    name,
                    seen,
                ) {
                    return Some(def);
                }
            }
        }
        None
    }
    fn compact_type_has_ref_type(&self, ty: &CompactType) -> bool {
        ty.cons.iter().any(|con| self.is_ref_type_path(&con.path))
    }
}

fn lookup_small_subst(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}

fn merge_unique_ref_selection_def(left: Option<DefId>, right: Option<DefId>) -> Option<DefId> {
    match (left, right) {
        (Some(left), Some(right)) if left == right => Some(left),
        (Some(_), Some(_)) => None,
        (Some(def), None) | (None, Some(def)) => Some(def),
        (None, None) => None,
    }
}
