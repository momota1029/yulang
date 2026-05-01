use std::collections::HashSet;

use crate::ids::{DefId, TypeVar, fresh_type_var};
use crate::scheme::{OwnedSchemeInstance, SmallSubst, instantiate_frozen_scheme_with_subst};
use crate::simplify::compact::CompactType;
use crate::solve::{
    DeferredSelection, EffectMethodInfo, ExtensionMethodInfo, Infer, RefFieldProjection,
    RoleMethodInfo,
};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

use super::effect_method::EffectMethodResolution;

impl Infer {
    pub fn resolve_deferred_selections(&self) {
        let keys: Vec<_> = self.deferred_selections.borrow().keys().copied().collect();
        for recv_tv in keys {
            self.resolve_deferred_selections_for(recv_tv);
        }
        self.resolve_deferred_role_method_calls();
    }

    pub(crate) fn resolve_selection_def(
        &self,
        recv_tv: TypeVar,
        name: &crate::symbols::Name,
    ) -> Option<DefId> {
        let mut seen = HashSet::new();
        self.resolve_selection_def_inner(recv_tv, name, &mut seen)
    }

    pub(crate) fn resolve_deferred_selections_for(&self, recv_tv: TypeVar) {
        let Some(selections) = self.deferred_selections.borrow().get(&recv_tv).cloned() else {
            return;
        };

        let mut unresolved = Vec::new();
        for selection in selections {
            if let Some(def) = self.resolve_selection_def(recv_tv, &selection.name) {
                if self.resolve_method_def_selection(recv_tv, &selection, def) {
                    continue;
                }
            }

            if let Some(def) = self.resolve_ref_selection_def(recv_tv, &selection.name) {
                if self.resolve_method_def_selection(recv_tv, &selection, def) {
                    continue;
                }
            }

            if let Some(projection) =
                self.resolve_ref_field_projection_info(recv_tv, &selection.name)
            {
                if self.resolve_ref_field_projection_selection(recv_tv, &selection, projection) {
                    continue;
                }
            }

            if let Some(info) = self.role_methods.get(&selection.name).cloned() {
                if self.resolve_deferred_selection(recv_tv, &selection, &info) {
                    continue;
                }
            }

            match self.resolve_effect_method_info_from(
                selection.module,
                selection.recv_eff,
                &selection.name,
            ) {
                EffectMethodResolution::Unique(info) => {
                    if self.resolve_effect_method_selection(recv_tv, &selection, &info) {
                        continue;
                    }
                }
                EffectMethodResolution::Ambiguous(candidates) => {
                    self.report_ambiguous_effect_method(
                        &selection.name,
                        &candidates,
                        selection.result_tv,
                    );
                    if let Some(owner) = selection.owner {
                        self.decrement_pending_selection(owner);
                    }
                    continue;
                }
                EffectMethodResolution::None => {}
            }

            if let Some(info) = super::extension::resolve_extension_method_info_from(
                self,
                selection.module,
                &selection.name,
            ) {
                if self.resolve_extension_method_selection(recv_tv, &selection, &info) {
                    continue;
                }
            }
            unresolved.push(selection);
        }

        if unresolved.is_empty() {
            self.deferred_selections.borrow_mut().remove(&recv_tv);
        } else {
            self.deferred_selections
                .borrow_mut()
                .insert(recv_tv, unresolved);
        }
    }

    pub(super) fn resolve_selection_def_inner(
        &self,
        recv_tv: TypeVar,
        name: &crate::symbols::Name,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<DefId> {
        if !seen.insert(recv_tv) {
            return None;
        }

        for lower in self.lower_refs_of(recv_tv) {
            match self.arena.get_pos(lower) {
                Pos::Con(path, _) => {
                    if let Some(methods) = self.type_methods.get(&path) {
                        if let Some(&def) = methods.get(name) {
                            return Some(def);
                        }
                    }
                }
                Pos::Var(inner) | Pos::Raw(inner) => {
                    if let Some(def) = self.resolve_selection_def_inner(inner, name, seen) {
                        return Some(def);
                    }
                }
                _ => {}
            }
        }

        for instance in self.compact_lower_instances_of(recv_tv) {
            if let Some(def) = super::compact_lookup::resolve_selection_def_from_compact_instance(
                self, &instance, name, seen,
            ) {
                return Some(def);
            }
        }

        None
    }

    fn resolve_method_def_selection(
        &self,
        recv_tv: TypeVar,
        selection: &DeferredSelection,
        def: DefId,
    ) -> bool {
        let Some((method_tv, _)) = self.selection_method_use_tv(def, selection.result_tv, None)
        else {
            return false;
        };

        if let Some(owner) = selection.owner {
            self.add_edge(owner, def);
            self.decrement_pending_selection(owner);
        }
        self.record_resolved_selection(selection, def);
        self.constrain_selected_method_call(
            method_tv,
            recv_tv,
            selection,
            SelectedReceiverStyle::Value,
        );
        true
    }

    fn resolve_ref_field_projection_selection(
        &self,
        recv_tv: TypeVar,
        selection: &DeferredSelection,
        projection: RefFieldProjection,
    ) -> bool {
        if self
            .resolved_ref_field_projections
            .borrow()
            .contains_key(&selection.result_tv)
        {
            return true;
        }
        self.resolved_ref_field_projections
            .borrow_mut()
            .insert(selection.result_tv, projection.clone());

        let eff_tv = fresh_type_var();
        let inner_tv = fresh_type_var();
        let field_tv = fresh_type_var();
        let field_call_eff = fresh_type_var();
        let level = self.level_of(selection.result_tv);
        self.register_level(eff_tv, level);
        self.register_level(inner_tv, level);
        self.register_level(field_tv, level);
        self.register_level(field_call_eff, self.level_of(selection.result_eff));

        let Some((field_method_tv, _)) =
            self.selection_method_use_tv(projection.field.def, selection.result_tv, Some(inner_tv))
        else {
            return false;
        };

        let recv_ref_args = invariant_type_args(self, &[eff_tv, inner_tv]);
        self.constrain_with_cause(
            self.alloc_pos(Pos::Con(std_var_ref_path(), recv_ref_args.clone())),
            self.alloc_neg(Neg::Var(recv_tv)),
            selection.cause.clone(),
        );
        self.constrain_with_cause(
            self.alloc_pos(Pos::Var(recv_tv)),
            self.alloc_neg(Neg::Con(std_var_ref_path(), recv_ref_args)),
            selection.cause.clone(),
        );

        self.constrain_with_cause(
            self.alloc_pos(Pos::Var(field_method_tv)),
            self.alloc_neg(Neg::Fun {
                arg: self.alloc_pos(Pos::Var(inner_tv)),
                arg_eff: pure_pos_row(self),
                ret_eff: self.alloc_neg(Neg::Var(field_call_eff)),
                ret: self.alloc_neg(Neg::Var(field_tv)),
            }),
            selection.cause.clone(),
        );

        let result_ref_args = invariant_type_args(self, &[eff_tv, field_tv]);
        self.constrain_with_cause(
            self.alloc_pos(Pos::Con(std_var_ref_path(), result_ref_args.clone())),
            self.alloc_neg(Neg::Var(selection.result_tv)),
            selection.cause.clone(),
        );
        self.constrain_with_cause(
            self.alloc_pos(Pos::Var(selection.result_tv)),
            self.alloc_neg(Neg::Con(std_var_ref_path(), result_ref_args)),
            selection.cause.clone(),
        );

        self.constrain(Pos::Var(selection.recv_eff), Neg::Var(selection.result_eff));
        self.constrain(Pos::Var(field_call_eff), Neg::Var(selection.result_eff));

        if let Some(owner) = selection.owner {
            self.add_edge(owner, projection.field.def);
            self.add_edge(owner, projection.constructor);
            for field in &projection.fields {
                self.add_edge(owner, field.def);
            }
            self.decrement_pending_selection(owner);
        }
        true
    }

    fn resolve_deferred_selection(
        &self,
        recv_tv: TypeVar,
        selection: &DeferredSelection,
        info: &RoleMethodInfo,
    ) -> bool {
        let Some((method_tv, subst)) =
            self.selection_method_use_tv(info.def, selection.result_tv, Some(recv_tv))
        else {
            return false;
        };

        if let Some(owner) = selection.owner {
            self.add_edge(owner, info.def);
            self.decrement_pending_selection(owner);
            self.instantiate_role_constraints_for_owner(info.def, owner, &subst);
        }
        let resolved_def = self
            .resolve_concrete_role_method_call_def(info, Some(recv_tv), &[])
            .unwrap_or(info.def);
        self.record_resolved_selection(selection, resolved_def);
        self.constrain_selected_method_call(
            method_tv,
            recv_tv,
            selection,
            SelectedReceiverStyle::Value,
        );
        true
    }

    fn resolve_extension_method_selection(
        &self,
        recv_tv: TypeVar,
        selection: &DeferredSelection,
        info: &ExtensionMethodInfo,
    ) -> bool {
        let Some((method_tv, _)) =
            self.selection_method_use_tv(info.def, selection.result_tv, Some(recv_tv))
        else {
            return false;
        };

        if let Some(owner) = selection.owner {
            self.add_edge(owner, info.def);
            self.decrement_pending_selection(owner);
        }
        self.record_resolved_selection(selection, info.def);
        self.constrain_selected_method_call(
            method_tv,
            recv_tv,
            selection,
            if info.receiver_expects_computation {
                SelectedReceiverStyle::Computation
            } else {
                SelectedReceiverStyle::Value
            },
        );
        true
    }

    fn resolve_effect_method_selection(
        &self,
        recv_tv: TypeVar,
        selection: &DeferredSelection,
        info: &EffectMethodInfo,
    ) -> bool {
        let Some((method_tv, _)) =
            self.selection_method_use_tv(info.def, selection.result_tv, Some(recv_tv))
        else {
            return false;
        };

        if let Some(owner) = selection.owner {
            self.add_edge(owner, info.def);
            self.decrement_pending_selection(owner);
        }
        self.record_resolved_selection(selection, info.def);
        self.constrain_selected_method_call(
            method_tv,
            recv_tv,
            selection,
            if info.receiver_expects_computation {
                SelectedReceiverStyle::Computation
            } else {
                SelectedReceiverStyle::Value
            },
        );
        true
    }

    fn record_resolved_selection(&self, selection: &DeferredSelection, def: DefId) {
        self.resolved_selections
            .borrow_mut()
            .insert(selection.result_tv, def);
    }

    fn selection_method_use_tv(
        &self,
        def: DefId,
        level_source: TypeVar,
        receiver_tv: Option<TypeVar>,
    ) -> Option<(TypeVar, SmallSubst)> {
        if let Some(scheme) = self.frozen_schemes.borrow().get(&def).cloned() {
            let tv = fresh_type_var();
            let level = self.level_of(level_source);
            self.register_level(tv, level);
            let mut preset = SmallSubst::new();
            if let Some(receiver_tv) = receiver_tv {
                if let Some(receiver_param) =
                    super::scheme_arg::first_fun_arg_var_in_scheme(self, &scheme)
                {
                    preset.push((receiver_param, receiver_tv));
                }
            }
            let subst = instantiate_frozen_scheme_with_subst(self, &scheme, tv, preset.as_slice());
            return Some((tv, subst));
        }

        self.def_tvs
            .borrow()
            .get(&def)
            .map(|&v| (v, SmallSubst::new()))
    }

    fn constrain_selected_method_call(
        &self,
        method_tv: TypeVar,
        recv_tv: TypeVar,
        selection: &DeferredSelection,
        receiver_style: SelectedReceiverStyle,
    ) {
        let call_eff = fresh_type_var();
        let level = self.level_of(selection.result_eff);
        self.register_level(call_eff, level);
        let receiver_arg_eff = match receiver_style {
            SelectedReceiverStyle::Value => pure_pos_row(self),
            SelectedReceiverStyle::Computation => self.alloc_pos(Pos::Var(selection.recv_eff)),
        };
        self.constrain_with_cause(
            self.alloc_pos(Pos::Var(method_tv)),
            self.alloc_neg(Neg::Fun {
                arg: self.alloc_pos(Pos::Var(recv_tv)),
                arg_eff: receiver_arg_eff,
                ret_eff: self.alloc_neg(Neg::Var(call_eff)),
                ret: self.alloc_neg(Neg::Var(selection.result_tv)),
            }),
            selection.cause.clone(),
        );
        if matches!(receiver_style, SelectedReceiverStyle::Value) {
            self.constrain(Pos::Var(selection.recv_eff), Neg::Var(call_eff));
        }
        self.constrain(Pos::Var(call_eff), Neg::Var(selection.result_eff));
    }

    pub(crate) fn resolve_extension_method_def(&self, name: &Name) -> Option<DefId> {
        super::extension::resolve_extension_method_def(self, name)
    }

    fn resolve_ref_field_projection_info(
        &self,
        recv_tv: TypeVar,
        name: &Name,
    ) -> Option<RefFieldProjection> {
        let mut seen = HashSet::new();
        self.resolve_ref_field_projection_info_inner(recv_tv, name, &mut seen)
    }

    fn resolve_ref_field_projection_info_inner(
        &self,
        recv_tv: TypeVar,
        name: &Name,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<RefFieldProjection> {
        if !seen.insert(recv_tv) {
            return None;
        }

        for lower in self.lower_refs_of(recv_tv) {
            match self.arena.get_pos(lower) {
                Pos::Con(path, args) if is_std_var_ref_path(&path) && args.len() >= 2 => {
                    if let Some(projection) = self
                        .resolve_ref_field_projection_from_inner_pos(args[1].0, name, recv_tv, seen)
                    {
                        return Some(projection);
                    }
                }
                Pos::Var(inner) | Pos::Raw(inner) => {
                    if let Some(projection) =
                        self.resolve_ref_field_projection_info_inner(inner, name, seen)
                    {
                        return Some(projection);
                    }
                }
                _ => {}
            }
        }

        for instance in self.compact_lower_instances_of(recv_tv) {
            if let Some(projection) = self
                .resolve_ref_field_projection_from_compact_instance(&instance, name, recv_tv, seen)
            {
                return Some(projection);
            }
        }

        None
    }

    fn resolve_ref_field_projection_from_inner_pos(
        &self,
        inner: crate::ids::PosId,
        name: &Name,
        dependent: TypeVar,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<RefFieldProjection> {
        match self.arena.get_pos(inner) {
            Pos::Con(path, _) => self.ref_field_projection_for_type(&path, name),
            Pos::Var(tv) | Pos::Raw(tv) => {
                self.add_selection_var_dependent(tv, dependent);
                if !seen.insert(tv) {
                    return None;
                }
                for lower in self.lower_refs_of(tv) {
                    if let Some(projection) = self
                        .resolve_ref_field_projection_from_inner_pos(lower, name, dependent, seen)
                    {
                        return Some(projection);
                    }
                }
                for instance in self.compact_lower_instances_of(tv) {
                    if let Some(projection) = self
                        .resolve_ref_field_projection_from_compact_instance(
                            &instance, name, dependent, seen,
                        )
                    {
                        return Some(projection);
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn resolve_ref_field_projection_from_compact_instance(
        &self,
        instance: &OwnedSchemeInstance,
        name: &Name,
        dependent: TypeVar,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<RefFieldProjection> {
        self.resolve_ref_field_projection_from_compact_type(
            &instance.scheme.compact.cty.lower,
            instance.subst.as_slice(),
            name,
            dependent,
            seen,
        )
    }

    fn resolve_ref_field_projection_from_compact_type(
        &self,
        ty: &CompactType,
        subst: &[(TypeVar, TypeVar)],
        name: &Name,
        dependent: TypeVar,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<RefFieldProjection> {
        for con in &ty.cons {
            if is_std_var_ref_path(&con.path) && con.args.len() >= 2 {
                if let Some(projection) = self.resolve_ref_field_projection_from_compact_inner_type(
                    &con.args[1].lower,
                    subst,
                    name,
                    dependent,
                    seen,
                ) {
                    return Some(projection);
                }
                if let Some(projection) = self.resolve_ref_field_projection_from_compact_inner_type(
                    &con.args[1].upper,
                    subst,
                    name,
                    dependent,
                    seen,
                ) {
                    return Some(projection);
                }
            }
        }
        for tv in &ty.vars {
            let mapped = lookup_small_subst(subst, *tv);
            self.add_selection_var_dependent(mapped, dependent);
            if let Some(projection) =
                self.resolve_ref_field_projection_info_inner(mapped, name, seen)
            {
                return Some(projection);
            }
        }
        None
    }

    fn resolve_ref_field_projection_from_compact_inner_type(
        &self,
        ty: &CompactType,
        subst: &[(TypeVar, TypeVar)],
        name: &Name,
        dependent: TypeVar,
        seen: &mut HashSet<TypeVar>,
    ) -> Option<RefFieldProjection> {
        for con in &ty.cons {
            if let Some(projection) = self.ref_field_projection_for_type(&con.path, name) {
                return Some(projection);
            }
        }
        for tv in &ty.vars {
            let mapped = lookup_small_subst(subst, *tv);
            self.add_selection_var_dependent(mapped, dependent);
            if let Some(projection) =
                self.resolve_ref_field_projection_info_inner(mapped, name, seen)
            {
                return Some(projection);
            }
        }
        None
    }

    fn ref_field_projection_for_type(
        &self,
        type_path: &Path,
        name: &Name,
    ) -> Option<RefFieldProjection> {
        let field_def = self
            .type_fields
            .get(type_path)
            .and_then(|fields| fields.get(name))
            .copied()?;
        if self
            .ref_type_methods
            .get(type_path)
            .is_some_and(|methods| methods.contains_key(name))
        {
            return None;
        }
        if self
            .type_methods
            .get(type_path)
            .and_then(|methods| methods.get(name))
            .is_some_and(|&method_def| method_def != field_def)
        {
            return None;
        }
        let field_set = self.type_field_sets.get(type_path)?;
        let field = field_set
            .fields
            .iter()
            .find(|field| field.name == *name && field.def == field_def)?
            .clone();
        Some(RefFieldProjection {
            type_path: type_path.clone(),
            field,
            fields: field_set.fields.clone(),
            constructor: field_set.constructor,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SelectedReceiverStyle {
    Value,
    Computation,
}

fn std_var_ref_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
        ],
    }
}

fn is_std_var_ref_path(path: &Path) -> bool {
    let [std, var, reference] = path.segments.as_slice() else {
        return false;
    };
    std.0 == "std" && var.0 == "var" && reference.0 == "ref"
}

fn invariant_type_args(
    infer: &Infer,
    tvs: &[TypeVar],
) -> Vec<(crate::ids::PosId, crate::ids::NegId)> {
    tvs.iter()
        .map(|&tv| (infer.alloc_pos(Pos::Var(tv)), infer.alloc_neg(Neg::Var(tv))))
        .collect()
}

fn pure_pos_row(infer: &Infer) -> crate::ids::PosId {
    let tail = infer.alloc_pos(Pos::Bot);
    infer.alloc_pos(Pos::Row(vec![], tail))
}

fn lookup_small_subst(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}
