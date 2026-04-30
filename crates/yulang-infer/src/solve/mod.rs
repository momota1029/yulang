use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::mem;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::ids::{DefId, NegId, PosId, TypeVar};
use crate::symbols::{ModuleId, ModuleTable, Name, Path};
use crate::types::arena::TypeArena;
use crate::types::{Neg, Pos, Variance};

use crate::diagnostic::{ConstraintCause, TypeError, TypeOrigin};
use crate::scheme::{FrozenScheme, OwnedSchemeInstance};
use crate::simplify::compact::CompactTypeScheme;
use crate::simplify::cooccur::CompactRoleConstraint;

pub mod constrain;
pub mod effect_row;
pub mod role;
pub mod selection;

pub use role::{RoleArgInfo, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleMethodInfo};

pub trait IntoPosId {
    fn into_pos_id(self, infer: &Infer) -> PosId;
}

pub trait IntoNegId {
    fn into_neg_id(self, infer: &Infer) -> NegId;
}

impl IntoPosId for PosId {
    fn into_pos_id(self, _: &Infer) -> PosId {
        self
    }
}

impl IntoPosId for Pos {
    fn into_pos_id(self, infer: &Infer) -> PosId {
        infer.alloc_pos(self)
    }
}

impl IntoNegId for NegId {
    fn into_neg_id(self, _: &Infer) -> NegId {
        self
    }
}

impl IntoNegId for Neg {
    fn into_neg_id(self, infer: &Infer) -> NegId {
        infer.alloc_neg(self)
    }
}

#[derive(Debug, Clone)]
pub struct DeferredSelection {
    pub name: Name,
    pub module: ModuleId,
    pub recv_eff: TypeVar,
    pub result_tv: TypeVar,
    pub result_eff: TypeVar,
    pub owner: Option<DefId>,
    pub cause: ConstraintCause,
}

#[derive(Debug, Clone)]
pub struct DeferredRoleMethodCall {
    pub name: Name,
    pub recv_tv: TypeVar,
    pub arg_tvs: Vec<TypeVar>,
    pub result_tv: TypeVar,
}

#[derive(Debug, Clone)]
pub struct ExtensionMethodInfo {
    pub name: Name,
    pub def: DefId,
    pub module: ModuleId,
    pub visibility: crate::symbols::Visibility,
    pub receiver_expects_computation: bool,
}

#[derive(Debug, Clone)]
pub struct EffectMethodInfo {
    pub name: Name,
    pub effect: Path,
    pub def: DefId,
    pub module: ModuleId,
    pub visibility: crate::symbols::Visibility,
    pub receiver_expects_computation: bool,
}

#[derive(Debug, Clone)]
pub struct TypeFieldInfo {
    pub name: Name,
    pub def: DefId,
}

#[derive(Debug, Clone)]
pub struct TypeFieldSet {
    pub constructor: DefId,
    pub fields: Vec<TypeFieldInfo>,
}

#[derive(Debug, Clone)]
pub struct RefFieldProjection {
    pub type_path: Path,
    pub field: TypeFieldInfo,
    pub fields: Vec<TypeFieldInfo>,
    pub constructor: DefId,
}

pub struct Infer {
    pub arena: TypeArena,
    pub lower: RefCell<FxHashMap<TypeVar, SmallVec<[PosId; 2]>>>,
    pub upper: RefCell<FxHashMap<TypeVar, SmallVec<[NegId; 2]>>>,
    pub lower_members: RefCell<FxHashSet<(TypeVar, PosId)>>,
    pub upper_members: RefCell<FxHashSet<(TypeVar, NegId)>>,
    pub compact_lower_instances: RefCell<FxHashMap<TypeVar, SmallVec<[OwnedSchemeInstance; 2]>>>,
    pub through: RefCell<FxHashSet<TypeVar>>,
    pub levels: RefCell<FxHashMap<TypeVar, u32>>,
    pub origins: RefCell<FxHashMap<TypeVar, TypeOrigin>>,
    pub errors: RefCell<Vec<TypeError>>,
    pub expansive: HashSet<TypeVar>,
    pub variances: HashMap<Path, Vec<Variance>>,
    pub def_tvs: RefCell<FxHashMap<DefId, TypeVar>>,
    pub compact_schemes: RefCell<FxHashMap<DefId, CompactTypeScheme>>,
    pub compact_role_constraints: RefCell<FxHashMap<DefId, Vec<CompactRoleConstraint>>>,
    pub role_impl_candidates: RefCell<FxHashMap<Path, Vec<RoleImplCandidate>>>,
    pub role_arg_infos: RefCell<FxHashMap<Path, Vec<RoleArgInfo>>>,
    pub frozen_schemes: RefCell<FxHashMap<DefId, FrozenScheme>>,
    pub frozen_ref_commits: RefCell<FxHashMap<DefId, ()>>,
    pub role_constraints: RefCell<FxHashMap<DefId, Vec<RoleConstraint>>>,
    pub non_generic_vars: RefCell<FxHashMap<DefId, HashSet<TypeVar>>>,
    pub components: Vec<SmallVec<[DefId; 1]>>,
    pub def_to_component: FxHashMap<DefId, usize>,
    pub component_edges: Vec<RefCell<SmallVec<[usize; 4]>>>,
    pub component_pending_selections: Vec<RefCell<usize>>,
    pub deferred_selections: RefCell<FxHashMap<TypeVar, Vec<DeferredSelection>>>,
    pub selection_var_dependents: RefCell<FxHashMap<TypeVar, SmallVec<[TypeVar; 2]>>>,
    pub deferred_role_method_calls: RefCell<Vec<DeferredRoleMethodCall>>,
    pub resolved_selections: RefCell<FxHashMap<TypeVar, DefId>>,
    pub resolved_ref_field_projections: RefCell<FxHashMap<TypeVar, RefFieldProjection>>,
    pub type_methods: HashMap<Path, HashMap<Name, DefId>>,
    pub type_fields: HashMap<Path, HashMap<Name, DefId>>,
    pub type_field_owners: HashMap<DefId, Path>,
    pub type_field_sets: HashMap<Path, TypeFieldSet>,
    pub ref_type_methods: HashMap<Path, HashMap<Name, DefId>>,
    pub effect_methods: HashMap<Name, Vec<EffectMethodInfo>>,
    pub role_methods: HashMap<Name, RoleMethodInfo>,
    pub role_methods_by_role: RefCell<FxHashMap<Path, Vec<RoleMethodInfo>>>,
    pub extension_methods: HashMap<Name, Vec<ExtensionMethodInfo>>,
}

impl Infer {
    pub fn new() -> Self {
        Self {
            arena: TypeArena::new(),
            lower: RefCell::new(FxHashMap::default()),
            upper: RefCell::new(FxHashMap::default()),
            lower_members: RefCell::new(FxHashSet::default()),
            upper_members: RefCell::new(FxHashSet::default()),
            compact_lower_instances: RefCell::new(FxHashMap::default()),
            through: RefCell::new(FxHashSet::default()),
            levels: RefCell::new(FxHashMap::default()),
            origins: RefCell::new(FxHashMap::default()),
            errors: RefCell::new(Vec::new()),
            expansive: HashSet::new(),
            variances: HashMap::new(),
            def_tvs: RefCell::new(FxHashMap::default()),
            compact_schemes: RefCell::new(FxHashMap::default()),
            compact_role_constraints: RefCell::new(FxHashMap::default()),
            role_impl_candidates: RefCell::new(FxHashMap::default()),
            role_arg_infos: RefCell::new(FxHashMap::default()),
            frozen_schemes: RefCell::new(FxHashMap::default()),
            frozen_ref_commits: RefCell::new(FxHashMap::default()),
            role_constraints: RefCell::new(FxHashMap::default()),
            non_generic_vars: RefCell::new(FxHashMap::default()),
            components: Vec::new(),
            def_to_component: FxHashMap::default(),
            component_edges: Vec::new(),
            component_pending_selections: Vec::new(),
            deferred_selections: RefCell::new(FxHashMap::default()),
            selection_var_dependents: RefCell::new(FxHashMap::default()),
            deferred_role_method_calls: RefCell::new(Vec::new()),
            resolved_selections: RefCell::new(FxHashMap::default()),
            resolved_ref_field_projections: RefCell::new(FxHashMap::default()),
            type_methods: HashMap::new(),
            type_fields: HashMap::new(),
            type_field_owners: HashMap::new(),
            type_field_sets: HashMap::new(),
            ref_type_methods: HashMap::new(),
            effect_methods: HashMap::new(),
            role_methods: HashMap::new(),
            role_methods_by_role: RefCell::new(FxHashMap::default()),
            extension_methods: HashMap::new(),
        }
    }

    pub fn register_level(&self, tv: TypeVar, level: u32) {
        self.levels.borrow_mut().insert(tv, level);
    }

    pub fn register_origin(&self, tv: TypeVar, origin: TypeOrigin) {
        self.origins.borrow_mut().insert(tv, origin);
    }

    pub fn origin_of(&self, tv: TypeVar) -> Option<TypeOrigin> {
        self.origins.borrow().get(&tv).cloned()
    }

    pub fn type_errors(&self) -> Vec<TypeError> {
        self.errors.borrow().clone()
    }

    pub fn report_synthetic_type_error(
        &self,
        kind: crate::diagnostic::TypeErrorKind,
        label: impl Into<String>,
    ) {
        let error = TypeError {
            cause: ConstraintCause::unknown(),
            kind,
            pos: self.alloc_pos(Pos::Bot),
            neg: self.alloc_neg(Neg::Top),
            origins: vec![TypeOrigin::synthetic(label.into())],
        };
        let mut errors = self.errors.borrow_mut();
        if errors
            .iter()
            .any(|existing| existing.kind == error.kind && existing.origins == error.origins)
        {
            return;
        }
        errors.push(error);
    }

    pub fn level_of(&self, tv: TypeVar) -> u32 {
        self.levels.borrow().get(&tv).copied().unwrap_or(0)
    }

    pub fn mark_expansive(&mut self, tv: TypeVar) {
        self.expansive.insert(tv);
    }

    pub fn is_expansive(&self, tv: TypeVar) -> bool {
        self.expansive.contains(&tv)
    }

    pub fn register_def_tv(&self, def: DefId, tv: TypeVar) {
        self.def_tvs.borrow_mut().insert(def, tv);
    }

    pub fn store_compact_scheme(&self, def: DefId, scheme: CompactTypeScheme) {
        self.compact_schemes.borrow_mut().insert(def, scheme);
    }

    pub fn store_compact_role_constraints(
        &self,
        def: DefId,
        constraints: Vec<CompactRoleConstraint>,
    ) {
        self.compact_role_constraints
            .borrow_mut()
            .insert(def, constraints);
    }

    pub fn compact_role_constraints_of(&self, def: DefId) -> Vec<CompactRoleConstraint> {
        self.compact_role_constraints
            .borrow()
            .get(&def)
            .cloned()
            .unwrap_or_default()
    }

    pub fn register_role_impl_candidate(&self, candidate: RoleImplCandidate) {
        let mut map = self.role_impl_candidates.borrow_mut();
        map.entry(candidate.role.clone())
            .or_default()
            .push(candidate);
    }

    pub fn role_impl_candidates_of(&self, role: &Path) -> Vec<RoleImplCandidate> {
        self.role_impl_candidates
            .borrow()
            .get(role)
            .cloned()
            .unwrap_or_default()
    }

    pub fn register_role_arg_infos(&self, role: Path, infos: Vec<RoleArgInfo>) {
        self.role_arg_infos.borrow_mut().insert(role, infos);
    }

    pub fn mark_role_input_args(&self, role: &Path, input_names: &HashSet<String>) {
        let mut infos = self.role_arg_infos.borrow_mut();
        let Some(entries) = infos.get_mut(role) else {
            return;
        };
        for info in entries {
            if input_names.contains(&info.name) {
                info.is_input = true;
            }
        }
    }

    pub fn role_arg_infos_of(&self, role: &Path) -> Vec<RoleArgInfo> {
        self.role_arg_infos
            .borrow()
            .get(role)
            .cloned()
            .unwrap_or_default()
    }

    pub fn store_frozen_scheme(&self, def: DefId, scheme: FrozenScheme) {
        self.frozen_schemes.borrow_mut().insert(def, scheme);
    }

    pub fn mark_frozen_ref_committed(&self, def: DefId) {
        self.frozen_ref_commits.borrow_mut().insert(def, ());
    }

    pub fn is_frozen_ref_committed(&self, def: DefId) -> bool {
        self.frozen_ref_commits.borrow().contains_key(&def)
    }

    pub fn register_role_method(&mut self, name: Name, info: RoleMethodInfo) {
        self.role_methods.insert(name, info.clone());
        self.role_methods_by_role
            .borrow_mut()
            .entry(info.role.clone())
            .or_default()
            .push(info);
    }

    pub fn register_extension_method(&mut self, info: ExtensionMethodInfo) {
        self.extension_methods
            .entry(info.name.clone())
            .or_default()
            .push(info);
    }

    pub fn register_effect_method(&mut self, info: EffectMethodInfo) {
        self.effect_methods
            .entry(info.name.clone())
            .or_default()
            .push(info);
    }

    pub fn set_extension_method_receiver_expects_computation(
        &mut self,
        def: DefId,
        expects_computation: bool,
    ) {
        for infos in self.extension_methods.values_mut() {
            if let Some(info) = infos.iter_mut().find(|info| info.def == def) {
                info.receiver_expects_computation = expects_computation;
                break;
            }
        }
    }

    pub fn set_effect_method_receiver_expects_computation(
        &mut self,
        def: DefId,
        expects_computation: bool,
    ) {
        for infos in self.effect_methods.values_mut() {
            if let Some(info) = infos.iter_mut().find(|info| info.def == def) {
                info.receiver_expects_computation = expects_computation;
                break;
            }
        }
    }

    pub fn role_method_infos_of(&self, role: &Path) -> Vec<RoleMethodInfo> {
        self.role_methods_by_role
            .borrow()
            .get(role)
            .cloned()
            .unwrap_or_default()
    }

    pub fn add_role_constraint(&self, owner: DefId, constraint: RoleConstraint) {
        let mut map = self.role_constraints.borrow_mut();
        let entry = map.entry(owner).or_default();
        if !entry.contains(&constraint) {
            entry.push(constraint);
        }
    }

    pub fn role_constraints_of(&self, def: DefId) -> Vec<RoleConstraint> {
        self.role_constraints
            .borrow()
            .get(&def)
            .cloned()
            .unwrap_or_default()
    }

    pub fn add_non_generic_var(&self, owner: DefId, tv: TypeVar) {
        self.non_generic_vars
            .borrow_mut()
            .entry(owner)
            .or_default()
            .insert(tv);
    }

    pub fn non_generic_vars_of(&self, owner: DefId) -> HashSet<TypeVar> {
        self.non_generic_vars
            .borrow()
            .get(&owner)
            .cloned()
            .unwrap_or_default()
    }

    pub fn is_role_method_def(&self, def: DefId) -> bool {
        self.role_methods.values().any(|info| info.def == def)
    }

    pub fn role_method_info_for_def(&self, def: DefId) -> Option<RoleMethodInfo> {
        self.role_methods
            .values()
            .find(|info| info.def == def)
            .cloned()
    }

    pub fn register_def(&mut self, def: DefId) {
        let idx = {
            let idx = self.components.len();
            self.components.push(SmallVec::from_slice(&[def]));
            idx
        };
        self.def_to_component.insert(def, idx);
        self.component_edges.push(RefCell::new(SmallVec::new()));
        self.component_pending_selections.push(RefCell::new(0));
    }

    pub fn add_edge(&self, from: DefId, to: DefId) {
        let from_idx = self.def_to_component.get(&from).copied();
        let to_idx = self.def_to_component.get(&to).copied();
        let (Some(from_idx), Some(to_idx)) = (from_idx, to_idx) else {
            return;
        };
        if from_idx == to_idx {
            return;
        }
        let edges = &self.component_edges;
        if !edges[from_idx].borrow().contains(&to_idx) {
            edges[from_idx].borrow_mut().push(to_idx);
        }
    }

    pub fn increment_pending_selection(&self, owner: DefId) {
        let Some(idx) = self.def_to_component.get(&owner).copied() else {
            return;
        };
        *self.component_pending_selections[idx].borrow_mut() += 1;
    }

    pub fn decrement_pending_selection(&self, owner: DefId) {
        let Some(idx) = self.def_to_component.get(&owner).copied() else {
            return;
        };
        let mut pending = self.component_pending_selections[idx].borrow_mut();
        *pending = pending.saturating_sub(1);
    }

    pub fn lower_refs_of(&self, tv: TypeVar) -> SmallVec<[PosId; 4]> {
        match self.lower.borrow().get(&tv) {
            Some(v) => v.iter().copied().collect(),
            None => SmallVec::new(),
        }
    }

    pub fn upper_refs_of(&self, tv: TypeVar) -> SmallVec<[NegId; 4]> {
        match self.upper.borrow().get(&tv) {
            Some(v) => v.iter().copied().collect(),
            None => SmallVec::new(),
        }
    }

    pub fn compact_lower_instances_of(&self, tv: TypeVar) -> SmallVec<[OwnedSchemeInstance; 2]> {
        match self.compact_lower_instances.borrow().get(&tv) {
            Some(v) => v.iter().cloned().collect(),
            None => SmallVec::new(),
        }
    }

    pub fn materialize_compact_lower_instance(&self, instance: &OwnedSchemeInstance) -> PosId {
        debug_materialize_compact_lower(self, instance)
    }

    pub fn lowers_of(&self, tv: TypeVar) -> Vec<Pos> {
        let mut lowers = self
            .lower_refs_of(tv)
            .into_iter()
            .map(|id| self.arena.get_pos(id))
            .collect::<Vec<_>>();
        for instance in self.compact_lower_instances_of(tv) {
            let body = debug_materialize_compact_lower(self, &instance);
            lowers.push(self.arena.get_pos(body));
        }
        lowers
    }

    pub fn uppers_of(&self, tv: TypeVar) -> Vec<Neg> {
        self.upper_refs_of(tv)
            .into_iter()
            .map(|id| self.arena.get_neg(id))
            .collect()
    }

    pub fn add_lower<P: IntoPosId>(&self, tv: TypeVar, pos: P) -> bool {
        let pos = pos.into_pos_id(self);
        if !self.lower_members.borrow_mut().insert((tv, pos)) {
            return false;
        }
        self.lower.borrow_mut().entry(tv).or_default().push(pos);
        if let Pos::Var(source) | Pos::Raw(source) = self.arena.get_pos(pos) {
            self.add_selection_var_dependent(source, tv);
        }
        self.resolve_deferred_selections_for(tv);
        self.resolve_deferred_selection_dependents_for(tv);
        true
    }

    fn add_selection_var_dependent(&self, source: TypeVar, dependent: TypeVar) {
        let mut dependents = self.selection_var_dependents.borrow_mut();
        let entry = dependents.entry(source).or_default();
        if !entry.contains(&dependent) {
            entry.push(dependent);
        }
    }

    fn resolve_deferred_selection_dependents_for(&self, source: TypeVar) {
        let mut seen = FxHashSet::default();
        let mut stack = vec![source];
        while let Some(changed) = stack.pop() {
            let dependents = self
                .selection_var_dependents
                .borrow()
                .get(&changed)
                .cloned()
                .unwrap_or_default();
            for dependent in dependents {
                if !seen.insert(dependent) {
                    continue;
                }
                self.resolve_deferred_selections_for(dependent);
                stack.push(dependent);
            }
        }
    }

    pub fn add_upper<N: IntoNegId>(&self, tv: TypeVar, neg: N) -> bool {
        let neg = neg.into_neg_id(self);
        if !self.upper_members.borrow_mut().insert((tv, neg)) {
            return false;
        }
        self.upper.borrow_mut().entry(tv).or_default().push(neg);
        true
    }

    pub fn add_compact_lower_instance(&self, tv: TypeVar, instance: OwnedSchemeInstance) -> bool {
        {
            let mut map = self.compact_lower_instances.borrow_mut();
            let entry = map.entry(tv).or_default();
            if entry.contains(&instance) {
                return false;
            }
            entry.push(instance);
        }
        self.resolve_deferred_selections_for(tv);
        self.resolve_deferred_selection_dependents_for(tv);
        true
    }

    pub fn flush_compact_lower_instances(&self) {
        loop {
            let pending = {
                let mut map = self.compact_lower_instances.borrow_mut();
                if map.is_empty() {
                    break;
                }
                mem::take(&mut *map)
            };
            for (tv, instances) in pending {
                for instance in instances {
                    let body = debug_materialize_compact_lower(self, &instance);
                    self.constrain_instantiated_ref(body, tv);
                }
            }
        }
    }

    pub fn alloc_pos(&self, p: Pos) -> PosId {
        self.arena.alloc_pos(p)
    }

    pub fn alloc_neg(&self, n: Neg) -> NegId {
        self.arena.alloc_neg(n)
    }

    pub fn mark_through(&self, tv: TypeVar) {
        self.through.borrow_mut().insert(tv);
    }

    pub fn is_through(&self, tv: TypeVar) -> bool {
        self.through.borrow().contains(&tv)
    }

    pub fn clear_through(&self, tv: TypeVar) {
        self.through.borrow_mut().remove(&tv);
    }

    pub fn rebuild_type_methods(&mut self, modules: &ModuleTable) {
        self.type_methods.clear();
        self.collect_type_methods(modules, ModuleId(0), Vec::new());
    }

    pub fn register_ref_type_method(&mut self, type_path: Path, name: Name, def: DefId) {
        self.ref_type_methods
            .entry(type_path)
            .or_default()
            .insert(name, def);
    }

    pub fn register_type_field(&mut self, type_path: Path, name: Name, def: DefId) {
        self.type_fields
            .entry(type_path.clone())
            .or_default()
            .insert(name, def);
        self.type_field_owners.insert(def, type_path);
    }

    pub fn type_field_owner(&self, field_def: DefId) -> Option<Path> {
        self.type_field_owners.get(&field_def).cloned()
    }

    pub fn register_type_field_set(
        &mut self,
        type_path: Path,
        constructor: DefId,
        fields: Vec<(Name, DefId)>,
    ) {
        self.type_field_sets.insert(
            type_path,
            TypeFieldSet {
                constructor,
                fields: fields
                    .into_iter()
                    .map(|(name, def)| TypeFieldInfo { name, def })
                    .collect(),
            },
        );
    }

    fn collect_type_methods(
        &mut self,
        modules: &ModuleTable,
        module_id: ModuleId,
        prefix: Vec<Name>,
    ) {
        let node = modules.node(module_id);

        for type_name in node.types.keys() {
            let mut type_path = prefix.clone();
            type_path.push(type_name.clone());
            let Some(&companion_id) = node.modules.get(type_name) else {
                continue;
            };
            let methods = modules
                .node(companion_id)
                .values
                .iter()
                .map(|(name, def)| (name.clone(), *def))
                .collect::<HashMap<_, _>>();
            if !methods.is_empty() {
                self.type_methods.insert(
                    Path {
                        segments: type_path,
                    },
                    methods,
                );
            }
        }

        for (name, child_id) in &node.modules {
            let mut child_prefix = prefix.clone();
            child_prefix.push(name.clone());
            self.collect_type_methods(modules, *child_id, child_prefix);
        }
    }
}

fn debug_materialize_compact_lower(infer: &Infer, instance: &OwnedSchemeInstance) -> PosId {
    if let Some(tv) = compact_instance_direct_var(instance) {
        return infer.alloc_pos(Pos::Var(tv));
    }
    crate::scheme::materialize_body(infer, instance)
}

fn compact_instance_direct_var(instance: &OwnedSchemeInstance) -> Option<TypeVar> {
    let ty = &instance.scheme.compact.cty.lower;
    if ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && ty.vars.len() == 1
    {
        ty.vars
            .iter()
            .copied()
            .next()
            .map(|tv| crate::simplify::compact::subst_lookup_small(instance.subst.as_slice(), tv))
    } else {
        None
    }
}
