use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::collections::HashSet;
use std::mem;
use std::time::Duration;

use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

use crate::ids::{DefId, NegId, PosId, TypeVar};
use crate::symbols::{ModuleId, ModuleTable, Name, Path};
use crate::types::arena::TypeArena;
use crate::types::{EffectAtom, Neg, Pos, Variance};

use crate::diagnostic::{ConstraintCause, TypeError, TypeOrigin};
use crate::scheme::{FrozenScheme, OwnedSchemeInstance};
use crate::simplify::compact::CompactTypeScheme;
use crate::simplify::cooccur::CompactRoleConstraint;

pub mod constrain;
pub mod effect_row;
pub mod role;
pub mod selection;

pub use role::{RoleArgInfo, RoleConstraint, RoleConstraintArg, RoleImplCandidate, RoleMethodInfo};
pub(crate) use selection::CastMethodResolution;

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
    pub structural_record_allowed: bool,
    pub receiver_is_plain_pure_value: bool,
}

#[derive(Debug, Clone)]
pub struct DeferredRoleMethodCall {
    pub name: Name,
    pub role_path: Option<Path>,
    pub cast_coercion: bool,
    pub owner: Option<DefId>,
    pub recv_tv: TypeVar,
    pub arg_tvs: Vec<TypeVar>,
    pub result_tv: TypeVar,
}

#[derive(Debug, Clone)]
pub struct HandlerMatchEdge {
    pub actual: TypeVar,
    pub keep: ShiftKeep,
    pub handled: Vec<NegId>,
    pub residual: TypeVar,
    pub solve_open_rows: bool,
    pub cause: ConstraintCause,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShiftKeep {
    None,
    CallBoundary,
    Surface,
    Set(Vec<Path>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EffectSubtractability {
    Empty,
    All,
    AllExcept(Vec<EffectAtom>),
    Set(Vec<EffectAtom>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectVarKind {
    ExactPure,
    GeneratedExecution,
    LatentFunctionResult,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EffectSubtractId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectSubtractFact {
    pub id: EffectSubtractId,
    pub subtractability: EffectSubtractability,
}

/// Subtract ids attached to one side of a weighted constraint.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct EffectConstraintWeight(SmallVec<[EffectSubtractId; 2]>);

impl EffectConstraintWeight {
    pub fn empty() -> Self {
        Self(SmallVec::new())
    }

    pub fn from_ids(ids: impl IntoIterator<Item = EffectSubtractId>) -> Self {
        let mut ids = ids.into_iter().collect::<SmallVec<[_; 2]>>();
        ids.sort();
        ids.dedup();
        Self(ids)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn contains(&self, id: EffectSubtractId) -> bool {
        self.0.contains(&id)
    }

    pub fn iter(&self) -> impl Iterator<Item = EffectSubtractId> + '_ {
        self.0.iter().copied()
    }

    pub fn union(&self, other: &Self) -> Self {
        Self::from_ids(self.iter().chain(other.iter()))
    }
}

/// The `#A/#B` in `T #A <: #B U`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct EffectConstraintWeights {
    pub left: EffectConstraintWeight,
    pub right: EffectConstraintWeight,
}

impl EffectConstraintWeights {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.left.is_empty() && self.right.is_empty()
    }

    pub fn swapped(&self) -> Self {
        Self {
            left: self.right.clone(),
            right: self.left.clone(),
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        Self {
            left: self.left.union(&other.left),
            right: self.right.union(&other.right),
        }
    }
}

/// Lower bounds keep weights separately from the public unweighted bound view.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct WeightedLowerBound {
    pub pos: PosId,
    pub weights: EffectConstraintWeights,
}

/// Upper bounds keep weights separately from the public unweighted bound view.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct WeightedUpperBound {
    pub neg: NegId,
    pub weights: EffectConstraintWeights,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BoundInsert {
    pub unweighted: bool,
    pub weighted: bool,
}

impl EffectSubtractability {
    pub fn from_paths(paths: Vec<Path>) -> Self {
        Self::set(
            paths
                .into_iter()
                .map(|path| EffectAtom {
                    path,
                    args: Vec::new(),
                })
                .collect(),
        )
    }

    pub fn set(atoms: Vec<EffectAtom>) -> Self {
        let atoms = unique_effect_atom_families(atoms);
        if atoms.is_empty() {
            Self::Empty
        } else {
            Self::Set(atoms)
        }
    }

    pub fn all_except(atoms: Vec<EffectAtom>) -> Self {
        let atoms = unique_effect_atom_families(atoms);
        if atoms.is_empty() {
            Self::All
        } else {
            Self::AllExcept(atoms)
        }
    }

    pub fn union(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Empty, other) | (other, Self::Empty) => other,
            (Self::All, _) | (_, Self::All) => Self::All,
            (Self::Set(lhs), Self::Set(rhs)) => Self::set(union_effect_atom_families(lhs, rhs)),
            (Self::AllExcept(excluded), Self::Set(atoms))
            | (Self::Set(atoms), Self::AllExcept(excluded)) => {
                Self::all_except(remove_effect_atom_families(excluded, &atoms))
            }
            (Self::AllExcept(lhs), Self::AllExcept(rhs)) => {
                Self::all_except(intersect_effect_atom_families(lhs, &rhs))
            }
        }
    }

    pub fn allows_atom_family(&self, atom: &EffectAtom) -> bool {
        match self {
            Self::Empty => false,
            Self::All => true,
            Self::AllExcept(excluded) => !excluded
                .iter()
                .any(|excluded| effect_atom_families_overlap(excluded, atom)),
            Self::Set(allowed) => allowed
                .iter()
                .any(|allowed| effect_atom_families_overlap(allowed, atom)),
        }
    }
}

pub fn effect_atom_families_overlap(lhs: &EffectAtom, rhs: &EffectAtom) -> bool {
    lhs.path == rhs.path
}

fn unique_effect_atom_families(atoms: Vec<EffectAtom>) -> Vec<EffectAtom> {
    let mut out = Vec::new();
    for atom in atoms {
        if !out
            .iter()
            .any(|existing| effect_atom_families_overlap(existing, &atom))
        {
            out.push(atom);
        }
    }
    out
}

fn union_effect_atom_families(mut lhs: Vec<EffectAtom>, rhs: Vec<EffectAtom>) -> Vec<EffectAtom> {
    for atom in rhs {
        if !lhs
            .iter()
            .any(|existing| effect_atom_families_overlap(existing, &atom))
        {
            lhs.push(atom);
        }
    }
    lhs
}

fn remove_effect_atom_families(atoms: Vec<EffectAtom>, removed: &[EffectAtom]) -> Vec<EffectAtom> {
    atoms
        .into_iter()
        .filter(|atom| {
            !removed
                .iter()
                .any(|removed| effect_atom_families_overlap(atom, removed))
        })
        .collect()
}

fn intersect_effect_atom_families(lhs: Vec<EffectAtom>, rhs: &[EffectAtom]) -> Vec<EffectAtom> {
    lhs.into_iter()
        .filter(|atom| {
            rhs.iter()
                .any(|rhs| effect_atom_families_overlap(atom, rhs))
        })
        .collect()
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InferProfile {
    pub constrain: Duration,
    pub constrain_instantiated_ref: Duration,
    pub constrain_instantiated_ref_instance: Duration,
    pub add_lower_bound: Duration,
    pub add_upper_bound: Duration,
    pub add_compact_lower_instance: Duration,
    pub add_role_constraint: Duration,
    pub add_non_generic_var: Duration,
    pub add_edge: Duration,
    pub compact_role_constraints_of: Duration,
    pub compact_lower_instances_of: Duration,
}

#[derive(Clone)]
pub struct Infer {
    pub arena: TypeArena,
    pub lower: RefCell<FxHashMap<TypeVar, SmallVec<[PosId; 2]>>>,
    pub upper: RefCell<FxHashMap<TypeVar, SmallVec<[NegId; 2]>>>,
    pub lower_members: RefCell<FxHashSet<(TypeVar, PosId)>>,
    pub upper_members: RefCell<FxHashSet<(TypeVar, NegId)>>,
    pub(crate) weighted_lower_bounds:
        RefCell<FxHashMap<TypeVar, SmallVec<[WeightedLowerBound; 2]>>>,
    pub(crate) weighted_upper_bounds:
        RefCell<FxHashMap<TypeVar, SmallVec<[WeightedUpperBound; 2]>>>,
    pub(crate) weighted_lower_members: RefCell<FxHashSet<(TypeVar, WeightedLowerBound)>>,
    pub(crate) weighted_upper_members: RefCell<FxHashSet<(TypeVar, WeightedUpperBound)>>,
    pub compact_lower_instances: RefCell<FxHashMap<TypeVar, SmallVec<[OwnedSchemeInstance; 2]>>>,
    pub handler_matches: RefCell<Vec<HandlerMatchEdge>>,
    pub handler_match_dependents: RefCell<FxHashMap<TypeVar, SmallVec<[usize; 2]>>>,
    pub effect_boundary_keeps: RefCell<FxHashMap<TypeVar, ShiftKeep>>,
    pub effect_var_kinds: RefCell<FxHashMap<TypeVar, EffectVarKind>>,
    pub effect_subtracts: RefCell<FxHashMap<TypeVar, Vec<EffectSubtractFact>>>,
    pub effect_non_subtracts: RefCell<FxHashMap<TypeVar, FxHashSet<EffectSubtractId>>>,
    pub effect_subtract_call_non_subtract_ids: RefCell<FxHashSet<EffectSubtractId>>,
    pub next_effect_subtract_id: Cell<u32>,
    pub levels: RefCell<FxHashMap<TypeVar, u32>>,
    // 型ノードの最大 level のメモ化（論文 Fig.6 の lazy val level 相当）。
    // var の level は register 後に変わらないので PosId/NegId → level を永続キャッシュできる。
    pub(crate) pos_max_level_cache: RefCell<FxHashMap<PosId, u32>>,
    pub(crate) neg_max_level_cache: RefCell<FxHashMap<NegId, u32>>,
    // 代入版 extrude は型グラフをコピーしないので、コピー結果のキャッシュは不要。
    // --- 診断用（暴走源特定）。YULANG_EXTRUDE_LIMIT 未設定なら無効 ---
    pub(crate) extrude_call_count: std::cell::Cell<u64>,
    pub origins: RefCell<FxHashMap<TypeVar, TypeOrigin>>,
    pub errors: RefCell<Vec<TypeError>>,
    pub expansive: HashSet<TypeVar>,
    pub expansive_context_roots: FxHashMap<TypeVar, Vec<TypeVar>>,
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
    /// DefId → その def を generalize する境界レベル（宣言時の current_level）。
    /// 量化判定の固定された物差し。老化で動く変数 level とは別に控えておく。
    pub def_levels: RefCell<FxHashMap<DefId, u32>>,
    pub components: Vec<SmallVec<[DefId; 1]>>,
    pub def_to_component: FxHashMap<DefId, usize>,
    pub component_edges: Vec<RefCell<SmallVec<[usize; 4]>>>,
    pub component_pending_selections: Vec<RefCell<usize>>,
    pub deferred_selections: RefCell<FxHashMap<TypeVar, Vec<DeferredSelection>>>,
    pub selection_var_dependents: RefCell<FxHashMap<TypeVar, SmallVec<[TypeVar; 2]>>>,
    pub deferred_role_method_calls: RefCell<Vec<DeferredRoleMethodCall>>,
    pub resolved_selections: RefCell<FxHashMap<TypeVar, DefId>>,
    pub resolved_ref_field_projections: RefCell<FxHashMap<TypeVar, RefFieldProjection>>,
    pub ref_projection_preferred_selections: RefCell<FxHashSet<TypeVar>>,
    pub type_methods: HashMap<Path, HashMap<Name, DefId>>,
    pub type_fields: HashMap<Path, HashMap<Name, DefId>>,
    pub type_field_owners: HashMap<DefId, Path>,
    pub type_field_sets: HashMap<Path, TypeFieldSet>,
    pub ref_type_paths: HashSet<Path>,
    pub ref_type_methods: HashMap<Path, HashMap<Name, DefId>>,
    pub effect_methods: HashMap<Name, Vec<EffectMethodInfo>>,
    pub role_methods: HashMap<Name, RoleMethodInfo>,
    pub role_methods_by_role: RefCell<FxHashMap<Path, Vec<RoleMethodInfo>>>,
    pub extension_methods: HashMap<Name, Vec<ExtensionMethodInfo>>,
    profile: RefCell<InferProfile>,
}

impl Infer {
    pub fn new() -> Self {
        Self {
            arena: TypeArena::new(),
            lower: RefCell::new(FxHashMap::default()),
            upper: RefCell::new(FxHashMap::default()),
            lower_members: RefCell::new(FxHashSet::default()),
            upper_members: RefCell::new(FxHashSet::default()),
            weighted_lower_bounds: RefCell::new(FxHashMap::default()),
            weighted_upper_bounds: RefCell::new(FxHashMap::default()),
            weighted_lower_members: RefCell::new(FxHashSet::default()),
            weighted_upper_members: RefCell::new(FxHashSet::default()),
            compact_lower_instances: RefCell::new(FxHashMap::default()),
            handler_matches: RefCell::new(Vec::new()),
            handler_match_dependents: RefCell::new(FxHashMap::default()),
            effect_boundary_keeps: RefCell::new(FxHashMap::default()),
            effect_var_kinds: RefCell::new(FxHashMap::default()),
            effect_subtracts: RefCell::new(FxHashMap::default()),
            effect_non_subtracts: RefCell::new(FxHashMap::default()),
            effect_subtract_call_non_subtract_ids: RefCell::new(FxHashSet::default()),
            next_effect_subtract_id: Cell::new(0),
            levels: RefCell::new(FxHashMap::default()),
            pos_max_level_cache: RefCell::new(FxHashMap::default()),
            neg_max_level_cache: RefCell::new(FxHashMap::default()),
            extrude_call_count: std::cell::Cell::new(0),
            origins: RefCell::new(FxHashMap::default()),
            errors: RefCell::new(Vec::new()),
            expansive: HashSet::new(),
            expansive_context_roots: FxHashMap::default(),
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
            def_levels: RefCell::new(FxHashMap::default()),
            components: Vec::new(),
            def_to_component: FxHashMap::default(),
            component_edges: Vec::new(),
            component_pending_selections: Vec::new(),
            deferred_selections: RefCell::new(FxHashMap::default()),
            selection_var_dependents: RefCell::new(FxHashMap::default()),
            deferred_role_method_calls: RefCell::new(Vec::new()),
            resolved_selections: RefCell::new(FxHashMap::default()),
            resolved_ref_field_projections: RefCell::new(FxHashMap::default()),
            ref_projection_preferred_selections: RefCell::new(FxHashSet::default()),
            type_methods: HashMap::new(),
            type_fields: HashMap::new(),
            type_field_owners: HashMap::new(),
            type_field_sets: HashMap::new(),
            ref_type_paths: HashSet::new(),
            ref_type_methods: HashMap::new(),
            effect_methods: HashMap::new(),
            role_methods: HashMap::new(),
            role_methods_by_role: RefCell::new(FxHashMap::default()),
            extension_methods: HashMap::new(),
            profile: RefCell::new(InferProfile::default()),
        }
    }

    pub fn profile(&self) -> InferProfile {
        self.profile.borrow().clone()
    }

    pub(crate) fn record_profile(
        &self,
        start: crate::profile::ProfileClock,
        record: impl FnOnce(&mut InferProfile, Duration),
    ) {
        if !crate::profile::profile_enabled() {
            return;
        }
        let elapsed = start.elapsed();
        record(&mut self.profile.borrow_mut(), elapsed);
    }

    pub fn register_level(&self, tv: TypeVar, level: u32) {
        let previous = self.levels.borrow_mut().insert(tv, level);
        if previous != Some(level) {
            self.pos_max_level_cache.borrow_mut().clear();
            self.neg_max_level_cache.borrow_mut().clear();
        }
    }

    pub fn register_origin(&self, tv: TypeVar, origin: TypeOrigin) {
        self.origins.borrow_mut().insert(tv, origin);
    }

    pub fn register_effect_var_kind(&self, tv: TypeVar, kind: EffectVarKind) {
        let mut kinds = self.effect_var_kinds.borrow_mut();
        match (kinds.get(&tv).copied(), kind) {
            (Some(EffectVarKind::ExactPure), _) => {}
            (_, EffectVarKind::ExactPure) => {
                kinds.insert(tv, EffectVarKind::ExactPure);
            }
            (
                None,
                kind @ (EffectVarKind::GeneratedExecution | EffectVarKind::LatentFunctionResult),
            ) => {
                kinds.insert(tv, kind);
            }
            (Some(EffectVarKind::GeneratedExecution), EffectVarKind::GeneratedExecution) => {}
            (Some(EffectVarKind::GeneratedExecution), EffectVarKind::LatentFunctionResult)
            | (Some(EffectVarKind::LatentFunctionResult), EffectVarKind::GeneratedExecution)
            | (Some(EffectVarKind::LatentFunctionResult), EffectVarKind::LatentFunctionResult) => {}
        }
    }

    pub fn effect_var_kind(&self, tv: TypeVar) -> Option<EffectVarKind> {
        self.effect_var_kinds.borrow().get(&tv).copied()
    }

    pub fn effect_var_is_exact_pure(&self, tv: TypeVar) -> bool {
        self.effect_var_kind(tv) == Some(EffectVarKind::ExactPure)
    }

    pub fn effect_var_defaults_to_empty(&self, tv: TypeVar) -> bool {
        matches!(
            self.effect_var_kind(tv),
            Some(EffectVarKind::ExactPure | EffectVarKind::GeneratedExecution)
        )
    }

    pub fn effect_var_is_latent_function_result(&self, tv: TypeVar) -> bool {
        self.effect_var_kind(tv) == Some(EffectVarKind::LatentFunctionResult)
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
        self.report_synthetic_type_error_with_cause(kind, label, ConstraintCause::unknown());
    }

    pub fn report_synthetic_type_error_with_cause(
        &self,
        kind: crate::diagnostic::TypeErrorKind,
        label: impl Into<String>,
        cause: ConstraintCause,
    ) {
        self.report_synthetic_type_error_with_cause_and_origins(kind, label, cause, Vec::new());
    }

    pub fn report_synthetic_type_error_with_cause_and_origins(
        &self,
        kind: crate::diagnostic::TypeErrorKind,
        label: impl Into<String>,
        cause: ConstraintCause,
        origins: Vec<TypeOrigin>,
    ) {
        let mut all_origins = Vec::with_capacity(origins.len() + 1);
        all_origins.push(TypeOrigin::synthetic(label.into()));
        all_origins.extend(origins);
        let error = TypeError {
            cause,
            kind,
            pos: self.alloc_pos(Pos::Bot),
            neg: self.alloc_neg(Neg::Top),
            origins: all_origins,
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

    pub fn mark_expansive_computation_roots(
        &mut self,
        tv: TypeVar,
        roots: impl IntoIterator<Item = TypeVar>,
    ) {
        self.expansive.insert(tv);
        let entry = self.expansive_context_roots.entry(tv).or_default();
        for root in roots {
            if !entry.contains(&root) {
                entry.push(root);
            }
        }
    }

    pub fn is_expansive(&self, tv: TypeVar) -> bool {
        self.expansive.contains(&tv)
    }

    pub fn expansive_context_roots_of(&self, tv: TypeVar) -> Vec<TypeVar> {
        self.expansive_context_roots
            .get(&tv)
            .cloned()
            .unwrap_or_default()
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
        let start = crate::profile::ProfileClock::now();
        let constraints = self
            .compact_role_constraints
            .borrow()
            .get(&def)
            .cloned()
            .unwrap_or_default();
        self.record_profile(start, |profile, elapsed| {
            profile.compact_role_constraints_of += elapsed;
        });
        constraints
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

    pub fn frozen_scheme_of(&self, def: DefId) -> Option<FrozenScheme> {
        if let Some(scheme) = self.frozen_schemes.borrow().get(&def).cloned() {
            return Some(scheme);
        }
        let compact = self.compact_schemes.borrow().get(&def).cloned()?;
        let constraints = self.compact_role_constraints_of(def);
        let extra_quantified =
            crate::scheme::collect_compact_role_constraint_free_vars(&constraints);
        let frozen = crate::scheme::freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
            self,
            compact,
            extra_quantified.as_slice(),
            &self.non_generic_vars_of(def),
        );
        self.store_frozen_scheme(def, frozen.clone());
        Some(frozen)
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
        let start = crate::profile::ProfileClock::now();
        let mut map = self.role_constraints.borrow_mut();
        let entry = map.entry(owner).or_default();
        if !entry.contains(&constraint) {
            entry.push(constraint);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.add_role_constraint += elapsed;
        });
    }

    pub fn role_constraints_of(&self, def: DefId) -> Vec<RoleConstraint> {
        self.role_constraints
            .borrow()
            .get(&def)
            .cloned()
            .unwrap_or_default()
    }

    pub fn has_role_constraints(&self, def: DefId) -> bool {
        self.role_constraints
            .borrow()
            .get(&def)
            .is_some_and(|constraints| !constraints.is_empty())
    }

    pub fn add_non_generic_var(&self, owner: DefId, tv: TypeVar) {
        let start = crate::profile::ProfileClock::now();
        self.non_generic_vars
            .borrow_mut()
            .entry(owner)
            .or_default()
            .insert(tv);
        self.record_profile(start, |profile, elapsed| {
            profile.add_non_generic_var += elapsed;
        });
    }

    pub fn non_generic_vars_of(&self, owner: DefId) -> HashSet<TypeVar> {
        self.non_generic_vars
            .borrow()
            .get(&owner)
            .cloned()
            .unwrap_or_default()
    }

    pub fn register_def_level(&self, def: DefId, level: u32) {
        self.def_levels.borrow_mut().insert(def, level);
    }

    pub fn def_level_of(&self, def: DefId) -> u32 {
        self.def_levels.borrow().get(&def).copied().unwrap_or(0)
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
        let start = crate::profile::ProfileClock::now();
        let from_idx = self.def_to_component.get(&from).copied();
        let to_idx = self.def_to_component.get(&to).copied();
        let (Some(from_idx), Some(to_idx)) = (from_idx, to_idx) else {
            self.record_profile(start, |profile, elapsed| {
                profile.add_edge += elapsed;
            });
            return;
        };
        if from_idx == to_idx {
            self.record_profile(start, |profile, elapsed| {
                profile.add_edge += elapsed;
            });
            return;
        }
        let edges = &self.component_edges;
        if !edges[from_idx].borrow().contains(&to_idx) {
            edges[from_idx].borrow_mut().push(to_idx);
        }
        self.record_profile(start, |profile, elapsed| {
            profile.add_edge += elapsed;
        });
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

    pub(crate) fn weighted_lower_bounds_of(
        &self,
        tv: TypeVar,
    ) -> SmallVec<[WeightedLowerBound; 4]> {
        match self.weighted_lower_bounds.borrow().get(&tv) {
            Some(v) => v.iter().cloned().collect(),
            None => SmallVec::new(),
        }
    }

    pub(crate) fn weighted_upper_bounds_of(
        &self,
        tv: TypeVar,
    ) -> SmallVec<[WeightedUpperBound; 4]> {
        match self.weighted_upper_bounds.borrow().get(&tv) {
            Some(v) => v.iter().cloned().collect(),
            None => SmallVec::new(),
        }
    }

    pub fn compact_lower_instances_of(&self, tv: TypeVar) -> SmallVec<[OwnedSchemeInstance; 2]> {
        let start = crate::profile::ProfileClock::now();
        let instances = match self.compact_lower_instances.borrow().get(&tv) {
            Some(v) => v.iter().cloned().collect(),
            None => SmallVec::new(),
        };
        self.record_profile(start, |profile, elapsed| {
            profile.compact_lower_instances_of += elapsed;
        });
        instances
    }

    pub fn materialize_compact_lower_instance(&self, instance: &OwnedSchemeInstance) -> PosId {
        materialize_compact_lower(self, instance)
    }

    pub fn lowers_of(&self, tv: TypeVar) -> Vec<Pos> {
        let mut lowers = self
            .lower_refs_of(tv)
            .into_iter()
            .map(|id| self.arena.get_pos(id))
            .collect::<Vec<_>>();
        for instance in self.compact_lower_instances_of(tv) {
            let body = materialize_compact_lower(self, &instance);
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
        let inserted = self.add_lower_raw(tv, pos);
        if !inserted {
            return false;
        }
        self.resolve_deferred_selections_for(tv);
        self.resolve_deferred_selection_dependents_for(tv);
        true
    }

    /// deferred selection 解決をトリガーしない生の lower 追加。
    /// 論文 extrude の `nvs.lowerBounds = ...`（純粋な bounds 代入）に対応する。
    /// add_lower は副作用で deferred selection を発火するため、extrude 内で使うと
    /// selection 解決 → constrain → extrude → add_lower … の無限再帰に落ちる。
    pub fn add_lower_raw<P: IntoPosId>(&self, tv: TypeVar, pos: P) -> bool {
        let pos = pos.into_pos_id(self);
        self.add_weighted_lower_raw(tv, pos, EffectConstraintWeights::empty())
            .unweighted
    }

    pub(crate) fn add_weighted_lower_raw(
        &self,
        tv: TypeVar,
        pos: PosId,
        weights: EffectConstraintWeights,
    ) -> BoundInsert {
        let unweighted = self.insert_unweighted_lower(tv, pos);
        let bound = WeightedLowerBound { pos, weights };
        let weighted = self
            .weighted_lower_members
            .borrow_mut()
            .insert((tv, bound.clone()));
        if weighted {
            self.weighted_lower_bounds
                .borrow_mut()
                .entry(tv)
                .or_default()
                .push(bound);
        }
        BoundInsert {
            unweighted,
            weighted,
        }
    }

    fn insert_unweighted_lower(&self, tv: TypeVar, pos: PosId) -> bool {
        if !self.lower_members.borrow_mut().insert((tv, pos)) {
            return false;
        }
        self.lower.borrow_mut().entry(tv).or_default().push(pos);
        if let Pos::Var(source) | Pos::Raw(source) = self.arena.get_pos(pos) {
            self.add_selection_var_dependent(source, tv);
        }
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
        self.add_weighted_upper_raw(tv, neg, EffectConstraintWeights::empty())
            .unweighted
    }

    pub(crate) fn add_weighted_upper_raw(
        &self,
        tv: TypeVar,
        neg: NegId,
        weights: EffectConstraintWeights,
    ) -> BoundInsert {
        let unweighted = self.insert_unweighted_upper(tv, neg);
        let bound = WeightedUpperBound { neg, weights };
        let weighted = self
            .weighted_upper_members
            .borrow_mut()
            .insert((tv, bound.clone()));
        if weighted {
            self.weighted_upper_bounds
                .borrow_mut()
                .entry(tv)
                .or_default()
                .push(bound);
        }
        BoundInsert {
            unweighted,
            weighted,
        }
    }

    fn insert_unweighted_upper(&self, tv: TypeVar, neg: NegId) -> bool {
        if !self.upper_members.borrow_mut().insert((tv, neg)) {
            return false;
        }
        self.upper.borrow_mut().entry(tv).or_default().push(neg);
        true
    }

    pub fn add_compact_lower_instance(&self, tv: TypeVar, instance: OwnedSchemeInstance) -> bool {
        let start = crate::profile::ProfileClock::now();
        {
            let mut map = self.compact_lower_instances.borrow_mut();
            let entry = map.entry(tv).or_default();
            if entry.contains(&instance) {
                self.record_profile(start, |profile, elapsed| {
                    profile.add_compact_lower_instance += elapsed;
                });
                return false;
            }
            entry.push(instance);
        }
        self.resolve_deferred_selections_for(tv);
        self.resolve_deferred_selection_dependents_for(tv);
        self.record_profile(start, |profile, elapsed| {
            profile.add_compact_lower_instance += elapsed;
        });
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
                    let body = materialize_compact_lower(self, &instance);
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

    pub fn reserve_effect_subtract_ids_through(&self, max: EffectSubtractId) {
        let next = max.0.saturating_add(1);
        if self.next_effect_subtract_id.get() < next {
            self.next_effect_subtract_id.set(next);
        }
    }

    pub fn pos_effect_union(&self, items: Vec<PosId>, tail: PosId) -> PosId {
        let mut acc = if self.pos_effect_lower_is_empty(tail) {
            self.arena.bot
        } else {
            tail
        };
        for item in items.into_iter().rev() {
            if self.pos_effect_lower_is_empty(item) {
                continue;
            }
            acc = if self.pos_effect_lower_is_empty(acc) {
                item
            } else {
                self.arena.alloc_pos(Pos::Union(item, acc))
            };
        }
        acc
    }

    pub fn pos_effect_union_node(&self, items: Vec<Pos>, tail: Pos) -> Pos {
        let items = items
            .into_iter()
            .map(|item| self.arena.alloc_pos(item))
            .collect();
        let tail = self.arena.alloc_pos(tail);
        self.arena.get_pos(self.pos_effect_union(items, tail))
    }

    pub fn pos_effect_lower_is_empty(&self, pos: PosId) -> bool {
        match self.arena.get_pos(pos) {
            Pos::Bot => true,
            Pos::Row(items, tail) => items.is_empty() && self.pos_effect_lower_is_empty(tail),
            Pos::Union(left, right) => {
                self.pos_effect_lower_is_empty(left) && self.pos_effect_lower_is_empty(right)
            }
            _ => false,
        }
    }

    pub fn effect_is_all_subtractable(&self, tv: TypeVar) -> bool {
        matches!(
            self.effect_subtractability(tv),
            None | Some(EffectSubtractability::All)
        )
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

    pub fn register_ref_type_path(&mut self, type_path: Path) {
        self.ref_type_paths.insert(type_path);
    }

    pub fn is_ref_type_path(&self, type_path: &Path) -> bool {
        self.ref_type_paths.contains(type_path)
    }

    pub fn primary_ref_type_path(&self) -> Option<Path> {
        self.ref_type_paths.iter().next().cloned()
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

fn materialize_compact_lower(infer: &Infer, instance: &OwnedSchemeInstance) -> PosId {
    if let Some(tv) = compact_instance_direct_var(instance) {
        return infer.alloc_pos(Pos::Var(tv));
    }
    crate::scheme::materialize_body(infer, instance)
}

fn compact_instance_direct_var(instance: &OwnedSchemeInstance) -> Option<TypeVar> {
    let ty = instance.scheme.compact.cty.lower();
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ref_method_owner_does_not_become_ref_wrapper_type() {
        let mut infer = Infer::new();
        let ref_path = crate::std_ref_paths::standard_ref_type_path();
        let list_path = Path {
            segments: vec![
                Name("std".to_string()),
                Name("list".to_string()),
                Name("list".to_string()),
            ],
        };
        let push = Name("push".to_string());
        let push_def = DefId(1);

        infer.register_ref_type_path(ref_path.clone());
        infer.register_ref_type_method(list_path.clone(), push.clone(), push_def);

        assert_eq!(infer.primary_ref_type_path(), Some(ref_path));
        assert!(!infer.is_ref_type_path(&list_path));
        assert_eq!(
            infer
                .ref_type_methods
                .get(&list_path)
                .and_then(|methods| methods.get(&push).copied()),
            Some(push_def),
        );
    }
}
