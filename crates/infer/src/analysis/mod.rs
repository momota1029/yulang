//! constraint / selection / SCC の間をつなぐ coordinator。
//!
//! constraint machine は型の上下界だけを伝播し、selection や SCC の意味は知らない。
//! `AnalysisSession` は constraint event を見て selection probe を起こし、名前解決や method selection が
//! 確定したら `poly` へ解決結果を書き戻しつつ SCC machine へ dependency を渡す。

#[allow(
    dead_code,
    reason = "Stage 2 capture is retained as the input to the later joint-freeze/artifact slice"
)]
mod cache_interface;
mod method_taint;
mod projection;
mod session;
#[cfg(test)]
mod tests;
mod timing;
mod trace;
mod work;

use std::{collections::VecDeque, sync::OnceLock};

use poly::expr::{Arena as PolyArena, Def, DefId, SelectId};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, RolePredicate, RolePredicateArg, Scheme,
    Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::arena::Arena as InferArena;
use crate::casts::CastTable;
#[cfg(test)]
use crate::compact::compact_reachable_role_constraints;
use crate::compact::{
    CompactBounds, CompactCastApplication, CompactCastKey, CompactMergeConstraint,
    CompactMergeConstraintKey, CompactRoleArg, CompactRoleConstraint, CompactRoot,
    CompactSimplification, CompactSubtypeConstraintKey, CompactType, IntervalDominanceMetrics,
    apply_compact_merge_constraints, apply_compact_subtype_constraints,
    coalesce_floor_interval_equalities, coalesce_floor_variable_sandwiches,
    collect_interval_dominance_constraints_with_metrics,
    compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints,
    compact_role_constraint, compact_role_constraint_recording_merge_constraints,
    compact_root_has_interval_bounds, compact_subtype_constraint_keys,
    compact_type_var_recording_merge_constraints,
    compact_type_var_recording_merge_constraints_for_scheme, eliminate_floor_redundant_variables,
    finalize_compact_bounds_to_constraint, finalize_compact_type_to_neg_constraint,
    finalize_compact_type_to_pos_constraint, find_next_compact_cast, normalize_compact_casts,
    normalize_var_substitutions, simplify_compact_root_with_roles_and_non_generic,
    unapplied_compact_merge_constraint_count, unapplied_compact_subtype_constraint_count,
    unapplied_compact_subtype_constraint_count_with_known,
};
use crate::constraints::{ConstraintEpoch, ConstraintEvent, ConstraintWeights, TypeLevel};
use crate::generalize::{
    GeneralizedCompactRoot, apply_compact_simplifications_to_root_and_roles,
    clone_role_impl_candidate_between_arenas, compact_boundary_bound_vars,
    finalize_compact_boundary_bounds, finalize_generalized_compact_root_with_ancestors,
    generalize_alias_expanded_compact_root, generalized_compact_boundary_vars,
    prepare_alias_expanded_compact_root_with_role_variances,
    prune_generalized_compact_root_for_cache,
};
use crate::instantiate::{
    freshen_role_impl_candidate, instantiate_scheme, instantiate_scheme_with_roles,
};
use crate::methods::{
    CompanionMethodTable, EffectMethodCandidate, EffectMethodTable, RoleMethodTable,
    TypeMethodTable,
};
#[cfg(test)]
use crate::role_solve::coalesce_role_constraints;
use crate::role_solve::{
    RoleResolution, RoleResolutionKey, coalesce_role_constraints_recording_merge_constraints,
    resolve_role_constraints, resolve_role_constraints_with_method_taint_stats,
    resolve_role_constraints_with_stats_and_dispositions, role_constraint_could_resolve,
};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleConstraintTable, RoleEpoch,
    RoleImplTable, RoleInputVariance, RoleInputVarianceTable,
};
use crate::scc::{SccEvent, SccInput, SccMachine};
use crate::time::{Duration, Instant};
use crate::typing::BindingFetch;
use crate::uses::{LocalDefUseTable, RefUseTable, SelectionUse, SelectionUseTable};
pub(crate) use cache_interface::BoundaryCaptureError;
use method_taint::{
    MethodTaintIndex, build_method_taint_index, compact_role_constraint_has_method_taint,
};
use projection::role_impl_member_projection_substitutions;
pub use timing::AnalysisTiming;
use timing::{AnalysisSccEventTimingKind, AnalysisWorkTimingKind, InstantiatePredicateShape};
use trace::{
    AnalysisDrainTrace, AnalysisTraceMode, analysis_trace_mode, analysis_work_kind,
    trace_constraint_events, trace_instantiate_phase, trace_scheme_requested,
    trace_select_bound_limit, trace_select_requested,
};
pub use work::{AnalysisDiagnostic, AnalysisWork, SelectionTarget};

/// 推論中の複数 machine を束ねる session。
///
/// `poly` は最終 IR と解決結果を持つ。`infer` は型制約 machine を持つ。
/// `refs` / `selections` は use-site 型と parent、`scc` は def 間依存を持つ。
/// それぞれの責務を分けたまま、event queue で進行を同期する。
pub struct AnalysisSession {
    pub poly: PolyArena,
    pub infer: InferArena,
    pub local_defs: LocalDefUseTable,
    pub refs: RefUseTable,
    pub selections: SelectionUseTable,
    pub roles: RoleConstraintTable,
    pub role_impls: RoleImplTable,
    pub casts: CastTable,
    pub methods: TypeMethodTable,
    pub effect_methods: EffectMethodTable,
    pub role_methods: RoleMethodTable,
    pub role_input_variances: RoleInputVarianceTable,
    pub local_methods: CompanionMethodTable,
    pub scc: SccMachine,
    role_impl_members: FxHashMap<DefId, DefId>,
    role_impl_member_sets: FxHashMap<DefId, Vec<DefId>>,
    role_impl_member_simplifications: FxHashMap<DefId, Vec<CompactSimplification>>,
    role_impl_member_projections: FxHashMap<DefId, CompactRoot>,
    applied_method_role_resolutions: FxHashSet<RoleResolutionKey>,
    cache_interface_applied_merge_constraints: FxHashSet<CompactMergeConstraintKey>,
    cache_interface_applied_subtype_constraints: FxHashSet<CompactSubtypeConstraintKey>,
    schemes: FxHashMap<DefId, GeneralizedCompactRoot>,
    binding_fetches: FxHashMap<DefId, BindingFetch>,
    diagnostics: Vec<AnalysisDiagnostic>,
    scc_events: Vec<SccEvent>,
    work: VecDeque<AnalysisWork>,
    generalize_compact_shadow: Option<GeneralizeCompactShadow>,
    generalize_compact_cache: Option<GeneralizeCompactCache>,
    generalize_role_view_shadow: Option<GeneralizeRoleViewShadow>,
    timing: AnalysisTiming,
    instantiated_targets: FxHashSet<DefId>,
    def_parent_map: DefParentMapCache,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GeneralizeCompactEpochKey {
    root: TypeVar,
    constraint_epoch: u64,
}

#[derive(Debug, Default)]
struct GeneralizeCompactShadow {
    seen: FxHashSet<GeneralizeCompactEpochKey>,
}

impl GeneralizeCompactShadow {
    fn from_env() -> Option<Self> {
        generalize_compact_shadow_enabled().then(Self::default)
    }

    fn observe(&mut self, root: TypeVar, constraint_epoch: ConstraintEpoch) -> bool {
        !self.seen.insert(GeneralizeCompactEpochKey {
            root,
            constraint_epoch: constraint_epoch.as_u64(),
        })
    }
}

#[derive(Debug, Clone)]
struct GeneralizeCompactCacheEntry {
    compact: CompactRoot,
    merge_constraints: Vec<CompactMergeConstraint>,
}

#[derive(Debug, Default)]
struct GeneralizeCompactCache {
    entries: FxHashMap<GeneralizeCompactEpochKey, GeneralizeCompactCacheEntry>,
}

impl GeneralizeCompactCache {
    fn from_env() -> Option<Self> {
        generalize_compact_cache_enabled().then(Self::default)
    }

    fn get(
        &self,
        root: TypeVar,
        constraint_epoch: ConstraintEpoch,
    ) -> Option<(CompactRoot, Vec<CompactMergeConstraint>)> {
        self.entries
            .get(&GeneralizeCompactEpochKey {
                root,
                constraint_epoch: constraint_epoch.as_u64(),
            })
            .map(|entry| (entry.compact.clone(), entry.merge_constraints.clone()))
    }

    fn insert(
        &mut self,
        root: TypeVar,
        constraint_epoch: ConstraintEpoch,
        compact: &CompactRoot,
        merge_constraints: &[CompactMergeConstraint],
    ) {
        self.entries.insert(
            GeneralizeCompactEpochKey {
                root,
                constraint_epoch: constraint_epoch.as_u64(),
            },
            GeneralizeCompactCacheEntry {
                compact: compact.clone(),
                merge_constraints: merge_constraints.to_vec(),
            },
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GeneralizeRoleViewShadowKey {
    def: DefId,
    root: TypeVar,
    constraint_epoch: u64,
    role_epoch: u64,
    role_count: usize,
    simplification_level: u32,
}

#[derive(Debug, Default)]
struct GeneralizeRoleViewShadow {
    seen: FxHashSet<GeneralizeRoleViewShadowKey>,
}

impl GeneralizeRoleViewShadow {
    fn from_env() -> Option<Self> {
        generalize_role_view_shadow_enabled().then(Self::default)
    }

    fn observe(
        &mut self,
        def: DefId,
        root: TypeVar,
        constraint_epoch: ConstraintEpoch,
        role_epoch: RoleEpoch,
        role_count: usize,
        simplification_boundary: TypeLevel,
    ) -> bool {
        !self.seen.insert(GeneralizeRoleViewShadowKey {
            def,
            root,
            constraint_epoch: constraint_epoch.as_u64(),
            role_epoch: role_epoch.as_u64(),
            role_count,
            simplification_level: simplification_boundary.depth(),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis) struct SccInstantiateUse {
    pub parent: DefId,
    pub target: DefId,
    pub use_value: TypeVar,
}

#[derive(Debug, Default)]
struct DefParentMapCache {
    def_count: Option<usize>,
    parents: FxHashMap<DefId, DefId>,
}

impl DefParentMapCache {
    fn refresh(&mut self, poly: &PolyArena) {
        let def_count = poly.defs.len();
        if self.def_count == Some(def_count) {
            return;
        }
        self.parents = def_parent_map(poly);
        self.def_count = Some(def_count);
    }
}

#[derive(Debug, Default)]
pub(super) struct GeneralizeRootMetrics {
    pub iterations: usize,
    pub constraint_epoch_start: ConstraintEpoch,
    pub constraint_epoch_end: ConstraintEpoch,
    pub role_epoch_start: RoleEpoch,
    pub role_epoch_end: RoleEpoch,
    pub merge_restarts: usize,
    pub subtype_restarts: usize,
    pub cast_restarts: usize,
    pub role_restarts: usize,
    pub first_compact_nodes: usize,
    pub first_compact_vars: FxHashSet<TypeVar>,
    pub compact_iteration_nodes: usize,
    pub compact_iteration_vars: usize,
    pub role_input_constraints: usize,
    pub reachable_role_constraints: usize,
    pub coalesced_role_constraints: usize,
    pub dominance_role_constraints: usize,
    pub dominance_interval_inputs: usize,
    pub dominance_polarity_vars: usize,
    pub dominance_polarity_occurrences: usize,
    pub dominance_subtype_constraints: usize,
    pub role_resolve_inputs: usize,
    pub role_resolutions: usize,
    compact_shape_iterations: usize,
}

impl GeneralizeRootMetrics {
    pub(super) fn record_compact_iteration(&mut self, compact: &CompactRoot) {
        self.iterations += 1;
        if !generalize_shape_metrics_enabled() {
            return;
        }
        let shape = compact_shape_metrics(compact);
        if self.compact_shape_iterations == 0 {
            self.first_compact_nodes = shape.nodes;
            self.first_compact_vars = shape.vars.clone();
        }
        self.compact_shape_iterations += 1;
        self.compact_iteration_nodes += shape.nodes;
        self.compact_iteration_vars += shape.vars.len();
    }

    pub(super) fn record_constraint_epoch_start(&mut self, epoch: ConstraintEpoch) {
        self.constraint_epoch_start = epoch;
        self.constraint_epoch_end = epoch;
    }

    pub(super) fn record_constraint_epoch_end(&mut self, epoch: ConstraintEpoch) {
        self.constraint_epoch_end = epoch;
    }

    pub(super) fn constraint_epoch_delta(&self) -> u64 {
        self.constraint_epoch_end
            .as_u64()
            .saturating_sub(self.constraint_epoch_start.as_u64())
    }

    pub(super) fn record_role_epoch_start(&mut self, epoch: RoleEpoch) {
        self.role_epoch_start = epoch;
        self.role_epoch_end = epoch;
    }

    pub(super) fn record_role_epoch_end(&mut self, epoch: RoleEpoch) {
        self.role_epoch_end = epoch;
    }

    pub(super) fn role_epoch_delta(&self) -> u64 {
        self.role_epoch_end
            .as_u64()
            .saturating_sub(self.role_epoch_start.as_u64())
    }

    pub(super) fn record_merge_restart(&mut self) {
        self.merge_restarts += 1;
    }

    pub(super) fn record_subtype_restart(&mut self) {
        self.subtype_restarts += 1;
    }

    pub(super) fn record_cast_restart(&mut self) {
        self.cast_restarts += 1;
    }

    pub(super) fn record_role_restart(&mut self) {
        self.role_restarts += 1;
    }

    pub(super) fn record_role_constraints(
        &mut self,
        input_count: usize,
        reachable_count: usize,
        coalesced_count: usize,
    ) {
        self.role_input_constraints += input_count;
        self.reachable_role_constraints += reachable_count;
        self.coalesced_role_constraints += coalesced_count;
    }

    pub(super) fn record_dominance_input(&mut self, role_count: usize) {
        self.dominance_role_constraints += role_count;
    }

    pub(super) fn record_dominance_scan(&mut self, dominance: IntervalDominanceMetrics) {
        self.dominance_interval_inputs += dominance.interval_inputs;
        self.dominance_polarity_vars += dominance.polarity_vars;
        self.dominance_polarity_occurrences += dominance.polarity_occurrences;
    }

    pub(super) fn record_dominance_constraints(&mut self, subtype_count: usize) {
        self.dominance_subtype_constraints += subtype_count;
    }

    pub(super) fn record_role_resolve_inputs(&mut self, count: usize) {
        self.role_resolve_inputs += count;
    }

    pub(super) fn record_role_resolutions(&mut self, count: usize) {
        self.role_resolutions += count;
    }

    fn restart_count(&self) -> usize {
        self.merge_restarts + self.subtype_restarts + self.cast_restarts + self.role_restarts
    }
}

fn generalize_shape_metrics_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("YULANG_GENERALIZE_SHAPE_TIMING")
            .is_ok_and(|value| !value.is_empty() && value != "0")
    })
}

fn generalize_compact_shadow_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("YULANG_GENERALIZE_COMPACT_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0")
    })
}

fn generalize_compact_cache_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    // Exact cache keyed by the global constraint epoch. Keep a one-variable opt-out for
    // bisecting inference regressions without rebuilding the compiler.
    *ENABLED.get_or_init(|| match std::env::var("YULANG_GENERALIZE_COMPACT_CACHE") {
        Ok(value) => !value.is_empty() && value != "0",
        Err(_) => true,
    })
}

fn generalize_role_view_shadow_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("YULANG_GENERALIZE_ROLE_VIEW_SHADOW")
            .is_ok_and(|value| !value.is_empty() && value != "0")
    })
}

#[derive(Debug, Default)]
pub(super) struct GeneralizeComponentMetrics {
    pub root_compact_nodes: usize,
    pub root_compact_vars: usize,
    pub unique_compact_vars: FxHashSet<TypeVar>,
    pub compact_iteration_nodes: usize,
    pub compact_iteration_vars: usize,
    pub roots_with_restarts: usize,
    pub max_iterations_per_root: usize,
    pub max_restarts_per_root: usize,
}

impl GeneralizeComponentMetrics {
    pub(super) fn add_root(&mut self, metrics: GeneralizeRootMetrics) {
        let restart_count = metrics.restart_count();
        if restart_count > 0 {
            self.roots_with_restarts += 1;
        }
        self.max_iterations_per_root = self.max_iterations_per_root.max(metrics.iterations);
        self.max_restarts_per_root = self.max_restarts_per_root.max(restart_count);
        self.root_compact_nodes += metrics.first_compact_nodes;
        self.root_compact_vars += metrics.first_compact_vars.len();
        self.unique_compact_vars
            .extend(metrics.first_compact_vars.iter().copied());
        self.compact_iteration_nodes += metrics.compact_iteration_nodes;
        self.compact_iteration_vars += metrics.compact_iteration_vars;
    }
}

#[derive(Debug, Default)]
struct CompactShapeMetrics {
    nodes: usize,
    vars: FxHashSet<TypeVar>,
}

fn compact_shape_metrics(root: &CompactRoot) -> CompactShapeMetrics {
    let mut metrics = CompactShapeMetrics::default();
    record_compact_type_shape(&root.root, &mut metrics);
    for rec in &root.rec_vars {
        metrics.nodes += 1;
        metrics.vars.insert(rec.var);
        record_compact_bounds_shape(&rec.bounds, &mut metrics);
    }
    metrics
}

fn record_compact_type_shape(ty: &CompactType, metrics: &mut CompactShapeMetrics) {
    metrics.nodes += 1;
    metrics.nodes += ty.vars.len() + ty.builtins.len();
    for var in &ty.vars {
        metrics.vars.insert(var.var);
    }
    for args in ty.cons.values() {
        metrics.nodes += 1;
        for arg in args {
            record_compact_bounds_shape(arg, metrics);
        }
    }
    for fun in &ty.funs {
        metrics.nodes += 1;
        record_compact_type_shape(&fun.arg, metrics);
        record_compact_type_shape(&fun.arg_eff, metrics);
        record_compact_type_shape(&fun.ret_eff, metrics);
        record_compact_type_shape(&fun.ret, metrics);
    }
    for record in &ty.records {
        metrics.nodes += 1;
        for field in &record.fields {
            record_compact_type_shape(&field.value, metrics);
        }
    }
    for spread in &ty.record_spreads {
        metrics.nodes += 1;
        for field in &spread.fields {
            record_compact_type_shape(&field.value, metrics);
        }
        record_compact_type_shape(&spread.tail, metrics);
    }
    for variant in &ty.poly_variants {
        metrics.nodes += 1;
        for (_, payload) in &variant.items {
            for item in payload {
                record_compact_type_shape(item, metrics);
            }
        }
    }
    for tuple in &ty.tuples {
        metrics.nodes += 1;
        for item in &tuple.items {
            record_compact_type_shape(item, metrics);
        }
    }
    for row in &ty.rows {
        metrics.nodes += 1;
        for args in row.items.values() {
            metrics.nodes += 1;
            for arg in args {
                record_compact_bounds_shape(arg, metrics);
            }
        }
        record_compact_type_shape(&row.tail, metrics);
    }
}

fn record_compact_bounds_shape(bounds: &CompactBounds, metrics: &mut CompactShapeMetrics) {
    metrics.nodes += 1;
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            record_compact_type_shape(lower, metrics);
            record_compact_type_shape(upper, metrics);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                record_compact_bounds_shape(arg, metrics);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            record_compact_bounds_shape(arg, metrics);
            record_compact_bounds_shape(arg_eff, metrics);
            record_compact_bounds_shape(ret_eff, metrics);
            record_compact_bounds_shape(ret, metrics);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                record_compact_bounds_shape(&field.value, metrics);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payload) in items {
                for item in payload {
                    record_compact_bounds_shape(item, metrics);
                }
            }
        }
    }
}

fn def_parent_map(poly: &PolyArena) -> FxHashMap<DefId, DefId> {
    let mut parents = FxHashMap::default();
    for (parent, def) in poly.defs.iter() {
        match def {
            Def::Mod { children, .. } | Def::Let { children, .. } => {
                for child in children {
                    parents.insert(*child, parent);
                }
            }
            Def::Arg => {}
        }
    }
    parents
}

fn method_target_from_candidates(
    candidates: &[crate::methods::TypeMethodCandidate],
) -> Option<SelectionTarget> {
    match candidates {
        [candidate] => Some(SelectionTarget::Method { def: candidate.def }),
        [] | [_, ..] => None,
    }
}

fn effect_method_target_from_candidates(
    candidates: &[&EffectMethodCandidate],
) -> Option<SelectionTarget> {
    match candidates {
        [candidate] => Some(SelectionTarget::EffectMethod { def: candidate.def }),
        [] | [_, ..] => None,
    }
}

fn collect_subtractability_effect_paths(
    subtractability: &Subtractability,
    out: &mut Vec<Vec<String>>,
) {
    match subtractability {
        Subtractability::Set(path, _) => push_unique_path(out, path.clone()),
        Subtractability::SetMany(families) => {
            for (path, _) in families {
                push_unique_path(out, path.clone());
            }
        }
        Subtractability::Empty
        | Subtractability::All
        | Subtractability::AllExcept(_, _)
        | Subtractability::AllExceptMany(_) => {}
    }
}

fn collect_constraint_weight_effect_paths(weights: &ConstraintWeights, out: &mut Vec<Vec<String>>) {
    collect_stack_weight_effect_paths(&weights.left.to_stack_weight(), out);
}

fn collect_stack_weight_effect_paths(
    weight: &crate::constraints::ConstraintWeight,
    out: &mut Vec<Vec<String>>,
) {
    collect_subtractability_effect_paths(weight.filter_set(), out);
    for subtractability in weight.active_stack_items() {
        collect_subtractability_effect_paths(subtractability, out);
    }
}

fn push_unique_path(out: &mut Vec<Vec<String>>, path: Vec<String>) {
    if !out.contains(&path) {
        out.push(path);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RefPayloadProbe {
    lower: PosId,
    var: Option<TypeVar>,
}

fn collect_pos_top_vars(types: &TypeArena, id: PosId, out: &mut Vec<TypeVar>) {
    match types.pos(id) {
        Pos::Var(var) => out.push(*var),
        Pos::Union(left, right) => {
            collect_pos_top_vars(types, *left, out);
            collect_pos_top_vars(types, *right, out);
        }
        _ => {}
    }
}

fn collect_neg_top_vars(types: &TypeArena, id: NegId, out: &mut Vec<TypeVar>) {
    match types.neg(id) {
        Neg::Var(var) => out.push(*var),
        Neg::Intersection(left, right) => {
            collect_neg_top_vars(types, *left, out);
            collect_neg_top_vars(types, *right, out);
        }
        _ => {}
    }
}
