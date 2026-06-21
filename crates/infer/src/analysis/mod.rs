//! constraint / selection / SCC の間をつなぐ coordinator。
//!
//! constraint machine は型の上下界だけを伝播し、selection や SCC の意味は知らない。
//! `AnalysisSession` は constraint event を見て selection probe を起こし、名前解決や method selection が
//! 確定したら `poly` へ解決結果を書き戻しつつ SCC machine へ dependency を渡す。

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
    CompactBounds, CompactCastApplication, CompactCastKey, CompactMergeConstraintKey,
    CompactRoleArg, CompactRoleConstraint, CompactRoot, CompactSimplification,
    CompactSubtypeConstraintKey, CompactType, apply_compact_merge_constraints,
    apply_compact_subtype_constraints, coalesce_floor_interval_equalities,
    coalesce_floor_variable_sandwiches, collect_interval_dominance_constraints,
    compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints,
    compact_role_constraint, compact_role_constraint_recording_merge_constraints,
    compact_root_has_interval_bounds, compact_type_var_recording_merge_constraints,
    compact_type_var_recording_merge_constraints_for_scheme, eliminate_floor_redundant_variables,
    finalize_compact_bounds_to_constraint, finalize_compact_type_to_neg_constraint,
    finalize_compact_type_to_pos_constraint, find_next_compact_cast, normalize_compact_casts,
    normalize_var_substitutions, simplify_compact_root_with_roles_and_non_generic,
};
use crate::constraints::{ConstraintEvent, ConstraintWeights, TypeLevel};
use crate::generalize::{
    GeneralizedCompactRoot, apply_compact_simplifications_to_root_and_roles,
    clone_role_impl_candidate_between_arenas, finalize_generalized_compact_root_with_ancestors,
    generalize_prepared_compact_root_with_role_variances_and_boundaries,
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
    resolve_role_constraints, resolve_role_constraints_with_method_taint,
    role_constraint_could_resolve,
};
use crate::roles::{
    RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg, RoleConstraintTable,
    RoleImplTable, RoleInputVariance, RoleInputVarianceTable,
};
use crate::scc::{SccEvent, SccInput, SccMachine};
use crate::time::{Duration, Instant};
use crate::typing::BindingFetch;
use crate::uses::{LocalDefUseTable, RefUseTable, SelectionUse, SelectionUseTable};
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
    schemes: FxHashMap<DefId, GeneralizedCompactRoot>,
    binding_fetches: FxHashMap<DefId, BindingFetch>,
    diagnostics: Vec<AnalysisDiagnostic>,
    scc_events: Vec<SccEvent>,
    work: VecDeque<AnalysisWork>,
    timing: AnalysisTiming,
    instantiated_targets: FxHashSet<DefId>,
    def_parent_map: DefParentMapCache,
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
    pub first_compact_nodes: usize,
    pub first_compact_vars: FxHashSet<TypeVar>,
    pub compact_iteration_nodes: usize,
    pub compact_iteration_vars: usize,
    compact_iterations: usize,
}

impl GeneralizeRootMetrics {
    pub(super) fn record_compact_iteration(&mut self, compact: &CompactRoot) {
        if !generalize_shape_metrics_enabled() {
            return;
        }
        let shape = compact_shape_metrics(compact);
        if self.compact_iterations == 0 {
            self.first_compact_nodes = shape.nodes;
            self.first_compact_vars = shape.vars.clone();
        }
        self.compact_iterations += 1;
        self.compact_iteration_nodes += shape.nodes;
        self.compact_iteration_vars += shape.vars.len();
    }
}

fn generalize_shape_metrics_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("YULANG_GENERALIZE_SHAPE_TIMING")
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
}

impl GeneralizeComponentMetrics {
    pub(super) fn add_root(&mut self, metrics: GeneralizeRootMetrics) {
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
