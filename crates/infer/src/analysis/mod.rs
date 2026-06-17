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

use std::collections::VecDeque;

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
    CompactCastApplication, CompactCastKey, CompactMergeConstraintKey, CompactRoleArg,
    CompactRoleConstraint, CompactRoot, CompactSimplification, CompactSubtypeConstraintKey,
    apply_compact_merge_constraints, apply_compact_subtype_constraints,
    coalesce_floor_interval_equalities, coalesce_floor_variable_sandwiches,
    collect_interval_dominance_constraints,
    compact_reachable_role_constraints_recording_merge_constraints, compact_role_constraint,
    compact_role_constraint_recording_merge_constraints,
    compact_type_var_recording_merge_constraints,
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
use crate::uses::{RefUseTable, SelectionUse, SelectionUseTable};
use method_taint::{
    MethodTaintIndex, build_method_taint_index, compact_role_constraint_has_method_taint,
};
use projection::role_impl_member_projection_substitutions;
pub use timing::AnalysisTiming;
use timing::{AnalysisWorkTimingKind, InstantiatePredicateShape};
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
    collect_stack_weight_effect_paths(&weights.left, out);
}

fn collect_stack_weight_effect_paths(
    weight: &crate::constraints::ConstraintWeight,
    out: &mut Vec<Vec<String>>,
) {
    for subtractability in weight.stack_items() {
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
