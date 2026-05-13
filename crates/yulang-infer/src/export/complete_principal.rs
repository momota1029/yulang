//! Build fully-principal export evidence for runtime specialization.
//!
//! This module owns the infer-side algorithm that should eventually make
//! runtime monomorphization a direct type-substitution step.  The key rule is
//! that co-occurrence and polar elimination are applied at the export slot that
//! owns the evidence, not as one global type-variable union.
//!
//! The longer-term target is principal elaboration evidence, not just a
//! substitution table.  A call site should expose the type it naturally
//! synthesizes, the contextual type required by the parent expression, and the
//! coercion/adapter holes needed to cross that boundary.  Runtime lowering can
//! then fill those holes with `Coerce`, thunk wrappers, `BindHere`, or handler
//! adapters instead of rediscovering the same subtyping facts through demand
//! monomorphization.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::time::Duration;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::time::Instant;
use yulang_typed_ir as typed_ir;

use crate::diagnostic::{
    ExpectedAdapterEdge, ExpectedAdapterEdgeId, ExpectedAdapterEdgeKind, ExpectedEdge,
    ExpectedEdgeId, ExpectedEdgeKind,
};
use crate::ids::{NegId, TypeVar};
use crate::lower::LowerState;
use crate::solve::{Infer, ShiftKeep};
use crate::types::Neg;

use super::names::export_path;
use super::types::{
    collect_core_type_vars, export_coalesced_apply_evidence_bounds,
    export_coalesced_coerce_evidence_bounds, export_coalesced_type_bounds_for_tv,
    export_relevant_type_bounds_for_tv_cached, export_type_bounds_for_tv,
    export_type_bounds_for_tvs, project_core_value_type_or_any,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CompleteApplyPrincipalEvidence {
    pub(super) principal_callee: typed_ir::Type,
    pub(super) substitutions: Vec<typed_ir::TypeSubstitution>,
    pub(super) substitution_candidates: Vec<typed_ir::PrincipalSubstitutionCandidate>,
}

#[derive(Debug, Default)]
pub(crate) struct CompletePrincipalCache {
    monomorphic_types: HashMap<TypeVar, Option<typed_ir::Type>>,
}

#[derive(Debug, Default)]
pub(crate) struct CompletePrincipalStepProfile {
    pub substitutions: Duration,
    pub substitution_slots: Duration,
    pub substitution_export: Duration,
    pub substitution_roles: Duration,
    pub substitution_emit: Duration,
    pub candidates: Duration,
}

struct CompletePrincipalClock {
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    start: Option<Instant>,
}

impl CompletePrincipalClock {
    fn now(enabled: bool) -> Self {
        Self {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            start: enabled.then(Instant::now),
        }
    }

    fn elapsed(&self) -> Duration {
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        {
            self.start.map(|start| start.elapsed()).unwrap_or_default()
        }
        #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
        {
            Duration::ZERO
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedEdgeEvidence {
    pub id: ExpectedEdgeId,
    pub kind: ExpectedEdgeKind,
    pub source_range: Option<typed_ir::SourceRange>,
    pub actual: typed_ir::TypeBounds,
    pub expected: typed_ir::TypeBounds,
    pub actual_effect: Option<typed_ir::TypeBounds>,
    pub expected_effect: Option<typed_ir::TypeBounds>,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedAdapterEdgeEvidence {
    pub id: ExpectedAdapterEdgeId,
    pub source_expected_edge: Option<ExpectedEdgeId>,
    pub kind: ExpectedAdapterEdgeKind,
    pub source_range: Option<typed_ir::SourceRange>,
    pub actual_value: Option<typed_ir::TypeBounds>,
    pub expected_value: Option<typed_ir::TypeBounds>,
    pub actual_effect: Option<typed_ir::TypeBounds>,
    pub expected_effect: Option<typed_ir::TypeBounds>,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandlerMatchEvidence {
    pub id: u32,
    pub source_range: Option<typed_ir::SourceRange>,
    pub actual_effect: typed_ir::TypeBounds,
    pub keep: typed_ir::DelimiterKeepEvidence,
    pub handled: Vec<typed_ir::TypeBounds>,
    pub residual_effect: typed_ir::TypeBounds,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivedExpectedEdgeEvidence {
    pub parent: ExpectedEdgeId,
    pub kind: DerivedExpectedEdgeKind,
    pub polarity: EdgePolarity,
    pub path: Vec<EdgePathSegment>,
    pub actual: typed_ir::TypeBounds,
    pub expected: typed_ir::TypeBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgePolarity {
    Covariant,
    Contravariant,
    Invariant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivedExpectedEdgeKind {
    RecordField,
    TupleItem,
    VariantPayload,
    FunctionParam,
    FunctionReturn,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EdgePathSegment {
    Field(typed_ir::Name),
    TupleIndex(usize),
    VariantCase(typed_ir::Name),
    PayloadIndex(usize),
    FunctionParam,
    FunctionReturn,
}

pub(super) fn complete_coerce_principal_evidence(
    infer: &Infer,
    source_edge: Option<ExpectedEdgeId>,
    actual_tv: TypeVar,
    expected_tv: TypeVar,
) -> typed_ir::CoerceEvidence {
    let relevant_vars = BTreeSet::new();
    let (actual, expected) =
        export_coalesced_coerce_evidence_bounds(infer, actual_tv, expected_tv, &relevant_vars);
    typed_ir::CoerceEvidence {
        source_edge: source_edge.map(|id| id.0),
        actual,
        expected,
    }
}

#[allow(dead_code)]
pub(super) fn complete_apply_principal_evidence(
    infer: &Infer,
    principal_scheme: typed_ir::Scheme,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
) -> Option<CompleteApplyPrincipalEvidence> {
    let slot_bounds = apply_slot_bounds(infer, callee_tv, arg_tv, result_tv);
    let mut cache = CompletePrincipalCache::default();
    complete_apply_principal_evidence_from_slot_bounds_cached(
        infer,
        principal_scheme,
        arg_tv,
        result_tv,
        &slot_bounds,
        callee_edge_evidence,
        arg_edge_evidence,
        &mut cache,
    )
}

#[allow(dead_code)]
pub(super) fn complete_apply_principal_evidence_from_slot_bounds(
    infer: &Infer,
    principal_scheme: typed_ir::Scheme,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
) -> Option<CompleteApplyPrincipalEvidence> {
    let mut cache = CompletePrincipalCache::default();
    complete_apply_principal_evidence_from_slot_bounds_cached(
        infer,
        principal_scheme,
        arg_tv,
        result_tv,
        slot_bounds,
        callee_edge_evidence,
        arg_edge_evidence,
        &mut cache,
    )
}

pub(super) fn complete_apply_principal_evidence_from_slot_bounds_cached(
    infer: &Infer,
    principal_scheme: typed_ir::Scheme,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
    cache: &mut CompletePrincipalCache,
) -> Option<CompleteApplyPrincipalEvidence> {
    complete_apply_principal_evidence_from_slot_bounds_cached_profiled(
        infer,
        principal_scheme,
        arg_tv,
        result_tv,
        slot_bounds,
        callee_edge_evidence,
        arg_edge_evidence,
        None,
        cache,
        None,
    )
}

pub(super) fn complete_apply_principal_evidence_from_slot_bounds_cached_profiled(
    infer: &Infer,
    principal_scheme: typed_ir::Scheme,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
    base_bounds_cache: Option<&mut HashMap<TypeVar, typed_ir::TypeBounds>>,
    cache: &mut CompletePrincipalCache,
    mut profile: Option<&mut CompletePrincipalStepProfile>,
) -> Option<CompleteApplyPrincipalEvidence> {
    let principal_callee = &principal_scheme.body;
    let Some((param, ret)) = principal_fun_param_ret(principal_callee) else {
        return None;
    };
    let params = collect_principal_params(principal_callee);
    if params.is_empty() {
        return None;
    }

    let t = CompletePrincipalClock::now(profile.is_some());
    let mut substitutions = apply_principal_substitutions_from_parts(
        infer,
        &principal_scheme.requirements,
        param,
        ret,
        &params,
        arg_tv,
        result_tv,
        slot_bounds,
        base_bounds_cache,
        cache,
        profile.as_deref_mut(),
    );
    if let Some(profile) = profile.as_deref_mut() {
        profile.substitutions += t.elapsed();
    }
    let mut substitution_candidates = if substitution_vars_cover_params(&substitutions, &params) {
        Vec::new()
    } else {
        let t = CompletePrincipalClock::now(profile.is_some());
        let candidates = apply_principal_substitution_candidates_from_parts(
            principal_callee,
            param,
            ret,
            &params,
            callee_edge_evidence,
            arg_edge_evidence,
            &slot_bounds,
        );
        if let Some(profile) = profile.as_deref_mut() {
            profile.candidates += t.elapsed();
        }
        candidates
    };
    complete_substitutions_from_candidates_and_irrelevant_ret(
        principal_callee,
        ret,
        &params,
        &mut substitutions,
        &mut substitution_candidates,
    );
    (!substitutions.is_empty() || !substitution_candidates.is_empty()).then_some(
        CompleteApplyPrincipalEvidence {
            principal_callee: principal_scheme.body,
            substitutions,
            substitution_candidates,
        },
    )
}

pub fn collect_expected_edge_evidence(state: &LowerState) -> Vec<ExpectedEdgeEvidence> {
    if source_only_expected_edge_evidence_enabled() {
        return collect_source_only_expected_edge_evidence(state);
    }
    if !coalesce_expected_edge_evidence_enabled() {
        return collect_fast_expected_edge_evidence(state);
    }
    let mut coalesce_cache: HashMap<TypeVar, typed_ir::TypeBounds> = HashMap::new();
    state
        .expected_edges
        .iter()
        .map(|edge| complete_expected_edge_evidence_cached(&state.infer, edge, &mut coalesce_cache))
        .collect()
}

fn source_only_expected_edge_evidence_enabled() -> bool {
    std::env::var_os("YULANG_DISABLE_PRINCIPAL_ELABORATE").is_none()
        && std::env::var_os("YULANG_EXPORT_DEBUG_EVIDENCE").is_none()
        && std::env::var_os("YULANG_COALESCE_EXPECTED_EDGE_EVIDENCE").is_none()
}

fn collect_source_only_expected_edge_evidence(state: &LowerState) -> Vec<ExpectedEdgeEvidence> {
    state
        .expected_edges
        .iter()
        .map(|edge| ExpectedEdgeEvidence {
            id: edge.id,
            kind: edge.kind,
            source_range: source_range(edge.cause.span),
            actual: typed_ir::TypeBounds::default(),
            expected: typed_ir::TypeBounds::default(),
            actual_effect: None,
            expected_effect: None,
            closed: false,
            informative: false,
            runtime_usable: false,
        })
        .collect()
}

fn collect_fast_expected_edge_evidence(state: &LowerState) -> Vec<ExpectedEdgeEvidence> {
    let mut vars = HashSet::new();
    for edge in &state.expected_edges {
        vars.insert(edge.actual_tv);
        vars.insert(edge.expected_tv);
        if let Some(tv) = edge.actual_eff {
            vars.insert(tv);
        }
        if let Some(tv) = edge.expected_eff {
            vars.insert(tv);
        }
    }
    let mut vars = vars.into_iter().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    let bounds = export_type_bounds_for_tvs(&state.infer, &vars);
    let mut coalesce_cache = HashMap::new();
    state
        .expected_edges
        .iter()
        .map(|edge| {
            if expected_edge_kind_needs_precise_evidence(edge.kind) {
                complete_expected_edge_evidence_cached(&state.infer, edge, &mut coalesce_cache)
            } else {
                complete_expected_edge_evidence_from_bounds(edge, &bounds)
            }
        })
        .collect()
}

fn expected_edge_kind_needs_precise_evidence(kind: ExpectedEdgeKind) -> bool {
    !matches!(
        kind,
        ExpectedEdgeKind::ApplicationCallee | ExpectedEdgeKind::ApplicationArgument
    )
}

pub fn collect_expected_adapter_edge_evidence(
    state: &LowerState,
) -> Vec<ExpectedAdapterEdgeEvidence> {
    state
        .expected_adapter_edges
        .iter()
        .map(|edge| complete_expected_adapter_edge_evidence(&state.infer, edge))
        .collect()
}

pub fn collect_handler_match_evidence(state: &LowerState) -> Vec<HandlerMatchEvidence> {
    let edges = state.infer.handler_matches.borrow();
    if edges.is_empty() {
        return Vec::new();
    }

    let mut cache: HashMap<TypeVar, typed_ir::TypeBounds> = HashMap::new();
    edges
        .iter()
        .enumerate()
        .map(|(index, edge)| {
            let actual_effect = coalesced_bounds_cached(&state.infer, edge.actual, &mut cache);
            let residual_effect = coalesced_bounds_cached(&state.infer, edge.residual, &mut cache);
            let handled = edge
                .handled
                .iter()
                .map(|handled| handler_match_handled_bounds(&state.infer, *handled, &mut cache))
                .collect::<Vec<_>>();
            let closed = type_bounds_closed(&actual_effect)
                && type_bounds_closed(&residual_effect)
                && handled.iter().all(type_bounds_closed);
            let informative = type_bounds_informative(&actual_effect)
                || type_bounds_informative(&residual_effect)
                || handled.iter().any(type_bounds_informative);
            let runtime_usable = closed
                && informative
                && effect_type_bounds_runtime_usable(&actual_effect)
                && effect_type_bounds_runtime_usable(&residual_effect)
                && handled.iter().all(effect_type_bounds_runtime_usable);
            HandlerMatchEvidence {
                id: index as u32,
                source_range: source_range(edge.cause.span),
                actual_effect,
                keep: export_delimiter_keep_evidence(&edge.keep),
                handled,
                residual_effect,
                closed,
                informative,
                runtime_usable,
            }
        })
        .collect()
}

pub fn collect_derived_expected_edge_evidence(
    state: &LowerState,
) -> Vec<DerivedExpectedEdgeEvidence> {
    collect_expected_edge_evidence_for_derivation(state)
        .iter()
        .flat_map(derive_expected_edge_evidence)
        .collect()
}

fn collect_expected_edge_evidence_for_derivation(state: &LowerState) -> Vec<ExpectedEdgeEvidence> {
    if coalesce_expected_edge_evidence_enabled() {
        let mut coalesce_cache: HashMap<TypeVar, typed_ir::TypeBounds> = HashMap::new();
        return state
            .expected_edges
            .iter()
            .map(|edge| {
                complete_expected_edge_evidence_cached(&state.infer, edge, &mut coalesce_cache)
            })
            .collect();
    }
    collect_fast_expected_edge_evidence(state)
}

fn coalesce_expected_edge_evidence_enabled() -> bool {
    std::env::var_os("YULANG_COALESCE_EXPECTED_EDGE_EVIDENCE").is_some()
}

pub fn derive_all_expected_edge_evidence(
    edges: &[ExpectedEdgeEvidence],
) -> Vec<DerivedExpectedEdgeEvidence> {
    edges
        .iter()
        .flat_map(derive_expected_edge_evidence)
        .collect()
}

fn complete_expected_adapter_edge_evidence(
    infer: &Infer,
    edge: &ExpectedAdapterEdge,
) -> ExpectedAdapterEdgeEvidence {
    let actual_value = edge
        .actual_value
        .map(|tv| export_coalesced_type_bounds_for_tv(infer, tv));
    let expected_value = edge
        .expected_value
        .map(|tv| export_coalesced_type_bounds_for_tv(infer, tv));
    let actual_effect = edge
        .actual_effect
        .map(|tv| export_coalesced_type_bounds_for_tv(infer, tv));
    let expected_effect = edge
        .expected_effect
        .map(|tv| export_coalesced_type_bounds_for_tv(infer, tv));
    let closed = actual_value.as_ref().is_none_or(type_bounds_closed)
        && expected_value.as_ref().is_none_or(type_bounds_closed)
        && actual_effect.as_ref().is_none_or(type_bounds_closed)
        && expected_effect.as_ref().is_none_or(type_bounds_closed);
    let informative = actual_value.as_ref().is_some_and(type_bounds_informative)
        || expected_value.as_ref().is_some_and(type_bounds_informative)
        || actual_effect.as_ref().is_some_and(type_bounds_informative)
        || expected_effect
            .as_ref()
            .is_some_and(type_bounds_informative);
    let runtime_usable = closed
        && informative
        && actual_value
            .as_ref()
            .is_none_or(value_type_bounds_runtime_usable)
        && expected_value
            .as_ref()
            .is_none_or(value_type_bounds_runtime_usable)
        && actual_effect
            .as_ref()
            .is_none_or(effect_type_bounds_runtime_usable)
        && expected_effect
            .as_ref()
            .is_none_or(effect_type_bounds_runtime_usable);
    ExpectedAdapterEdgeEvidence {
        id: edge.id,
        source_expected_edge: edge.source_expected_edge,
        kind: edge.kind,
        source_range: source_range(edge.cause.span),
        actual_value,
        expected_value,
        actual_effect,
        expected_effect,
        closed,
        informative,
        runtime_usable,
    }
}

#[cfg(test)]
fn complete_expected_edge_evidence(infer: &Infer, edge: &ExpectedEdge) -> ExpectedEdgeEvidence {
    let mut cache = HashMap::new();
    complete_expected_edge_evidence_cached(infer, edge, &mut cache)
}

fn coalesced_bounds_cached(
    infer: &Infer,
    tv: TypeVar,
    cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
) -> typed_ir::TypeBounds {
    if let Some(cached) = cache.get(&tv) {
        return cached.clone();
    }
    let bounds = export_coalesced_type_bounds_for_tv(infer, tv);
    cache.insert(tv, bounds.clone());
    bounds
}

fn handler_match_handled_bounds(
    infer: &Infer,
    handled: NegId,
    cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
) -> typed_ir::TypeBounds {
    match infer.arena.get_neg(handled) {
        Neg::Atom(atom) => typed_ir::TypeBounds::exact(typed_ir::Type::Named {
            path: export_path(&atom.path),
            args: atom
                .args
                .iter()
                .map(|(pos, neg)| {
                    let lower = coalesced_bounds_cached(infer, *pos, cache)
                        .lower
                        .unwrap_or_else(|| Box::new(typed_ir::Type::Var(export_type_var(*pos))));
                    let upper = coalesced_bounds_cached(infer, *neg, cache)
                        .upper
                        .unwrap_or_else(|| Box::new(typed_ir::Type::Var(export_type_var(*neg))));
                    typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                        lower: Some(lower),
                        upper: Some(upper),
                    })
                })
                .collect(),
        }),
        Neg::Var(tv) => coalesced_bounds_cached(infer, tv, cache),
        _ => typed_ir::TypeBounds::default(),
    }
}

fn export_type_var(tv: TypeVar) -> typed_ir::TypeVar {
    typed_ir::TypeVar(format!("t{}", tv.0))
}

fn export_delimiter_keep_evidence(keep: &ShiftKeep) -> typed_ir::DelimiterKeepEvidence {
    match keep {
        ShiftKeep::None | ShiftKeep::CallBoundary => typed_ir::DelimiterKeepEvidence::None,
        ShiftKeep::Surface => typed_ir::DelimiterKeepEvidence::Surface,
        ShiftKeep::Set(paths) => {
            typed_ir::DelimiterKeepEvidence::Set(paths.iter().map(export_path).collect())
        }
    }
}

fn complete_expected_edge_evidence_cached(
    infer: &Infer,
    edge: &ExpectedEdge,
    cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
) -> ExpectedEdgeEvidence {
    let actual = coalesced_bounds_cached(infer, edge.actual_tv, cache);
    let expected = coalesced_bounds_cached(infer, edge.expected_tv, cache);
    let actual_effect = edge
        .actual_eff
        .map(|tv| coalesced_bounds_cached(infer, tv, cache));
    let expected_effect = edge
        .expected_eff
        .map(|tv| coalesced_bounds_cached(infer, tv, cache));
    let closed = type_bounds_closed(&actual)
        && type_bounds_closed(&expected)
        && actual_effect.as_ref().is_none_or(type_bounds_closed)
        && expected_effect.as_ref().is_none_or(type_bounds_closed);
    let informative = type_bounds_informative(&actual)
        || type_bounds_informative(&expected)
        || actual_effect.as_ref().is_some_and(type_bounds_informative)
        || expected_effect
            .as_ref()
            .is_some_and(type_bounds_informative);
    let runtime_usable = closed
        && informative
        && value_type_bounds_runtime_usable(&actual)
        && value_type_bounds_runtime_usable(&expected)
        && actual_effect
            .as_ref()
            .is_none_or(effect_type_bounds_runtime_usable)
        && expected_effect
            .as_ref()
            .is_none_or(effect_type_bounds_runtime_usable);
    ExpectedEdgeEvidence {
        id: edge.id,
        kind: edge.kind,
        source_range: source_range(edge.cause.span),
        actual,
        expected,
        actual_effect,
        expected_effect,
        closed,
        informative,
        runtime_usable,
    }
}

fn complete_expected_edge_evidence_from_bounds(
    edge: &ExpectedEdge,
    bounds: &HashMap<TypeVar, typed_ir::TypeBounds>,
) -> ExpectedEdgeEvidence {
    let actual = bounds.get(&edge.actual_tv).cloned().unwrap_or_default();
    let expected = bounds.get(&edge.expected_tv).cloned().unwrap_or_default();
    let actual_effect = edge
        .actual_eff
        .map(|tv| bounds.get(&tv).cloned().unwrap_or_default());
    let expected_effect = edge
        .expected_eff
        .map(|tv| bounds.get(&tv).cloned().unwrap_or_default());
    let closed = type_bounds_closed(&actual)
        && type_bounds_closed(&expected)
        && actual_effect.as_ref().is_none_or(type_bounds_closed)
        && expected_effect.as_ref().is_none_or(type_bounds_closed);
    let informative = type_bounds_informative(&actual)
        || type_bounds_informative(&expected)
        || actual_effect.as_ref().is_some_and(type_bounds_informative)
        || expected_effect
            .as_ref()
            .is_some_and(type_bounds_informative);
    let runtime_usable = closed
        && informative
        && value_type_bounds_runtime_usable(&actual)
        && value_type_bounds_runtime_usable(&expected)
        && actual_effect
            .as_ref()
            .is_none_or(effect_type_bounds_runtime_usable)
        && expected_effect
            .as_ref()
            .is_none_or(effect_type_bounds_runtime_usable);
    ExpectedEdgeEvidence {
        id: edge.id,
        kind: edge.kind,
        source_range: source_range(edge.cause.span),
        actual,
        expected,
        actual_effect,
        expected_effect,
        closed,
        informative,
        runtime_usable,
    }
}

fn source_range(range: Option<rowan::TextRange>) -> Option<typed_ir::SourceRange> {
    range.map(|range| typed_ir::SourceRange {
        start: u32::from(range.start()),
        end: u32::from(range.end()),
    })
}

fn apply_principal_substitutions_from_parts(
    infer: &Infer,
    _requirements: &[typed_ir::RoleRequirement],
    param: &typed_ir::Type,
    ret: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
    mut base_bounds_cache: Option<&mut HashMap<TypeVar, typed_ir::TypeBounds>>,
    cache: &mut CompletePrincipalCache,
    mut profile: Option<&mut CompletePrincipalStepProfile>,
) -> Vec<typed_ir::TypeSubstitution> {
    let mut unifier = PrincipalSubstitutionUnifier::new(&params);
    let t = CompletePrincipalClock::now(profile.is_some());
    if let Some(arg_ty) = monomorphic_type_from_bounds_ref(&slot_bounds.arg) {
        unifier.infer_value(param, arg_ty);
    }
    if let Some(result_ty) = monomorphic_type_from_bounds_ref(&slot_bounds.result) {
        unifier.infer_value(ret, result_ty);
    }
    if let Some(profile) = profile.as_deref_mut() {
        profile.substitution_slots += t.elapsed();
    }

    let t = CompletePrincipalClock::now(profile.is_some());
    if !unifier.covers_params() {
        if let Some(arg_ty) = export_monomorphic_type_for_tv_cached(
            infer,
            arg_tv,
            base_bounds_cache.as_deref_mut(),
            cache,
        ) {
            unifier.infer_value(param, &arg_ty);
        }
        if let Some(result_ty) = export_monomorphic_type_for_tv_cached(
            infer,
            result_tv,
            base_bounds_cache.as_deref_mut(),
            cache,
        ) {
            unifier.infer_value(ret, &result_ty);
        }
    }
    if let Some(profile) = profile.as_deref_mut() {
        profile.substitution_export += t.elapsed();
    }

    if let Some(profile) = profile.as_deref_mut() {
        profile.substitution_roles += Duration::ZERO;
    }

    let t = CompletePrincipalClock::now(profile.is_some());
    let substitutions = unifier
        .into_substitutions()
        .filter(|(_, ty)| substitution_type_usable(ty, false))
        .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
        .collect::<Vec<_>>();
    if let Some(profile) = profile.as_deref_mut() {
        profile.substitution_emit += t.elapsed();
    }
    substitutions
}

fn complete_substitutions_from_candidates_and_irrelevant_ret(
    principal_callee: &typed_ir::Type,
    ret: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    substitutions: &mut Vec<typed_ir::TypeSubstitution>,
    candidates: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    promote_unambiguous_candidate_substitutions(substitutions, candidates);
    let covered = substitutions
        .iter()
        .map(|substitution| substitution.var.clone())
        .collect::<BTreeSet<_>>();
    let mut result_value_vars = BTreeSet::new();
    collect_runtime_value_type_vars(ret, &mut result_value_vars);
    let mut callee_value_vars = BTreeSet::new();
    collect_runtime_value_type_vars(principal_callee, &mut callee_value_vars);
    for param in params {
        if covered.contains(param) || result_value_vars.contains(param) {
            continue;
        }
        substitutions.push(typed_ir::TypeSubstitution {
            var: param.clone(),
            ty: if callee_value_vars.contains(param) {
                typed_ir::Type::Tuple(Vec::new())
            } else {
                typed_ir::Type::Never
            },
        });
    }
    let covered = substitutions
        .iter()
        .map(|substitution| substitution.var.clone())
        .collect::<BTreeSet<_>>();
    candidates.retain(|candidate| !covered.contains(&candidate.var));
}

fn promote_unambiguous_candidate_substitutions(
    substitutions: &mut Vec<typed_ir::TypeSubstitution>,
    candidates: &[typed_ir::PrincipalSubstitutionCandidate],
) {
    let covered = substitutions
        .iter()
        .map(|substitution| substitution.var.clone())
        .collect::<BTreeSet<_>>();
    let mut by_var = BTreeMap::<typed_ir::TypeVar, Vec<typed_ir::Type>>::new();
    for candidate in candidates {
        if covered.contains(&candidate.var) || !substitution_type_usable(&candidate.ty, false) {
            continue;
        }
        let choices = by_var.entry(candidate.var.clone()).or_default();
        if !choices.contains(&candidate.ty) {
            choices.push(candidate.ty.clone());
        }
    }
    for (var, choices) in by_var {
        if choices.len() != 1 {
            continue;
        }
        let ty = choices.into_iter().next().unwrap_or(typed_ir::Type::Never);
        substitutions.push(typed_ir::TypeSubstitution { var, ty });
    }
}

fn collect_runtime_value_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_runtime_value_type_arg_vars(arg, vars);
            }
        }
        typed_ir::Type::Fun { param, ret, .. } => {
            collect_runtime_value_type_vars(param, vars);
            collect_runtime_value_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_runtime_value_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_runtime_value_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        collect_runtime_value_type_vars(ty, vars);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_runtime_value_type_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_runtime_value_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_runtime_value_type_vars(item, vars);
            }
            collect_runtime_value_type_vars(tail, vars);
        }
        typed_ir::Type::Recursive { body, .. } => collect_runtime_value_type_vars(body, vars),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
    }
}

fn collect_runtime_value_type_arg_vars(
    arg: &typed_ir::TypeArg,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_runtime_value_type_vars(ty, vars),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = &bounds.lower {
                collect_runtime_value_type_vars(lower, vars);
            }
            if let Some(upper) = &bounds.upper {
                collect_runtime_value_type_vars(upper, vars);
            }
        }
    }
}

fn collect_principal_params(principal_callee: &typed_ir::Type) -> BTreeSet<typed_ir::TypeVar> {
    let mut params = BTreeSet::new();
    collect_core_type_vars(principal_callee, &mut params);
    params
}

fn apply_principal_substitution_candidates_from_parts(
    principal_callee: &typed_ir::Type,
    param: &typed_ir::Type,
    ret: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
    slot_bounds: &ApplySlotBounds,
) -> Vec<typed_ir::PrincipalSubstitutionCandidate> {
    let mut candidates = Vec::new();
    collect_candidates_from_bounds(
        principal_callee,
        &slot_bounds.callee,
        &params,
        callee_edge_evidence.map(|e| e.id),
        &mut vec![typed_ir::PrincipalSlotPathSegment::Callee],
        &mut candidates,
    );
    if let Some(evidence) = callee_edge_evidence {
        collect_candidates_from_expected_edge(
            evidence,
            &params,
            &mut vec![typed_ir::PrincipalSlotPathSegment::Callee],
            &mut candidates,
        );
    }
    collect_candidates_from_bounds(
        param,
        &slot_bounds.arg,
        &params,
        arg_edge_evidence.map(|e| e.id),
        &mut vec![typed_ir::PrincipalSlotPathSegment::Arg],
        &mut candidates,
    );
    if let Some(evidence) = arg_edge_evidence {
        collect_candidates_from_expected_edge(
            evidence,
            &params,
            &mut vec![typed_ir::PrincipalSlotPathSegment::Arg],
            &mut candidates,
        );
    }
    collect_candidates_from_bounds(
        ret,
        &slot_bounds.result,
        &params,
        None,
        &mut vec![typed_ir::PrincipalSlotPathSegment::Result],
        &mut candidates,
    );
    dedupe_principal_substitution_candidates(&mut candidates);
    candidates
}

#[allow(dead_code)]
pub(super) fn residual_apply_principal_scheme(
    infer: &Infer,
    principal_scheme: &typed_ir::Scheme,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Option<typed_ir::Scheme> {
    let mut cache = CompletePrincipalCache::default();
    residual_apply_principal_scheme_cached(
        infer,
        principal_scheme,
        callee_tv,
        arg_tv,
        result_tv,
        &mut cache,
    )
}

pub(super) fn residual_apply_principal_scheme_cached(
    infer: &Infer,
    principal_scheme: &typed_ir::Scheme,
    _callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    cache: &mut CompletePrincipalCache,
) -> Option<typed_ir::Scheme> {
    let principal_callee = &principal_scheme.body;
    let Some((param, ret)) = principal_fun_param_ret(principal_callee) else {
        return None;
    };
    let params = collect_principal_params(principal_callee);
    let substitutions = apply_principal_substitutions_from_monomorphic_tvs(
        infer,
        &principal_scheme.requirements,
        param,
        ret,
        &params,
        arg_tv,
        result_tv,
        cache,
    );
    let substitutions = substitutions
        .into_iter()
        .map(|substitution| (substitution.var, substitution.ty))
        .collect::<BTreeMap<_, _>>();
    let body = substitute_core_type(&principal_scheme.body, &substitutions);
    let (_, ret) = principal_fun_param_ret(&body)?;
    Some(typed_ir::Scheme {
        requirements: principal_scheme.requirements.clone(),
        body: ret.clone(),
    })
}

fn apply_principal_substitutions_from_monomorphic_tvs(
    infer: &Infer,
    _requirements: &[typed_ir::RoleRequirement],
    param: &typed_ir::Type,
    ret: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    cache: &mut CompletePrincipalCache,
) -> Vec<typed_ir::TypeSubstitution> {
    if params.is_empty() {
        return Vec::new();
    }
    let mut unifier = PrincipalSubstitutionUnifier::new(params);
    if let Some(arg_ty) = export_monomorphic_type_for_tv_cached(infer, arg_tv, None, cache) {
        unifier.infer_value(param, &arg_ty);
    }
    if let Some(result_ty) = export_monomorphic_type_for_tv_cached(infer, result_tv, None, cache) {
        unifier.infer_value(ret, &result_ty);
    }
    unifier
        .into_substitutions()
        .filter(|(_, ty)| substitution_type_usable(ty, false))
        .map(|(var, ty)| typed_ir::TypeSubstitution { var, ty })
        .collect()
}

fn substitution_vars_cover_params(
    substitutions: &[typed_ir::TypeSubstitution],
    params: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    if params.is_empty() {
        return true;
    }
    let substitution_vars = substitutions
        .iter()
        .map(|substitution| &substitution.var)
        .collect::<BTreeSet<_>>();
    params.iter().all(|param| substitution_vars.contains(param))
}

pub(super) struct ApplySlotBounds {
    pub(super) callee: typed_ir::TypeBounds,
    pub(super) arg: typed_ir::TypeBounds,
    pub(super) result: typed_ir::TypeBounds,
}

fn apply_slot_bounds(
    infer: &Infer,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> ApplySlotBounds {
    let relevant_vars = BTreeSet::new();
    let (callee, arg, result) =
        export_coalesced_apply_evidence_bounds(infer, callee_tv, arg_tv, result_tv, &relevant_vars);
    ApplySlotBounds {
        callee,
        arg,
        result,
    }
}

fn monomorphic_type_from_bounds_ref(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::Type> {
    bounds
        .lower
        .as_deref()
        .and_then(primary_structural_or_concrete_type)
        .or_else(|| {
            bounds
                .upper
                .as_deref()
                .and_then(primary_structural_or_concrete_type)
        })
        .filter(|ty| substitution_type_usable(ty, false))
}

fn collect_candidates_from_bounds(
    template: &typed_ir::Type,
    bounds: &typed_ir::TypeBounds,
    params: &BTreeSet<typed_ir::TypeVar>,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<typed_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    if !type_mentions_any_param(template, params) {
        return;
    }
    if let Some(lower) = &bounds.lower {
        collect_candidates_from_type(
            template,
            lower,
            params,
            typed_ir::PrincipalCandidateRelation::Lower,
            source_edge,
            path,
            out,
        );
    }
    if let Some(upper) = &bounds.upper {
        collect_candidates_from_type(
            template,
            upper,
            params,
            typed_ir::PrincipalCandidateRelation::Upper,
            source_edge,
            path,
            out,
        );
    }
    if let (Some(lower), Some(upper)) = (&bounds.lower, &bounds.upper)
        && lower == upper
    {
        collect_candidates_from_type(
            template,
            lower,
            params,
            typed_ir::PrincipalCandidateRelation::Exact,
            source_edge,
            path,
            out,
        );
    }
}

fn collect_candidates_from_type(
    template: &typed_ir::Type,
    actual: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    relation: typed_ir::PrincipalCandidateRelation,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<typed_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    match (template, actual) {
        (typed_ir::Type::Var(var), actual) if params.contains(var) => {
            if principal_candidate_type_recordable(var, actual) {
                out.push(typed_ir::PrincipalSubstitutionCandidate {
                    var: var.clone(),
                    relation,
                    ty: actual.clone(),
                    source_edge: source_edge.map(|id| id.0),
                    path: path.clone(),
                });
            }
        }
        (
            typed_ir::Type::Named {
                path: template_path,
                args,
            },
            typed_ir::Type::Named {
                path: actual_path,
                args: actual_args,
            },
        ) if template_path == actual_path && args.len() == actual_args.len() => {
            for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                collect_candidates_from_arg(
                    template_arg,
                    actual_arg,
                    params,
                    relation,
                    source_edge,
                    path,
                    out,
                );
            }
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect: _,
                ret_effect: _,
                ret,
            },
            typed_ir::Type::Fun {
                param: actual_param,
                param_effect: _,
                ret_effect: _,
                ret: actual_ret,
            },
        ) => {
            path.push(typed_ir::PrincipalSlotPathSegment::FunctionParam);
            collect_candidates_from_type(
                param,
                actual_param,
                params,
                flip_candidate_relation(relation),
                source_edge,
                path,
                out,
            );
            path.pop();

            path.push(typed_ir::PrincipalSlotPathSegment::FunctionReturn);
            collect_candidates_from_type(ret, actual_ret, params, relation, source_edge, path, out);
            path.pop();
        }
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
            if items.len() == actual_items.len() =>
        {
            for (item, actual_item) in items.iter().zip(actual_items) {
                collect_candidates_from_type(
                    item,
                    actual_item,
                    params,
                    relation,
                    source_edge,
                    path,
                    out,
                );
            }
        }
        (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
            for item in items {
                collect_candidates_from_type(
                    item,
                    actual,
                    params,
                    relation,
                    source_edge,
                    path,
                    out,
                );
            }
        }
        (typed_ir::Type::Recursive { body, .. }, actual) => {
            collect_candidates_from_type(body, actual, params, relation, source_edge, path, out);
        }
        (template, typed_ir::Type::Recursive { body, .. }) => {
            collect_candidates_from_type(template, body, params, relation, source_edge, path, out);
        }
        _ => {}
    }
}

fn type_mentions_any_param(ty: &typed_ir::Type, params: &BTreeSet<typed_ir::TypeVar>) -> bool {
    match ty {
        typed_ir::Type::Var(var) => params.contains(var),
        typed_ir::Type::Named { args, .. } => args
            .iter()
            .any(|arg| type_arg_mentions_any_param(arg, params)),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_mentions_any_param(param, params)
                || type_mentions_any_param(param_effect, params)
                || type_mentions_any_param(ret_effect, params)
                || type_mentions_any_param(ret, params)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items)
        | typed_ir::Type::Row { items, .. } => items
            .iter()
            .any(|item| type_mentions_any_param(item, params)),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_mentions_any_param(&field.value, params))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_mentions_any_param(ty, params)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|payload| type_mentions_any_param(payload, params))
            }) || variant
                .tail
                .as_ref()
                .is_some_and(|tail| type_mentions_any_param(tail, params))
        }
        typed_ir::Type::Recursive { body, .. } => type_mentions_any_param(body, params),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn type_arg_mentions_any_param(
    arg: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_mentions_any_param(ty, params),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_mentions_any_param(ty, params))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_mentions_any_param(ty, params))
        }
    }
}

fn collect_candidates_from_arg(
    template: &typed_ir::TypeArg,
    actual: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    relation: typed_ir::PrincipalCandidateRelation,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<typed_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    match (template, actual) {
        (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
            collect_candidates_from_type(
                template,
                actual,
                params,
                relation,
                source_edge,
                path,
                out,
            );
        }
        (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
            if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                collect_candidates_from_type(
                    template,
                    actual,
                    params,
                    relation,
                    source_edge,
                    path,
                    out,
                );
            }
            if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                collect_candidates_from_type(
                    template,
                    actual,
                    params,
                    relation,
                    source_edge,
                    path,
                    out,
                );
            }
        }
        _ => {}
    }
}

fn collect_candidates_from_expected_edge(
    evidence: &ExpectedEdgeEvidence,
    params: &BTreeSet<typed_ir::TypeVar>,
    path_prefix: &mut Vec<typed_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    if let (Some(actual), Some(expected)) = (
        bounds_primary_type(&evidence.actual),
        bounds_primary_type(&evidence.expected),
    ) {
        collect_candidates_from_expected_relation(
            actual,
            expected,
            EdgePolarity::Covariant,
            params,
            Some(evidence.id),
            path_prefix,
            out,
        );
    }
    for derived in derive_expected_edge_evidence(evidence) {
        let Some(actual) = bounds_primary_type(&derived.actual) else {
            continue;
        };
        let Some(expected) = bounds_primary_type(&derived.expected) else {
            continue;
        };
        let old_len = path_prefix.len();
        path_prefix.extend(
            derived
                .path
                .iter()
                .map(principal_slot_path_segment_from_edge_path_segment),
        );
        collect_candidates_from_expected_relation(
            actual,
            expected,
            derived.polarity,
            params,
            Some(evidence.id),
            path_prefix,
            out,
        );
        path_prefix.truncate(old_len);
    }
}

fn collect_candidates_from_expected_relation(
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
    polarity: EdgePolarity,
    params: &BTreeSet<typed_ir::TypeVar>,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<typed_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    let (expected_relation, actual_relation) = match polarity {
        EdgePolarity::Covariant | EdgePolarity::Invariant => (
            typed_ir::PrincipalCandidateRelation::Lower,
            typed_ir::PrincipalCandidateRelation::Upper,
        ),
        EdgePolarity::Contravariant => (
            typed_ir::PrincipalCandidateRelation::Upper,
            typed_ir::PrincipalCandidateRelation::Lower,
        ),
    };
    collect_candidates_from_type(
        expected,
        actual,
        params,
        expected_relation,
        source_edge,
        path,
        out,
    );
    collect_candidates_from_type(
        actual,
        expected,
        params,
        actual_relation,
        source_edge,
        path,
        out,
    );
}

fn principal_slot_path_segment_from_edge_path_segment(
    segment: &EdgePathSegment,
) -> typed_ir::PrincipalSlotPathSegment {
    match segment {
        EdgePathSegment::Field(name) => typed_ir::PrincipalSlotPathSegment::Field(name.clone()),
        EdgePathSegment::TupleIndex(index) => {
            typed_ir::PrincipalSlotPathSegment::TupleIndex(*index)
        }
        EdgePathSegment::VariantCase(name) => {
            typed_ir::PrincipalSlotPathSegment::VariantCase(name.clone())
        }
        EdgePathSegment::PayloadIndex(index) => {
            typed_ir::PrincipalSlotPathSegment::PayloadIndex(*index)
        }
        EdgePathSegment::FunctionParam => typed_ir::PrincipalSlotPathSegment::FunctionParam,
        EdgePathSegment::FunctionReturn => typed_ir::PrincipalSlotPathSegment::FunctionReturn,
    }
}

fn dedupe_principal_substitution_candidates(
    candidates: &mut Vec<typed_ir::PrincipalSubstitutionCandidate>,
) {
    let mut deduped = Vec::with_capacity(candidates.len());
    for candidate in candidates.drain(..) {
        if !deduped.iter().any(|existing| existing == &candidate) {
            deduped.push(candidate);
        }
    }
    *candidates = deduped;
}

fn flip_candidate_relation(
    relation: typed_ir::PrincipalCandidateRelation,
) -> typed_ir::PrincipalCandidateRelation {
    match relation {
        typed_ir::PrincipalCandidateRelation::Lower => typed_ir::PrincipalCandidateRelation::Upper,
        typed_ir::PrincipalCandidateRelation::Upper => typed_ir::PrincipalCandidateRelation::Lower,
        typed_ir::PrincipalCandidateRelation::Exact => typed_ir::PrincipalCandidateRelation::Exact,
    }
}

fn principal_candidate_type_recordable(var: &typed_ir::TypeVar, ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Any | typed_ir::Type::Never => false,
        typed_ir::Type::Var(actual) => actual != var,
        _ => true,
    }
}

fn principal_fun_param_ret(ty: &typed_ir::Type) -> Option<(&typed_ir::Type, &typed_ir::Type)> {
    match ty {
        typed_ir::Type::Fun { param, ret, .. } => Some((param, ret)),
        typed_ir::Type::Recursive { body, .. } => principal_fun_param_ret(body),
        typed_ir::Type::Inter(items) | typed_ir::Type::Union(items) => {
            items.iter().find_map(principal_fun_param_ret)
        }
        _ => None,
    }
}

fn substitute_core_type(
    ty: &typed_ir::Type,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => substitutions
            .get(var)
            .cloned()
            .unwrap_or_else(|| typed_ir::Type::Var(var.clone())),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_core_type_arg(arg, substitutions))
                .collect(),
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(substitute_core_type(param, substitutions)),
            param_effect: Box::new(substitute_core_type(param_effect, substitutions)),
            ret_effect: Box::new(substitute_core_type(ret_effect, substitutions)),
            ret: Box::new(substitute_core_type(ret, substitutions)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: substitute_core_type(&field.value, substitutions),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(substitute_core_type(ty, substitutions)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(substitute_core_type(ty, substitutions)))
                }
            }),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name.clone(),
                    payloads: case
                        .payloads
                        .iter()
                        .map(|payload| substitute_core_type(payload, substitutions))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(substitute_core_type(tail, substitutions))),
        }),
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
            tail: Box::new(substitute_core_type(tail, substitutions)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
        ),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(substitute_core_type(body, substitutions)),
        },
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => ty.clone(),
    }
}

fn substitute_core_type_arg(
    arg: &typed_ir::TypeArg,
    substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(substitute_core_type(ty, substitutions))
        }
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(substitute_core_type(ty, substitutions))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(substitute_core_type(ty, substitutions))),
        }),
    }
}

fn export_monomorphic_type_for_tv_cached(
    infer: &Infer,
    tv: TypeVar,
    base_bounds_cache: Option<&mut HashMap<TypeVar, typed_ir::TypeBounds>>,
    cache: &mut CompletePrincipalCache,
) -> Option<typed_ir::Type> {
    if let Some(cached) = cache.monomorphic_types.get(&tv) {
        return cached.clone();
    }
    let bounds = match base_bounds_cache {
        Some(cache) => {
            export_relevant_type_bounds_for_tv_cached(infer, tv, &BTreeSet::new(), cache)
        }
        None => export_type_bounds_for_tv(infer, tv),
    };
    let ty = bounds
        .lower
        .as_deref()
        .or(bounds.upper.as_deref())
        .cloned()
        .map(|ty| project_core_value_type_or_any(ty, &BTreeSet::new()))
        .filter(|ty| substitution_type_usable(ty, false));
    cache.monomorphic_types.insert(tv, ty.clone());
    ty
}

fn derive_expected_edge_evidence(
    evidence: &ExpectedEdgeEvidence,
) -> Vec<DerivedExpectedEdgeEvidence> {
    let mut derived = Vec::new();
    if let (Some(actual), Some(expected)) = (
        bounds_primary_type(&evidence.actual),
        bounds_primary_type(&evidence.expected),
    ) {
        derive_structural_edges(
            evidence.id,
            EdgePolarity::Covariant,
            actual,
            expected,
            &mut Vec::new(),
            &mut derived,
            0,
        );
    }
    derived
}

const MAX_DERIVED_EDGE_DEPTH: usize = 4;

fn derive_structural_edges(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    match (actual, expected) {
        (typed_ir::Type::Record(actual), typed_ir::Type::Record(expected)) => {
            derive_record_field_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        (typed_ir::Type::Tuple(actual), typed_ir::Type::Tuple(expected)) => {
            derive_tuple_item_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        (typed_ir::Type::Variant(actual), typed_ir::Type::Variant(expected)) => {
            derive_variant_payload_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        (typed_ir::Type::Fun { .. }, typed_ir::Type::Fun { .. }) => {
            derive_function_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        _ => {}
    }
}

fn derive_record_field_edges(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &typed_ir::RecordType,
    expected: &typed_ir::RecordType,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    for expected_field in &expected.fields {
        let Some(actual_field) = actual
            .fields
            .iter()
            .find(|field| field.name == expected_field.name)
        else {
            continue;
        };
        path.push(EdgePathSegment::Field(expected_field.name.clone()));
        push_derived_edge(
            parent,
            DerivedExpectedEdgeKind::RecordField,
            polarity,
            path,
            &actual_field.value,
            &expected_field.value,
            derived,
        );
        derive_child_edge(
            parent,
            polarity,
            &actual_field.value,
            &expected_field.value,
            path,
            derived,
            depth,
        );
        path.pop();
    }
}

fn derive_tuple_item_edges(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &[typed_ir::Type],
    expected: &[typed_ir::Type],
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    if actual.len() != expected.len() {
        return;
    }
    for (index, (actual_item, expected_item)) in actual.iter().zip(expected).enumerate() {
        path.push(EdgePathSegment::TupleIndex(index));
        push_derived_edge(
            parent,
            DerivedExpectedEdgeKind::TupleItem,
            polarity,
            path,
            actual_item,
            expected_item,
            derived,
        );
        derive_child_edge(
            parent,
            polarity,
            actual_item,
            expected_item,
            path,
            derived,
            depth,
        );
        path.pop();
    }
}

fn derive_variant_payload_edges(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &typed_ir::VariantType,
    expected: &typed_ir::VariantType,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    for expected_case in &expected.cases {
        let Some(actual_case) = actual
            .cases
            .iter()
            .find(|case| case.name == expected_case.name)
        else {
            continue;
        };
        if actual_case.payloads.len() != expected_case.payloads.len() {
            continue;
        }
        path.push(EdgePathSegment::VariantCase(expected_case.name.clone()));
        for (index, (actual_payload, expected_payload)) in actual_case
            .payloads
            .iter()
            .zip(&expected_case.payloads)
            .enumerate()
        {
            path.push(EdgePathSegment::PayloadIndex(index));
            push_derived_edge(
                parent,
                DerivedExpectedEdgeKind::VariantPayload,
                polarity,
                path,
                actual_payload,
                expected_payload,
                derived,
            );
            derive_child_edge(
                parent,
                polarity,
                actual_payload,
                expected_payload,
                path,
                derived,
                depth,
            );
            path.pop();
        }
        path.pop();
    }
}

fn derive_function_edges(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    let (
        typed_ir::Type::Fun {
            param: actual_param,
            ret: actual_ret,
            ..
        },
        typed_ir::Type::Fun {
            param: expected_param,
            ret: expected_ret,
            ..
        },
    ) = (actual, expected)
    else {
        return;
    };
    let param_polarity = polarity.flip();
    path.push(EdgePathSegment::FunctionParam);
    push_derived_edge(
        parent,
        DerivedExpectedEdgeKind::FunctionParam,
        param_polarity,
        path,
        actual_param,
        expected_param,
        derived,
    );
    derive_child_edge(
        parent,
        param_polarity,
        actual_param,
        expected_param,
        path,
        derived,
        depth,
    );
    path.pop();

    path.push(EdgePathSegment::FunctionReturn);
    push_derived_edge(
        parent,
        DerivedExpectedEdgeKind::FunctionReturn,
        polarity,
        path,
        actual_ret,
        expected_ret,
        derived,
    );
    derive_child_edge(
        parent,
        polarity,
        actual_ret,
        expected_ret,
        path,
        derived,
        depth,
    );
    path.pop();
}

fn push_derived_edge(
    parent: ExpectedEdgeId,
    kind: DerivedExpectedEdgeKind,
    polarity: EdgePolarity,
    path: &[EdgePathSegment],
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
) {
    derived.push(DerivedExpectedEdgeEvidence {
        parent,
        kind,
        polarity,
        path: path.to_vec(),
        actual: typed_ir::TypeBounds::exact(derived_actual_slot_type(actual, expected)),
        expected: typed_ir::TypeBounds::exact(derived_slot_type(expected)),
    });
}

fn derived_actual_slot_type(actual: &typed_ir::Type, expected: &typed_ir::Type) -> typed_ir::Type {
    let expected = derived_slot_type(expected);
    primary_structural_or_concrete_type_not_equal(actual, &expected)
        .or_else(|| primary_structural_or_concrete_type(actual))
        .unwrap_or(actual)
        .clone()
}

fn derived_slot_type(ty: &typed_ir::Type) -> typed_ir::Type {
    primary_structural_or_concrete_type(ty)
        .unwrap_or(ty)
        .clone()
}

fn derive_child_edge(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &typed_ir::Type,
    expected: &typed_ir::Type,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    if depth + 1 >= MAX_DERIVED_EDGE_DEPTH {
        return;
    }
    let actual = derived_slot_type(actual);
    let expected = derived_slot_type(expected);
    derive_structural_edges(
        parent,
        polarity,
        &actual,
        &expected,
        path,
        derived,
        depth + 1,
    );
}

impl EdgePolarity {
    fn flip(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Invariant => Self::Invariant,
        }
    }
}

fn bounds_primary_type(bounds: &typed_ir::TypeBounds) -> Option<&typed_ir::Type> {
    bounds
        .lower
        .as_deref()
        .and_then(primary_structural_or_concrete_type)
        .or_else(|| {
            bounds
                .upper
                .as_deref()
                .and_then(primary_structural_or_concrete_type)
        })
}

fn primary_structural_or_concrete_type(ty: &typed_ir::Type) -> Option<&typed_ir::Type> {
    match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items
            .iter()
            .find_map(primary_structural_or_concrete_type)
            .or(Some(ty)),
        typed_ir::Type::Var(_) | typed_ir::Type::Any | typed_ir::Type::Never => None,
        _ => Some(ty),
    }
}

fn primary_structural_or_concrete_type_not_equal<'a>(
    ty: &'a typed_ir::Type,
    expected: &typed_ir::Type,
) -> Option<&'a typed_ir::Type> {
    match ty {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items
            .iter()
            .filter_map(primary_structural_or_concrete_type)
            .find(|item| *item != expected),
        typed_ir::Type::Var(_) | typed_ir::Type::Any | typed_ir::Type::Never => None,
        _ if ty != expected => Some(ty),
        _ => None,
    }
}

struct PrincipalSubstitutionUnifier<'a> {
    params: &'a BTreeSet<typed_ir::TypeVar>,
    substitutions: BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    conflicts: BTreeSet<typed_ir::TypeVar>,
}

impl<'a> PrincipalSubstitutionUnifier<'a> {
    fn new(params: &'a BTreeSet<typed_ir::TypeVar>) -> Self {
        Self {
            params,
            substitutions: BTreeMap::new(),
            conflicts: BTreeSet::new(),
        }
    }

    fn covers_params(&self) -> bool {
        self.params
            .iter()
            .all(|param| self.substitutions.contains_key(param))
    }

    fn into_substitutions(self) -> impl Iterator<Item = (typed_ir::TypeVar, typed_ir::Type)> {
        let conflicts = self.conflicts;
        self.substitutions
            .into_iter()
            .filter(move |(var, _)| !conflicts.contains(var))
    }

    fn infer_value(&mut self, template: &typed_ir::Type, actual: &typed_ir::Type) {
        self.infer(template, actual, false);
    }

    fn infer_effect(&mut self, template: &typed_ir::Type, actual: &typed_ir::Type) {
        self.infer(template, actual, true);
    }

    fn infer(&mut self, template: &typed_ir::Type, actual: &typed_ir::Type, allow_never: bool) {
        match (template, actual) {
            (typed_ir::Type::Var(var), actual) if self.params.contains(var) => {
                self.bind(var, actual, allow_never);
            }
            (
                typed_ir::Type::Named { path, args },
                typed_ir::Type::Named {
                    path: actual_path,
                    args: actual_args,
                },
            ) if path == actual_path && args.len() == actual_args.len() => {
                for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                    self.infer_arg(template_arg, actual_arg, allow_never);
                }
            }
            (
                typed_ir::Type::Fun {
                    param,
                    param_effect,
                    ret_effect,
                    ret,
                },
                typed_ir::Type::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                },
            ) => {
                self.infer_value(param, actual_param);
                self.infer_effect(param_effect, actual_param_effect);
                self.infer_effect(ret_effect, actual_ret_effect);
                self.infer_value(ret, actual_ret);
            }
            (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(actual_items))
                if items.len() == actual_items.len() =>
            {
                for (item, actual_item) in items.iter().zip(actual_items) {
                    self.infer(item, actual_item, allow_never);
                }
            }
            (typed_ir::Type::Record(record), typed_ir::Type::Record(actual_record)) => {
                for field in &record.fields {
                    if let Some(actual_field) = actual_record
                        .fields
                        .iter()
                        .find(|actual| actual.name == field.name)
                    {
                        self.infer(&field.value, &actual_field.value, allow_never);
                    }
                }
            }
            (typed_ir::Type::Union(items) | typed_ir::Type::Inter(items), actual) => {
                for item in items {
                    self.infer(item, actual, allow_never);
                }
            }
            (typed_ir::Type::Recursive { var, body }, actual) => {
                if !self.params.contains(var) {
                    self.infer(body, actual, allow_never);
                }
            }
            _ => {}
        }
    }

    fn infer_arg(
        &mut self,
        template: &typed_ir::TypeArg,
        actual: &typed_ir::TypeArg,
        allow_never: bool,
    ) {
        match (template, actual) {
            (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
                self.infer(template, actual, allow_never);
            }
            (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
                if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                    self.infer(template, actual, allow_never);
                }
                if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                    self.infer(template, actual, allow_never);
                }
            }
            _ => {}
        }
    }

    fn bind(&mut self, var: &typed_ir::TypeVar, actual: &typed_ir::Type, allow_never: bool) {
        if !substitution_type_usable(actual, allow_never) {
            return;
        }
        if self.conflicts.contains(var) {
            return;
        }
        match self.substitutions.get(var) {
            Some(existing) if existing == actual => {}
            Some(existing) => {
                if let Some(merged) = merge_substitution_type(existing, actual) {
                    self.substitutions.insert(var.clone(), merged);
                } else {
                    self.substitutions.remove(var);
                    self.conflicts.insert(var.clone());
                }
            }
            None => {
                self.substitutions.insert(var.clone(), actual.clone());
            }
        }
    }
}

fn merge_substitution_type(
    left: &typed_ir::Type,
    right: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if left == right {
        return Some(left.clone());
    }
    if type_has_vars(left) && !type_has_vars(right) {
        return Some(right.clone());
    }
    if !type_has_vars(left) && type_has_vars(right) {
        return Some(left.clone());
    }
    match (left, right) {
        (
            typed_ir::Type::Named { path, args },
            typed_ir::Type::Named {
                path: right_path,
                args: right_args,
            },
        ) if path == right_path && args.len() == right_args.len() => {
            let args = args
                .iter()
                .zip(right_args)
                .map(|(left, right)| merge_type_arg(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Named {
                path: path.clone(),
                args,
            })
        }
        (
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            typed_ir::Type::Fun {
                param: right_param,
                param_effect: right_param_effect,
                ret_effect: right_ret_effect,
                ret: right_ret,
            },
        ) => Some(typed_ir::Type::Fun {
            param: Box::new(merge_substitution_type(param, right_param)?),
            param_effect: Box::new(merge_substitution_type(param_effect, right_param_effect)?),
            ret_effect: Box::new(merge_substitution_type(ret_effect, right_ret_effect)?),
            ret: Box::new(merge_substitution_type(ret, right_ret)?),
        }),
        (typed_ir::Type::Tuple(items), typed_ir::Type::Tuple(right_items))
            if items.len() == right_items.len() =>
        {
            let items = items
                .iter()
                .zip(right_items)
                .map(|(left, right)| merge_substitution_type(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(typed_ir::Type::Tuple(items))
        }
        _ => None,
    }
}

fn merge_type_arg(
    left: &typed_ir::TypeArg,
    right: &typed_ir::TypeArg,
) -> Option<typed_ir::TypeArg> {
    match (left, right) {
        (typed_ir::TypeArg::Type(left), typed_ir::TypeArg::Type(right)) => {
            merge_substitution_type(left, right).map(typed_ir::TypeArg::Type)
        }
        (typed_ir::TypeArg::Type(ty), typed_ir::TypeArg::Bounds(bounds))
        | (typed_ir::TypeArg::Bounds(bounds), typed_ir::TypeArg::Type(ty)) => {
            type_fits_bounds(ty, bounds).then(|| typed_ir::TypeArg::Type(ty.clone()))
        }
        (typed_ir::TypeArg::Bounds(left), typed_ir::TypeArg::Bounds(right)) => {
            Some(typed_ir::TypeArg::Bounds(merge_type_bounds(left, right)?))
        }
    }
}

fn merge_type_bounds(
    left: &typed_ir::TypeBounds,
    right: &typed_ir::TypeBounds,
) -> Option<typed_ir::TypeBounds> {
    let lower = merge_optional_bound(left.lower.as_deref(), right.lower.as_deref())?;
    let upper = merge_optional_bound(left.upper.as_deref(), right.upper.as_deref())?;
    Some(typed_ir::TypeBounds {
        lower: lower.map(Box::new),
        upper: upper.map(Box::new),
    })
}

fn merge_optional_bound(
    left: Option<&typed_ir::Type>,
    right: Option<&typed_ir::Type>,
) -> Option<Option<typed_ir::Type>> {
    match (left, right) {
        (Some(left), Some(right)) => merge_substitution_type(left, right).map(Some),
        (Some(ty), None) | (None, Some(ty)) => Some(Some(ty.clone())),
        (None, None) => Some(None),
    }
}

fn type_fits_bounds(ty: &typed_ir::Type, bounds: &typed_ir::TypeBounds) -> bool {
    bounds
        .lower
        .as_deref()
        .is_none_or(|lower| merge_substitution_type(lower, ty).is_some())
        && bounds
            .upper
            .as_deref()
            .is_none_or(|upper| merge_substitution_type(upper, ty).is_some())
}

fn type_has_vars(ty: &typed_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    !vars.is_empty()
}

fn substitution_type_usable(ty: &typed_ir::Type, allow_never: bool) -> bool {
    !matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_)
    ) && (allow_never || !matches!(ty, typed_ir::Type::Never))
        && !type_has_vars(ty)
        && !type_has_unknown(ty)
}

fn type_has_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_unknown),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_has_unknown(param)
                || type_has_unknown(param_effect)
                || type_has_unknown(ret_effect)
                || type_has_unknown(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_has_unknown),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_has_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_has_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_has_unknown))
                || variant.tail.as_deref().is_some_and(type_has_unknown)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_has_unknown) || type_has_unknown(tail)
        }
        typed_ir::Type::Recursive { body, .. } => type_has_unknown(body),
    }
}

fn type_arg_has_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_has_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_has_unknown)
                || bounds.upper.as_deref().is_some_and(type_has_unknown)
        }
    }
}

fn type_bounds_closed(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds.lower.as_deref().is_none_or(|ty| !type_has_vars(ty))
        && bounds.upper.as_deref().is_none_or(|ty| !type_has_vars(ty))
}

fn type_bounds_informative(bounds: &typed_ir::TypeBounds) -> bool {
    bounds.lower.as_deref().is_some_and(type_informative)
        || bounds.upper.as_deref().is_some_and(type_informative)
}

fn type_informative(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { .. } => true,
        typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record(_)
        | typed_ir::Type::Variant(_) => true,
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_informative) || type_informative(tail)
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            items.iter().any(type_informative)
        }
        typed_ir::Type::Recursive { body, .. } => type_informative(body),
    }
}

fn value_type_bounds_runtime_usable(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds
            .lower
            .as_deref()
            .is_none_or(value_type_runtime_usable)
        && bounds
            .upper
            .as_deref()
            .is_none_or(value_type_runtime_usable)
}

fn effect_type_bounds_runtime_usable(bounds: &typed_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds
            .lower
            .as_deref()
            .is_none_or(effect_type_runtime_usable)
        && bounds
            .upper
            .as_deref()
            .is_none_or(effect_type_runtime_usable)
}

fn value_type_runtime_usable(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Named { args, .. } => args.iter().all(type_arg_runtime_usable),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            value_type_runtime_usable(param)
                && effect_type_runtime_usable(param_effect)
                && effect_type_runtime_usable(ret_effect)
                && value_type_runtime_usable(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().all(value_type_runtime_usable),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| value_type_runtime_usable(&field.value))
                && record
                    .spread
                    .as_ref()
                    .is_none_or(record_spread_runtime_usable)
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(value_type_runtime_usable))
                && variant
                    .tail
                    .as_deref()
                    .is_none_or(value_type_runtime_usable)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(effect_type_runtime_usable) && effect_type_runtime_usable(tail)
        }
        typed_ir::Type::Recursive { body, .. } => value_type_runtime_usable(body),
    }
}

fn effect_type_runtime_usable(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Never => true,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
        typed_ir::Type::Row { items, tail } => {
            items.iter().all(effect_type_runtime_usable) && effect_type_runtime_usable(tail)
        }
        _ => value_type_runtime_usable(ty),
    }
}

fn record_spread_runtime_usable(spread: &typed_ir::RecordSpread) -> bool {
    match spread {
        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
            value_type_runtime_usable(ty)
        }
    }
}

fn type_arg_runtime_usable(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => value_type_runtime_usable(ty),
        typed_ir::TypeArg::Bounds(bounds) => value_type_bounds_runtime_usable(bounds),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowan::SyntaxNode;
    use yulang_parser::sink::YulangLanguage;

    use crate::{LowerState, diagnostic, lower_root};

    fn tv(name: &str) -> typed_ir::TypeVar {
        typed_ir::TypeVar(name.to_string())
    }

    fn named(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn list(arg: typed_ir::TypeArg) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path {
                segments: vec![
                    typed_ir::Name("std".to_string()),
                    typed_ir::Name("list".to_string()),
                    typed_ir::Name("list".to_string()),
                ],
            },
            args: vec![arg],
        }
    }

    fn fun(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn variant(case_name: &str, payloads: Vec<typed_ir::Type>) -> typed_ir::Type {
        typed_ir::Type::Variant(typed_ir::VariantType {
            cases: vec![typed_ir::VariantCase {
                name: typed_ir::Name(case_name.to_string()),
                payloads,
            }],
            tail: None,
        })
    }

    fn record(fields: Vec<(&str, typed_ir::Type)>) -> typed_ir::Type {
        typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .into_iter()
                .map(|(name, value)| typed_ir::RecordField {
                    name: typed_ir::Name(name.to_string()),
                    value,
                    optional: false,
                })
                .collect(),
            spread: None,
        })
    }

    fn parse_and_lower(src: &str) -> LowerState {
        let green = yulang_parser::parse_module_to_green(src);
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        lower_root(&mut state, &root);
        state
    }

    fn one_param_unifier() -> PrincipalSubstitutionUnifier<'static> {
        let params = Box::leak(Box::new(BTreeSet::from([tv("t")])));
        PrincipalSubstitutionUnifier::new(params)
    }

    #[test]
    fn merges_bounds_arg_to_concrete_type_arg() {
        let concrete = list(typed_ir::TypeArg::Type(named("int")));
        let bounded = list(typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: Some(Box::new(named("int"))),
            upper: None,
        }));

        assert_eq!(merge_substitution_type(&bounded, &concrete), Some(concrete));
    }

    #[test]
    fn value_position_does_not_bind_never() {
        let mut unifier = one_param_unifier();
        unifier.infer_value(&typed_ir::Type::Var(tv("t")), &typed_ir::Type::Never);

        assert!(unifier.into_substitutions().next().is_none());
    }

    #[test]
    fn effect_position_can_bind_never() {
        let mut unifier = one_param_unifier();
        unifier.infer_effect(&typed_ir::Type::Var(tv("t")), &typed_ir::Type::Never);

        assert_eq!(
            unifier.into_substitutions().collect::<Vec<_>>(),
            vec![(tv("t"), typed_ir::Type::Never)]
        );
    }

    #[test]
    fn conflicting_candidates_drop_the_substitution() {
        let mut unifier = one_param_unifier();
        unifier.infer_value(&typed_ir::Type::Var(tv("t")), &named("int"));
        unifier.infer_value(&typed_ir::Type::Var(tv("t")), &named("bool"));

        assert!(unifier.into_substitutions().next().is_none());
    }

    #[test]
    fn completes_expected_edge_evidence_with_exported_bounds() {
        let state = parse_and_lower("my f(x: int) = x\nf 1\n");
        let edge = state
            .expected_edges
            .iter()
            .find(|edge| edge.kind == diagnostic::ExpectedEdgeKind::ApplicationArgument)
            .expect("application argument edge");

        let evidence = complete_expected_edge_evidence(&state.infer, edge);

        assert_eq!(evidence.id, edge.id,);
        assert_eq!(
            evidence.kind,
            diagnostic::ExpectedEdgeKind::ApplicationArgument
        );
        assert_eq!(evidence.actual.lower.as_deref(), Some(&named("int")));
        assert_eq!(evidence.expected, typed_ir::TypeBounds::exact(named("int")));
        assert!(evidence.source_range.is_some());
        assert!(evidence.actual_effect.is_none());
        assert!(evidence.expected_effect.is_none());
        assert!(!evidence.closed);
        assert!(evidence.informative);
        assert!(!evidence.runtime_usable);
    }

    #[test]
    fn completes_expected_adapter_edge_evidence_with_exported_bounds() {
        let state = parse_and_lower("pub act out:\n  pub say: str -> ()\n\nout::say \"hi\"\n");

        let evidence = collect_expected_adapter_edge_evidence(&state)
            .into_iter()
            .find(|edge| edge.kind == ExpectedAdapterEdgeKind::EffectOperationArgument)
            .expect("effect operation argument adapter evidence");

        assert!(evidence.source_expected_edge.is_some());
        assert!(evidence.source_range.is_some());
        assert!(evidence.actual_value.is_some());
        assert!(evidence.expected_value.is_some());
        assert!(evidence.actual_effect.is_some());
        assert!(evidence.expected_effect.is_some());
        assert!(evidence.informative);
    }

    #[test]
    fn derives_record_field_expected_edge_evidence() {
        let state = parse_and_lower("my p: { x: int } = { x: 1 }\n");

        let derived = collect_derived_expected_edge_evidence(&state);
        let field = derived
            .iter()
            .find(|edge| {
                edge.kind == DerivedExpectedEdgeKind::RecordField
                    && edge.path == vec![EdgePathSegment::Field(typed_ir::Name("x".to_string()))]
            })
            .expect("record field derived edge");

        assert_eq!(field.actual, typed_ir::TypeBounds::exact(named("int")));
        assert_eq!(field.expected, typed_ir::TypeBounds::exact(named("int")));
        assert_eq!(field.polarity, EdgePolarity::Covariant);
    }

    #[test]
    fn derives_tuple_item_expected_edge_evidence() {
        let state = parse_and_lower("my p: (int, bool) = (1, true)\n");

        let derived = collect_derived_expected_edge_evidence(&state);
        let item = derived
            .iter()
            .find(|edge| {
                edge.kind == DerivedExpectedEdgeKind::TupleItem
                    && edge.path == vec![EdgePathSegment::TupleIndex(1)]
            })
            .expect("tuple item derived edge");

        assert_eq!(item.actual, typed_ir::TypeBounds::exact(named("bool")));
        assert_eq!(item.expected, typed_ir::TypeBounds::exact(named("bool")));
        assert_eq!(item.polarity, EdgePolarity::Covariant);
    }

    #[test]
    fn derives_function_expected_edge_evidence() {
        let evidence = ExpectedEdgeEvidence {
            id: ExpectedEdgeId(7),
            kind: ExpectedEdgeKind::Annotation,
            source_range: None,
            actual: typed_ir::TypeBounds::exact(fun(named("str"), named("bool"))),
            expected: typed_ir::TypeBounds::exact(fun(named("int"), named("int"))),
            actual_effect: None,
            expected_effect: None,
            closed: true,
            informative: true,
            runtime_usable: true,
        };

        let derived = derive_expected_edge_evidence(&evidence);
        let param = derived
            .iter()
            .find(|edge| {
                edge.kind == DerivedExpectedEdgeKind::FunctionParam
                    && edge.path == vec![EdgePathSegment::FunctionParam]
            })
            .expect("function param derived edge");
        let ret = derived
            .iter()
            .find(|edge| {
                edge.kind == DerivedExpectedEdgeKind::FunctionReturn
                    && edge.path == vec![EdgePathSegment::FunctionReturn]
            })
            .expect("function return derived edge");

        assert_eq!(param.parent, ExpectedEdgeId(7));
        assert_eq!(ret.parent, ExpectedEdgeId(7));
        assert_eq!(param.polarity, EdgePolarity::Contravariant);
        assert_eq!(ret.polarity, EdgePolarity::Covariant);
        assert_eq!(param.actual, typed_ir::TypeBounds::exact(named("str")));
        assert_eq!(param.expected, typed_ir::TypeBounds::exact(named("int")));
        assert_eq!(ret.actual, typed_ir::TypeBounds::exact(named("bool")));
        assert_eq!(ret.expected, typed_ir::TypeBounds::exact(named("int")));
    }

    #[test]
    fn derives_variant_payload_expected_edge_evidence() {
        let evidence = ExpectedEdgeEvidence {
            id: ExpectedEdgeId(9),
            kind: ExpectedEdgeKind::Annotation,
            source_range: None,
            actual: typed_ir::TypeBounds::exact(variant("some", vec![named("str"), named("bool")])),
            expected: typed_ir::TypeBounds::exact(variant(
                "some",
                vec![named("int"), named("int")],
            )),
            actual_effect: None,
            expected_effect: None,
            closed: true,
            informative: true,
            runtime_usable: true,
        };

        let derived = derive_expected_edge_evidence(&evidence);
        let payload = derived
            .iter()
            .find(|edge| {
                edge.kind == DerivedExpectedEdgeKind::VariantPayload
                    && edge.path
                        == vec![
                            EdgePathSegment::VariantCase(typed_ir::Name("some".to_string())),
                            EdgePathSegment::PayloadIndex(1),
                        ]
            })
            .expect("variant payload derived edge");

        assert_eq!(payload.parent, ExpectedEdgeId(9));
        assert_eq!(payload.polarity, EdgePolarity::Covariant);
        assert_eq!(payload.actual, typed_ir::TypeBounds::exact(named("bool")));
        assert_eq!(payload.expected, typed_ir::TypeBounds::exact(named("int")));
    }

    #[test]
    fn recursively_derives_nested_expected_edge_evidence() {
        let evidence = ExpectedEdgeEvidence {
            id: ExpectedEdgeId(11),
            kind: ExpectedEdgeKind::Annotation,
            source_range: None,
            actual: typed_ir::TypeBounds::exact(record(vec![(
                "a",
                record(vec![("b", named("str"))]),
            )])),
            expected: typed_ir::TypeBounds::exact(record(vec![(
                "a",
                record(vec![("b", named("int"))]),
            )])),
            actual_effect: None,
            expected_effect: None,
            closed: true,
            informative: true,
            runtime_usable: true,
        };

        let derived = derive_expected_edge_evidence(&evidence);
        let nested = derived
            .iter()
            .find(|edge| {
                edge.kind == DerivedExpectedEdgeKind::RecordField
                    && edge.path
                        == vec![
                            EdgePathSegment::Field(typed_ir::Name("a".to_string())),
                            EdgePathSegment::Field(typed_ir::Name("b".to_string())),
                        ]
            })
            .expect("nested record field derived edge");

        assert_eq!(nested.parent, ExpectedEdgeId(11));
        assert_eq!(nested.polarity, EdgePolarity::Covariant);
        assert_eq!(nested.actual, typed_ir::TypeBounds::exact(named("str")));
        assert_eq!(nested.expected, typed_ir::TypeBounds::exact(named("int")));
    }
}
