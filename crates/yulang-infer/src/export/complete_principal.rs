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
use std::sync::OnceLock;

use yulang_core_ir as core_ir;

use crate::diagnostic::{
    ExpectedAdapterEdge, ExpectedAdapterEdgeId, ExpectedAdapterEdgeKind, ExpectedEdge,
    ExpectedEdgeId, ExpectedEdgeKind,
};
use crate::ids::TypeVar;
use crate::lower::LowerState;
use crate::solve::Infer;

use super::types::{
    collect_core_type_vars, export_coalesced_apply_evidence_bounds,
    export_coalesced_coerce_evidence_bounds, export_coalesced_type_bounds_for_tv,
    export_type_bounds_for_tv, export_type_bounds_for_tvs, project_core_value_type_or_any,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CompleteApplyPrincipalEvidence {
    pub(super) principal_callee: core_ir::Type,
    pub(super) substitutions: Vec<core_ir::TypeSubstitution>,
    pub(super) substitution_candidates: Vec<core_ir::PrincipalSubstitutionCandidate>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedEdgeEvidence {
    pub id: ExpectedEdgeId,
    pub kind: ExpectedEdgeKind,
    pub source_range: Option<core_ir::SourceRange>,
    pub actual: core_ir::TypeBounds,
    pub expected: core_ir::TypeBounds,
    pub actual_effect: Option<core_ir::TypeBounds>,
    pub expected_effect: Option<core_ir::TypeBounds>,
    pub closed: bool,
    pub informative: bool,
    pub runtime_usable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedAdapterEdgeEvidence {
    pub id: ExpectedAdapterEdgeId,
    pub source_expected_edge: Option<ExpectedEdgeId>,
    pub kind: ExpectedAdapterEdgeKind,
    pub source_range: Option<core_ir::SourceRange>,
    pub actual_value: Option<core_ir::TypeBounds>,
    pub expected_value: Option<core_ir::TypeBounds>,
    pub actual_effect: Option<core_ir::TypeBounds>,
    pub expected_effect: Option<core_ir::TypeBounds>,
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
    pub actual: core_ir::TypeBounds,
    pub expected: core_ir::TypeBounds,
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
    Field(core_ir::Name),
    TupleIndex(usize),
    VariantCase(core_ir::Name),
    PayloadIndex(usize),
    FunctionParam,
    FunctionReturn,
}

pub(super) fn complete_coerce_principal_evidence(
    infer: &Infer,
    source_edge: Option<ExpectedEdgeId>,
    actual_tv: TypeVar,
    expected_tv: TypeVar,
) -> core_ir::CoerceEvidence {
    let relevant_vars = BTreeSet::new();
    let (actual, expected) =
        export_coalesced_coerce_evidence_bounds(infer, actual_tv, expected_tv, &relevant_vars);
    core_ir::CoerceEvidence {
        source_edge: source_edge.map(|id| id.0),
        actual,
        expected,
    }
}

pub(super) fn complete_apply_principal_evidence(
    infer: &Infer,
    principal_scheme: core_ir::Scheme,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
) -> Option<CompleteApplyPrincipalEvidence> {
    let slot_bounds = apply_slot_bounds(infer, callee_tv, arg_tv, result_tv);
    complete_apply_principal_evidence_from_slot_bounds(
        infer,
        principal_scheme,
        arg_tv,
        result_tv,
        &slot_bounds,
        callee_edge_evidence,
        arg_edge_evidence,
    )
}

pub(super) fn complete_apply_principal_evidence_from_slot_bounds(
    infer: &Infer,
    principal_scheme: core_ir::Scheme,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
) -> Option<CompleteApplyPrincipalEvidence> {
    let substitutions =
        apply_principal_substitutions(infer, &principal_scheme, arg_tv, result_tv, &slot_bounds);
    let substitution_candidates = apply_principal_substitution_candidates(
        infer,
        &principal_scheme,
        callee_edge_evidence,
        arg_edge_evidence,
        &slot_bounds,
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
    let mut coalesce_cache: HashMap<TypeVar, core_ir::TypeBounds> = HashMap::new();
    state
        .expected_edges
        .iter()
        .map(|edge| complete_expected_edge_evidence_cached(&state.infer, edge, &mut coalesce_cache))
        .collect()
}

fn source_only_expected_edge_evidence_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var_os("YULANG_DISABLE_PRINCIPAL_ELABORATE").is_none()
            && std::env::var_os("YULANG_EXPORT_DEBUG_EVIDENCE").is_none()
            && std::env::var_os("YULANG_COALESCE_EXPECTED_EDGE_EVIDENCE").is_none()
    })
}

fn collect_source_only_expected_edge_evidence(state: &LowerState) -> Vec<ExpectedEdgeEvidence> {
    state
        .expected_edges
        .iter()
        .map(|edge| ExpectedEdgeEvidence {
            id: edge.id,
            kind: edge.kind,
            source_range: source_range(edge.cause.span),
            actual: core_ir::TypeBounds::default(),
            expected: core_ir::TypeBounds::default(),
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
        let mut coalesce_cache: HashMap<TypeVar, core_ir::TypeBounds> = HashMap::new();
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
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_COALESCE_EXPECTED_EDGE_EVIDENCE").is_some())
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
    cache: &mut HashMap<TypeVar, core_ir::TypeBounds>,
) -> core_ir::TypeBounds {
    if let Some(cached) = cache.get(&tv) {
        return cached.clone();
    }
    let bounds = export_coalesced_type_bounds_for_tv(infer, tv);
    cache.insert(tv, bounds.clone());
    bounds
}

fn complete_expected_edge_evidence_cached(
    infer: &Infer,
    edge: &ExpectedEdge,
    cache: &mut HashMap<TypeVar, core_ir::TypeBounds>,
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
    bounds: &HashMap<TypeVar, core_ir::TypeBounds>,
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

fn source_range(range: Option<rowan::TextRange>) -> Option<core_ir::SourceRange> {
    range.map(|range| core_ir::SourceRange {
        start: u32::from(range.start()),
        end: u32::from(range.end()),
    })
}

fn apply_principal_substitutions(
    infer: &Infer,
    principal_scheme: &core_ir::Scheme,
    arg_tv: TypeVar,
    result_tv: TypeVar,
    slot_bounds: &ApplySlotBounds,
) -> Vec<core_ir::TypeSubstitution> {
    let principal_callee = &principal_scheme.body;
    let Some((param, ret)) = principal_fun_param_ret(principal_callee) else {
        return Vec::new();
    };
    let mut params = BTreeSet::new();
    collect_core_type_vars(principal_callee, &mut params);
    if params.is_empty() {
        return Vec::new();
    }

    let mut unifier = PrincipalSubstitutionUnifier::new(&params);
    if let Some(arg_ty) = monomorphic_type_from_bounds(slot_bounds.arg.clone()) {
        unifier.infer_value(param, &arg_ty);
    }
    if let Some(result_ty) = monomorphic_type_from_bounds(slot_bounds.result.clone()) {
        unifier.infer_value(ret, &result_ty);
    }
    if unifier.is_empty() {
        if let Some(arg_ty) = export_monomorphic_type_for_tv(infer, arg_tv) {
            unifier.infer_value(param, &arg_ty);
        }
        if let Some(result_ty) = export_monomorphic_type_for_tv(infer, result_tv) {
            unifier.infer_value(ret, &result_ty);
        }
    }
    unifier.infer_role_associated_requirements(&principal_scheme.requirements);

    unifier
        .into_substitutions()
        .filter(|(_, ty)| substitution_type_usable(ty, false))
        .map(|(var, ty)| core_ir::TypeSubstitution { var, ty })
        .collect()
}

fn apply_principal_substitution_candidates(
    _infer: &Infer,
    principal_scheme: &core_ir::Scheme,
    callee_edge_evidence: Option<&ExpectedEdgeEvidence>,
    arg_edge_evidence: Option<&ExpectedEdgeEvidence>,
    slot_bounds: &ApplySlotBounds,
) -> Vec<core_ir::PrincipalSubstitutionCandidate> {
    let principal_callee = &principal_scheme.body;
    let Some((param, ret)) = principal_fun_param_ret(principal_callee) else {
        return Vec::new();
    };
    let mut params = BTreeSet::new();
    collect_core_type_vars(principal_callee, &mut params);
    if params.is_empty() {
        return Vec::new();
    }
    let mut candidates = Vec::new();
    collect_candidates_from_bounds(
        principal_callee,
        &slot_bounds.callee,
        &params,
        callee_edge_evidence.map(|e| e.id),
        &mut vec![core_ir::PrincipalSlotPathSegment::Callee],
        &mut candidates,
    );
    if let Some(evidence) = callee_edge_evidence {
        collect_candidates_from_expected_edge(
            evidence,
            &params,
            &mut vec![core_ir::PrincipalSlotPathSegment::Callee],
            &mut candidates,
        );
    }
    collect_candidates_from_bounds(
        param,
        &slot_bounds.arg,
        &params,
        arg_edge_evidence.map(|e| e.id),
        &mut vec![core_ir::PrincipalSlotPathSegment::Arg],
        &mut candidates,
    );
    if let Some(evidence) = arg_edge_evidence {
        collect_candidates_from_expected_edge(
            evidence,
            &params,
            &mut vec![core_ir::PrincipalSlotPathSegment::Arg],
            &mut candidates,
        );
    }
    collect_candidates_from_bounds(
        ret,
        &slot_bounds.result,
        &params,
        None,
        &mut vec![core_ir::PrincipalSlotPathSegment::Result],
        &mut candidates,
    );
    dedupe_principal_substitution_candidates(&mut candidates);
    candidates
}

pub(super) fn residual_apply_principal_scheme(
    infer: &Infer,
    principal_scheme: &core_ir::Scheme,
    callee_tv: TypeVar,
    arg_tv: TypeVar,
    result_tv: TypeVar,
) -> Option<core_ir::Scheme> {
    let substitutions = complete_apply_principal_evidence(
        infer,
        principal_scheme.clone(),
        callee_tv,
        arg_tv,
        result_tv,
        None,
        None,
    )
    .map(|principal| {
        principal
            .substitutions
            .into_iter()
            .map(|substitution| (substitution.var, substitution.ty))
            .collect::<BTreeMap<_, _>>()
    })
    .unwrap_or_default();
    let body = substitute_core_type(&principal_scheme.body, &substitutions);
    let (_, ret) = principal_fun_param_ret(&body)?;
    Some(core_ir::Scheme {
        requirements: principal_scheme.requirements.clone(),
        body: ret.clone(),
    })
}

pub(super) struct ApplySlotBounds {
    pub(super) callee: core_ir::TypeBounds,
    pub(super) arg: core_ir::TypeBounds,
    pub(super) result: core_ir::TypeBounds,
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

fn monomorphic_type_from_bounds(bounds: core_ir::TypeBounds) -> Option<core_ir::Type> {
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
        .cloned()
        .filter(|ty| substitution_type_usable(ty, false))
}

fn collect_candidates_from_bounds(
    template: &core_ir::Type,
    bounds: &core_ir::TypeBounds,
    params: &BTreeSet<core_ir::TypeVar>,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<core_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<core_ir::PrincipalSubstitutionCandidate>,
) {
    if let Some(lower) = &bounds.lower {
        collect_candidates_from_type(
            template,
            lower,
            params,
            core_ir::PrincipalCandidateRelation::Lower,
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
            core_ir::PrincipalCandidateRelation::Upper,
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
            core_ir::PrincipalCandidateRelation::Exact,
            source_edge,
            path,
            out,
        );
    }
}

fn collect_candidates_from_type(
    template: &core_ir::Type,
    actual: &core_ir::Type,
    params: &BTreeSet<core_ir::TypeVar>,
    relation: core_ir::PrincipalCandidateRelation,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<core_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<core_ir::PrincipalSubstitutionCandidate>,
) {
    match (template, actual) {
        (core_ir::Type::Var(var), actual) if params.contains(var) => {
            if principal_candidate_type_recordable(var, actual) {
                out.push(core_ir::PrincipalSubstitutionCandidate {
                    var: var.clone(),
                    relation,
                    ty: actual.clone(),
                    source_edge: source_edge.map(|id| id.0),
                    path: path.clone(),
                });
            }
        }
        (
            core_ir::Type::Named {
                path: template_path,
                args,
            },
            core_ir::Type::Named {
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
            core_ir::Type::Fun {
                param,
                param_effect: _,
                ret_effect: _,
                ret,
            },
            core_ir::Type::Fun {
                param: actual_param,
                param_effect: _,
                ret_effect: _,
                ret: actual_ret,
            },
        ) => {
            path.push(core_ir::PrincipalSlotPathSegment::FunctionParam);
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

            path.push(core_ir::PrincipalSlotPathSegment::FunctionReturn);
            collect_candidates_from_type(ret, actual_ret, params, relation, source_edge, path, out);
            path.pop();
        }
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
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
        (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual) => {
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
        (core_ir::Type::Recursive { body, .. }, actual) => {
            collect_candidates_from_type(body, actual, params, relation, source_edge, path, out);
        }
        (template, core_ir::Type::Recursive { body, .. }) => {
            collect_candidates_from_type(template, body, params, relation, source_edge, path, out);
        }
        _ => {}
    }
}

fn collect_candidates_from_arg(
    template: &core_ir::TypeArg,
    actual: &core_ir::TypeArg,
    params: &BTreeSet<core_ir::TypeVar>,
    relation: core_ir::PrincipalCandidateRelation,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<core_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<core_ir::PrincipalSubstitutionCandidate>,
) {
    match (template, actual) {
        (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
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
        (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
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
    params: &BTreeSet<core_ir::TypeVar>,
    path_prefix: &mut Vec<core_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<core_ir::PrincipalSubstitutionCandidate>,
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
    actual: &core_ir::Type,
    expected: &core_ir::Type,
    polarity: EdgePolarity,
    params: &BTreeSet<core_ir::TypeVar>,
    source_edge: Option<ExpectedEdgeId>,
    path: &mut Vec<core_ir::PrincipalSlotPathSegment>,
    out: &mut Vec<core_ir::PrincipalSubstitutionCandidate>,
) {
    let (expected_relation, actual_relation) = match polarity {
        EdgePolarity::Covariant | EdgePolarity::Invariant => (
            core_ir::PrincipalCandidateRelation::Lower,
            core_ir::PrincipalCandidateRelation::Upper,
        ),
        EdgePolarity::Contravariant => (
            core_ir::PrincipalCandidateRelation::Upper,
            core_ir::PrincipalCandidateRelation::Lower,
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
) -> core_ir::PrincipalSlotPathSegment {
    match segment {
        EdgePathSegment::Field(name) => core_ir::PrincipalSlotPathSegment::Field(name.clone()),
        EdgePathSegment::TupleIndex(index) => core_ir::PrincipalSlotPathSegment::TupleIndex(*index),
        EdgePathSegment::VariantCase(name) => {
            core_ir::PrincipalSlotPathSegment::VariantCase(name.clone())
        }
        EdgePathSegment::PayloadIndex(index) => {
            core_ir::PrincipalSlotPathSegment::PayloadIndex(*index)
        }
        EdgePathSegment::FunctionParam => core_ir::PrincipalSlotPathSegment::FunctionParam,
        EdgePathSegment::FunctionReturn => core_ir::PrincipalSlotPathSegment::FunctionReturn,
    }
}

fn dedupe_principal_substitution_candidates(
    candidates: &mut Vec<core_ir::PrincipalSubstitutionCandidate>,
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
    relation: core_ir::PrincipalCandidateRelation,
) -> core_ir::PrincipalCandidateRelation {
    match relation {
        core_ir::PrincipalCandidateRelation::Lower => core_ir::PrincipalCandidateRelation::Upper,
        core_ir::PrincipalCandidateRelation::Upper => core_ir::PrincipalCandidateRelation::Lower,
        core_ir::PrincipalCandidateRelation::Exact => core_ir::PrincipalCandidateRelation::Exact,
    }
}

fn principal_candidate_type_recordable(var: &core_ir::TypeVar, ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Any | core_ir::Type::Never => false,
        core_ir::Type::Var(actual) => actual != var,
        _ => true,
    }
}

fn principal_fun_param_ret(ty: &core_ir::Type) -> Option<(&core_ir::Type, &core_ir::Type)> {
    match ty {
        core_ir::Type::Fun { param, ret, .. } => Some((param, ret)),
        core_ir::Type::Recursive { body, .. } => principal_fun_param_ret(body),
        core_ir::Type::Inter(items) | core_ir::Type::Union(items) => {
            items.iter().find_map(principal_fun_param_ret)
        }
        _ => None,
    }
}

fn substitute_core_type(
    ty: &core_ir::Type,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::Type {
    match ty {
        core_ir::Type::Var(var) => substitutions
            .get(var)
            .cloned()
            .unwrap_or_else(|| core_ir::Type::Var(var.clone())),
        core_ir::Type::Named { path, args } => core_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_core_type_arg(arg, substitutions))
                .collect(),
        },
        core_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(substitute_core_type(param, substitutions)),
            param_effect: Box::new(substitute_core_type(param_effect, substitutions)),
            ret_effect: Box::new(substitute_core_type(ret_effect, substitutions)),
            ret: Box::new(substitute_core_type(ret, substitutions)),
        },
        core_ir::Type::Tuple(items) => core_ir::Type::Tuple(
            items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
        ),
        core_ir::Type::Record(record) => core_ir::Type::Record(core_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| core_ir::RecordField {
                    name: field.name.clone(),
                    value: substitute_core_type(&field.value, substitutions),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                core_ir::RecordSpread::Head(ty) => {
                    core_ir::RecordSpread::Head(Box::new(substitute_core_type(ty, substitutions)))
                }
                core_ir::RecordSpread::Tail(ty) => {
                    core_ir::RecordSpread::Tail(Box::new(substitute_core_type(ty, substitutions)))
                }
            }),
        }),
        core_ir::Type::Variant(variant) => core_ir::Type::Variant(core_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| core_ir::VariantCase {
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
        core_ir::Type::Row { items, tail } => core_ir::Type::Row {
            items: items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
            tail: Box::new(substitute_core_type(tail, substitutions)),
        },
        core_ir::Type::Union(items) => core_ir::Type::Union(
            items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
        ),
        core_ir::Type::Inter(items) => core_ir::Type::Inter(
            items
                .iter()
                .map(|item| substitute_core_type(item, substitutions))
                .collect(),
        ),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(substitute_core_type(body, substitutions)),
        },
        core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Any => ty.clone(),
    }
}

fn substitute_core_type_arg(
    arg: &core_ir::TypeArg,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> core_ir::TypeArg {
    match arg {
        core_ir::TypeArg::Type(ty) => {
            core_ir::TypeArg::Type(substitute_core_type(ty, substitutions))
        }
        core_ir::TypeArg::Bounds(bounds) => core_ir::TypeArg::Bounds(core_ir::TypeBounds {
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

fn export_monomorphic_type_for_tv(infer: &Infer, tv: TypeVar) -> Option<core_ir::Type> {
    let bounds = export_type_bounds_for_tv(infer, tv);
    bounds
        .lower
        .as_deref()
        .or(bounds.upper.as_deref())
        .cloned()
        .map(|ty| project_core_value_type_or_any(ty, &BTreeSet::new()))
        .filter(|ty| substitution_type_usable(ty, false))
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
    actual: &core_ir::Type,
    expected: &core_ir::Type,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    match (actual, expected) {
        (core_ir::Type::Record(actual), core_ir::Type::Record(expected)) => {
            derive_record_field_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        (core_ir::Type::Tuple(actual), core_ir::Type::Tuple(expected)) => {
            derive_tuple_item_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        (core_ir::Type::Variant(actual), core_ir::Type::Variant(expected)) => {
            derive_variant_payload_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        (core_ir::Type::Fun { .. }, core_ir::Type::Fun { .. }) => {
            derive_function_edges(parent, polarity, actual, expected, path, derived, depth);
        }
        _ => {}
    }
}

fn derive_record_field_edges(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &core_ir::RecordType,
    expected: &core_ir::RecordType,
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
    actual: &[core_ir::Type],
    expected: &[core_ir::Type],
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
    actual: &core_ir::VariantType,
    expected: &core_ir::VariantType,
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
    actual: &core_ir::Type,
    expected: &core_ir::Type,
    path: &mut Vec<EdgePathSegment>,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
    depth: usize,
) {
    let (
        core_ir::Type::Fun {
            param: actual_param,
            ret: actual_ret,
            ..
        },
        core_ir::Type::Fun {
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
    actual: &core_ir::Type,
    expected: &core_ir::Type,
    derived: &mut Vec<DerivedExpectedEdgeEvidence>,
) {
    derived.push(DerivedExpectedEdgeEvidence {
        parent,
        kind,
        polarity,
        path: path.to_vec(),
        actual: core_ir::TypeBounds::exact(derived_actual_slot_type(actual, expected)),
        expected: core_ir::TypeBounds::exact(derived_slot_type(expected)),
    });
}

fn derived_actual_slot_type(actual: &core_ir::Type, expected: &core_ir::Type) -> core_ir::Type {
    let expected = derived_slot_type(expected);
    primary_structural_or_concrete_type_not_equal(actual, &expected)
        .or_else(|| primary_structural_or_concrete_type(actual))
        .unwrap_or(actual)
        .clone()
}

fn derived_slot_type(ty: &core_ir::Type) -> core_ir::Type {
    primary_structural_or_concrete_type(ty)
        .unwrap_or(ty)
        .clone()
}

fn derive_child_edge(
    parent: ExpectedEdgeId,
    polarity: EdgePolarity,
    actual: &core_ir::Type,
    expected: &core_ir::Type,
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

fn bounds_primary_type(bounds: &core_ir::TypeBounds) -> Option<&core_ir::Type> {
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

fn primary_structural_or_concrete_type(ty: &core_ir::Type) -> Option<&core_ir::Type> {
    match ty {
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => items
            .iter()
            .find_map(primary_structural_or_concrete_type)
            .or(Some(ty)),
        core_ir::Type::Var(_) | core_ir::Type::Any | core_ir::Type::Never => None,
        _ => Some(ty),
    }
}

fn primary_structural_or_concrete_type_not_equal<'a>(
    ty: &'a core_ir::Type,
    expected: &core_ir::Type,
) -> Option<&'a core_ir::Type> {
    match ty {
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => items
            .iter()
            .filter_map(primary_structural_or_concrete_type)
            .find(|item| *item != expected),
        core_ir::Type::Var(_) | core_ir::Type::Any | core_ir::Type::Never => None,
        _ if ty != expected => Some(ty),
        _ => None,
    }
}

struct PrincipalSubstitutionUnifier<'a> {
    params: &'a BTreeSet<core_ir::TypeVar>,
    substitutions: BTreeMap<core_ir::TypeVar, core_ir::Type>,
    conflicts: BTreeSet<core_ir::TypeVar>,
}

impl<'a> PrincipalSubstitutionUnifier<'a> {
    fn new(params: &'a BTreeSet<core_ir::TypeVar>) -> Self {
        Self {
            params,
            substitutions: BTreeMap::new(),
            conflicts: BTreeSet::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.substitutions.is_empty()
    }

    fn into_substitutions(self) -> impl Iterator<Item = (core_ir::TypeVar, core_ir::Type)> {
        let conflicts = self.conflicts;
        self.substitutions
            .into_iter()
            .filter(move |(var, _)| !conflicts.contains(var))
    }

    fn infer_role_associated_requirements(&mut self, requirements: &[core_ir::RoleRequirement]) {
        for requirement in requirements {
            let Some(input) = first_requirement_input(requirement)
                .and_then(|bounds| self.substitute_bounds(bounds))
                .and_then(monomorphic_type_from_bounds)
            else {
                continue;
            };
            for associated in requirement.args.iter().filter_map(requirement_associated) {
                self.infer_fold_item_associated(&input, associated);
            }
        }
    }

    fn infer_fold_item_associated(
        &mut self,
        input: &core_ir::Type,
        associated: (&core_ir::Name, &core_ir::TypeBounds),
    ) {
        let (name, bounds) = associated;
        if name.0 != "item" {
            return;
        }
        let Some(item) = fold_item_type(input) else {
            return;
        };
        if let Some(lower) = &bounds.lower {
            self.infer_value(lower, &item);
        }
        if let Some(upper) = &bounds.upper {
            self.infer_value(upper, &item);
        }
    }

    fn substitute_bounds(&self, bounds: &core_ir::TypeBounds) -> Option<core_ir::TypeBounds> {
        Some(core_ir::TypeBounds {
            lower: substitute_optional_box(bounds.lower.as_deref(), |ty| self.substitute_type(ty))?,
            upper: substitute_optional_box(bounds.upper.as_deref(), |ty| self.substitute_type(ty))?,
        })
    }

    fn substitute_type(&self, ty: &core_ir::Type) -> Option<core_ir::Type> {
        match ty {
            core_ir::Type::Var(var) if self.conflicts.contains(var) => None,
            core_ir::Type::Var(var) => self
                .substitutions
                .get(var)
                .cloned()
                .or_else(|| Some(core_ir::Type::Var(var.clone()))),
            core_ir::Type::Named { path, args } => Some(core_ir::Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.substitute_arg(arg))
                    .collect::<Option<Vec<_>>>()?,
            }),
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Some(core_ir::Type::Fun {
                param: Box::new(self.substitute_type(param)?),
                param_effect: Box::new(self.substitute_type(param_effect)?),
                ret_effect: Box::new(self.substitute_type(ret_effect)?),
                ret: Box::new(self.substitute_type(ret)?),
            }),
            core_ir::Type::Tuple(items) => Some(core_ir::Type::Tuple(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            core_ir::Type::Record(record) => Some(core_ir::Type::Record(core_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| {
                        Some(core_ir::RecordField {
                            name: field.name.clone(),
                            value: self.substitute_type(&field.value)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                spread: match &record.spread {
                    Some(core_ir::RecordSpread::Head(ty)) => Some(core_ir::RecordSpread::Head(
                        Box::new(self.substitute_type(ty)?),
                    )),
                    Some(core_ir::RecordSpread::Tail(ty)) => Some(core_ir::RecordSpread::Tail(
                        Box::new(self.substitute_type(ty)?),
                    )),
                    None => None,
                },
            })),
            core_ir::Type::Variant(variant) => Some(core_ir::Type::Variant(core_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| {
                        Some(core_ir::VariantCase {
                            name: case.name.clone(),
                            payloads: case
                                .payloads
                                .iter()
                                .map(|payload| self.substitute_type(payload))
                                .collect::<Option<Vec<_>>>()?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?,
                tail: substitute_optional_box(variant.tail.as_deref(), |tail| {
                    self.substitute_type(tail)
                })?,
            })),
            core_ir::Type::Row { items, tail } => Some(core_ir::Type::Row {
                items: items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
                tail: Box::new(self.substitute_type(tail)?),
            }),
            core_ir::Type::Union(items) => Some(core_ir::Type::Union(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            core_ir::Type::Inter(items) => Some(core_ir::Type::Inter(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect::<Option<Vec<_>>>()?,
            )),
            core_ir::Type::Recursive { var, body } => Some(core_ir::Type::Recursive {
                var: var.clone(),
                body: Box::new(self.substitute_type(body)?),
            }),
            core_ir::Type::Unknown | core_ir::Type::Never | core_ir::Type::Any => Some(ty.clone()),
        }
    }

    fn substitute_arg(&self, arg: &core_ir::TypeArg) -> Option<core_ir::TypeArg> {
        match arg {
            core_ir::TypeArg::Type(ty) => Some(core_ir::TypeArg::Type(self.substitute_type(ty)?)),
            core_ir::TypeArg::Bounds(bounds) => {
                Some(core_ir::TypeArg::Bounds(self.substitute_bounds(bounds)?))
            }
        }
    }

    fn infer_value(&mut self, template: &core_ir::Type, actual: &core_ir::Type) {
        self.infer(template, actual, false);
    }

    fn infer_effect(&mut self, template: &core_ir::Type, actual: &core_ir::Type) {
        self.infer(template, actual, true);
    }

    fn infer(&mut self, template: &core_ir::Type, actual: &core_ir::Type, allow_never: bool) {
        match (template, actual) {
            (core_ir::Type::Var(var), actual) if self.params.contains(var) => {
                self.bind(var, actual, allow_never);
            }
            (
                core_ir::Type::Named { path, args },
                core_ir::Type::Named {
                    path: actual_path,
                    args: actual_args,
                },
            ) if path == actual_path && args.len() == actual_args.len() => {
                for (template_arg, actual_arg) in args.iter().zip(actual_args) {
                    self.infer_arg(template_arg, actual_arg, allow_never);
                }
            }
            (
                core_ir::Type::Fun {
                    param,
                    param_effect,
                    ret_effect,
                    ret,
                },
                core_ir::Type::Fun {
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
            (core_ir::Type::Tuple(items), core_ir::Type::Tuple(actual_items))
                if items.len() == actual_items.len() =>
            {
                for (item, actual_item) in items.iter().zip(actual_items) {
                    self.infer(item, actual_item, allow_never);
                }
            }
            (core_ir::Type::Record(record), core_ir::Type::Record(actual_record)) => {
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
            (core_ir::Type::Union(items) | core_ir::Type::Inter(items), actual) => {
                for item in items {
                    self.infer(item, actual, allow_never);
                }
            }
            (core_ir::Type::Recursive { var, body }, actual) => {
                if !self.params.contains(var) {
                    self.infer(body, actual, allow_never);
                }
            }
            _ => {}
        }
    }

    fn infer_arg(
        &mut self,
        template: &core_ir::TypeArg,
        actual: &core_ir::TypeArg,
        allow_never: bool,
    ) {
        match (template, actual) {
            (core_ir::TypeArg::Type(template), core_ir::TypeArg::Type(actual)) => {
                self.infer(template, actual, allow_never);
            }
            (core_ir::TypeArg::Bounds(template), core_ir::TypeArg::Bounds(actual)) => {
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

    fn bind(&mut self, var: &core_ir::TypeVar, actual: &core_ir::Type, allow_never: bool) {
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

fn first_requirement_input(requirement: &core_ir::RoleRequirement) -> Option<&core_ir::TypeBounds> {
    requirement.args.iter().find_map(|arg| match arg {
        core_ir::RoleRequirementArg::Input(bounds) => Some(bounds),
        core_ir::RoleRequirementArg::Associated { .. } => None,
    })
}

fn requirement_associated(
    arg: &core_ir::RoleRequirementArg,
) -> Option<(&core_ir::Name, &core_ir::TypeBounds)> {
    match arg {
        core_ir::RoleRequirementArg::Associated { name, bounds } => Some((name, bounds)),
        core_ir::RoleRequirementArg::Input(_) => None,
    }
}

fn fold_item_type(ty: &core_ir::Type) -> Option<core_ir::Type> {
    let core_ir::Type::Named { path, args } = ty else {
        return None;
    };
    if path.segments.last().is_some_and(|name| name.0 == "range") && args.is_empty() {
        return Some(core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name("int".to_string())),
            args: Vec::new(),
        });
    }
    if !path.segments.last().is_some_and(|name| name.0 == "list") || args.len() != 1 {
        return None;
    }
    match &args[0] {
        core_ir::TypeArg::Type(ty) => Some(ty.clone()),
        core_ir::TypeArg::Bounds(bounds) => monomorphic_type_from_bounds(bounds.clone()),
    }
}

fn substitute_optional_box<T>(
    value: Option<&core_ir::Type>,
    mut substitute: impl FnMut(&core_ir::Type) -> Option<T>,
) -> Option<Option<Box<T>>> {
    match value {
        Some(ty) => substitute(ty).map(Box::new).map(Some),
        None => Some(None),
    }
}

fn merge_substitution_type(left: &core_ir::Type, right: &core_ir::Type) -> Option<core_ir::Type> {
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
            core_ir::Type::Named { path, args },
            core_ir::Type::Named {
                path: right_path,
                args: right_args,
            },
        ) if path == right_path && args.len() == right_args.len() => {
            let args = args
                .iter()
                .zip(right_args)
                .map(|(left, right)| merge_type_arg(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Named {
                path: path.clone(),
                args,
            })
        }
        (
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            core_ir::Type::Fun {
                param: right_param,
                param_effect: right_param_effect,
                ret_effect: right_ret_effect,
                ret: right_ret,
            },
        ) => Some(core_ir::Type::Fun {
            param: Box::new(merge_substitution_type(param, right_param)?),
            param_effect: Box::new(merge_substitution_type(param_effect, right_param_effect)?),
            ret_effect: Box::new(merge_substitution_type(ret_effect, right_ret_effect)?),
            ret: Box::new(merge_substitution_type(ret, right_ret)?),
        }),
        (core_ir::Type::Tuple(items), core_ir::Type::Tuple(right_items))
            if items.len() == right_items.len() =>
        {
            let items = items
                .iter()
                .zip(right_items)
                .map(|(left, right)| merge_substitution_type(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(core_ir::Type::Tuple(items))
        }
        _ => None,
    }
}

fn merge_type_arg(left: &core_ir::TypeArg, right: &core_ir::TypeArg) -> Option<core_ir::TypeArg> {
    match (left, right) {
        (core_ir::TypeArg::Type(left), core_ir::TypeArg::Type(right)) => {
            merge_substitution_type(left, right).map(core_ir::TypeArg::Type)
        }
        (core_ir::TypeArg::Type(ty), core_ir::TypeArg::Bounds(bounds))
        | (core_ir::TypeArg::Bounds(bounds), core_ir::TypeArg::Type(ty)) => {
            type_fits_bounds(ty, bounds).then(|| core_ir::TypeArg::Type(ty.clone()))
        }
        (core_ir::TypeArg::Bounds(left), core_ir::TypeArg::Bounds(right)) => {
            Some(core_ir::TypeArg::Bounds(merge_type_bounds(left, right)?))
        }
    }
}

fn merge_type_bounds(
    left: &core_ir::TypeBounds,
    right: &core_ir::TypeBounds,
) -> Option<core_ir::TypeBounds> {
    let lower = merge_optional_bound(left.lower.as_deref(), right.lower.as_deref())?;
    let upper = merge_optional_bound(left.upper.as_deref(), right.upper.as_deref())?;
    Some(core_ir::TypeBounds {
        lower: lower.map(Box::new),
        upper: upper.map(Box::new),
    })
}

fn merge_optional_bound(
    left: Option<&core_ir::Type>,
    right: Option<&core_ir::Type>,
) -> Option<Option<core_ir::Type>> {
    match (left, right) {
        (Some(left), Some(right)) => merge_substitution_type(left, right).map(Some),
        (Some(ty), None) | (None, Some(ty)) => Some(Some(ty.clone())),
        (None, None) => Some(None),
    }
}

fn type_fits_bounds(ty: &core_ir::Type, bounds: &core_ir::TypeBounds) -> bool {
    bounds
        .lower
        .as_deref()
        .is_none_or(|lower| merge_substitution_type(lower, ty).is_some())
        && bounds
            .upper
            .as_deref()
            .is_none_or(|upper| merge_substitution_type(upper, ty).is_some())
}

fn type_has_vars(ty: &core_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    !vars.is_empty()
}

fn substitution_type_usable(ty: &core_ir::Type, allow_never: bool) -> bool {
    !matches!(
        ty,
        core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_)
    ) && (allow_never || !matches!(ty, core_ir::Type::Never))
        && !type_has_vars(ty)
        && !type_has_unknown(ty)
}

fn type_has_unknown(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Unknown => true,
        core_ir::Type::Never | core_ir::Type::Any | core_ir::Type::Var(_) => false,
        core_ir::Type::Named { args, .. } => args.iter().any(type_arg_has_unknown),
        core_ir::Type::Fun {
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
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(type_has_unknown)
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_has_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                        type_has_unknown(ty)
                    }
                })
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_has_unknown))
                || variant.tail.as_deref().is_some_and(type_has_unknown)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().any(type_has_unknown) || type_has_unknown(tail)
        }
        core_ir::Type::Recursive { body, .. } => type_has_unknown(body),
    }
}

fn type_arg_has_unknown(arg: &core_ir::TypeArg) -> bool {
    match arg {
        core_ir::TypeArg::Type(ty) => type_has_unknown(ty),
        core_ir::TypeArg::Bounds(bounds) => {
            bounds.lower.as_deref().is_some_and(type_has_unknown)
                || bounds.upper.as_deref().is_some_and(type_has_unknown)
        }
    }
}

fn type_bounds_closed(bounds: &core_ir::TypeBounds) -> bool {
    (bounds.lower.is_some() || bounds.upper.is_some())
        && bounds.lower.as_deref().is_none_or(|ty| !type_has_vars(ty))
        && bounds.upper.as_deref().is_none_or(|ty| !type_has_vars(ty))
}

fn type_bounds_informative(bounds: &core_ir::TypeBounds) -> bool {
    bounds.lower.as_deref().is_some_and(type_informative)
        || bounds.upper.as_deref().is_some_and(type_informative)
}

fn type_informative(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Unknown
        | core_ir::Type::Never
        | core_ir::Type::Any
        | core_ir::Type::Var(_) => false,
        core_ir::Type::Named { .. } => true,
        core_ir::Type::Fun { .. }
        | core_ir::Type::Tuple(_)
        | core_ir::Type::Record(_)
        | core_ir::Type::Variant(_) => true,
        core_ir::Type::Row { items, tail } => {
            items.iter().any(type_informative) || type_informative(tail)
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().any(type_informative)
        }
        core_ir::Type::Recursive { body, .. } => type_informative(body),
    }
}

fn value_type_bounds_runtime_usable(bounds: &core_ir::TypeBounds) -> bool {
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

fn effect_type_bounds_runtime_usable(bounds: &core_ir::TypeBounds) -> bool {
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

fn value_type_runtime_usable(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Unknown
        | core_ir::Type::Never
        | core_ir::Type::Any
        | core_ir::Type::Var(_) => false,
        core_ir::Type::Named { args, .. } => args.iter().all(type_arg_runtime_usable),
        core_ir::Type::Fun {
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
        core_ir::Type::Tuple(items) | core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            items.iter().all(value_type_runtime_usable)
        }
        core_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| value_type_runtime_usable(&field.value))
                && record
                    .spread
                    .as_ref()
                    .is_none_or(record_spread_runtime_usable)
        }
        core_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .all(|case| case.payloads.iter().all(value_type_runtime_usable))
                && variant
                    .tail
                    .as_deref()
                    .is_none_or(value_type_runtime_usable)
        }
        core_ir::Type::Row { items, tail } => {
            items.iter().all(effect_type_runtime_usable) && effect_type_runtime_usable(tail)
        }
        core_ir::Type::Recursive { body, .. } => value_type_runtime_usable(body),
    }
}

fn effect_type_runtime_usable(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Never => true,
        core_ir::Type::Unknown | core_ir::Type::Any | core_ir::Type::Var(_) => false,
        core_ir::Type::Row { items, tail } => {
            items.iter().all(effect_type_runtime_usable) && effect_type_runtime_usable(tail)
        }
        _ => value_type_runtime_usable(ty),
    }
}

fn record_spread_runtime_usable(spread: &core_ir::RecordSpread) -> bool {
    match spread {
        core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
            value_type_runtime_usable(ty)
        }
    }
}

fn type_arg_runtime_usable(arg: &core_ir::TypeArg) -> bool {
    match arg {
        core_ir::TypeArg::Type(ty) => value_type_runtime_usable(ty),
        core_ir::TypeArg::Bounds(bounds) => value_type_bounds_runtime_usable(bounds),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowan::SyntaxNode;
    use yulang_parser::sink::YulangLanguage;

    use crate::{LowerState, diagnostic, lower_root};

    fn tv(name: &str) -> core_ir::TypeVar {
        core_ir::TypeVar(name.to_string())
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn list(arg: core_ir::TypeArg) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path {
                segments: vec![
                    core_ir::Name("std".to_string()),
                    core_ir::Name("list".to_string()),
                    core_ir::Name("list".to_string()),
                ],
            },
            args: vec![arg],
        }
    }

    fn range() -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path {
                segments: vec![
                    core_ir::Name("std".to_string()),
                    core_ir::Name("range".to_string()),
                    core_ir::Name("range".to_string()),
                ],
            },
            args: Vec::new(),
        }
    }

    fn fun(param: core_ir::Type, ret: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn variant(case_name: &str, payloads: Vec<core_ir::Type>) -> core_ir::Type {
        core_ir::Type::Variant(core_ir::VariantType {
            cases: vec![core_ir::VariantCase {
                name: core_ir::Name(case_name.to_string()),
                payloads,
            }],
            tail: None,
        })
    }

    fn record(fields: Vec<(&str, core_ir::Type)>) -> core_ir::Type {
        core_ir::Type::Record(core_ir::RecordType {
            fields: fields
                .into_iter()
                .map(|(name, value)| core_ir::RecordField {
                    name: core_ir::Name(name.to_string()),
                    value,
                    optional: false,
                })
                .collect(),
            spread: None,
        })
    }

    fn fold_path() -> core_ir::Path {
        core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("fold".to_string()),
                core_ir::Name("Fold".to_string()),
            ],
        }
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
        let concrete = list(core_ir::TypeArg::Type(named("int")));
        let bounded = list(core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: Some(Box::new(named("int"))),
            upper: None,
        }));

        assert_eq!(merge_substitution_type(&bounded, &concrete), Some(concrete));
    }

    #[test]
    fn value_position_does_not_bind_never() {
        let mut unifier = one_param_unifier();
        unifier.infer_value(&core_ir::Type::Var(tv("t")), &core_ir::Type::Never);

        assert!(unifier.into_substitutions().next().is_none());
    }

    #[test]
    fn effect_position_can_bind_never() {
        let mut unifier = one_param_unifier();
        unifier.infer_effect(&core_ir::Type::Var(tv("t")), &core_ir::Type::Never);

        assert_eq!(
            unifier.into_substitutions().collect::<Vec<_>>(),
            vec![(tv("t"), core_ir::Type::Never)]
        );
    }

    #[test]
    fn conflicting_candidates_drop_the_substitution() {
        let mut unifier = one_param_unifier();
        unifier.infer_value(&core_ir::Type::Var(tv("t")), &named("int"));
        unifier.infer_value(&core_ir::Type::Var(tv("t")), &named("bool"));

        assert!(unifier.into_substitutions().next().is_none());
    }

    #[test]
    fn infers_fold_item_associated_from_list_input() {
        let params = Box::leak(Box::new(BTreeSet::from([tv("xs"), tv("item")])));
        let mut unifier = PrincipalSubstitutionUnifier::new(params);
        unifier.infer_value(
            &core_ir::Type::Var(tv("xs")),
            &list(core_ir::TypeArg::Type(named("int"))),
        );
        unifier.infer_role_associated_requirements(&[core_ir::RoleRequirement {
            role: fold_path(),
            args: vec![
                core_ir::RoleRequirementArg::Input(core_ir::TypeBounds::exact(core_ir::Type::Var(
                    tv("xs"),
                ))),
                core_ir::RoleRequirementArg::Associated {
                    name: core_ir::Name("item".to_string()),
                    bounds: core_ir::TypeBounds::exact(core_ir::Type::Var(tv("item"))),
                },
            ],
        }]);

        assert_eq!(
            unifier.into_substitutions().collect::<Vec<_>>(),
            vec![
                (tv("item"), named("int")),
                (tv("xs"), list(core_ir::TypeArg::Type(named("int")))),
            ]
        );
    }

    #[test]
    fn infers_fold_item_associated_from_range_input() {
        let params = Box::leak(Box::new(BTreeSet::from([tv("xs"), tv("item")])));
        let mut unifier = PrincipalSubstitutionUnifier::new(params);
        unifier.infer_value(&core_ir::Type::Var(tv("xs")), &range());
        unifier.infer_role_associated_requirements(&[core_ir::RoleRequirement {
            role: fold_path(),
            args: vec![
                core_ir::RoleRequirementArg::Input(core_ir::TypeBounds::exact(core_ir::Type::Var(
                    tv("xs"),
                ))),
                core_ir::RoleRequirementArg::Associated {
                    name: core_ir::Name("item".to_string()),
                    bounds: core_ir::TypeBounds::exact(core_ir::Type::Var(tv("item"))),
                },
            ],
        }]);

        assert_eq!(
            unifier.into_substitutions().collect::<Vec<_>>(),
            vec![(tv("item"), named("int")), (tv("xs"), range())]
        );
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
        assert_eq!(evidence.expected, core_ir::TypeBounds::exact(named("int")));
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
                    && edge.path == vec![EdgePathSegment::Field(core_ir::Name("x".to_string()))]
            })
            .expect("record field derived edge");

        assert_eq!(field.actual, core_ir::TypeBounds::exact(named("int")));
        assert_eq!(field.expected, core_ir::TypeBounds::exact(named("int")));
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

        assert_eq!(item.actual, core_ir::TypeBounds::exact(named("bool")));
        assert_eq!(item.expected, core_ir::TypeBounds::exact(named("bool")));
        assert_eq!(item.polarity, EdgePolarity::Covariant);
    }

    #[test]
    fn derives_function_expected_edge_evidence() {
        let evidence = ExpectedEdgeEvidence {
            id: ExpectedEdgeId(7),
            kind: ExpectedEdgeKind::Annotation,
            source_range: None,
            actual: core_ir::TypeBounds::exact(fun(named("str"), named("bool"))),
            expected: core_ir::TypeBounds::exact(fun(named("int"), named("int"))),
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
        assert_eq!(param.actual, core_ir::TypeBounds::exact(named("str")));
        assert_eq!(param.expected, core_ir::TypeBounds::exact(named("int")));
        assert_eq!(ret.actual, core_ir::TypeBounds::exact(named("bool")));
        assert_eq!(ret.expected, core_ir::TypeBounds::exact(named("int")));
    }

    #[test]
    fn derives_variant_payload_expected_edge_evidence() {
        let evidence = ExpectedEdgeEvidence {
            id: ExpectedEdgeId(9),
            kind: ExpectedEdgeKind::Annotation,
            source_range: None,
            actual: core_ir::TypeBounds::exact(variant("some", vec![named("str"), named("bool")])),
            expected: core_ir::TypeBounds::exact(variant("some", vec![named("int"), named("int")])),
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
                            EdgePathSegment::VariantCase(core_ir::Name("some".to_string())),
                            EdgePathSegment::PayloadIndex(1),
                        ]
            })
            .expect("variant payload derived edge");

        assert_eq!(payload.parent, ExpectedEdgeId(9));
        assert_eq!(payload.polarity, EdgePolarity::Covariant);
        assert_eq!(payload.actual, core_ir::TypeBounds::exact(named("bool")));
        assert_eq!(payload.expected, core_ir::TypeBounds::exact(named("int")));
    }

    #[test]
    fn recursively_derives_nested_expected_edge_evidence() {
        let evidence = ExpectedEdgeEvidence {
            id: ExpectedEdgeId(11),
            kind: ExpectedEdgeKind::Annotation,
            source_range: None,
            actual: core_ir::TypeBounds::exact(record(vec![(
                "a",
                record(vec![("b", named("str"))]),
            )])),
            expected: core_ir::TypeBounds::exact(record(vec![(
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
                            EdgePathSegment::Field(core_ir::Name("a".to_string())),
                            EdgePathSegment::Field(core_ir::Name("b".to_string())),
                        ]
            })
            .expect("nested record field derived edge");

        assert_eq!(nested.parent, ExpectedEdgeId(11));
        assert_eq!(nested.polarity, EdgePolarity::Covariant);
        assert_eq!(nested.actual, core_ir::TypeBounds::exact(named("str")));
        assert_eq!(nested.expected, core_ir::TypeBounds::exact(named("int")));
    }
}
