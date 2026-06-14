use std::collections::{HashMap, HashSet};

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
use super::type_props::{
    bounds_primary_type, effect_type_bounds_runtime_usable, primary_structural_or_concrete_type,
    primary_structural_or_concrete_type_not_equal, type_bounds_closed, type_bounds_informative,
    value_type_bounds_runtime_usable,
};
use super::types::{export_coalesced_type_bounds_for_tv, export_type_bounds_for_tvs};

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
pub(super) fn complete_expected_edge_evidence(
    infer: &Infer,
    edge: &ExpectedEdge,
) -> ExpectedEdgeEvidence {
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

pub(super) fn derive_expected_edge_evidence(
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
