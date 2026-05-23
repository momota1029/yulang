use std::collections::{BTreeSet, HashMap, HashSet};

use yulang_typed_ir as typed_ir;

use super::apply_principal::CompletePrincipalCache;
use super::bindings::export_bindings_for_paths;
use super::evidence::{
    DerivedExpectedEdgeEvidence, DerivedExpectedEdgeKind, EdgePathSegment, EdgePolarity,
    ExpectedAdapterEdgeEvidence, ExpectedEdgeEvidence, HandlerMatchEvidence,
    collect_expected_adapter_edge_evidence, collect_expected_edge_evidence,
    collect_handler_match_evidence, derive_all_expected_edge_evidence,
};
use super::expr::ExprExporter;
use super::names::{export_path, path_key};
use super::paths::collect_canonical_binding_paths;
use super::roles::canonical_runtime_export_def;
use super::spine::collect_apply_spine;
use super::timing::ExportClock;
use super::type_props::{
    closed_runtime_type_from_bounds, core_type_has_no_vars, core_value_type_has_unknown,
    erase_open_vars_from_runtime_type,
};
use super::types::{
    export_coalesced_type_bounds_for_tv, export_compact_type_bounds,
    export_relevant_type_bounds_for_tv, export_type_bounds_for_tv,
};
use crate::ast::expr::{CatchArmKind, ExprKind, TypedBlock, TypedExpr, TypedStmt};
use crate::diagnostic::ExpectedEdgeId;
use crate::ids::{DefId, TypeVar};
use crate::lower::LowerState;
use crate::symbols::Path;

pub fn export_core_program(state: &mut LowerState) -> typed_ir::CoreProgram {
    let export_timing = std::env::var_os("YULANG_EXPORT_TIMING").is_some();
    let t0 = ExportClock::now(export_timing);
    let t_setup_refresh_before = ExportClock::now(export_timing);
    state.refresh_selection_environment();
    if export_timing {
        eprintln!(
            "  export: setup.refresh_before={:.3}ms",
            t_setup_refresh_before.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t_binding_paths = ExportClock::now(export_timing);
    let binding_paths = state.ctx.collect_all_binding_paths();
    if export_timing {
        eprintln!(
            "  export: setup.binding_paths={:.3}ms count={}",
            t_binding_paths.elapsed().as_secs_f64() * 1000.0,
            binding_paths.len()
        );
    }
    let t_target_defs = ExportClock::now(export_timing);
    let target_defs = collect_export_target_defs(state, &binding_paths);
    if export_timing {
        eprintln!(
            "  export: setup.target_defs={:.3}ms count={}",
            t_target_defs.elapsed().as_secs_f64() * 1000.0,
            target_defs.len()
        );
    }
    let t_finalize = ExportClock::now(export_timing);
    state.finalize_compact_results_for_defs(&target_defs);
    if export_timing {
        eprintln!(
            "  export: setup.finalize={:.3}ms",
            t_finalize.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t_setup_refresh_after = ExportClock::now(export_timing);
    state.refresh_selection_environment();
    if export_timing {
        eprintln!(
            "  export: setup.refresh_after={:.3}ms",
            t_setup_refresh_after.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t_selected_paths = ExportClock::now(export_timing);
    let selected_paths = binding_paths
        .iter()
        .filter(|(_, def)| target_defs.contains(def))
        .cloned()
        .collect::<Vec<_>>();
    if export_timing {
        eprintln!(
            "  export: setup.selected_paths={:.3}ms count={}",
            t_selected_paths.elapsed().as_secs_f64() * 1000.0,
            selected_paths.len()
        );
    }
    if export_timing {
        eprintln!(
            "  export: setup={:.3}ms",
            t0.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t1 = ExportClock::now(export_timing);
    let expected_edge_evidence = collect_expected_edge_evidence(state);
    if export_timing {
        eprintln!(
            "  export: collect_edge_evidence={:.3}ms edges={}",
            t1.elapsed().as_secs_f64() * 1000.0,
            expected_edge_evidence.len()
        );
    }
    let edge_evidence_cache: HashMap<ExpectedEdgeId, ExpectedEdgeEvidence> = expected_edge_evidence
        .iter()
        .cloned()
        .map(|e| (e.id, e))
        .collect();
    let t2 = ExportClock::now(export_timing);
    let root_exprs = export_root_exprs(state, &edge_evidence_cache);
    if export_timing {
        eprintln!(
            "  export: root_exprs={:.3}ms",
            t2.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t3 = ExportClock::now(export_timing);
    let mut bindings =
        export_bindings_for_paths(state, &selected_paths, &root_exprs, &edge_evidence_cache);
    if export_timing {
        eprintln!(
            "  export: bindings={:.3}ms count={}",
            t3.elapsed().as_secs_f64() * 1000.0,
            bindings.len()
        );
    }
    let t4 = ExportClock::now(export_timing);
    refine_runtime_binding_scheme_bodies(state, &selected_paths, &mut bindings);
    if export_timing {
        eprintln!(
            "  export: refine_schemes={:.3}ms",
            t4.elapsed().as_secs_f64() * 1000.0
        );
    }
    let roots = (0..root_exprs.len())
        .map(typed_ir::PrincipalRoot::Expr)
        .collect();
    let t5 = ExportClock::now(export_timing);
    let graph = export_type_graph_view_for_paths(state, &selected_paths, &bindings);
    if export_timing {
        eprintln!(
            "  export: type_graph={:.3}ms",
            t5.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t6 = ExportClock::now(export_timing);
    let export_debug_evidence = export_debug_principal_evidence_enabled();
    let derived_edges = if export_debug_evidence {
        derive_all_expected_edge_evidence(&expected_edge_evidence)
    } else {
        Vec::new()
    };
    let adapter_edges = if export_debug_evidence {
        collect_expected_adapter_edge_evidence(state)
    } else {
        Vec::new()
    };
    let handler_matches = collect_handler_match_evidence(state);
    if export_timing {
        eprintln!(
            "  export: derived_edges={:.3}ms count={} adapter_edges={} handler_matches={}",
            t6.elapsed().as_secs_f64() * 1000.0,
            derived_edges.len(),
            adapter_edges.len(),
            handler_matches.len()
        );
    }
    if export_timing {
        eprintln!(
            "  export: total={:.3}ms",
            t0.elapsed().as_secs_f64() * 1000.0
        );
    }
    typed_ir::CoreProgram {
        program: typed_ir::PrincipalModule {
            path: typed_ir::Path::default(),
            bindings,
            root_exprs,
            roots,
        },
        graph,
        evidence: typed_ir::PrincipalEvidence {
            expected_edges: expected_edge_evidence
                .into_iter()
                .map(export_expected_edge_evidence)
                .collect(),
            expected_adapter_edges: adapter_edges
                .into_iter()
                .map(export_expected_adapter_edge_evidence)
                .collect(),
            derived_expected_edges: derived_edges
                .into_iter()
                .map(export_derived_expected_edge_evidence)
                .collect(),
            handler_matches: handler_matches
                .into_iter()
                .map(export_handler_match_evidence)
                .collect(),
        },
    }
}

fn export_debug_principal_evidence_enabled() -> bool {
    std::env::var_os("YULANG_DISABLE_PRINCIPAL_ELABORATE").is_some()
        || std::env::var_os("YULANG_EXPORT_DEBUG_EVIDENCE").is_some()
        || std::env::var_os("YULANG_VERBOSE_IR").is_some()
}

fn export_expected_edge_evidence(evidence: ExpectedEdgeEvidence) -> typed_ir::ExpectedEdgeEvidence {
    typed_ir::ExpectedEdgeEvidence {
        id: evidence.id.0,
        kind: export_expected_edge_kind(evidence.kind),
        source_range: evidence.source_range,
        actual: evidence.actual,
        expected: evidence.expected,
        actual_effect: evidence.actual_effect,
        expected_effect: evidence.expected_effect,
        closed: evidence.closed,
        informative: evidence.informative,
        runtime_usable: evidence.runtime_usable,
    }
}

fn export_handler_match_evidence(evidence: HandlerMatchEvidence) -> typed_ir::HandlerMatchEvidence {
    typed_ir::HandlerMatchEvidence {
        id: evidence.id,
        source_range: evidence.source_range,
        actual_effect: evidence.actual_effect,
        keep: evidence.keep,
        handled: evidence.handled,
        residual_effect: evidence.residual_effect,
        closed: evidence.closed,
        informative: evidence.informative,
        runtime_usable: evidence.runtime_usable,
    }
}

fn export_derived_expected_edge_evidence(
    evidence: DerivedExpectedEdgeEvidence,
) -> typed_ir::DerivedExpectedEdgeEvidence {
    typed_ir::DerivedExpectedEdgeEvidence {
        parent: evidence.parent.0,
        kind: export_derived_expected_edge_kind(evidence.kind),
        polarity: export_edge_polarity(evidence.polarity),
        path: evidence
            .path
            .into_iter()
            .map(export_edge_path_segment)
            .collect(),
        actual: evidence.actual,
        expected: evidence.expected,
    }
}

fn export_derived_expected_edge_kind(
    kind: DerivedExpectedEdgeKind,
) -> typed_ir::DerivedExpectedEdgeKind {
    match kind {
        DerivedExpectedEdgeKind::RecordField => typed_ir::DerivedExpectedEdgeKind::RecordField,
        DerivedExpectedEdgeKind::TupleItem => typed_ir::DerivedExpectedEdgeKind::TupleItem,
        DerivedExpectedEdgeKind::VariantPayload => {
            typed_ir::DerivedExpectedEdgeKind::VariantPayload
        }
        DerivedExpectedEdgeKind::FunctionParam => typed_ir::DerivedExpectedEdgeKind::FunctionParam,
        DerivedExpectedEdgeKind::FunctionReturn => {
            typed_ir::DerivedExpectedEdgeKind::FunctionReturn
        }
    }
}

fn export_edge_polarity(polarity: EdgePolarity) -> typed_ir::EdgePolarity {
    match polarity {
        EdgePolarity::Covariant => typed_ir::EdgePolarity::Covariant,
        EdgePolarity::Contravariant => typed_ir::EdgePolarity::Contravariant,
        EdgePolarity::Invariant => typed_ir::EdgePolarity::Invariant,
    }
}

fn export_edge_path_segment(segment: EdgePathSegment) -> typed_ir::EdgePathSegment {
    match segment {
        EdgePathSegment::Field(name) => typed_ir::EdgePathSegment::Field(name),
        EdgePathSegment::TupleIndex(index) => typed_ir::EdgePathSegment::TupleIndex(index),
        EdgePathSegment::VariantCase(name) => typed_ir::EdgePathSegment::VariantCase(name),
        EdgePathSegment::PayloadIndex(index) => typed_ir::EdgePathSegment::PayloadIndex(index),
        EdgePathSegment::FunctionParam => typed_ir::EdgePathSegment::FunctionParam,
        EdgePathSegment::FunctionReturn => typed_ir::EdgePathSegment::FunctionReturn,
    }
}

fn export_expected_adapter_edge_evidence(
    evidence: ExpectedAdapterEdgeEvidence,
) -> typed_ir::ExpectedAdapterEdgeEvidence {
    typed_ir::ExpectedAdapterEdgeEvidence {
        id: evidence.id.0,
        source_expected_edge: evidence.source_expected_edge.map(|id| id.0),
        kind: export_expected_adapter_edge_kind(evidence.kind),
        source_range: evidence.source_range,
        actual_value: evidence.actual_value,
        expected_value: evidence.expected_value,
        actual_effect: evidence.actual_effect,
        expected_effect: evidence.expected_effect,
        closed: evidence.closed,
        informative: evidence.informative,
        runtime_usable: evidence.runtime_usable,
    }
}

fn export_expected_adapter_edge_kind(
    kind: crate::diagnostic::ExpectedAdapterEdgeKind,
) -> typed_ir::ExpectedAdapterEdgeKind {
    match kind {
        crate::diagnostic::ExpectedAdapterEdgeKind::EffectOperationArgument => {
            typed_ir::ExpectedAdapterEdgeKind::EffectOperationArgument
        }
        crate::diagnostic::ExpectedAdapterEdgeKind::ValueToThunk => {
            typed_ir::ExpectedAdapterEdgeKind::ValueToThunk
        }
        crate::diagnostic::ExpectedAdapterEdgeKind::ThunkToValue => {
            typed_ir::ExpectedAdapterEdgeKind::ThunkToValue
        }
        crate::diagnostic::ExpectedAdapterEdgeKind::BindHere => {
            typed_ir::ExpectedAdapterEdgeKind::BindHere
        }
        crate::diagnostic::ExpectedAdapterEdgeKind::HandlerResidual => {
            typed_ir::ExpectedAdapterEdgeKind::HandlerResidual
        }
        crate::diagnostic::ExpectedAdapterEdgeKind::HandlerReturn => {
            typed_ir::ExpectedAdapterEdgeKind::HandlerReturn
        }
        crate::diagnostic::ExpectedAdapterEdgeKind::ResumeArgument => {
            typed_ir::ExpectedAdapterEdgeKind::ResumeArgument
        }
    }
}

fn export_expected_edge_kind(
    kind: crate::diagnostic::ExpectedEdgeKind,
) -> typed_ir::ExpectedEdgeKind {
    match kind {
        crate::diagnostic::ExpectedEdgeKind::IfCondition => typed_ir::ExpectedEdgeKind::IfCondition,
        crate::diagnostic::ExpectedEdgeKind::IfBranch => typed_ir::ExpectedEdgeKind::IfBranch,
        crate::diagnostic::ExpectedEdgeKind::MatchGuard => typed_ir::ExpectedEdgeKind::MatchGuard,
        crate::diagnostic::ExpectedEdgeKind::MatchBranch => typed_ir::ExpectedEdgeKind::MatchBranch,
        crate::diagnostic::ExpectedEdgeKind::CatchGuard => typed_ir::ExpectedEdgeKind::CatchGuard,
        crate::diagnostic::ExpectedEdgeKind::CatchBranch => typed_ir::ExpectedEdgeKind::CatchBranch,
        crate::diagnostic::ExpectedEdgeKind::ApplicationCallee => {
            typed_ir::ExpectedEdgeKind::ApplicationCallee
        }
        crate::diagnostic::ExpectedEdgeKind::ApplicationArgument => {
            typed_ir::ExpectedEdgeKind::ApplicationArgument
        }
        crate::diagnostic::ExpectedEdgeKind::Annotation => typed_ir::ExpectedEdgeKind::Annotation,
        crate::diagnostic::ExpectedEdgeKind::RecordField => typed_ir::ExpectedEdgeKind::RecordField,
        crate::diagnostic::ExpectedEdgeKind::VariantPayload => {
            typed_ir::ExpectedEdgeKind::VariantPayload
        }
        crate::diagnostic::ExpectedEdgeKind::AssignmentValue => {
            typed_ir::ExpectedEdgeKind::AssignmentValue
        }
        crate::diagnostic::ExpectedEdgeKind::RepresentationCoerce => {
            typed_ir::ExpectedEdgeKind::RepresentationCoerce
        }
    }
}

fn refine_runtime_binding_scheme_bodies(
    state: &LowerState,
    paths: &[(Path, DefId)],
    bindings: &mut [typed_ir::PrincipalBinding],
) {
    for binding in bindings {
        let Some((_, def)) = paths
            .iter()
            .find(|(path, _)| export_path(path) == binding.name)
        else {
            continue;
        };
        if state.runtime_export_schemes.contains_key(def) {
            continue;
        }
        if binding
            .name
            .segments
            .first()
            .map(|segment| segment.0.as_str() == "std")
            .unwrap_or(false)
        {
            continue;
        }
        let Some(&body_tv) = state.def_tvs.get(def) else {
            continue;
        };
        if let Some(closed) = erase_open_vars_from_runtime_type(&binding.scheme.body)
            && core_type_has_no_vars(&closed)
            && !core_value_type_has_unknown(&closed)
        {
            binding.scheme.body = closed;
            binding.scheme.requirements.clear();
            continue;
        }
        let bounds = export_coalesced_type_bounds_for_tv(&state.infer, body_tv);
        let (Some(lower), Some(upper)) = (bounds.lower.as_deref(), bounds.upper.as_deref()) else {
            continue;
        };
        if lower == upper && core_type_has_no_vars(lower) {
            binding.scheme.body = lower.clone();
            binding.scheme.requirements.clear();
            continue;
        }
        if let Some(closed) = closed_runtime_type_from_bounds(lower, upper) {
            binding.scheme.body = closed;
            binding.scheme.requirements.clear();
        }
    }
}

pub fn export_principal_module(state: &mut LowerState) -> typed_ir::PrincipalModule {
    state.refresh_selection_environment();
    let paths = collect_user_observable_binding_paths(state);
    let mut target_defs = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment();
    let edge_evidence = build_edge_evidence_cache(state);
    let root_exprs = export_root_exprs(state, &edge_evidence);
    typed_ir::PrincipalModule {
        path: typed_ir::Path::default(),
        bindings: export_bindings_for_paths(state, &paths, &root_exprs, &edge_evidence),
        roots: (0..root_exprs.len())
            .map(typed_ir::PrincipalRoot::Expr)
            .collect(),
        root_exprs,
    }
}

pub fn export_principal_bindings(state: &mut LowerState) -> Vec<typed_ir::PrincipalBinding> {
    state.refresh_selection_environment();
    let paths = collect_user_observable_binding_paths(state);
    let mut target_defs = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment();
    let edge_evidence = build_edge_evidence_cache(state);
    export_bindings_for_paths(state, &paths, &[], &edge_evidence)
}

pub fn export_core_program_for_binding_paths(
    state: &mut LowerState,
    paths: &[(Path, DefId)],
) -> typed_ir::CoreProgram {
    state.refresh_selection_environment();
    let target_defs = collect_export_target_defs_for_binding_paths(state, paths);
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment();
    let expected_edge_evidence = collect_expected_edge_evidence(state);
    let edge_evidence_cache = expected_edge_evidence
        .iter()
        .cloned()
        .map(|e| (e.id, e))
        .collect::<HashMap<_, _>>();
    let root_exprs = Vec::new();
    let mut bindings = export_bindings_for_paths(state, paths, &root_exprs, &edge_evidence_cache);
    refine_runtime_binding_scheme_bodies(state, paths, &mut bindings);
    let graph = export_type_graph_view_for_paths(state, paths, &bindings);
    let export_debug_evidence = export_debug_principal_evidence_enabled();
    let derived_edges = if export_debug_evidence {
        derive_all_expected_edge_evidence(&expected_edge_evidence)
    } else {
        Vec::new()
    };
    let adapter_edges = if export_debug_evidence {
        collect_expected_adapter_edge_evidence(state)
    } else {
        Vec::new()
    };
    let handler_matches = collect_handler_match_evidence(state);

    typed_ir::CoreProgram {
        program: typed_ir::PrincipalModule {
            path: typed_ir::Path::default(),
            bindings,
            root_exprs,
            roots: Vec::new(),
        },
        graph,
        evidence: typed_ir::PrincipalEvidence {
            expected_edges: expected_edge_evidence
                .into_iter()
                .map(export_expected_edge_evidence)
                .collect(),
            expected_adapter_edges: adapter_edges
                .into_iter()
                .map(export_expected_adapter_edge_evidence)
                .collect(),
            derived_expected_edges: derived_edges
                .into_iter()
                .map(export_derived_expected_edge_evidence)
                .collect(),
            handler_matches: handler_matches
                .into_iter()
                .map(export_handler_match_evidence)
                .collect(),
        },
    }
}

fn collect_export_target_defs_for_binding_paths(
    state: &LowerState,
    binding_paths: &[(Path, DefId)],
) -> HashSet<DefId> {
    let exportable_defs = state
        .ctx
        .collect_all_binding_paths()
        .into_iter()
        .map(|(_, def)| def)
        .collect::<HashSet<_>>();
    let mut target_defs = HashSet::new();
    let mut pending = Vec::new();
    for (_, def) in binding_paths {
        if target_defs.insert(*def) {
            pending.push(*def);
        }
    }
    while let Some(def) = pending.pop() {
        let Some(body) = state.principal_bodies.get(&def) else {
            continue;
        };
        extend_target_defs_from_expr(
            state,
            body,
            &exportable_defs,
            &mut target_defs,
            &mut pending,
        );
    }
    target_defs
}

fn build_edge_evidence_cache(state: &LowerState) -> HashMap<ExpectedEdgeId, ExpectedEdgeEvidence> {
    collect_expected_edge_evidence(state)
        .into_iter()
        .map(|e| (e.id, e))
        .collect()
}

fn collect_user_observable_binding_paths(state: &LowerState) -> Vec<(Path, DefId)> {
    let canonical = collect_canonical_binding_paths(state);
    let mut paths = state
        .ctx
        .collect_observable_binding_paths()
        .into_iter()
        .filter(|(_, def)| {
            canonical
                .get(def)
                .and_then(|path| path.segments.first().cloned())
                .or_else(|| {
                    state
                        .ctx
                        .collect_all_binding_paths()
                        .into_iter()
                        .find_map(|(path, current)| (current == *def).then_some(path))
                        .and_then(|path| path.segments.first().cloned())
                })
                .map(|name| name.0.as_str() != "std")
                .unwrap_or(true)
        })
        .collect::<Vec<_>>();
    extend_hir_role_rewrite_support_paths(state, &canonical, &mut paths);
    paths
}

fn export_type_graph_view_for_paths(
    state: &LowerState,
    paths: &[(Path, DefId)],
    bindings: &[typed_ir::PrincipalBinding],
) -> typed_ir::CoreGraphView {
    let binding_nodes = paths
        .iter()
        .filter_map(|(path, def)| {
            let body_tv = state.def_tvs.get(def).copied()?;
            let binding = bindings
                .iter()
                .find(|binding| binding.name == export_path(path))?;
            Some(typed_ir::BindingGraphNode {
                binding: binding.name.clone(),
                scheme_body: binding.scheme.body.clone(),
                body_bounds: export_type_bounds_for_tv(&state.infer, body_tv),
            })
        })
        .collect();
    let root_exprs = export_root_expr_nodes(state);
    let runtime_symbols = export_runtime_symbols(state, paths);
    let role_impls = export_role_impl_graph_nodes(state, paths);
    let primitive_types = state.primitive_paths.export_core_type_nodes();
    typed_ir::CoreGraphView {
        bindings: binding_nodes,
        root_exprs,
        runtime_symbols,
        role_impls,
        primitive_types,
    }
}

fn export_role_impl_graph_nodes(
    state: &LowerState,
    paths: &[(Path, DefId)],
) -> Vec<typed_ir::RoleImplGraphNode> {
    let mut def_paths = paths
        .iter()
        .map(|(path, def)| (*def, export_path(path)))
        .collect::<HashMap<_, _>>();
    for (def, path) in collect_canonical_binding_paths(state) {
        def_paths.entry(def).or_insert_with(|| export_path(&path));
    }
    for (path, def) in state.ctx.collect_all_binding_paths() {
        def_paths.entry(def).or_insert_with(|| export_path(&path));
    }
    let mut out = Vec::new();
    for candidate in state
        .infer
        .role_impl_candidates
        .borrow()
        .values()
        .flat_map(|candidates| candidates.iter())
    {
        let members = candidate
            .member_defs
            .iter()
            .filter_map(|(name, def)| {
                def_paths.get(def).map(|path| typed_ir::RecordField {
                    name: typed_ir::Name(name.0.clone()),
                    value: path.clone(),
                    optional: false,
                })
            })
            .collect::<Vec<_>>();
        if members.is_empty() {
            continue;
        }
        let role_infos = state.infer.role_arg_infos_of(&candidate.role);
        let mut inputs = Vec::new();
        let mut associated_types = Vec::new();
        for (index, arg) in candidate.compact_args.iter().enumerate() {
            let bounds = export_compact_type_bounds(arg);
            match role_infos.get(index) {
                Some(info) if !info.is_input => associated_types.push(typed_ir::RecordField {
                    name: typed_ir::Name(info.name.clone()),
                    value: bounds,
                    optional: false,
                }),
                _ => inputs.push(bounds),
            }
        }
        out.push(typed_ir::RoleImplGraphNode {
            role: export_path(&candidate.role),
            inputs,
            associated_types,
            members,
        });
    }
    out.sort_by(|lhs, rhs| {
        lhs.role
            .segments
            .cmp(&rhs.role.segments)
            .then_with(|| format!("{:?}", lhs.inputs).cmp(&format!("{:?}", rhs.inputs)))
    });
    out.dedup();
    out
}

fn export_runtime_symbols(
    state: &LowerState,
    paths: &[(Path, DefId)],
) -> Vec<typed_ir::RuntimeSymbol> {
    let canonical_paths = state.ctx.canonical_value_paths();
    let mut symbol_paths = paths.to_vec();
    let all_binding_paths = state.ctx.collect_all_binding_paths();
    for def in state.effect_op_args.keys().copied() {
        if symbol_paths.iter().any(|(_, current)| *current == def) {
            continue;
        }
        if let Some(path) = canonical_paths.get(&def).cloned().or_else(|| {
            all_binding_paths
                .iter()
                .find_map(|(path, current)| (*current == def).then_some(path))
                .cloned()
        }) {
            symbol_paths.push((path, def));
        }
    }
    let mut symbols = symbol_paths
        .iter()
        .map(|(path, def)| {
            let kind = if state.effect_op_args.contains_key(def) {
                typed_ir::RuntimeSymbolKind::EffectOperation
            } else if state.infer.is_role_method_def(*def) || role_method_path(state, path) {
                typed_ir::RuntimeSymbolKind::RoleMethod
            } else {
                typed_ir::RuntimeSymbolKind::Value
            };
            let path = if kind == typed_ir::RuntimeSymbolKind::EffectOperation {
                canonical_paths.get(def).unwrap_or(path)
            } else {
                path
            };
            typed_ir::RuntimeSymbol {
                path: export_path(path),
                kind,
            }
        })
        .collect::<Vec<_>>();
    for info in state.infer.role_methods.values() {
        let mut path = info.role.clone();
        path.segments.push(info.name.clone());
        let exported = export_path(&path);
        if !symbols.iter().any(|symbol| symbol.path == exported) {
            symbols.push(typed_ir::RuntimeSymbol {
                path: exported,
                kind: typed_ir::RuntimeSymbolKind::RoleMethod,
            });
        }
    }
    symbols.sort_by(|lhs, rhs| lhs.path.segments.cmp(&rhs.path.segments));
    symbols.dedup_by(|lhs, rhs| lhs.path == rhs.path);
    symbols
}

fn role_method_path(state: &LowerState, path: &Path) -> bool {
    state.infer.role_methods.values().any(|info| {
        let mut method_path = info.role.clone();
        method_path.segments.push(info.name.clone());
        method_path == *path
    })
}

fn collect_export_target_defs(
    state: &LowerState,
    binding_paths: &[(Path, DefId)],
) -> HashSet<DefId> {
    let exportable_defs = binding_paths
        .iter()
        .map(|(_, def)| *def)
        .collect::<HashSet<_>>();
    let mut target_defs = HashSet::new();
    let mut pending = Vec::new();

    for (path, block) in &state.top_level_blocks {
        if !path.segments.is_empty() {
            continue;
        }
        extend_target_defs_from_block(
            state,
            block,
            &exportable_defs,
            &mut target_defs,
            &mut pending,
        );
    }
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    target_defs.extend(collect_hir_role_rewrite_support_defs(state));

    while let Some(def) = pending.pop() {
        let Some(body) = state.principal_bodies.get(&def) else {
            continue;
        };
        extend_target_defs_from_expr(
            state,
            body,
            &exportable_defs,
            &mut target_defs,
            &mut pending,
        );
    }

    target_defs
}

fn extend_target_defs_from_block(
    state: &LowerState,
    block: &TypedBlock,
    exportable_defs: &HashSet<DefId>,
    target_defs: &mut HashSet<DefId>,
    pending: &mut Vec<DefId>,
) {
    for stmt in &block.stmts {
        match stmt {
            TypedStmt::Let(_, value) | TypedStmt::Expr(value) => {
                extend_target_defs_from_expr(state, value, exportable_defs, target_defs, pending);
            }
            TypedStmt::Module(def, body) => {
                if exportable_defs.contains(def) && target_defs.insert(*def) {
                    pending.push(*def);
                }
                extend_target_defs_from_block(state, body, exportable_defs, target_defs, pending);
            }
        }
    }
    if let Some(tail) = &block.tail {
        extend_target_defs_from_expr(state, tail, exportable_defs, target_defs, pending);
    }
}

fn extend_target_defs_from_expr(
    state: &LowerState,
    expr: &TypedExpr,
    exportable_defs: &HashSet<DefId>,
    target_defs: &mut HashSet<DefId>,
    pending: &mut Vec<DefId>,
) {
    match &expr.kind {
        ExprKind::PrimitiveOp(_) => {}
        ExprKind::Lit(_) => {}
        ExprKind::Var(def) => {
            if exportable_defs.contains(def) && target_defs.insert(*def) {
                pending.push(*def);
            }
        }
        ExprKind::Ref(ref_id) => {
            if let Some(def) = state.ctx.refs.get(*ref_id) {
                if exportable_defs.contains(&def) && target_defs.insert(def) {
                    pending.push(def);
                }
            }
        }
        ExprKind::App { callee, arg, .. } => {
            if let Some((def, args)) = collect_transparent_role_wrapper_application_def(state, expr)
            {
                if exportable_defs.contains(&def) && target_defs.insert(def) {
                    pending.push(def);
                }
                for arg in args {
                    extend_target_defs_from_expr(state, arg, exportable_defs, target_defs, pending);
                }
                return;
            }
            for def in collect_export_method_defs(state, expr) {
                if exportable_defs.contains(&def) && target_defs.insert(def) {
                    pending.push(def);
                }
            }
            extend_target_defs_from_expr(state, callee, exportable_defs, target_defs, pending);
            extend_target_defs_from_expr(state, arg, exportable_defs, target_defs, pending);
        }
        ExprKind::RefSet { reference, value } => {
            extend_target_defs_from_expr(state, reference, exportable_defs, target_defs, pending);
            extend_target_defs_from_expr(state, value, exportable_defs, target_defs, pending);
        }
        ExprKind::Lam(_, body)
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::BindHere(body)
        | ExprKind::PackForall(_, body) => {
            extend_target_defs_from_expr(state, body, exportable_defs, target_defs, pending);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                extend_target_defs_from_expr(state, item, exportable_defs, target_defs, pending);
            }
        }
        ExprKind::Record { fields, spread } => {
            for (_, value) in fields {
                extend_target_defs_from_expr(state, value, exportable_defs, target_defs, pending);
            }
            if let Some(spread) = spread {
                match spread {
                    crate::ast::expr::RecordSpread::Head(expr)
                    | crate::ast::expr::RecordSpread::Tail(expr) => {
                        extend_target_defs_from_expr(
                            state,
                            expr,
                            exportable_defs,
                            target_defs,
                            pending,
                        );
                    }
                }
            }
        }
        ExprKind::PolyVariant(_, payloads, _) => {
            for payload in payloads {
                extend_target_defs_from_expr(state, payload, exportable_defs, target_defs, pending);
            }
        }
        ExprKind::Select { recv, .. } => {
            extend_target_defs_from_expr(state, recv, exportable_defs, target_defs, pending);
            if let crate::ast::expr::ExprKind::Select { name, .. } = &expr.kind {
                for def in collect_export_select_defs(state, expr.tv, recv.tv, name) {
                    if exportable_defs.contains(&def) && target_defs.insert(def) {
                        pending.push(def);
                    }
                }
            }
        }
        ExprKind::Match(scrutinee, arms) => {
            extend_target_defs_from_expr(state, scrutinee, exportable_defs, target_defs, pending);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    extend_target_defs_from_expr(
                        state,
                        guard,
                        exportable_defs,
                        target_defs,
                        pending,
                    );
                }
                extend_target_defs_from_expr(
                    state,
                    &arm.body,
                    exportable_defs,
                    target_defs,
                    pending,
                );
            }
        }
        ExprKind::Catch(body, arms) => {
            extend_target_defs_from_expr(state, body, exportable_defs, target_defs, pending);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    extend_target_defs_from_expr(
                        state,
                        guard,
                        exportable_defs,
                        target_defs,
                        pending,
                    );
                }
                match &arm.kind {
                    CatchArmKind::Value(_, body) => {
                        extend_target_defs_from_expr(
                            state,
                            body,
                            exportable_defs,
                            target_defs,
                            pending,
                        );
                    }
                    CatchArmKind::Effect { body, .. } => {
                        extend_target_defs_from_expr(
                            state,
                            body,
                            exportable_defs,
                            target_defs,
                            pending,
                        );
                    }
                }
            }
        }
        ExprKind::Block(block) => {
            extend_target_defs_from_block(state, block, exportable_defs, target_defs, pending);
        }
    }
}

#[allow(dead_code)]
fn _path_key(path: &Path) -> String {
    path_key(path)
}

fn export_root_exprs(
    state: &LowerState,
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> Vec<typed_ir::Expr> {
    let globals = collect_canonical_binding_paths(state);
    let mut principal_scheme_cache = HashMap::new();
    let mut base_bounds_cache = HashMap::new();
    let mut complete_principal_cache = CompletePrincipalCache::default();
    let owner_roots = export_owner_root_exprs(
        state,
        &globals,
        &mut principal_scheme_cache,
        &mut base_bounds_cache,
        &mut complete_principal_cache,
        edge_evidence,
    );
    if !owner_roots.is_empty() {
        return owner_roots;
    }

    let mut exporter = ExprExporter::new(
        state,
        &globals,
        &mut principal_scheme_cache,
        &mut base_bounds_cache,
        &mut complete_principal_cache,
        None,
        BTreeSet::new(),
        edge_evidence,
    );
    let mut roots = Vec::new();
    for (path, block) in &state.top_level_blocks {
        if !path.segments.is_empty() {
            continue;
        }
        for stmt in &block.stmts {
            if let crate::ast::expr::TypedStmt::Expr(expr) = stmt {
                roots.push(exporter.export_expr(expr));
            }
        }
        if let Some(tail) = &block.tail {
            roots.push(exporter.export_expr(tail));
        }
    }
    roots
}

fn export_owner_root_exprs(
    state: &LowerState,
    globals: &HashMap<DefId, Path>,
    principal_scheme_cache: &mut HashMap<DefId, Option<typed_ir::Scheme>>,
    base_bounds_cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
    complete_principal_cache: &mut CompletePrincipalCache,
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> Vec<typed_ir::Expr> {
    let mut roots = Vec::new();
    for owner in &state.top_level_expr_owners {
        let Some(body) = state.principal_bodies.get(owner) else {
            continue;
        };
        let mut exporter = ExprExporter::new(
            state,
            globals,
            principal_scheme_cache,
            base_bounds_cache,
            complete_principal_cache,
            None,
            BTreeSet::new(),
            edge_evidence,
        );
        roots.push(exporter.export_expr(body));
    }
    roots
}

fn collect_export_method_defs(state: &LowerState, expr: &TypedExpr) -> Vec<DefId> {
    if let Some((def, _)) = collect_transparent_role_wrapper_application_def(state, expr) {
        return vec![def];
    }
    if let Some(def) = state.infer.resolved_selection_def(expr.tv) {
        return vec![canonical_runtime_export_def(state, def)];
    }
    let (head, _args) = collect_apply_spine(expr);
    match &head.kind {
        ExprKind::Select { .. } => {
            if let Some(def) = state.infer.resolved_selection_def(head.tv) {
                return vec![canonical_runtime_export_def(state, def)];
            }
            Vec::new()
        }
        ExprKind::Var(_) => Vec::new(),
        _ => Vec::new(),
    }
}

fn collect_export_select_defs(
    state: &LowerState,
    select_tv: crate::ids::TypeVar,
    _recv_tv: crate::ids::TypeVar,
    name: &crate::symbols::Name,
) -> Vec<DefId> {
    if let Some(def) = state.infer.resolved_selection_def(select_tv) {
        return vec![canonical_runtime_export_def(state, def)];
    }
    if let Some(def) = state.infer.resolve_extension_method_def(name) {
        return vec![canonical_runtime_export_def(state, def)];
    }
    Vec::new()
}

fn collect_transparent_role_wrapper_application_def<'a>(
    state: &LowerState,
    expr: &'a TypedExpr,
) -> Option<(DefId, Vec<&'a TypedExpr>)> {
    let (head, args) = collect_apply_spine(expr);
    let ExprKind::Var(def) = &head.kind else {
        return None;
    };
    if !state.ctx.is_operator_def(*def) {
        return None;
    }
    let (method_name, role_arg_count) = transparent_role_wrapper_method(state, *def)?;
    let info = state.infer.role_methods.get(&method_name)?;
    let (recv, rest) = args.split_first()?;
    let role_args = rest
        .iter()
        .take(role_arg_count)
        .map(|arg| arg.tv)
        .collect::<Vec<_>>();
    let def = state
        .infer
        .resolve_concrete_role_method_call_def(info, Some(recv.tv), &role_args)?;
    Some((canonical_runtime_export_def(state, def), args))
}

fn transparent_role_wrapper_method(
    state: &LowerState,
    def: DefId,
) -> Option<(crate::symbols::Name, usize)> {
    let body = state.principal_bodies.get(&def)?;
    let mut params = Vec::new();
    let mut current: &TypedExpr = body;
    while let ExprKind::Lam(param, body) = &current.kind {
        params.push(*param);
        current = body;
    }
    let (head, args) = collect_apply_spine(current);
    let ExprKind::Select { recv, name } = &head.kind else {
        return None;
    };
    let ExprKind::Var(recv_def) = recv.kind else {
        return None;
    };
    if params.first().copied() != Some(recv_def) {
        return None;
    }
    if args.len() + 1 != params.len() {
        return None;
    }
    for (arg, param) in args.iter().zip(params.iter().skip(1)) {
        let ExprKind::Var(arg_def) = arg.kind else {
            return None;
        };
        if arg_def != *param {
            return None;
        }
    }
    Some((name.clone(), args.len()))
}

fn collect_hir_role_rewrite_support_defs(state: &LowerState) -> Vec<DefId> {
    let mut defs = Vec::new();
    for info in state.infer.role_methods.values() {
        defs.extend(collect_role_method_candidate_defs(state, &info.name, info));
    }
    defs
}

fn extend_hir_role_rewrite_support_paths(
    state: &LowerState,
    canonical: &std::collections::HashMap<DefId, Path>,
    paths: &mut Vec<(Path, DefId)>,
) {
    let mut known = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    for def in collect_hir_role_rewrite_support_defs(state) {
        if !known.insert(def) {
            continue;
        }
        if let Some(path) = canonical.get(&def) {
            paths.push((path.clone(), def));
        }
    }
}

fn collect_role_method_candidate_defs(
    state: &LowerState,
    name: &crate::symbols::Name,
    info: &crate::solve::RoleMethodInfo,
) -> Vec<DefId> {
    let mut defs = Vec::new();
    for candidate in state.infer.role_impl_candidates_of(&info.role) {
        if let Some(&def) = candidate.member_defs.get(name) {
            if !defs.contains(&def) {
                defs.push(def);
            }
        }
    }
    defs
}

fn export_root_expr_nodes(state: &LowerState) -> Vec<typed_ir::ExprGraphNode> {
    let owner_nodes = export_owner_root_expr_nodes(state);
    if !owner_nodes.is_empty() {
        return owner_nodes;
    }

    let mut nodes = Vec::new();
    for (path, block) in &state.top_level_blocks {
        if !path.segments.is_empty() {
            continue;
        }
        for stmt in &block.stmts {
            if let crate::ast::expr::TypedStmt::Expr(expr) = stmt {
                nodes.push(typed_ir::ExprGraphNode {
                    owner: typed_ir::GraphOwner::RootExpr(nodes.len()),
                    bounds: export_relevant_type_bounds_for_tv(
                        &state.infer,
                        expr.tv,
                        &BTreeSet::new(),
                    ),
                });
            }
        }
        if let Some(tail) = &block.tail {
            nodes.push(typed_ir::ExprGraphNode {
                owner: typed_ir::GraphOwner::RootExpr(nodes.len()),
                bounds: export_relevant_type_bounds_for_tv(&state.infer, tail.tv, &BTreeSet::new()),
            });
        }
    }
    nodes
}

fn export_owner_root_expr_nodes(state: &LowerState) -> Vec<typed_ir::ExprGraphNode> {
    let mut nodes = Vec::new();
    for owner in &state.top_level_expr_owners {
        let tv = match state.principal_bodies.get(owner) {
            Some(body) => body.tv,
            None => match state.def_tvs.get(owner) {
                Some(&tv) => tv,
                None => continue,
            },
        };
        nodes.push(typed_ir::ExprGraphNode {
            owner: typed_ir::GraphOwner::RootExpr(nodes.len()),
            bounds: export_relevant_type_bounds_for_tv(&state.infer, tv, &BTreeSet::new()),
        });
    }
    nodes
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::thread;

    use super::{export_core_program, export_principal_bindings, export_principal_module};
    use crate::lower::LowerState;
    use crate::source::lower_virtual_source_with_options;
    use rowan::SyntaxNode;
    use yulang_parser::sink::YulangLanguage;
    use yulang_sources::SourceOptions;
    use yulang_typed_ir as typed_ir;

    fn parse_and_lower(src: &str) -> LowerState {
        let green = yulang_parser::parse_module_to_green(src);
        let root: SyntaxNode<YulangLanguage> = SyntaxNode::new_root(green);
        let mut state = LowerState::new();
        crate::lower::stmt::lower_root(&mut state, &root);
        state
    }

    #[test]
    fn export_core_program_records_runtime_symbol_kinds() {
        let mut state = parse_and_lower(
            "act undet:\n  our bool: () -> bool\n\n\
             role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             my y = undet::bool()\n",
        );

        let program = export_core_program(&mut state);

        assert!(program.graph.runtime_symbols.iter().any(|symbol| {
            path_segments(&symbol.path) == vec!["undet", "bool"]
                && symbol.kind == typed_ir::RuntimeSymbolKind::EffectOperation
        }));
        assert!(program.graph.runtime_symbols.iter().any(|symbol| {
            path_segments(&symbol.path) == vec!["Add", "add"]
                && symbol.kind == typed_ir::RuntimeSymbolKind::RoleMethod
        }));
    }

    fn lower_with_std(src: &str) -> LowerState {
        let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("lib")
            .join("std");
        lower_virtual_source_with_options(
            src,
            None,
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
        )
        .unwrap()
        .state
    }

    fn path_segments(path: &typed_ir::Path) -> Vec<&str> {
        path.segments
            .iter()
            .map(|segment| segment.0.as_str())
            .collect()
    }

    fn run_with_large_stack<T>(f: impl FnOnce() -> T + Send + 'static) -> T
    where
        T: Send + 'static,
    {
        thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(f)
            .expect("spawn large-stack test thread")
            .join()
            .unwrap()
    }

    #[test]
    fn export_principal_module_includes_observable_bindings() {
        let mut state = parse_and_lower("my id x = x\nmy one = 1\n");
        let module = export_principal_module(&mut state);
        let names = module
            .bindings
            .iter()
            .map(|binding| {
                binding
                    .name
                    .segments
                    .iter()
                    .map(|segment| segment.0.as_str())
                    .collect::<Vec<_>>()
                    .join("::")
            })
            .collect::<Vec<_>>();
        assert_eq!(names, vec!["id".to_string(), "one".to_string()]);
        assert!(module.root_exprs.is_empty());
    }

    #[test]
    fn export_principal_bindings_keeps_role_requirements() {
        let mut state =
            parse_and_lower("role Display 'a:\n  our a.display: string\n\nmy show x = x.display\n");
        let bindings = export_principal_bindings(&mut state);
        let show = bindings
            .iter()
            .find(|binding| {
                binding.name.segments.last().map(|name| name.0.as_str()) == Some("show")
            })
            .unwrap();
        assert_eq!(show.scheme.requirements.len(), 1);
        assert_eq!(
            show.scheme.requirements[0].role.segments,
            vec![typed_ir::Name("Display".to_string())]
        );
    }

    #[test]
    fn export_principal_bindings_resolve_associated_outputs_in_body() {
        let mut state = parse_and_lower(
            "role Index 'container 'key:\n  type value\n  our container.index: 'key -> value\n\n\
             impl Index int bool:\n  type value = string\n  our x.index y = \"ok\"\n\n\
             my shown = 1.index true\n",
        );
        let bindings = export_principal_bindings(&mut state);
        let shown = bindings
            .iter()
            .find(|binding| {
                binding.name.segments.last().map(|name| name.0.as_str()) == Some("shown")
            })
            .unwrap();
        assert_eq!(
            shown.scheme.body,
            typed_ir::Type::Named {
                path: typed_ir::Path::new(vec![
                    typed_ir::Name("std".to_string()),
                    typed_ir::Name("str".to_string()),
                    typed_ir::Name("str".to_string()),
                ]),
                args: Vec::new(),
            }
        );
        match &shown.body {
            typed_ir::Expr::Apply { callee, arg, .. } => {
                assert_eq!(
                    arg.as_ref(),
                    &typed_ir::Expr::Lit(typed_ir::Lit::Bool(true))
                );
                match callee.as_ref() {
                    typed_ir::Expr::Apply { callee, arg, .. } => {
                        assert!(matches!(
                            arg.as_ref(),
                            typed_ir::Expr::Lit(typed_ir::Lit::Int(_))
                        ));
                        match callee.as_ref() {
                            typed_ir::Expr::Var(path) => {
                                let rendered = path
                                    .segments
                                    .iter()
                                    .map(|segment| segment.0.as_str())
                                    .collect::<Vec<_>>()
                                    .join("::");
                                assert!(
                                    rendered.contains("&impl#"),
                                    "expected concrete impl member path, got {rendered}"
                                );
                            }
                            other => panic!("expected concrete impl callee, got {other:?}"),
                        }
                    }
                    other => panic!("expected applied concrete callee, got {other:?}"),
                }
            }
            other => panic!("expected apply body, got {other:?}"),
        }
    }

    #[test]
    fn export_principal_module_resolves_simple_role_method_root() {
        let mut state = parse_and_lower(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int:\n  our x.add y = x\n\n\
             1.add 2\n",
        );
        let module = export_principal_module(&mut state);
        match &module.root_exprs[0] {
            typed_ir::Expr::Apply { callee, arg, .. } => {
                assert_eq!(
                    arg.as_ref(),
                    &typed_ir::Expr::Lit(typed_ir::Lit::Int("2".to_string()))
                );
                match callee.as_ref() {
                    typed_ir::Expr::Apply { callee, arg, .. } => {
                        assert_eq!(
                            arg.as_ref(),
                            &typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string()))
                        );
                        assert!(matches!(callee.as_ref(), typed_ir::Expr::Var(_)));
                    }
                    other => panic!("expected concrete impl apply chain, got {other:?}"),
                }
            }
            other => panic!("expected root apply, got {other:?}"),
        }
    }

    #[test]
    fn export_principal_bindings_resolve_role_methods_through_helper_binding() {
        let mut state = parse_and_lower(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int:\n  our x.add y = x\n\n\
             my plus1 = Add::add 1\n\
             my shown = plus1 2\n",
        );
        let bindings = export_principal_bindings(&mut state);
        let plus1 = bindings
            .iter()
            .find(|binding| {
                binding.name.segments.last().map(|name| name.0.as_str()) == Some("plus1")
            })
            .unwrap();
        match &plus1.body {
            typed_ir::Expr::Apply { callee, arg, .. } => {
                assert!(matches!(
                    arg.as_ref(),
                    typed_ir::Expr::Lit(typed_ir::Lit::Int(_))
                ));
                assert!(matches!(callee.as_ref(), typed_ir::Expr::Var(_)));
            }
            other => panic!("expected concrete helper body, got {other:?}"),
        }
    }

    #[test]
    fn export_principal_bindings_resolve_role_methods_through_generic_wrapper() {
        let mut state = parse_and_lower(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int:\n  our x.add y = x\n\n\
             my plus x y = x.add y\n\
             my shown = plus 1 2\n",
        );
        let bindings = export_principal_bindings(&mut state);
        let shown = bindings
            .iter()
            .find(|binding| {
                binding.name.segments.last().map(|name| name.0.as_str()) == Some("shown")
            })
            .unwrap();
        assert!(
            !format!("{:?}", shown.body).contains("ref_"),
            "generic role wrapper should not export unresolved ref paths: {:?}",
            shown.body
        );
    }

    #[test]
    fn export_principal_bindings_resolve_direct_role_method_generic_wrapper() {
        let mut state = parse_and_lower(
            "role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int:\n  our x.add y = x\n\n\
             my plus = \\x -> \\y -> Add::add x y\n\
             my shown = plus 1 2\n",
        );
        let bindings = export_principal_bindings(&mut state);
        let shown = bindings
            .iter()
            .find(|binding| {
                binding.name.segments.last().map(|name| name.0.as_str()) == Some("shown")
            })
            .unwrap();
        assert!(
            !format!("{:?}", shown.body).contains("ref_"),
            "direct role method wrapper should not export unresolved ref paths: {:?}",
            shown.body
        );
    }

    #[test]
    fn export_principal_bindings_resolve_forward_role_method_generic_wrapper() {
        let mut state = parse_and_lower(
            "my plus = \\x -> \\y -> Add::add x y\n\n\
             role Add 'a:\n  our a.add: 'a -> 'a\n\n\
             impl Add int:\n  our x.add y = x\n\n\
             my shown = plus 1 2\n",
        );
        let bindings = export_principal_bindings(&mut state);
        let shown = bindings
            .iter()
            .find(|binding| {
                binding.name.segments.last().map(|name| name.0.as_str()) == Some("shown")
            })
            .unwrap();
        assert!(
            !format!("{:?}", shown.body).contains("ref_"),
            "forward role method wrapper should not export unresolved ref paths: {:?}",
            shown.body
        );
    }

    #[test]
    fn export_principal_bindings_includes_desugared_lambda_body() {
        let mut state = parse_and_lower("my id x = x\n");
        let bindings = export_principal_bindings(&mut state);
        let id = bindings
            .iter()
            .find(|binding| binding.name.segments.last().map(|name| name.0.as_str()) == Some("id"))
            .unwrap();
        match &id.body {
            typed_ir::Expr::Lambda { param, body, .. } => {
                assert!(param.0.starts_with("x#local_"));
                assert_eq!(
                    body.as_ref(),
                    &typed_ir::Expr::Var(typed_ir::Path::from_name(param.clone()))
                );
            }
            other => panic!("expected lambda body, got {other:?}"),
        }
    }

    #[test]
    fn export_principal_bindings_make_header_patterns_explicit() {
        let mut state = parse_and_lower("my f { width = 1, height } = (width, height)\n");
        let bindings = export_principal_bindings(&mut state);
        let f = bindings
            .iter()
            .find(|binding| binding.name.segments.last().map(|name| name.0.as_str()) == Some("f"))
            .unwrap();
        match &f.body {
            typed_ir::Expr::Lambda { param, body, .. } => match body.as_ref() {
                typed_ir::Expr::Block { stmts, tail } => {
                    assert_eq!(stmts.len(), 1);
                    match &stmts[0] {
                        typed_ir::Stmt::Let { pattern, value } => {
                            assert_eq!(
                                value,
                                &typed_ir::Expr::Var(typed_ir::Path::from_name(param.clone()))
                            );
                            match pattern {
                                typed_ir::Pattern::Record { fields, .. } => {
                                    assert_eq!(fields.len(), 2);
                                    assert_eq!(fields[0].name.0, "width");
                                    assert!(fields[0].default.is_some());
                                    assert_eq!(fields[1].name.0, "height");
                                    assert!(fields[1].default.is_none());
                                }
                                other => panic!("expected record pattern, got {other:?}"),
                            }
                        }
                        other => panic!("expected let statement, got {other:?}"),
                    }
                    assert!(tail.is_some());
                }
                other => panic!("expected block body, got {other:?}"),
            },
            other => panic!("expected lambda body, got {other:?}"),
        }
    }

    #[test]
    fn export_principal_bindings_attach_apply_evidence() {
        let mut state = parse_and_lower("my id x = x\nid 1\n");
        let module = export_principal_module(&mut state);
        match &module.root_exprs[0] {
            typed_ir::Expr::Apply { evidence, .. } => {
                let evidence = evidence.as_ref().expect("apply evidence");
                let arg_has_int = evidence
                    .arg
                    .lower
                    .as_deref()
                    .is_some_and(contains_named_int)
                    || evidence
                        .arg
                        .upper
                        .as_deref()
                        .is_some_and(contains_named_int);
                assert!(
                    arg_has_int,
                    "expected int in arg bounds, got {:?}",
                    evidence.arg
                );
                assert_eq!(
                    evidence.callee,
                    typed_ir::TypeBounds::default(),
                    "root apply should only keep concrete evidence when there is no parent scheme, got {:?}",
                    evidence.callee
                );
            }
            other => panic!("expected apply root, got {other:?}"),
        }
    }

    #[test]
    fn export_principal_bindings_attach_coerce_evidence() {
        let mut state = parse_and_lower("struct point { x: int }\n");
        let bindings = export_principal_bindings(&mut state);
        let evidence = bindings
            .iter()
            .find_map(|binding| find_coerce_evidence(&binding.body, concrete_coerce_evidence))
            .expect("synthetic field projection should carry concrete coerce evidence");

        assert!(
            evidence.actual.lower.is_some() || evidence.actual.upper.is_some(),
            "missing actual coerce bounds: {:?}",
            evidence.actual
        );
        assert!(
            evidence.expected.lower.is_some() || evidence.expected.upper.is_some(),
            "missing expected coerce bounds: {:?}",
            evidence.expected
        );
    }

    #[test]
    fn export_principal_module_collects_top_level_root_exprs() {
        let mut state = parse_and_lower("1\ntrue\n");
        let module = export_principal_module(&mut state);
        assert_eq!(
            module.roots,
            vec![
                typed_ir::PrincipalRoot::Expr(0),
                typed_ir::PrincipalRoot::Expr(1)
            ]
        );
        assert_eq!(
            module.root_exprs,
            vec![
                typed_ir::Expr::Lit(typed_ir::Lit::Int("1".to_string())),
                typed_ir::Expr::Lit(typed_ir::Lit::Bool(true)),
            ]
        );
    }

    #[test]
    fn export_core_program_includes_primitive_type_graph_nodes() {
        let mut state = parse_and_lower("my x = \"ok\"\n");
        let program = export_core_program(&mut state);

        assert!(program.graph.primitive_types.iter().any(|node| {
            node.family == typed_ir::PrimitiveTypeFamily::Str
                && node.path
                    == typed_ir::Path::new(vec![
                        typed_ir::Name("std".to_string()),
                        typed_ir::Name("str".to_string()),
                        typed_ir::Name("str".to_string()),
                    ])
        }));
        assert!(program.graph.primitive_types.iter().any(|node| {
            node.family == typed_ir::PrimitiveTypeFamily::Int
                && node.path == typed_ir::Path::from_name(typed_ir::Name("int".to_string()))
        }));
        assert!(program.graph.primitive_types.iter().any(|node| {
            node.family == typed_ir::PrimitiveTypeFamily::Frac
                && node.path
                    == typed_ir::Path::new(vec![
                        typed_ir::Name("std".to_string()),
                        typed_ir::Name("frac".to_string()),
                        typed_ir::Name("frac".to_string()),
                    ])
        }));
    }

    #[test]
    fn export_principal_module_handles_source_var_assignment_helpers() {
        run_with_large_stack(|| {
            let src = "my write_var =\n  my ($x) = 12\n  &x = 13\n  $x\n\nwrite_var\n";
            let mut state = lower_with_std(src);
            let module = export_principal_module(&mut state);
            let write_var = module
                .bindings
                .iter()
                .find(|binding| {
                    binding.name.segments.last().map(|name| name.0.as_str()) == Some("write_var")
                })
                .expect("write_var binding");
            assert_eq!(
                write_var.scheme.body,
                typed_ir::Type::Named {
                    path: typed_ir::Path::from_name(typed_ir::Name("int".to_string())),
                    args: Vec::new(),
                }
            );
            assert_eq!(module.roots, vec![typed_ir::PrincipalRoot::Expr(0)]);
            assert_eq!(
                module.root_exprs,
                vec![typed_ir::Expr::Var(typed_ir::Path::from_name(
                    typed_ir::Name("write_var".to_string(),)
                ))]
            );
        });
    }

    fn contains_named_int(ty: &typed_ir::Type) -> bool {
        match ty {
            typed_ir::Type::Named { path, .. } => {
                path.segments.last().map(|name| name.0.as_str()) == Some("int")
            }
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                contains_named_int(param)
                    || contains_named_int(param_effect)
                    || contains_named_int(ret_effect)
                    || contains_named_int(ret)
            }
            typed_ir::Type::Tuple(items)
            | typed_ir::Type::Union(items)
            | typed_ir::Type::Inter(items)
            | typed_ir::Type::Row { items, .. } => items.iter().any(contains_named_int),
            typed_ir::Type::Record(record) => {
                record
                    .fields
                    .iter()
                    .any(|field| contains_named_int(&field.value))
                    || record.spread.as_ref().is_some_and(|spread| match spread {
                        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                            contains_named_int(ty)
                        }
                    })
            }
            typed_ir::Type::Variant(variant) => {
                variant
                    .cases
                    .iter()
                    .any(|case| case.payloads.iter().any(contains_named_int))
                    || variant.tail.as_deref().is_some_and(contains_named_int)
            }
            typed_ir::Type::Recursive { body, .. } => contains_named_int(body),
            typed_ir::Type::Unknown
            | typed_ir::Type::Never
            | typed_ir::Type::Any
            | typed_ir::Type::Var(_) => false,
        }
    }

    fn concrete_coerce_evidence(evidence: &typed_ir::CoerceEvidence) -> bool {
        (evidence.actual.lower.is_some() || evidence.actual.upper.is_some())
            && (evidence.expected.lower.is_some() || evidence.expected.upper.is_some())
    }

    fn find_coerce_evidence(
        expr: &typed_ir::Expr,
        predicate: fn(&typed_ir::CoerceEvidence) -> bool,
    ) -> Option<&typed_ir::CoerceEvidence> {
        match expr {
            typed_ir::Expr::Coerce { evidence, expr } => evidence
                .as_ref()
                .filter(|evidence| predicate(evidence))
                .or_else(|| find_coerce_evidence(expr.as_ref(), predicate)),
            typed_ir::Expr::Lambda { body, .. } | typed_ir::Expr::Pack { expr: body, .. } => {
                find_coerce_evidence(body, predicate)
            }
            typed_ir::Expr::BindHere { expr } => find_coerce_evidence(expr, predicate),
            typed_ir::Expr::Apply { callee, arg, .. } => find_coerce_evidence(callee, predicate)
                .or_else(|| find_coerce_evidence(arg, predicate)),
            typed_ir::Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => find_coerce_evidence(cond, predicate)
                .or_else(|| find_coerce_evidence(then_branch, predicate))
                .or_else(|| find_coerce_evidence(else_branch, predicate)),
            typed_ir::Expr::Tuple(items) => items
                .iter()
                .find_map(|item| find_coerce_evidence(item, predicate)),
            typed_ir::Expr::Record { fields, spread } => fields
                .iter()
                .find_map(|field| find_coerce_evidence(&field.value, predicate))
                .or_else(|| match spread {
                    Some(typed_ir::RecordSpreadExpr::Head(expr))
                    | Some(typed_ir::RecordSpreadExpr::Tail(expr)) => {
                        find_coerce_evidence(expr, predicate)
                    }
                    None => None,
                }),
            typed_ir::Expr::Variant { value, .. } => value
                .as_deref()
                .and_then(|value| find_coerce_evidence(value, predicate)),
            typed_ir::Expr::Select { base, .. } => find_coerce_evidence(base, predicate),
            typed_ir::Expr::Match {
                scrutinee, arms, ..
            } => find_coerce_evidence(scrutinee, predicate).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| find_coerce_evidence(guard, predicate))
                        .or_else(|| find_coerce_evidence(&arm.body, predicate))
                })
            }),
            typed_ir::Expr::Block { stmts, tail } => stmts
                .iter()
                .find_map(|stmt| match stmt {
                    typed_ir::Stmt::Let { value, .. } | typed_ir::Stmt::Expr(value) => {
                        find_coerce_evidence(value, predicate)
                    }
                    typed_ir::Stmt::Module { body, .. } => find_coerce_evidence(body, predicate),
                })
                .or_else(|| {
                    tail.as_deref()
                        .and_then(|tail| find_coerce_evidence(tail, predicate))
                }),
            typed_ir::Expr::Handle { body, arms, .. } => find_coerce_evidence(body, predicate)
                .or_else(|| {
                    arms.iter().find_map(|arm| {
                        arm.guard
                            .as_ref()
                            .and_then(|guard| find_coerce_evidence(guard, predicate))
                            .or_else(|| find_coerce_evidence(&arm.body, predicate))
                    })
                }),
            typed_ir::Expr::Var(_) | typed_ir::Expr::PrimitiveOp(_) | typed_ir::Expr::Lit(_) => {
                None
            }
        }
    }
}
