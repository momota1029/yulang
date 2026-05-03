use std::collections::{BTreeSet, HashSet};

use yulang_core_ir as core_ir;

use super::complete_principal::collect_expected_edge_evidence;
use super::expr::export_expr;
use super::names::{export_path, path_key};
use super::paths::{collect_canonical_binding_paths, complete_referenced_binding_closure};
use super::roles::canonical_runtime_export_def;
use super::spine::collect_apply_spine;
use super::types::{
    collect_core_type_vars, export_coalesced_type_bounds_for_tv, export_frozen_scheme,
    export_frozen_scheme_body_type_vars, export_relevant_type_bounds_for_tv, export_scheme,
    export_scheme_body, export_scheme_body_type_vars, export_type_bounds_for_tv,
};
use crate::ast::expr::{CatchArmKind, ExprKind, TypedBlock, TypedExpr, TypedStmt};
use crate::ids::DefId;
use crate::lower::LowerState;
use crate::simplify::compact::compact_type_var;
use crate::simplify::cooccur::coalesce_by_co_occurrence;
use crate::symbols::Path;

pub fn export_core_program(state: &mut LowerState) -> core_ir::CoreProgram {
    state.refresh_selection_environment();
    let binding_paths = state.ctx.collect_all_binding_paths();
    let target_defs = collect_export_target_defs(state, &binding_paths);
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment();
    let selected_paths = binding_paths
        .iter()
        .filter(|(_, def)| target_defs.contains(def))
        .cloned()
        .collect::<Vec<_>>();
    let root_exprs = export_root_exprs(state);
    let mut bindings = export_bindings_for_paths(state, &selected_paths, &root_exprs);
    refine_runtime_binding_scheme_bodies(state, &selected_paths, &mut bindings);
    let roots = (0..root_exprs.len())
        .map(core_ir::PrincipalRoot::Expr)
        .collect();
    let graph = export_type_graph_view_for_paths(state, &selected_paths, &bindings);
    core_ir::CoreProgram {
        program: core_ir::PrincipalModule {
            path: core_ir::Path::default(),
            bindings,
            root_exprs,
            roots,
        },
        graph,
        evidence: core_ir::PrincipalEvidence {
            expected_edges: collect_expected_edge_evidence(state)
                .into_iter()
                .map(export_expected_edge_evidence)
                .collect(),
        },
    }
}

fn export_expected_edge_evidence(
    evidence: super::complete_principal::ExpectedEdgeEvidence,
) -> core_ir::ExpectedEdgeEvidence {
    core_ir::ExpectedEdgeEvidence {
        id: evidence.id.0,
        kind: export_expected_edge_kind(evidence.kind),
        actual: evidence.actual,
        expected: evidence.expected,
        actual_effect: evidence.actual_effect,
        expected_effect: evidence.expected_effect,
        closed: evidence.closed,
        informative: evidence.informative,
        runtime_usable: evidence.runtime_usable,
    }
}

fn export_expected_edge_kind(
    kind: crate::diagnostic::ExpectedEdgeKind,
) -> core_ir::ExpectedEdgeKind {
    match kind {
        crate::diagnostic::ExpectedEdgeKind::IfCondition => core_ir::ExpectedEdgeKind::IfCondition,
        crate::diagnostic::ExpectedEdgeKind::IfBranch => core_ir::ExpectedEdgeKind::IfBranch,
        crate::diagnostic::ExpectedEdgeKind::MatchGuard => core_ir::ExpectedEdgeKind::MatchGuard,
        crate::diagnostic::ExpectedEdgeKind::MatchBranch => core_ir::ExpectedEdgeKind::MatchBranch,
        crate::diagnostic::ExpectedEdgeKind::CatchGuard => core_ir::ExpectedEdgeKind::CatchGuard,
        crate::diagnostic::ExpectedEdgeKind::CatchBranch => core_ir::ExpectedEdgeKind::CatchBranch,
        crate::diagnostic::ExpectedEdgeKind::ApplicationArgument => {
            core_ir::ExpectedEdgeKind::ApplicationArgument
        }
        crate::diagnostic::ExpectedEdgeKind::Annotation => core_ir::ExpectedEdgeKind::Annotation,
        crate::diagnostic::ExpectedEdgeKind::RecordField => core_ir::ExpectedEdgeKind::RecordField,
        crate::diagnostic::ExpectedEdgeKind::VariantPayload => {
            core_ir::ExpectedEdgeKind::VariantPayload
        }
        crate::diagnostic::ExpectedEdgeKind::AssignmentValue => {
            core_ir::ExpectedEdgeKind::AssignmentValue
        }
        crate::diagnostic::ExpectedEdgeKind::RepresentationCoerce => {
            core_ir::ExpectedEdgeKind::RepresentationCoerce
        }
    }
}

fn refine_runtime_binding_scheme_bodies(
    state: &LowerState,
    paths: &[(Path, DefId)],
    bindings: &mut [core_ir::PrincipalBinding],
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
        let Some(&body_tv) = state.def_tvs.get(def) else {
            continue;
        };
        let bounds = export_coalesced_type_bounds_for_tv(&state.infer, body_tv);
        let (Some(lower), Some(upper)) = (bounds.lower.as_deref(), bounds.upper.as_deref()) else {
            continue;
        };
        if lower == upper && core_type_has_no_vars(lower) {
            binding.scheme.body = lower.clone();
        }
    }
}

fn core_type_has_no_vars(ty: &core_ir::Type) -> bool {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(ty, &mut vars);
    vars.is_empty()
}

pub fn export_principal_module(state: &mut LowerState) -> core_ir::PrincipalModule {
    state.refresh_selection_environment();
    let paths = collect_user_observable_binding_paths(state);
    let mut target_defs = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment();
    let root_exprs = export_root_exprs(state);
    core_ir::PrincipalModule {
        path: core_ir::Path::default(),
        bindings: export_bindings_for_paths(state, &paths, &root_exprs),
        roots: (0..root_exprs.len())
            .map(core_ir::PrincipalRoot::Expr)
            .collect(),
        root_exprs,
    }
}

pub fn export_principal_bindings(state: &mut LowerState) -> Vec<core_ir::PrincipalBinding> {
    state.refresh_selection_environment();
    let paths = collect_user_observable_binding_paths(state);
    let mut target_defs = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    target_defs.extend(state.top_level_expr_owners.iter().copied());
    state.finalize_compact_results_for_defs(&target_defs);
    state.refresh_selection_environment();
    export_bindings_for_paths(state, &paths, &[])
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

fn export_bindings_for_paths(
    state: &mut LowerState,
    paths: &[(Path, DefId)],
    extra_exprs: &[core_ir::Expr],
) -> Vec<core_ir::PrincipalBinding> {
    let canonical = collect_canonical_binding_paths(state);
    let mut bindings = canonical
        .into_iter()
        .filter(|(def, _)| paths.iter().any(|(_, path_def)| path_def == def))
        .filter_map(|(def, path)| export_principal_binding(state, &path, def))
        .collect::<Vec<_>>();
    complete_referenced_binding_closure(state, &mut bindings, extra_exprs);
    bindings.sort_by(|lhs, rhs| lhs.name.segments.cmp(&rhs.name.segments));
    dedup_bindings_by_runtime_path(&mut bindings);
    bindings
}

fn dedup_bindings_by_runtime_path(bindings: &mut Vec<core_ir::PrincipalBinding>) {
    let mut deduped: Vec<core_ir::PrincipalBinding> = Vec::with_capacity(bindings.len());
    for binding in bindings.drain(..) {
        match deduped.last_mut() {
            Some(current) if current.name == binding.name => {
                if binding_generality_score(&binding) > binding_generality_score(current) {
                    *current = binding;
                }
            }
            _ => deduped.push(binding),
        }
    }
    *bindings = deduped;
}

fn binding_generality_score(binding: &core_ir::PrincipalBinding) -> usize {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&binding.scheme.body, &mut vars);
    for requirement in &binding.scheme.requirements {
        for arg in &requirement.args {
            match arg {
                core_ir::RoleRequirementArg::Input(bounds)
                | core_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_bounds_vars(bounds, &mut vars);
                }
            }
        }
    }
    vars.len()
}

fn collect_bounds_vars(bounds: &core_ir::TypeBounds, vars: &mut BTreeSet<core_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_vars(upper, vars);
    }
}

fn export_type_graph_view_for_paths(
    state: &LowerState,
    paths: &[(Path, DefId)],
    bindings: &[core_ir::PrincipalBinding],
) -> core_ir::CoreGraphView {
    let binding_nodes = paths
        .iter()
        .filter_map(|(path, def)| {
            let body_tv = state.def_tvs.get(def).copied()?;
            let binding = bindings
                .iter()
                .find(|binding| binding.name == export_path(path))?;
            Some(core_ir::BindingGraphNode {
                binding: binding.name.clone(),
                scheme_body: binding.scheme.body.clone(),
                body_bounds: export_type_bounds_for_tv(&state.infer, body_tv),
            })
        })
        .collect();
    let root_exprs = export_root_expr_nodes(state);
    let runtime_symbols = export_runtime_symbols(state, paths);
    core_ir::CoreGraphView {
        bindings: binding_nodes,
        root_exprs,
        runtime_symbols,
    }
}

fn export_runtime_symbols(
    state: &LowerState,
    paths: &[(Path, DefId)],
) -> Vec<core_ir::RuntimeSymbol> {
    let mut symbols = paths
        .iter()
        .map(|(path, def)| {
            let kind = if state.effect_op_args.contains_key(def) {
                core_ir::RuntimeSymbolKind::EffectOperation
            } else if state.infer.is_role_method_def(*def) || role_method_path(state, path) {
                core_ir::RuntimeSymbolKind::RoleMethod
            } else {
                core_ir::RuntimeSymbolKind::Value
            };
            core_ir::RuntimeSymbol {
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
            symbols.push(core_ir::RuntimeSymbol {
                path: exported,
                kind: core_ir::RuntimeSymbolKind::RoleMethod,
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

pub(crate) fn export_principal_binding(
    state: &LowerState,
    path: &Path,
    def: DefId,
) -> Option<core_ir::PrincipalBinding> {
    let body = state.principal_bodies.get(&def)?;
    if let Some(scheme) = state.runtime_export_schemes.get(&def) {
        let relevant_vars = collect_runtime_scheme_body_type_vars(scheme);
        return Some(core_ir::PrincipalBinding {
            name: export_path(path),
            scheme: scheme.clone(),
            body: export_expr(state, body, relevant_vars),
        });
    }
    let frozen_scheme = state.infer.frozen_schemes.borrow().get(&def).cloned();
    let (scheme, relevant_vars) = if let Some(scheme) = state.compact_scheme_of(def) {
        let relevant_vars = export_scheme_body_type_vars(&scheme);
        if should_prefer_frozen_runtime_scheme(path, &relevant_vars) {
            if let Some(frozen) = frozen_scheme.as_ref() {
                (
                    export_frozen_scheme(&state.infer, frozen),
                    export_frozen_scheme_body_type_vars(&state.infer, frozen),
                )
            } else {
                let constraints = state.infer.compact_role_constraints_of(def);
                (
                    export_scheme(&state.infer, &scheme, &constraints),
                    relevant_vars,
                )
            }
        } else {
            let constraints = state.infer.compact_role_constraints_of(def);
            (
                export_scheme(&state.infer, &scheme, &constraints),
                relevant_vars,
            )
        }
    } else {
        if let Some(frozen) = frozen_scheme.as_ref() {
            (
                export_frozen_scheme(&state.infer, frozen),
                export_frozen_scheme_body_type_vars(&state.infer, frozen),
            )
        } else {
            let fallback_scheme = state
                .def_tvs
                .get(&def)
                .copied()
                .map(|tv| coalesce_by_co_occurrence(&compact_type_var(&state.infer, tv)));
            let fallback_body = fallback_scheme
                .as_ref()
                .map(export_scheme_body)
                .unwrap_or(core_ir::Type::Any);
            let relevant_vars = fallback_scheme
                .as_ref()
                .map(export_scheme_body_type_vars)
                .unwrap_or_default();
            (
                core_ir::Scheme {
                    requirements: Vec::new(),
                    body: fallback_body,
                },
                relevant_vars,
            )
        }
    };
    Some(core_ir::PrincipalBinding {
        name: export_path(path),
        scheme,
        body: export_expr(state, body, relevant_vars),
    })
}

fn collect_runtime_scheme_body_type_vars(scheme: &core_ir::Scheme) -> BTreeSet<core_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&scheme.body, &mut vars);
    vars
}

fn should_prefer_frozen_runtime_scheme(
    path: &Path,
    relevant_vars: &BTreeSet<core_ir::TypeVar>,
) -> bool {
    !relevant_vars.is_empty()
        && path
            .segments
            .first()
            .map(|segment| segment.0.starts_with("&impl#"))
            .unwrap_or(false)
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
        ExprKind::PolyVariant(_, payloads) => {
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

fn export_root_exprs(state: &LowerState) -> Vec<core_ir::Expr> {
    let owner_roots = export_owner_root_exprs(state);
    if !owner_roots.is_empty() {
        return owner_roots;
    }

    let mut exporter = super::expr::ExprExporter::new(state, BTreeSet::new());
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

fn export_owner_root_exprs(state: &LowerState) -> Vec<core_ir::Expr> {
    let mut roots = Vec::new();
    for owner in &state.top_level_expr_owners {
        let Some(body) = state.principal_bodies.get(owner) else {
            continue;
        };
        let mut exporter = super::expr::ExprExporter::new(state, BTreeSet::new());
        roots.push(exporter.export_expr(body));
    }
    roots
}

fn collect_export_method_defs(state: &LowerState, expr: &TypedExpr) -> Vec<DefId> {
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

fn export_root_expr_nodes(state: &LowerState) -> Vec<core_ir::ExprGraphNode> {
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
                nodes.push(core_ir::ExprGraphNode {
                    owner: core_ir::GraphOwner::RootExpr(nodes.len()),
                    bounds: export_relevant_type_bounds_for_tv(
                        &state.infer,
                        expr.tv,
                        &BTreeSet::new(),
                    ),
                });
            }
        }
        if let Some(tail) = &block.tail {
            nodes.push(core_ir::ExprGraphNode {
                owner: core_ir::GraphOwner::RootExpr(nodes.len()),
                bounds: export_relevant_type_bounds_for_tv(&state.infer, tail.tv, &BTreeSet::new()),
            });
        }
    }
    nodes
}

fn export_owner_root_expr_nodes(state: &LowerState) -> Vec<core_ir::ExprGraphNode> {
    let mut nodes = Vec::new();
    for owner in &state.top_level_expr_owners {
        let tv = match state.principal_bodies.get(owner) {
            Some(body) => body.tv,
            None => match state.def_tvs.get(owner) {
                Some(&tv) => tv,
                None => continue,
            },
        };
        nodes.push(core_ir::ExprGraphNode {
            owner: core_ir::GraphOwner::RootExpr(nodes.len()),
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
    use yulang_core_ir as core_ir;
    use yulang_parser::sink::YulangLanguage;
    use yulang_source::SourceOptions;

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
                && symbol.kind == core_ir::RuntimeSymbolKind::EffectOperation
        }));
        assert!(program.graph.runtime_symbols.iter().any(|symbol| {
            path_segments(&symbol.path) == vec!["Add", "add"]
                && symbol.kind == core_ir::RuntimeSymbolKind::RoleMethod
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

    fn path_segments(path: &core_ir::Path) -> Vec<&str> {
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
            vec![core_ir::Name("Display".to_string())]
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
            core_ir::Type::Named {
                path: core_ir::Path::new(vec![
                    core_ir::Name("std".to_string()),
                    core_ir::Name("str".to_string()),
                    core_ir::Name("str".to_string()),
                ]),
                args: Vec::new(),
            }
        );
        match &shown.body {
            core_ir::Expr::Apply { callee, arg, .. } => {
                assert_eq!(arg.as_ref(), &core_ir::Expr::Lit(core_ir::Lit::Bool(true)));
                match callee.as_ref() {
                    core_ir::Expr::Apply { callee, arg, .. } => {
                        assert!(matches!(
                            arg.as_ref(),
                            core_ir::Expr::Lit(core_ir::Lit::Int(_))
                        ));
                        match callee.as_ref() {
                            core_ir::Expr::Var(path) => {
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
            core_ir::Expr::Apply { callee, arg, .. } => {
                assert_eq!(
                    arg.as_ref(),
                    &core_ir::Expr::Lit(core_ir::Lit::Int("2".to_string()))
                );
                match callee.as_ref() {
                    core_ir::Expr::Apply { callee, arg, .. } => {
                        assert_eq!(
                            arg.as_ref(),
                            &core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string()))
                        );
                        assert!(matches!(callee.as_ref(), core_ir::Expr::Var(_)));
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
            core_ir::Expr::Apply { callee, arg, .. } => {
                assert!(matches!(
                    arg.as_ref(),
                    core_ir::Expr::Lit(core_ir::Lit::Int(_))
                ));
                assert!(matches!(callee.as_ref(), core_ir::Expr::Var(_)));
            }
            other => panic!("expected concrete helper body, got {other:?}"),
        }
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
            core_ir::Expr::Lambda { param, body, .. } => {
                assert_eq!(param.0, "x");
                assert_eq!(
                    body.as_ref(),
                    &core_ir::Expr::Var(core_ir::Path::from_name(param.clone()))
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
            core_ir::Expr::Lambda { param, body, .. } => match body.as_ref() {
                core_ir::Expr::Block { stmts, tail } => {
                    assert_eq!(stmts.len(), 1);
                    match &stmts[0] {
                        core_ir::Stmt::Let { pattern, value } => {
                            assert_eq!(
                                value,
                                &core_ir::Expr::Var(core_ir::Path::from_name(param.clone()))
                            );
                            match pattern {
                                core_ir::Pattern::Record { fields, .. } => {
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
            core_ir::Expr::Apply { evidence, .. } => {
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
                    core_ir::TypeBounds::default(),
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
                core_ir::PrincipalRoot::Expr(0),
                core_ir::PrincipalRoot::Expr(1)
            ]
        );
        assert_eq!(
            module.root_exprs,
            vec![
                core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string())),
                core_ir::Expr::Lit(core_ir::Lit::Bool(true)),
            ]
        );
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
                core_ir::Type::Named {
                    path: core_ir::Path::from_name(core_ir::Name("int".to_string())),
                    args: Vec::new(),
                }
            );
            assert_eq!(module.roots, vec![core_ir::PrincipalRoot::Expr(0)]);
            assert_eq!(
                module.root_exprs,
                vec![core_ir::Expr::Var(core_ir::Path::from_name(core_ir::Name(
                    "write_var".to_string(),
                )))]
            );
        });
    }

    fn contains_named_int(ty: &core_ir::Type) -> bool {
        match ty {
            core_ir::Type::Named { path, .. } => {
                path.segments.last().map(|name| name.0.as_str()) == Some("int")
            }
            core_ir::Type::Fun {
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
            core_ir::Type::Tuple(items)
            | core_ir::Type::Union(items)
            | core_ir::Type::Inter(items)
            | core_ir::Type::Row { items, .. } => items.iter().any(contains_named_int),
            core_ir::Type::Record(record) => {
                record
                    .fields
                    .iter()
                    .any(|field| contains_named_int(&field.value))
                    || record.spread.as_ref().is_some_and(|spread| match spread {
                        core_ir::RecordSpread::Head(ty) | core_ir::RecordSpread::Tail(ty) => {
                            contains_named_int(ty)
                        }
                    })
            }
            core_ir::Type::Variant(variant) => {
                variant
                    .cases
                    .iter()
                    .any(|case| case.payloads.iter().any(contains_named_int))
                    || variant.tail.as_deref().is_some_and(contains_named_int)
            }
            core_ir::Type::Recursive { body, .. } => contains_named_int(body),
            core_ir::Type::Never | core_ir::Type::Any | core_ir::Type::Var(_) => false,
        }
    }

    fn concrete_coerce_evidence(evidence: &core_ir::CoerceEvidence) -> bool {
        (evidence.actual.lower.is_some() || evidence.actual.upper.is_some())
            && (evidence.expected.lower.is_some() || evidence.expected.upper.is_some())
    }

    fn find_coerce_evidence(
        expr: &core_ir::Expr,
        predicate: fn(&core_ir::CoerceEvidence) -> bool,
    ) -> Option<&core_ir::CoerceEvidence> {
        match expr {
            core_ir::Expr::Coerce { evidence, expr } => evidence
                .as_ref()
                .filter(|evidence| predicate(evidence))
                .or_else(|| find_coerce_evidence(expr.as_ref(), predicate)),
            core_ir::Expr::Lambda { body, .. } | core_ir::Expr::Pack { expr: body, .. } => {
                find_coerce_evidence(body, predicate)
            }
            core_ir::Expr::Apply { callee, arg, .. } => find_coerce_evidence(callee, predicate)
                .or_else(|| find_coerce_evidence(arg, predicate)),
            core_ir::Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => find_coerce_evidence(cond, predicate)
                .or_else(|| find_coerce_evidence(then_branch, predicate))
                .or_else(|| find_coerce_evidence(else_branch, predicate)),
            core_ir::Expr::Tuple(items) => items
                .iter()
                .find_map(|item| find_coerce_evidence(item, predicate)),
            core_ir::Expr::Record { fields, spread } => fields
                .iter()
                .find_map(|field| find_coerce_evidence(&field.value, predicate))
                .or_else(|| match spread {
                    Some(core_ir::RecordSpreadExpr::Head(expr))
                    | Some(core_ir::RecordSpreadExpr::Tail(expr)) => {
                        find_coerce_evidence(expr, predicate)
                    }
                    None => None,
                }),
            core_ir::Expr::Variant { value, .. } => value
                .as_deref()
                .and_then(|value| find_coerce_evidence(value, predicate)),
            core_ir::Expr::Select { base, .. } => find_coerce_evidence(base, predicate),
            core_ir::Expr::Match {
                scrutinee, arms, ..
            } => find_coerce_evidence(scrutinee, predicate).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(|guard| find_coerce_evidence(guard, predicate))
                        .or_else(|| find_coerce_evidence(&arm.body, predicate))
                })
            }),
            core_ir::Expr::Block { stmts, tail } => stmts
                .iter()
                .find_map(|stmt| match stmt {
                    core_ir::Stmt::Let { value, .. } | core_ir::Stmt::Expr(value) => {
                        find_coerce_evidence(value, predicate)
                    }
                    core_ir::Stmt::Module { body, .. } => find_coerce_evidence(body, predicate),
                })
                .or_else(|| {
                    tail.as_deref()
                        .and_then(|tail| find_coerce_evidence(tail, predicate))
                }),
            core_ir::Expr::Handle { body, arms, .. } => find_coerce_evidence(body, predicate)
                .or_else(|| {
                    arms.iter().find_map(|arm| {
                        arm.guard
                            .as_ref()
                            .and_then(|guard| find_coerce_evidence(guard, predicate))
                            .or_else(|| find_coerce_evidence(&arm.body, predicate))
                    })
                }),
            core_ir::Expr::Var(_) | core_ir::Expr::PrimitiveOp(_) | core_ir::Expr::Lit(_) => None,
        }
    }
}
