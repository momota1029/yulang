use std::collections::{BTreeSet, HashMap, HashSet};

use yulang_typed_ir as typed_ir;

use crate::diagnostic::ExpectedEdgeId;
use crate::ids::{DefId, TypeVar};
use crate::lower::LowerState;
use crate::simplify::compact::compact_type_var;
use crate::simplify::cooccur::coalesce_by_co_occurrence;
use crate::symbols::Path;

use super::apply_principal::CompletePrincipalCache;
use super::evidence::ExpectedEdgeEvidence;
use super::expr::{ExprExportProfile, ExprExporter};
use super::names::{export_path, path_key};
use super::paths::collect_canonical_binding_paths;
use super::timing::{ExportClock, format_core_path_for_export_timing};
use super::types::{
    collect_core_type_vars, export_frozen_scheme, export_frozen_scheme_body_type_vars,
    export_scheme, export_scheme_body, export_scheme_body_type_vars,
};

pub(super) fn export_bindings_for_paths(
    state: &mut LowerState,
    paths: &[(Path, DefId)],
    extra_exprs: &[typed_ir::Expr],
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> Vec<typed_ir::PrincipalBinding> {
    let export_timing = std::env::var_os("YULANG_EXPORT_TIMING").is_some();
    let t_canonical = ExportClock::now(export_timing);
    let canonical = collect_canonical_binding_paths(state);
    if export_timing {
        eprintln!(
            "  export: bindings.canonical_paths={:.3}ms count={}",
            t_canonical.elapsed().as_secs_f64() * 1000.0,
            canonical.len()
        );
    }
    let globals = canonical.clone();
    let mut principal_scheme_cache = HashMap::new();
    let mut base_bounds_cache = HashMap::new();
    let mut complete_principal_cache = CompletePrincipalCache::default();
    let target_def_set = paths.iter().map(|(_, def)| *def).collect::<HashSet<_>>();
    let t_initial = ExportClock::now(export_timing);
    let mut binding_times = Vec::new();
    let mut bindings = Vec::new();
    let mut canonical_items = canonical.into_iter().collect::<Vec<_>>();
    canonical_items.sort_by_key(|(_, path)| path_key(path));
    for (def, path) in canonical_items {
        if !target_def_set.contains(&def) {
            continue;
        }
        let t_binding = ExportClock::now(export_timing);
        let mut expr_profile = export_timing.then(ExprExportProfile::default);
        if let Some(binding) = export_principal_binding(
            state,
            &globals,
            &mut principal_scheme_cache,
            &mut base_bounds_cache,
            &mut complete_principal_cache,
            expr_profile.as_mut(),
            &path,
            def,
            edge_evidence,
        ) {
            if export_timing {
                binding_times.push((binding.name.clone(), t_binding.elapsed(), expr_profile));
            }
            bindings.push(binding);
        }
    }
    if export_timing {
        eprintln!(
            "  export: bindings.initial={:.3}ms count={}",
            t_initial.elapsed().as_secs_f64() * 1000.0,
            bindings.len()
        );
        binding_times.sort_by(|(_, left, _), (_, right, _)| right.cmp(left));
        for (path, duration, profile) in binding_times.into_iter().take(12) {
            eprintln!(
                "    export binding {}={:.3}ms",
                format_core_path_for_export_timing(&path),
                duration.as_secs_f64() * 1000.0
            );
            if let Some(profile) = profile {
                eprintln!(
                    "      exprs={}, applies={}, bounds_misses={}, bounds={:.3}ms, coalesced_apply_bounds={:.3}ms, principal_scheme={:.3}ms (direct={:.3}ms, residual={:.3}ms), principal_evidence={:.3}ms (subs={:.3}ms [slots={:.3}ms, export={:.3}ms, roles={:.3}ms, emit={:.3}ms], candidates={:.3}ms), principal_plan={:.3}ms",
                    profile.exprs,
                    profile.applies,
                    profile.bounds_misses,
                    profile.bounds.as_secs_f64() * 1000.0,
                    profile.coalesced_apply_bounds.as_secs_f64() * 1000.0,
                    profile.principal_scheme.as_secs_f64() * 1000.0,
                    profile.principal_scheme_direct.as_secs_f64() * 1000.0,
                    profile.principal_scheme_residual.as_secs_f64() * 1000.0,
                    profile.principal_evidence.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitutions.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_slots.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_export.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_roles.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_emit.as_secs_f64() * 1000.0,
                    profile.principal_evidence_candidates.as_secs_f64() * 1000.0,
                    profile.principal_plan.as_secs_f64() * 1000.0,
                );
            }
        }
    }
    let t_closure = ExportClock::now(export_timing);
    complete_referenced_binding_closure(
        state,
        &globals,
        &mut principal_scheme_cache,
        &mut base_bounds_cache,
        &mut complete_principal_cache,
        &mut bindings,
        extra_exprs,
        edge_evidence,
    );
    if export_timing {
        eprintln!(
            "  export: bindings.referenced_closure={:.3}ms count={}",
            t_closure.elapsed().as_secs_f64() * 1000.0,
            bindings.len()
        );
    }
    let t_sort = ExportClock::now(export_timing);
    bindings.sort_by(|lhs, rhs| lhs.name.segments.cmp(&rhs.name.segments));
    if export_timing {
        eprintln!(
            "  export: bindings.sort={:.3}ms",
            t_sort.elapsed().as_secs_f64() * 1000.0
        );
    }
    let t_dedup = ExportClock::now(export_timing);
    dedup_bindings_by_runtime_path(&mut bindings);
    if export_timing {
        eprintln!(
            "  export: bindings.dedup={:.3}ms count={}",
            t_dedup.elapsed().as_secs_f64() * 1000.0,
            bindings.len()
        );
    }
    bindings
}

fn dedup_bindings_by_runtime_path(bindings: &mut Vec<typed_ir::PrincipalBinding>) {
    let mut deduped: Vec<typed_ir::PrincipalBinding> = Vec::with_capacity(bindings.len());
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

fn binding_generality_score(binding: &typed_ir::PrincipalBinding) -> usize {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&binding.scheme.body, &mut vars);
    for requirement in &binding.scheme.requirements {
        for arg in &requirement.args {
            match arg {
                typed_ir::RoleRequirementArg::Input(bounds)
                | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    collect_bounds_vars(bounds, &mut vars);
                }
            }
        }
    }
    vars.len()
}

fn collect_bounds_vars(bounds: &typed_ir::TypeBounds, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    if let Some(lower) = bounds.lower.as_deref() {
        collect_core_type_vars(lower, vars);
    }
    if let Some(upper) = bounds.upper.as_deref() {
        collect_core_type_vars(upper, vars);
    }
}
pub(crate) fn complete_referenced_binding_closure(
    state: &mut LowerState,
    globals: &HashMap<DefId, Path>,
    principal_scheme_cache: &mut HashMap<DefId, Option<typed_ir::Scheme>>,
    base_bounds_cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
    complete_principal_cache: &mut CompletePrincipalCache,
    bindings: &mut Vec<typed_ir::PrincipalBinding>,
    extra_exprs: &[typed_ir::Expr],
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) {
    let export_timing = std::env::var_os("YULANG_EXPORT_TIMING").is_some();
    let all_paths = globals
        .iter()
        .map(|(def, path)| (export_path(path), (path.clone(), *def)))
        .collect::<HashMap<_, _>>();
    let mut binding_times = Vec::new();
    let mut exported = bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    let mut pending_refs = HashSet::new();
    for expr in extra_exprs {
        collect_expr_binding_refs(expr, &mut pending_refs);
    }
    for binding in bindings.iter() {
        collect_expr_binding_refs(&binding.body, &mut pending_refs);
    }
    while !pending_refs.is_empty() {
        let mut pending = std::mem::take(&mut pending_refs)
            .into_iter()
            .collect::<Vec<_>>();
        pending.sort_by_key(format_core_path_for_export_timing);
        let mut changed = false;
        for path in pending {
            if exported.contains(&path) {
                continue;
            }
            let Some((source_path, def)) = all_paths.get(&path).cloned() else {
                continue;
            };
            let started = ExportClock::now(export_timing);
            let mut expr_profile = export_timing.then(ExprExportProfile::default);
            let Some(binding) = export_principal_binding(
                state,
                globals,
                principal_scheme_cache,
                base_bounds_cache,
                complete_principal_cache,
                expr_profile.as_mut(),
                &source_path,
                def,
                edge_evidence,
            ) else {
                continue;
            };
            if export_timing {
                binding_times.push((binding.name.clone(), started.elapsed(), expr_profile));
            }
            if exported.insert(binding.name.clone()) {
                collect_expr_binding_refs(&binding.body, &mut pending_refs);
                bindings.push(binding);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    if export_timing {
        binding_times.sort_by(|(_, left, _), (_, right, _)| right.cmp(left));
        for (path, duration, profile) in binding_times.into_iter().take(12) {
            eprintln!(
                "    export closure binding {}={:.3}ms",
                format_core_path_for_export_timing(&path),
                duration.as_secs_f64() * 1000.0
            );
            if let Some(profile) = profile {
                eprintln!(
                    "      exprs={}, applies={}, bounds_misses={}, bounds={:.3}ms, coalesced_apply_bounds={:.3}ms, principal_scheme={:.3}ms (direct={:.3}ms, residual={:.3}ms), principal_evidence={:.3}ms (subs={:.3}ms [slots={:.3}ms, export={:.3}ms, roles={:.3}ms, emit={:.3}ms], candidates={:.3}ms), principal_plan={:.3}ms",
                    profile.exprs,
                    profile.applies,
                    profile.bounds_misses,
                    profile.bounds.as_secs_f64() * 1000.0,
                    profile.coalesced_apply_bounds.as_secs_f64() * 1000.0,
                    profile.principal_scheme.as_secs_f64() * 1000.0,
                    profile.principal_scheme_direct.as_secs_f64() * 1000.0,
                    profile.principal_scheme_residual.as_secs_f64() * 1000.0,
                    profile.principal_evidence.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitutions.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_slots.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_export.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_roles.as_secs_f64() * 1000.0,
                    profile.principal_evidence_substitution_emit.as_secs_f64() * 1000.0,
                    profile.principal_evidence_candidates.as_secs_f64() * 1000.0,
                    profile.principal_plan.as_secs_f64() * 1000.0,
                );
            }
        }
    }
}
fn collect_expr_binding_refs(expr: &typed_ir::Expr, out: &mut HashSet<typed_ir::Path>) {
    match expr {
        typed_ir::Expr::Var(path) => {
            out.insert(path.clone());
        }
        typed_ir::Expr::PrimitiveOp(_) | typed_ir::Expr::Lit(_) => {}
        typed_ir::Expr::Lambda { body, .. }
        | typed_ir::Expr::Coerce { expr: body, .. }
        | typed_ir::Expr::BindHere { expr: body }
        | typed_ir::Expr::Pack { expr: body, .. } => {
            collect_expr_binding_refs(body, out);
        }
        typed_ir::Expr::Apply { callee, arg, .. } => {
            collect_expr_binding_refs(callee, out);
            collect_expr_binding_refs(arg, out);
        }
        typed_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_binding_refs(cond, out);
            collect_expr_binding_refs(then_branch, out);
            collect_expr_binding_refs(else_branch, out);
        }
        typed_ir::Expr::Tuple(items) => {
            for item in items {
                collect_expr_binding_refs(item, out);
            }
        }
        typed_ir::Expr::Record { fields, spread } => {
            for field in fields {
                collect_expr_binding_refs(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    typed_ir::RecordSpreadExpr::Head(expr)
                    | typed_ir::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_binding_refs(expr, out);
                    }
                }
            }
        }
        typed_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_binding_refs(value, out);
            }
        }
        typed_ir::Expr::Select { base, .. } => collect_expr_binding_refs(base, out),
        typed_ir::Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_binding_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_binding_refs(guard, out);
                }
                collect_expr_binding_refs(&arm.body, out);
            }
        }
        typed_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    typed_ir::Stmt::Let { value, .. } | typed_ir::Stmt::Expr(value) => {
                        collect_expr_binding_refs(value, out);
                    }
                    typed_ir::Stmt::Module { body, .. } => collect_expr_binding_refs(body, out),
                }
            }
            if let Some(tail) = tail {
                collect_expr_binding_refs(tail, out);
            }
        }
        typed_ir::Expr::Handle { body, arms, .. } => {
            collect_expr_binding_refs(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_binding_refs(guard, out);
                }
                collect_expr_binding_refs(&arm.body, out);
            }
        }
    }
}
pub(crate) fn export_principal_binding(
    state: &LowerState,
    globals: &HashMap<DefId, Path>,
    principal_scheme_cache: &mut HashMap<DefId, Option<typed_ir::Scheme>>,
    base_bounds_cache: &mut HashMap<TypeVar, typed_ir::TypeBounds>,
    complete_principal_cache: &mut CompletePrincipalCache,
    profile: Option<&mut ExprExportProfile>,
    path: &Path,
    def: DefId,
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> Option<typed_ir::PrincipalBinding> {
    let body = state.principal_bodies.get(&def)?;
    let mut profile = profile;
    if let Some(scheme) = state.runtime_export_schemes.get(&def) {
        let relevant_vars = collect_runtime_scheme_body_type_vars(scheme);
        let body = ExprExporter::new(
            state,
            globals,
            principal_scheme_cache,
            base_bounds_cache,
            complete_principal_cache,
            profile.as_deref_mut(),
            relevant_vars,
            edge_evidence,
        )
        .export_expr(body);
        return Some(typed_ir::PrincipalBinding {
            name: export_path(path),
            scheme: scheme.clone(),
            body,
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
                .unwrap_or(typed_ir::Type::Unknown);
            let relevant_vars = fallback_scheme
                .as_ref()
                .map(export_scheme_body_type_vars)
                .unwrap_or_default();
            (
                typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: fallback_body,
                },
                relevant_vars,
            )
        }
    };
    let body = ExprExporter::new(
        state,
        globals,
        principal_scheme_cache,
        base_bounds_cache,
        complete_principal_cache,
        profile.as_deref_mut(),
        relevant_vars,
        edge_evidence,
    )
    .export_expr(body);
    Some(typed_ir::PrincipalBinding {
        name: export_path(path),
        scheme,
        body,
    })
}

fn collect_runtime_scheme_body_type_vars(scheme: &typed_ir::Scheme) -> BTreeSet<typed_ir::TypeVar> {
    let mut vars = BTreeSet::new();
    collect_core_type_vars(&scheme.body, &mut vars);
    vars
}

fn should_prefer_frozen_runtime_scheme(
    path: &Path,
    relevant_vars: &BTreeSet<typed_ir::TypeVar>,
) -> bool {
    !relevant_vars.is_empty()
        && path
            .segments
            .first()
            .map(|segment| segment.0.starts_with("&impl#"))
            .unwrap_or(false)
}
