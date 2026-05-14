use std::collections::{HashMap, HashSet};
use std::time::Duration;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::time::Instant;

use yulang_typed_ir as typed_ir;

use crate::diagnostic::ExpectedEdgeId;
use crate::ids::{DefId, TypeVar};
use crate::lower::LowerState;
use crate::symbols::Path;

use super::apply_principal::CompletePrincipalCache;
use super::evidence::ExpectedEdgeEvidence;
use super::expr::ExprExportProfile;
use super::names::export_path;
use super::principal::export_principal_binding;

struct PathExportClock {
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    instant: Option<Instant>,
}

impl PathExportClock {
    fn now(enabled: bool) -> Self {
        Self {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            instant: enabled.then(Instant::now),
        }
    }

    fn elapsed(&self) -> Duration {
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        {
            return self
                .instant
                .map(|instant| instant.elapsed())
                .unwrap_or_default();
        }

        #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
        {
            Duration::ZERO
        }
    }
}

pub(crate) fn collect_canonical_binding_paths(state: &LowerState) -> HashMap<DefId, Path> {
    let mut canonical = state.ctx.canonical_value_paths();
    let defined_defs = canonical.keys().copied().collect::<HashSet<_>>();
    for (path, def) in state.ctx.collect_all_binding_paths() {
        if defined_defs.contains(&def) {
            continue;
        }
        match canonical.get_mut(&def) {
            Some(current) => choose_preferred_binding_path(current, path),
            None => {
                canonical.insert(def, path);
            }
        }
    }
    canonical
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
        let pending = std::mem::take(&mut pending_refs);
        let mut changed = false;
        for path in pending {
            if exported.contains(&path) {
                continue;
            }
            let Some((source_path, def)) = all_paths.get(&path).cloned() else {
                continue;
            };
            let started = PathExportClock::now(export_timing);
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

fn format_core_path_for_export_timing(path: &typed_ir::Path) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn choose_preferred_binding_path(current: &mut Path, candidate: Path) {
    let candidate_key = binding_path_preference_key(&candidate);
    let current_key = binding_path_preference_key(current);
    if candidate_key < current_key {
        *current = candidate;
    }
}

fn binding_path_preference_key(path: &Path) -> (usize, Vec<&str>) {
    let priority = path
        .segments
        .iter()
        .position(|segment| segment.0.starts_with('&') || segment.0.starts_with('#'))
        .unwrap_or(usize::MAX);
    let lexical = path
        .segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>();
    (priority, lexical)
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
