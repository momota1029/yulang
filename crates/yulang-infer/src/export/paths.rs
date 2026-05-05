use std::collections::{HashMap, HashSet};

use yulang_core_ir as core_ir;

use crate::diagnostic::ExpectedEdgeId;
use crate::ids::DefId;
use crate::lower::LowerState;
use crate::symbols::Path;

use super::complete_principal::ExpectedEdgeEvidence;
use super::names::export_path;
use super::principal::export_principal_binding;

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
    bindings: &mut Vec<core_ir::PrincipalBinding>,
    extra_exprs: &[core_ir::Expr],
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) {
    let all_paths = collect_canonical_binding_paths(state)
        .into_iter()
        .map(|(def, path)| (export_path(&path), (path, def)))
        .collect::<HashMap<_, _>>();
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
            let Some(binding) = export_principal_binding(state, &source_path, def, edge_evidence)
            else {
                continue;
            };
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

fn collect_expr_binding_refs(expr: &core_ir::Expr, out: &mut HashSet<core_ir::Path>) {
    match expr {
        core_ir::Expr::Var(path) => {
            out.insert(path.clone());
        }
        core_ir::Expr::PrimitiveOp(_) | core_ir::Expr::Lit(_) => {}
        core_ir::Expr::Lambda { body, .. }
        | core_ir::Expr::Coerce { expr: body, .. }
        | core_ir::Expr::Pack { expr: body, .. } => {
            collect_expr_binding_refs(body, out);
        }
        core_ir::Expr::Apply { callee, arg, .. } => {
            collect_expr_binding_refs(callee, out);
            collect_expr_binding_refs(arg, out);
        }
        core_ir::Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_binding_refs(cond, out);
            collect_expr_binding_refs(then_branch, out);
            collect_expr_binding_refs(else_branch, out);
        }
        core_ir::Expr::Tuple(items) => {
            for item in items {
                collect_expr_binding_refs(item, out);
            }
        }
        core_ir::Expr::Record { fields, spread } => {
            for field in fields {
                collect_expr_binding_refs(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    core_ir::RecordSpreadExpr::Head(expr)
                    | core_ir::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_binding_refs(expr, out);
                    }
                }
            }
        }
        core_ir::Expr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_binding_refs(value, out);
            }
        }
        core_ir::Expr::Select { base, .. } => collect_expr_binding_refs(base, out),
        core_ir::Expr::Match {
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
        core_ir::Expr::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    core_ir::Stmt::Let { value, .. } | core_ir::Stmt::Expr(value) => {
                        collect_expr_binding_refs(value, out);
                    }
                    core_ir::Stmt::Module { body, .. } => collect_expr_binding_refs(body, out),
                }
            }
            if let Some(tail) = tail {
                collect_expr_binding_refs(tail, out);
            }
        }
        core_ir::Expr::Handle { body, arms, .. } => {
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
