use crate::ast::expr::{ExprKind, TypedExpr};
use crate::ids::DefId;
use crate::lower::LowerState;

use super::spine::{collect_apply_spine, strip_transparent_wrappers};

pub(crate) fn canonical_runtime_export_def(state: &LowerState, def: DefId) -> DefId {
    let mut current = def;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let Some(next) = trivial_forward_target_def(state, current) else {
            break;
        };
        current = next;
    }
    current
}

fn trivial_forward_target_def(state: &LowerState, def: DefId) -> Option<DefId> {
    let body = state.principal_bodies.get(&def)?;
    let (params, body) = collect_lam_spine(body);
    if params.is_empty() {
        return None;
    }
    let (head, args) = collect_apply_spine(strip_transparent_wrappers(body));
    let target = match &head.kind {
        ExprKind::Var(def) => *def,
        _ => return None,
    };
    if args.len() != params.len() {
        return None;
    }
    let args_match = params
        .iter()
        .zip(args.iter())
        .all(|(param, arg)| matches!(&strip_transparent_wrappers(arg).kind, ExprKind::Var(def) if def == param));
    args_match.then_some(target)
}

fn collect_lam_spine<'a>(expr: &'a TypedExpr) -> (Vec<DefId>, &'a TypedExpr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let ExprKind::Lam(def, body) = &current.kind {
        params.push(*def);
        current = body;
    }
    (params, current)
}
