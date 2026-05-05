use crate::profile::ProfileClock as Instant;
use std::collections::HashSet;
use std::sync::OnceLock;

use crate::ast::expr::{ExprKind, Lit, TypedExpr};
use crate::lower::LowerState;
use crate::symbols::{Name, OperatorFixity, Path};
use crate::types::{Neg, Pos};

use super::prim_type;

// ── パス解決 ──────────────────────────────────────────────────────────────────

/// パスセグメントの列を名前解決して TypedExpr を生成する。
///
/// 解決できた場合: `def_tv <: tv`（定義の型が使用箇所に流れ込む）
/// 変数参照自体は純粋（副作用なし）なので `[] <: eff`
pub(in crate::lower) fn resolve_path_expr(state: &mut LowerState, segs: Vec<Name>) -> TypedExpr {
    let start = Instant::now();
    let path = Path { segments: segs };

    if let [Name(name)] = path.segments.as_slice() {
        if name == "true" || name == "false" {
            let tv = state.fresh_tv();
            let eff = state.fresh_exact_pure_eff_tv();
            state.infer.constrain(prim_type("bool"), Neg::Var(tv));
            let result = TypedExpr {
                tv,
                eff,
                kind: ExprKind::Lit(Lit::Bool(name == "true")),
            };
            state.lower_detail.resolve_path_expr += start.elapsed();
            return result;
        }
    }

    if path.segments.is_empty() {
        let tv = state.fresh_tv();
        let eff = state.fresh_exact_pure_eff_tv();
        let result = TypedExpr {
            tv,
            eff,
            kind: ExprKind::Lit(Lit::Unit),
        };
        state.lower_detail.resolve_path_expr += start.elapsed();
        return result;
    }

    let def = if path.segments.len() == 1 {
        state.ctx.resolve_value(&path.segments[0])
    } else {
        state.ctx.resolve_path_value(&path)
    };

    if let Some(def) = def {
        let result = resolve_bound_def_expr(state, def);
        state.lower_detail.resolve_path_expr += start.elapsed();
        return result;
    }

    // 解決できなかった → 未解決参照として記録
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let ref_id = state.ctx.fresh_ref();
    state.ctx.refs.push_unresolved(
        ref_id,
        crate::ref_table::UnresolvedRef {
            path,
            module: state.ctx.current_module,
            use_paths: state.ctx.current_use_paths(),
            ref_tv: tv,
            owner: state.current_owner,
        },
    );
    let result = TypedExpr {
        tv,
        eff,
        kind: ExprKind::Ref(ref_id),
    };
    state.lower_detail.resolve_path_expr += start.elapsed();
    result
}

fn alias_same_owner_ref_expr(state: &mut LowerState, def: crate::ids::DefId) -> Option<TypedExpr> {
    if !can_alias_direct_ref(state, def) {
        return None;
    }

    let tv = state.def_tvs.get(&def).copied()?;
    let eff = if let Some(&eff_tv) = state.def_eff_tvs.get(&def) {
        eff_tv
    } else {
        state.fresh_exact_pure_eff_tv()
    };

    Some(TypedExpr {
        tv,
        eff,
        kind: ExprKind::Var(def),
    })
}

pub(super) fn resolve_operator_expr(
    state: &mut LowerState,
    name: Name,
    fixity: OperatorFixity,
) -> TypedExpr {
    if let Some(expr) = try_resolve_operator_expr(state, &name, fixity) {
        return expr;
    }

    let path = Path {
        segments: vec![name],
    };
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let ref_id = state.ctx.fresh_ref();
    state.ctx.refs.push_unresolved(
        ref_id,
        crate::ref_table::UnresolvedRef {
            path,
            module: state.ctx.current_module,
            use_paths: state.ctx.current_use_paths(),
            ref_tv: tv,
            owner: state.current_owner,
        },
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Ref(ref_id),
    }
}

pub(crate) fn try_resolve_operator_expr(
    state: &mut LowerState,
    name: &Name,
    fixity: OperatorFixity,
) -> Option<TypedExpr> {
    state
        .ctx
        .resolve_operator_value(name, fixity)
        .map(|def| resolve_bound_def_expr(state, def))
}

pub(crate) fn try_resolve_local_operator_expr(
    state: &mut LowerState,
    name: &Name,
    fixity: OperatorFixity,
) -> Option<TypedExpr> {
    state
        .ctx
        .resolve_local_operator_value(name, fixity)
        .map(|def| resolve_bound_def_expr(state, def))
}

pub(in crate::lower::expr) fn resolve_bound_def_expr(
    state: &mut LowerState,
    def: crate::ids::DefId,
) -> TypedExpr {
    let debug_ref = debug_ref_enabled();
    if debug_ref {
        eprintln!(
            "-- resolve_bound_def_expr {:?} name={:?} owner={:?} def_owner={:?} frozen={} def_eff={} let_bound={}",
            def,
            state.def_names.get(&def),
            state.current_owner,
            state.def_owner(def),
            state.infer.frozen_schemes.borrow().contains_key(&def),
            state.def_eff_tvs.contains_key(&def),
            state.is_let_bound_def(def),
        );
    }
    if let (Some(owner), Some(def_owner)) = (state.current_owner, state.def_owner(def)) {
        if owner != def_owner {
            if let Some(&def_tv) = state.def_tvs.get(&def) {
                state.infer.add_non_generic_var(owner, def_tv);
            }
        }
    }
    if state.current_owner == Some(def) {
        if let Some(scheme) = state.provisional_self_schemes.get(&def).cloned() {
            state.mark_recursive_self_use(def);
            let tv = state.fresh_tv();
            let eff = state
                .def_eff_tvs
                .get(&def)
                .copied()
                .unwrap_or_else(|| state.fresh_exact_pure_eff_tv());
            crate::scheme::instantiate_frozen_scheme_with_subst(&state.infer, &scheme, tv, &[]);
            if let Some(&def_tv) = state.def_tvs.get(&def) {
                state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
                state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
            }
            let ref_id = state.ctx.fresh_ref();
            state.ctx.refs.resolve(ref_id, def, tv, state.current_owner);
            state.mark_resolved_ref_instantiated(ref_id);
            return TypedExpr {
                tv,
                eff,
                kind: ExprKind::Var(def),
            };
        }
    }
    if let Some(expr) = alias_same_owner_ref_expr(state, def) {
        return expr;
    }
    let tv = state.fresh_tv();
    let eff = state
        .def_eff_tvs
        .get(&def)
        .copied()
        .unwrap_or_else(|| state.fresh_exact_pure_eff_tv());
    if let (Some(owner), Some(def_owner)) = (state.current_owner, state.def_owner(def)) {
        if owner != def_owner {
            state.infer.add_non_generic_var(owner, tv);
        }
    }
    if state.def_eff_tvs.contains_key(&def) {
        if let Some(&def_tv) = state.def_tvs.get(&def) {
            state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
            state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
        }
    } else if let Some(scheme) = state.infer.frozen_schemes.borrow().get(&def) {
        let subst =
            crate::scheme::instantiate_frozen_scheme_with_subst(&state.infer, &scheme, tv, &[]);
        if debug_ref {
            eprintln!(
                "  instantiated frozen scheme {:?} -> tv {:?} lowers {:?} uppers {:?}",
                crate::display::dump::format_compact_scheme(&scheme.compact),
                tv,
                state.infer.lowers_of(tv),
                state.infer.uppers_of(tv)
            );
        }
        if let Some(owner) = state.current_owner {
            state
                .infer
                .instantiate_role_constraints_for_owner_with_scheme(
                    def,
                    owner,
                    &subst,
                    Some(scheme),
                );
        }
    } else if let Some(&def_tv) = state.def_tvs.get(&def) {
        if state.current_owner != Some(def)
            && state.is_let_bound_def(def)
            && principal_body_is_lambda_value(state, def)
        {
            if debug_ref {
                eprintln!(
                    "  before refresh deferred={} role_constraints={:?}",
                    state.infer.deferred_selections.borrow().len(),
                    state.infer.role_constraints_of(def),
                );
            }
            state.refresh_selection_environment();
            if debug_ref {
                eprintln!(
                    "  after refresh deferred={} role_constraints={:?}",
                    state.infer.deferred_selections.borrow().len(),
                    state.infer.role_constraints_of(def),
                );
            }
            let finalized_defs = HashSet::from([def]);
            state.finalize_compact_results_for_defs(&finalized_defs);
            let non_generic = state.infer.non_generic_vars_of(def);
            let compact_frozen = state.compact_scheme_of(def).map(|compact| {
                let compact_constraints = state.infer.compact_role_constraints_of(def);
                let extra_quantified =
                    crate::scheme::collect_compact_role_constraint_free_vars(&compact_constraints);
                crate::scheme::freeze_compact_scheme_with_non_generic_and_extra_vars(
                    &state.infer,
                    &compact,
                    extra_quantified.as_slice(),
                    &non_generic,
                )
            });
            let frozen = if !non_generic.is_empty() && !state.is_recursive_binding(def) {
                if let Some(frozen) = compact_frozen
                    .clone()
                    .filter(|frozen| !frozen_fun_has_empty_result(frozen))
                {
                    frozen
                } else if let Some(fun) = principal_body_fun_lower_pos_id(state, def) {
                    crate::scheme::freeze_pos_scheme_with_non_generic(
                        &state.infer,
                        fun,
                        &non_generic,
                    )
                } else {
                    crate::scheme::freeze_type_var_with_non_generic(
                        &state.infer,
                        def_tv,
                        &non_generic,
                    )
                }
            } else if let Some(frozen) = compact_frozen {
                frozen
            } else {
                crate::scheme::freeze_type_var_with_non_generic(&state.infer, def_tv, &non_generic)
            };
            let subst =
                crate::scheme::instantiate_frozen_scheme_with_subst(&state.infer, &frozen, tv, &[]);
            if debug_ref {
                eprintln!(
                    "  on-demand frozen scheme {:?} -> tv {:?} lowers {:?} uppers {:?}",
                    crate::display::dump::format_compact_scheme(&frozen.compact),
                    tv,
                    state.infer.lowers_of(tv),
                    state.infer.uppers_of(tv)
                );
            }
            if let Some(owner) = state.current_owner {
                state
                    .infer
                    .instantiate_role_constraints_for_owner_with_scheme(
                        def,
                        owner,
                        &subst,
                        Some(&frozen),
                    );
            }
        } else if state.is_let_bound_def(def) && state.current_owner != Some(def) {
            if let Some(owner) = state.current_owner {
                state.infer.add_edge(owner, def);
                state
                    .infer
                    .instantiate_role_constraints_for_owner(def, owner, &[]);
                state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
                state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
            } else {
                state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
                state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
            }
        } else {
            state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
            state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
        }
    }
    let ref_id = state.ctx.fresh_ref();
    state.ctx.refs.resolve(ref_id, def, tv, state.current_owner);
    state.mark_resolved_ref_instantiated(ref_id);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Var(def),
    }
}

fn debug_ref_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_DEBUG_REF").is_some())
}

fn can_alias_direct_ref(state: &LowerState, def: crate::ids::DefId) -> bool {
    if !state.infer.role_constraints_of(def).is_empty() {
        return false;
    }

    if let Some(owner) = state.current_owner {
        let same_owner = def == owner || state.def_owner(def) == Some(owner);
        let aliasable_same_owner = def == owner || !state.is_let_bound_def(def);
        if same_owner && aliasable_same_owner {
            return match state.infer.frozen_schemes.borrow().get(&def) {
                Some(scheme) => scheme.quantified.is_empty(),
                None => true,
            };
        }
    }

    let ownerless_frozen_mono = state.current_owner.is_none()
        && !state.is_continuation_def(def)
        && state.def_owner(def).is_none()
        && state
            .infer
            .frozen_schemes
            .borrow()
            .get(&def)
            .map(|scheme| scheme.quantified.is_empty())
            .unwrap_or(false);

    ownerless_frozen_mono
}

fn principal_body_is_lambda_value(state: &LowerState, def: crate::ids::DefId) -> bool {
    let Some(mut body) = state.principal_bodies.get(&def) else {
        return false;
    };
    loop {
        match &body.kind {
            ExprKind::Coerce { expr, .. } | ExprKind::PackForall(_, expr) => {
                body = expr;
            }
            ExprKind::Lam(_, _) => return true,
            _ => return false,
        }
    }
}

fn principal_body_fun_lower_pos_id(
    state: &LowerState,
    def: crate::ids::DefId,
) -> Option<crate::ids::PosId> {
    let body = state.principal_bodies.get(&def)?;
    state
        .infer
        .lower_refs_of(body.tv)
        .into_iter()
        .filter(|pos| matches!(state.infer.arena.get_pos(*pos), Pos::Fun { .. }))
        .max_by_key(|pos| principal_fun_lower_score(state, *pos))
}

fn frozen_fun_has_empty_result(scheme: &crate::FrozenScheme) -> bool {
    let Pos::Fun { ret_eff, ret, .. } = scheme.arena.get_pos(scheme.body) else {
        return false;
    };
    matches!(scheme.arena.get_pos(ret_eff), Pos::Bot)
        || matches!(scheme.arena.get_pos(ret), Pos::Bot)
}

fn principal_fun_lower_score(state: &LowerState, pos: crate::ids::PosId) -> usize {
    let Pos::Fun { ret_eff, ret, .. } = state.infer.arena.get_pos(pos) else {
        return 0;
    };
    compact_live_pos_score(state, ret) * 2 + compact_live_pos_score(state, ret_eff)
}

fn compact_live_pos_score(state: &LowerState, pos: crate::ids::PosId) -> usize {
    match state.infer.arena.get_pos(pos) {
        Pos::Bot => 0,
        Pos::Var(tv) | Pos::Raw(tv) => {
            if state.infer.lower_refs_of(tv).is_empty() && state.infer.upper_refs_of(tv).is_empty()
            {
                0
            } else {
                1
            }
        }
        _ => 2,
    }
}
