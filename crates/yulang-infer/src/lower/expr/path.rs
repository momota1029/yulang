use crate::profile::ProfileClock as Instant;
use std::collections::HashSet;
use std::sync::OnceLock;

use crate::ast::expr::{ExprKind, Lit, TypedExpr};
use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::ids::DefId;
use crate::lower::LowerState;
use crate::symbols::{ModuleId, Name, OperatorFixity, Path};
use crate::types::{Neg, Pos};

use super::prim_type;

// ── パス解決 ──────────────────────────────────────────────────────────────────

/// パスセグメントの列を名前解決して TypedExpr を生成する。
///
/// 解決できた場合: `def_tv <: tv`（定義の型が使用箇所に流れ込む）
/// 変数参照自体は純粋（副作用なし）なので `[] <: eff`
pub(in crate::lower) fn resolve_path_expr(state: &mut LowerState, segs: Vec<Name>) -> TypedExpr {
    resolve_path_expr_at(state, segs, None)
}

pub(in crate::lower) fn resolve_path_expr_at(
    state: &mut LowerState,
    segs: Vec<Name>,
    span: Option<rowan::TextRange>,
) -> TypedExpr {
    resolve_path_expr_at_use_site(state, segs, span, ValueUseSite::Value)
}

pub(in crate::lower) fn resolve_path_callee_expr_at(
    state: &mut LowerState,
    segs: Vec<Name>,
    span: Option<rowan::TextRange>,
) -> TypedExpr {
    resolve_path_expr_at_use_site(state, segs, span, ValueUseSite::Callee)
}

fn resolve_path_expr_at_use_site(
    state: &mut LowerState,
    segs: Vec<Name>,
    span: Option<rowan::TextRange>,
    use_site: ValueUseSite,
) -> TypedExpr {
    let start = Instant::now();
    let path = Path { segments: segs };

    if let [Name(name)] = path.segments.as_slice() {
        if name == "true" || name == "false" {
            let tv = state.fresh_tv_with_origin(TypeOrigin {
                span,
                file_span: None,
                kind: TypeOriginKind::Literal,
                label: Some(name.clone()),
            });
            let eff = state.fresh_exact_pure_eff_tv();
            state.infer.constrain(prim_type("bool"), Neg::Var(tv));
            let result = TypedExpr {
                tv,
                eff,
                kind: ExprKind::Lit(Lit::Bool(name == "true")),
            };
            let elapsed = start.elapsed();
            state.lower_detail.resolve_path_expr += elapsed;
            state.lower_detail.resolve_path_expr_literal += elapsed;
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
        let elapsed = start.elapsed();
        state.lower_detail.resolve_path_expr += elapsed;
        state.lower_detail.resolve_path_expr_unit += elapsed;
        return result;
    }

    let single_segment = path.segments.len() == 1;
    match resolve_value_use(state, path, use_site) {
        ResolvedValueUse::Resolved(def) => {
            let result = resolve_bound_def_expr(state, def);
            if let Some(span) = span {
                state.record_value_use_span(span, def);
            }
            let elapsed = start.elapsed();
            state.lower_detail.resolve_path_expr += elapsed;
            if single_segment {
                state.lower_detail.resolve_path_expr_resolved_single += elapsed;
            } else {
                state.lower_detail.resolve_path_expr_resolved_path += elapsed;
            }
            result
        }
        ResolvedValueUse::Unresolved(unresolved) => {
            let result = unresolved_value_use_expr(state, unresolved, span);
            let elapsed = start.elapsed();
            state.lower_detail.resolve_path_expr += elapsed;
            if single_segment {
                state.lower_detail.resolve_path_expr_unresolved_single += elapsed;
            } else {
                state.lower_detail.resolve_path_expr_unresolved_path += elapsed;
            }
            result
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ValueUseSite {
    Value,
    Callee,
}

enum ResolvedValueUse {
    Resolved(DefId),
    Unresolved(UnresolvedValueUse),
}

struct UnresolvedValueUse {
    path: Path,
    module: ModuleId,
    use_paths: Vec<Path>,
    owner: Option<DefId>,
}

fn resolve_value_use(state: &LowerState, path: Path, use_site: ValueUseSite) -> ResolvedValueUse {
    let def = match use_site {
        ValueUseSite::Value => {
            if path.segments.len() == 1 {
                state.ctx.resolve_value(&path.segments[0])
            } else {
                state.ctx.resolve_path_value(&path)
            }
        }
        ValueUseSite::Callee => resolve_callee_value_use(state, &path),
    };

    if let Some(def) = def {
        return ResolvedValueUse::Resolved(def);
    }

    ResolvedValueUse::Unresolved(UnresolvedValueUse {
        path,
        module: state.ctx.current_module,
        use_paths: state.ctx.current_use_paths(),
        owner: state.current_owner,
    })
}

fn resolve_callee_value_use(state: &LowerState, path: &Path) -> Option<DefId> {
    let candidates = if path.segments.len() == 1 {
        state.ctx.resolve_value_candidates(&path.segments[0])
    } else {
        state.ctx.resolve_path_value_candidates(path)
    };
    if candidates.len() <= 1 {
        return candidates.into_iter().next();
    }

    let mut first = None;
    let mut earlier_are_non_callable = true;
    for def in candidates {
        first.get_or_insert(def);
        match value_call_shape(state, def) {
            ValueCallShape::Callable if earlier_are_non_callable => return Some(def),
            ValueCallShape::Callable | ValueCallShape::Unknown => earlier_are_non_callable = false,
            ValueCallShape::NonCallable => {}
        }
    }
    first
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ValueCallShape {
    Callable,
    NonCallable,
    Unknown,
}

fn value_call_shape(state: &LowerState, def: DefId) -> ValueCallShape {
    if state.is_callable_value_def(def) {
        return ValueCallShape::Callable;
    }
    if state.is_non_callable_value_def(def) {
        return ValueCallShape::NonCallable;
    }

    if let Some(body) = state.principal_bodies.get(&def) {
        if expr_is_lambda_value(body) || matches!(body.kind, ExprKind::PrimitiveOp(_)) {
            return ValueCallShape::Callable;
        }
    }

    let Some(&tv) = state.def_tvs.get(&def) else {
        return frozen_value_call_shape(state, def);
    };

    let lowers = state.infer.lowers_of(tv);
    let uppers = state.infer.uppers_of(tv);
    if lowers.iter().any(pos_is_fun) || uppers.iter().any(neg_is_fun) {
        return ValueCallShape::Callable;
    }
    if !lowers.is_empty()
        && !uppers.is_empty()
        && lowers.iter().all(pos_is_known_non_fun)
        && uppers.iter().all(neg_is_known_non_fun)
    {
        return ValueCallShape::NonCallable;
    }
    frozen_value_call_shape(state, def)
}

fn frozen_value_call_shape(state: &LowerState, def: DefId) -> ValueCallShape {
    if let Some(scheme) = state.infer.frozen_scheme_of(def) {
        if compact_type_has_fun(&scheme.compact.cty.lower)
            || compact_type_has_fun(&scheme.compact.cty.upper)
        {
            return ValueCallShape::Callable;
        }
    }
    ValueCallShape::Unknown
}

fn expr_is_lambda_value(expr: &TypedExpr) -> bool {
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Coerce { expr, .. } | ExprKind::PackForall(_, expr) => {
                current = expr;
            }
            ExprKind::Lam(_, _) => return true,
            _ => return false,
        }
    }
}

fn compact_type_has_fun(ty: &crate::simplify::compact::CompactType) -> bool {
    !ty.funs.is_empty()
}

fn pos_is_fun(pos: &Pos) -> bool {
    matches!(pos, Pos::Fun { .. })
}

fn neg_is_fun(neg: &Neg) -> bool {
    matches!(neg, Neg::Fun { .. })
}

fn pos_is_known_non_fun(pos: &Pos) -> bool {
    matches!(
        pos,
        Pos::Con(_, _)
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_)
            | Pos::Row(_, _)
            | Pos::Atom(_)
    )
}

fn neg_is_known_non_fun(neg: &Neg) -> bool {
    matches!(
        neg,
        Neg::Con(_, _)
            | Neg::Record(_)
            | Neg::PolyVariant(_)
            | Neg::Tuple(_)
            | Neg::Row(_, _)
            | Neg::Atom(_)
    )
}

fn unresolved_value_use_expr(
    state: &mut LowerState,
    unresolved: UnresolvedValueUse,
    span: Option<rowan::TextRange>,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    let ref_id = state.ctx.fresh_ref();
    state.ctx.refs.push_unresolved(
        ref_id,
        crate::ref_table::UnresolvedRef {
            path: unresolved.path,
            module: unresolved.module,
            use_paths: unresolved.use_paths,
            ref_tv: tv,
            owner: unresolved.owner,
        },
    );
    if let Some(span) = span {
        state.record_ref_span(ref_id, span);
    }
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Ref(ref_id),
    }
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

pub(super) fn resolve_operator_expr_with_span(
    state: &mut LowerState,
    name: Name,
    fixity: OperatorFixity,
    span: Option<rowan::TextRange>,
) -> TypedExpr {
    if let Some(def) = state.ctx.resolve_operator_value(&name, fixity) {
        if let Some(span) = span {
            state.record_value_use_span(span, def);
        }
        return resolve_bound_def_expr(state, def);
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

pub(crate) fn resolve_bound_def_expr(state: &mut LowerState, def: crate::ids::DefId) -> TypedExpr {
    let start = Instant::now();
    let debug_ref = debug_ref_enabled();
    if debug_ref {
        eprintln!(
            "-- resolve_bound_def_expr {:?} name={:?} owner={:?} def_owner={:?} frozen={} def_eff={} let_bound={}",
            def,
            state.def_names.get(&def),
            state.current_owner,
            state.def_owner(def),
            state.infer.frozen_scheme_of(def).is_some(),
            state.def_eff_tvs.contains_key(&def),
            state.is_let_bound_def(def),
        );
    }
    if let (Some(owner), Some(def_owner)) = (state.current_owner, state.def_owner(def)) {
        if owner != def_owner {
            state.add_captured_def_non_generic_vars(owner, def);
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
            record_resolve_bound_def_expr(state, start, ResolveBoundDefKind::SelfRecursive);
            return TypedExpr {
                tv,
                eff,
                kind: ExprKind::Var(def),
            };
        }
        if let Some(instance) = state.active_recursive_self_instance(def) {
            state.mark_recursive_self_use(def);
            let ref_id = state.ctx.fresh_ref();
            state
                .ctx
                .refs
                .resolve(ref_id, def, instance.tv, state.current_owner);
            state.mark_resolved_ref_instantiated(ref_id);
            record_resolve_bound_def_expr(state, start, ResolveBoundDefKind::SelfRecursive);
            return TypedExpr {
                tv: instance.tv,
                eff: instance.eff_tv,
                kind: ExprKind::Var(def),
            };
        }
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
            record_resolve_bound_def_expr(state, start, ResolveBoundDefKind::SelfRecursive);
            return TypedExpr {
                tv,
                eff,
                kind: ExprKind::Var(def),
            };
        }
    }
    if let Some(expr) = alias_same_owner_ref_expr(state, def) {
        record_resolve_bound_def_expr(state, start, ResolveBoundDefKind::Alias);
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
    let mut resolve_kind = ResolveBoundDefKind::Direct;
    if state.def_eff_tvs.contains_key(&def) {
        if let Some(&def_tv) = state.def_tvs.get(&def) {
            state.infer.constrain(Pos::Var(def_tv), Neg::Var(tv));
            state.infer.constrain(Pos::Var(tv), Neg::Var(def_tv));
        }
    } else if let Some(scheme) = state.infer.frozen_scheme_of(def) {
        resolve_kind = ResolveBoundDefKind::Frozen;
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
                    Some(&scheme),
                );
        }
    } else if let Some(&def_tv) = state.def_tvs.get(&def) {
        if state.current_owner != Some(def)
            && state.is_let_bound_def(def)
            && principal_body_is_lambda_value(state, def)
        {
            resolve_kind = ResolveBoundDefKind::OnDemandLambda;
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
        } else if should_defer_unlowered_callable_ref(state, def) {
            resolve_kind = ResolveBoundDefKind::LetBound;
            if let Some(owner) = state.current_owner {
                state.infer.add_edge(owner, def);
            }
            let ref_id = state.ctx.fresh_ref();
            state.ctx.refs.resolve(ref_id, def, tv, state.current_owner);
            record_resolve_bound_def_expr(state, start, resolve_kind);
            return TypedExpr {
                tv,
                eff,
                kind: ExprKind::Var(def),
            };
        } else if state.is_let_bound_def(def) && state.current_owner != Some(def) {
            resolve_kind = ResolveBoundDefKind::LetBound;
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
    record_resolve_bound_def_expr(state, start, resolve_kind);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Var(def),
    }
}

enum ResolveBoundDefKind {
    SelfRecursive,
    Alias,
    Frozen,
    OnDemandLambda,
    LetBound,
    Direct,
}

fn record_resolve_bound_def_expr(
    state: &mut LowerState,
    start: Instant,
    kind: ResolveBoundDefKind,
) {
    let elapsed = start.elapsed();
    state.lower_detail.resolve_bound_def_expr += elapsed;
    match kind {
        ResolveBoundDefKind::SelfRecursive => {
            state.lower_detail.resolve_bound_def_self_recursive += elapsed;
        }
        ResolveBoundDefKind::Alias => {
            state.lower_detail.resolve_bound_def_alias += elapsed;
        }
        ResolveBoundDefKind::Frozen => {
            state.lower_detail.resolve_bound_def_frozen += elapsed;
        }
        ResolveBoundDefKind::OnDemandLambda => {
            state.lower_detail.resolve_bound_def_on_demand_lambda += elapsed;
        }
        ResolveBoundDefKind::LetBound => {
            state.lower_detail.resolve_bound_def_let_bound += elapsed;
        }
        ResolveBoundDefKind::Direct => {
            state.lower_detail.resolve_bound_def_direct += elapsed;
        }
    }
}

fn should_defer_unlowered_callable_ref(state: &LowerState, def: crate::ids::DefId) -> bool {
    state.is_let_bound_def(def)
        && state.current_owner != Some(def)
        && !state.principal_bodies.contains_key(&def)
        && state.is_callable_value_def(def)
}

fn debug_ref_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_DEBUG_REF").is_some())
}

fn can_alias_direct_ref(state: &LowerState, def: crate::ids::DefId) -> bool {
    let has_role_constraints = state.infer.has_role_constraints(def);
    let def_owner = state.def_owner(def);

    if let Some(owner) = state.current_owner {
        let same_owner = def == owner || def_owner == Some(owner);
        if same_owner {
            let is_let_bound = state.is_let_bound_def(def);
            let lambda_value = is_let_bound && principal_body_is_lambda_value(state, def);
            let aliasable_same_owner = def == owner || !is_let_bound || !lambda_value;
            if !aliasable_same_owner || (has_role_constraints && lambda_value) {
                return false;
            }
            return match state.infer.frozen_scheme_of(def) {
                Some(scheme) => scheme.quantified.is_empty(),
                None => true,
            };
        }
    }

    if has_role_constraints {
        return false;
    }

    let ownerless_frozen_mono = state.current_owner.is_none()
        && !state.is_continuation_def(def)
        && def_owner.is_none()
        && state
            .infer
            .frozen_scheme_of(def)
            .map(|scheme| scheme.quantified.is_empty())
            .unwrap_or(false);

    ownerless_frozen_mono
}

fn principal_body_is_lambda_value(state: &LowerState, def: crate::ids::DefId) -> bool {
    let Some(body) = state.principal_bodies.get(&def) else {
        return false;
    };
    let mut body: &TypedExpr = body;
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
