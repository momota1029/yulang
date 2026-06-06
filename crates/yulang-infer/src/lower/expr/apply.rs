use std::collections::HashSet;

use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{
    ConstraintCause, ExpectedAdapterEdgeKind, ExpectedEdgeKind, TypeErrorKind, TypeOrigin,
    TypeOriginKind,
};
use crate::ids::{DefId, PosId, TypeVar};
use crate::lower::{FunctionSigEffectHint, LowerState};
use crate::solve::DeferredRoleMethodCall;
use crate::solve::RoleMethodInfo;
use crate::solve::role::role_method_info_for_path;
use crate::solve::{EffectSubtractability, ShiftKeep};
use crate::types::{Neg, Pos};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgumentPassingStyle {
    Value,
    Computation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ApplicationEffectAssumption {
    value_argument_effect: bool,
    pure_argument_slot: bool,
    anf_argument: bool,
    direct_computation_argument_slot: bool,
    all_subtractable_argument_slot: bool,
    all_subtractable_result_effects: bool,
}

impl ApplicationEffectAssumption {
    fn infer(state: &LowerState, func: &TypedExpr, arg: &TypedExpr) -> Self {
        let passing_style = argument_passing_style(state, func);
        let direct_computation_argument_slot =
            matches!(passing_style, ArgumentPassingStyle::Computation)
                && !callee_is_continuation(state, func)
                && !callee_is_active_recursive_self(state, func);
        let value_argument_slot = matches!(passing_style, ArgumentPassingStyle::Value);
        Self {
            value_argument_effect: value_argument_slot,
            pure_argument_slot: func_accepts_pure_argument(state, func)
                || matches!(&func.kind, ExprKind::Select { .. })
                || selected_value_method_accepts_pure_next_arg(state, func),
            anf_argument: value_argument_slot && matches!(arg.kind, ExprKind::App { .. }),
            direct_computation_argument_slot,
            all_subtractable_argument_slot: callee_uses_all_subtractable_argument_slot(state, func),
            all_subtractable_result_effects: !direct_computation_argument_slot
                && callee_uses_all_subtractable_result_effects(state, func),
        }
    }

    fn argument_slot(
        self,
        state: &mut LowerState,
        arg: &TypedExpr,
        cross_owner: Option<DefId>,
    ) -> TypeVar {
        if self.direct_computation_argument_slot {
            return argument_effect_for_slot(state, arg);
        }
        if self.all_subtractable_argument_slot || !self.argument_slot_is_pure() {
            fresh_all_subtractable_arg_effect_slot(state, arg, cross_owner)
        } else {
            state.fresh_exact_pure_eff_tv()
        }
    }

    fn argument_slot_is_pure(self) -> bool {
        self.pure_argument_slot || self.anf_argument
    }

    fn mark_call_result_effects(
        self,
        state: &mut LowerState,
        call_eff: TypeVar,
        result_eff: TypeVar,
    ) {
        if self.all_subtractable_result_effects {
            state
                .infer
                .record_effect_subtractability(call_eff, EffectSubtractability::All);
            state
                .infer
                .record_effect_subtractability(result_eff, EffectSubtractability::All);
        }
    }

    fn argument_effect_flows_to_result(self) -> bool {
        self.value_argument_effect || self.anf_argument
    }
}

pub(crate) fn make_app(state: &mut LowerState, func: TypedExpr, arg: TypedExpr) -> TypedExpr {
    make_app_with_cause(state, func, arg, ConstraintCause::unknown())
}

pub(crate) fn make_app_with_cause(
    state: &mut LowerState,
    func: TypedExpr,
    arg: TypedExpr,
    cause: ConstraintCause,
) -> TypedExpr {
    resolve_pending_callee_selection(state, &func);
    record_callee_dependency(state, &func);
    let result_ty = crate::ast::expr::ComputationTy::new(
        state.fresh_tv_with_origin(TypeOrigin {
            span: cause.span,
            file_span: None,
            kind: TypeOriginKind::ApplicationResult,
            label: None,
        }),
        state.fresh_generated_effect_tv(),
    );
    let expected_callee_tv = state.fresh_tv();
    let expected_arg_tv = state.fresh_tv();
    let call_eff = if callee_uses_latent_result_effect(state, &func) {
        state.fresh_latent_function_result_effect_tv()
    } else {
        state.fresh_generated_effect_tv()
    };
    let cross_owner = cross_owner_function_ref_owner(state, &func);
    if let Some(owner) = cross_owner {
        state.infer.add_non_generic_var(owner, result_ty.value);
        state.infer.add_non_generic_var(owner, expected_callee_tv);
        state.infer.add_non_generic_var(owner, expected_arg_tv);
        state.infer.add_non_generic_var(owner, call_eff);
        state.infer.add_non_generic_var(owner, result_ty.effect);
    }
    let effect_assumption = ApplicationEffectAssumption::infer(state, &func, &arg);
    let arg_eff_for_slot = effect_assumption.argument_slot(state, &arg, cross_owner);
    let boundary_keep = thunk_boundary_keep_for_call(state, &func);
    let mut demanded_ret_eff = Neg::Var(call_eff);
    effect_assumption.mark_call_result_effects(state, call_eff, result_ty.effect);
    copy_continuation_result_effect_metadata(state, &func, call_eff, result_ty.effect);
    if let ExprKind::Var(def) = &func.kind {
        if let Some(hint) = state.lambda_param_function_sig_hint(*def) {
            match hint {
                FunctionSigEffectHint::Pure => {
                    state
                        .infer
                        .constrain(state.infer.arena.bot, Neg::Var(call_eff));
                    state
                        .infer
                        .constrain(Pos::Var(call_eff), state.infer.arena.empty_neg_row);
                    demanded_ret_eff = state
                        .infer
                        .arena
                        .get_neg(state.infer.arena.empty_neg_row)
                        .clone();
                }
                FunctionSigEffectHint::AllSubtractable { subtract_ids, .. } => {
                    if subtract_ids.is_empty() {
                        state
                            .infer
                            .record_effect_subtractability(call_eff, EffectSubtractability::All);
                    } else {
                        for id in subtract_ids {
                            state.infer.record_effect_subtractability_for_id(
                                call_eff,
                                id,
                                EffectSubtractability::All,
                            );
                        }
                    }
                }
                FunctionSigEffectHint::LowerBound(lower) => {
                    state.infer.constrain(lower, Neg::Var(call_eff));
                }
                FunctionSigEffectHint::Bounds {
                    lower,
                    upper,
                    subtract_ids: _,
                    non_subtract_targets: _,
                } => {
                    record_effect_subtractability_from_upper(state, call_eff, upper);
                    state.infer.constrain(lower, Neg::Var(call_eff));
                    state.infer.constrain(Pos::Var(call_eff), upper);
                    demanded_ret_eff = state.infer.arena.get_neg(upper).clone();
                }
            }
        }
    }
    record_call_boundary_effect_metadata(state, call_eff, result_ty.effect, boundary_keep.as_ref());

    state.infer.constrain_with_cause(
        Pos::Var(expected_callee_tv),
        state.neg_fun(
            Pos::Var(expected_arg_tv),
            Pos::Var(arg_eff_for_slot),
            demanded_ret_eff,
            Neg::Var(result_ty.value),
        ),
        cause.clone(),
    );
    let callee_edge_id = state.expect_value(
        func.tv,
        expected_callee_tv,
        ExpectedEdgeKind::ApplicationCallee,
        cause.clone(),
    );
    report_extra_struct_literal_fields(state, &func, &arg);
    let (arg, arg_edge_id) = state.implicit_cast_boundary(
        arg,
        expected_arg_tv,
        ExpectedEdgeKind::ApplicationArgument,
        cause.clone(),
        false,
    );
    if let ExprKind::Var(def) = &func.kind
        && state.effect_op_args.contains_key(def)
    {
        state.record_expected_adapter_edge(
            ExpectedAdapterEdgeKind::EffectOperationArgument,
            Some(arg_edge_id),
            Some(arg.tv),
            Some(expected_arg_tv),
            Some(arg.eff),
            Some(arg_eff_for_slot),
            cause.clone(),
        );
    }
    if matches!(&func.kind, ExprKind::Var(def) if state.is_continuation_def(*def)) {
        state.record_expected_adapter_edge(
            ExpectedAdapterEdgeKind::ResumeArgument,
            Some(arg_edge_id),
            Some(arg.tv),
            Some(expected_arg_tv),
            Some(arg.eff),
            Some(arg_eff_for_slot),
            cause.clone(),
        );
    }
    if effect_assumption.pure_argument_slot {
        state
            .infer
            .constrain(effect_lower_for_flow(state, arg.eff), Neg::Var(call_eff));
    }
    state.infer.constrain(
        effect_lower_for_flow(state, func.eff),
        Neg::Var(result_ty.effect),
    );
    state.infer.constrain(
        effect_lower_for_flow(state, call_eff),
        Neg::Var(result_ty.effect),
    );
    if effect_assumption.argument_effect_flows_to_result() {
        state.infer.constrain(
            effect_lower_for_flow(state, arg.eff),
            Neg::Var(result_ty.effect),
        );
    }
    if matches!(&func.kind, ExprKind::Var(def) if state.is_continuation_def(*def)) {
        state.infer.constrain(
            effect_lower_for_flow(state, arg.eff),
            Neg::Var(result_ty.effect),
        );
    }
    record_call_exposed_effect_non_subtracts(state, call_eff, result_ty);

    let result = TypedExpr::new(
        result_ty,
        ExprKind::App {
            callee: Box::new(func),
            arg: Box::new(arg),
            callee_edge_id: Some(callee_edge_id),
            expected_callee_tv,
            arg_edge_id: Some(arg_edge_id),
            expected_arg_tv,
        },
    );
    register_role_method_call_spine(state, &result);
    result
}

fn record_call_exposed_effect_non_subtracts(
    state: &LowerState,
    call_eff: TypeVar,
    result_ty: crate::ast::expr::ComputationTy,
) {
    let mut ids = state
        .infer
        .effect_subtract_facts(call_eff)
        .into_iter()
        .filter_map(|fact| {
            state
                .infer
                .effect_subtract_id_needs_call_non_subtract(fact.id)
                .then_some(fact.id)
        })
        .collect::<Vec<_>>();
    ids.sort();
    ids.dedup();
    for id in ids {
        state
            .infer
            .record_effect_non_subtract_deep(result_ty.value, id);
        state
            .infer
            .record_effect_non_subtract_deep(result_ty.effect, id);
    }
}

fn callee_uses_all_subtractable_argument_slot(state: &LowerState, func: &TypedExpr) -> bool {
    callee_is_unquantified_let_bound_value(state, func)
        || callee_is_active_recursive_self(state, func)
}

fn callee_uses_latent_result_effect(state: &LowerState, func: &TypedExpr) -> bool {
    matches!(&func.kind, ExprKind::Var(def) if state.is_unannotated_current_or_ancestor_lambda_param(*def))
}

fn callee_uses_all_subtractable_result_effects(state: &LowerState, func: &TypedExpr) -> bool {
    callee_uses_all_subtractable_argument_slot(state, func)
        || matches!(&func.kind, ExprKind::Select { .. })
        || callee_has_all_subtractable_return_effect(state, func)
}

fn fresh_all_subtractable_arg_effect_slot(
    state: &mut LowerState,
    arg: &TypedExpr,
    cross_owner: Option<DefId>,
) -> TypeVar {
    let slot = state.fresh_tv();
    state
        .infer
        .record_effect_subtractability(slot, EffectSubtractability::All);
    let actual = argument_effect_for_slot(state, arg);
    state
        .infer
        .constrain(effect_lower_for_flow(state, actual), Neg::Var(slot));
    if let Some(owner) = cross_owner {
        state.infer.add_non_generic_var(owner, slot);
    }
    slot
}

fn callee_is_unquantified_let_bound_value(state: &LowerState, func: &TypedExpr) -> bool {
    let ExprKind::Var(def) = &func.kind else {
        return false;
    };
    if !state.is_let_bound_def(*def) {
        return false;
    }
    if state.infer.frozen_schemes.borrow().contains_key(def) {
        return false;
    }
    !state.infer.compact_schemes.borrow().contains_key(def)
}

fn callee_is_active_recursive_self(state: &LowerState, func: &TypedExpr) -> bool {
    let ExprKind::Var(def) = &func.kind else {
        return false;
    };
    state.current_owner == Some(*def) && state.active_recursive_self_instance(*def).is_some()
}

fn callee_is_continuation(state: &LowerState, func: &TypedExpr) -> bool {
    matches!(&func.kind, ExprKind::Var(def) if state.is_continuation_def(*def))
}

fn copy_continuation_result_effect_metadata(
    state: &LowerState,
    func: &TypedExpr,
    call_eff: TypeVar,
    result_eff: TypeVar,
) {
    let ExprKind::Var(def) = &func.kind else {
        return;
    };
    let Some(source_eff) = state.continuation_result_eff_tv(*def) else {
        return;
    };
    state
        .infer
        .copy_effect_subtractability(source_eff, call_eff);
    state
        .infer
        .copy_effect_subtractability(source_eff, result_eff);
}

fn callee_has_all_subtractable_return_effect(state: &LowerState, func: &TypedExpr) -> bool {
    let mut seen = HashSet::new();
    pos_var_has_all_subtractable_return_effect(state, func.tv, &mut seen)
}

fn pos_var_has_all_subtractable_return_effect(
    state: &LowerState,
    tv: TypeVar,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    if !seen.insert(tv) {
        return false;
    }
    for lower in state.infer.lower_refs_of(tv) {
        if pos_id_has_all_subtractable_return_effect(state, lower, seen) {
            return true;
        }
    }
    for instance in state.infer.compact_lower_instances_of(tv) {
        let lower = state.infer.materialize_compact_lower_instance(&instance);
        if pos_id_has_all_subtractable_return_effect(state, lower, seen) {
            return true;
        }
    }
    false
}

fn pos_id_has_all_subtractable_return_effect(
    state: &LowerState,
    pos: PosId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_pos(pos) {
        Pos::Fun { ret_eff, .. } => pos_effect_is_all_subtractable(state, ret_eff, seen),
        Pos::Var(tv) | Pos::Raw(tv) => pos_var_has_all_subtractable_return_effect(state, tv, seen),
        Pos::Forall(_, body) => pos_id_has_all_subtractable_return_effect(state, body, seen),
        Pos::Union(lhs, rhs) => {
            pos_id_has_all_subtractable_return_effect(state, lhs, &mut seen.clone())
                || pos_id_has_all_subtractable_return_effect(state, rhs, &mut seen.clone())
        }
        _ => false,
    }
}

fn pos_effect_is_all_subtractable(
    state: &LowerState,
    pos: PosId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_pos(pos) {
        Pos::Var(tv) | Pos::Raw(tv) => {
            state.infer.effect_is_all_subtractable(tv)
                || pos_var_has_all_subtractable_return_effect(state, tv, seen)
        }
        Pos::Forall(_, body) => pos_effect_is_all_subtractable(state, body, seen),
        Pos::Union(lhs, rhs) => {
            pos_effect_is_all_subtractable(state, lhs, &mut seen.clone())
                || pos_effect_is_all_subtractable(state, rhs, &mut seen.clone())
        }
        _ => false,
    }
}

fn record_callee_dependency(state: &LowerState, func: &TypedExpr) {
    let ExprKind::Var(def) = &func.kind else {
        return;
    };
    let Some(owner) = state.current_owner else {
        return;
    };
    if owner != *def && state.is_let_bound_def(*def) {
        state.infer.add_edge(owner, *def);
    }
}

fn resolve_pending_callee_selection(state: &LowerState, func: &TypedExpr) {
    let ExprKind::Select { recv, .. } = &func.kind else {
        return;
    };
    state.infer.resolve_deferred_selections_for(recv.tv);
}

fn argument_effect_for_slot(state: &mut LowerState, arg: &TypedExpr) -> TypeVar {
    let ExprKind::Var(def) = &arg.kind else {
        return arg.eff;
    };
    let Some(source_eff) = state.lambda_param_source_eff_tvs.get(def).copied() else {
        return arg.eff;
    };
    source_eff
}

fn effect_lower_for_flow(state: &LowerState, effect: TypeVar) -> PosId {
    if state.exact_pure_effect_tvs.contains(&effect) || state.infer.effect_var_is_exact_pure(effect)
    {
        state.infer.arena.empty_pos_row
    } else {
        state.infer.alloc_pos(Pos::Var(effect))
    }
}

fn report_extra_struct_literal_fields(state: &LowerState, func: &TypedExpr, arg: &TypedExpr) {
    let ExprKind::Var(def) = &func.kind else {
        return;
    };
    let Some(field_set) = state
        .infer
        .type_field_sets
        .values()
        .find(|field_set| field_set.constructor == *def)
    else {
        return;
    };
    let ExprKind::Record { fields, .. } = &arg.kind else {
        return;
    };
    let allowed = field_set
        .fields
        .iter()
        .map(|field| &field.name)
        .collect::<HashSet<_>>();
    for (name, _) in fields {
        if !allowed.contains(name) {
            state.infer.report_synthetic_type_error(
                TypeErrorKind::UnknownRecordField {
                    name: name.0.clone(),
                },
                format!("struct constructor {}", def.0),
            );
        }
    }
}

fn thunk_boundary_keep_for_call(state: &LowerState, func: &TypedExpr) -> Option<ShiftKeep> {
    let ExprKind::Var(def) = &func.kind else {
        return None;
    };
    if state.is_unannotated_current_or_ancestor_lambda_param(*def) {
        return Some(ShiftKeep::None);
    }
    let allowed = state.lambda_param_function_allowed_effects.get(def)?;
    Some(match allowed {
        yulang_typed_ir::FunctionSigAllowedEffects::Wildcard => ShiftKeep::Surface,
        yulang_typed_ir::FunctionSigAllowedEffects::Effects(paths) => ShiftKeep::Set(
            paths
                .iter()
                .map(|path| crate::symbols::Path {
                    segments: path
                        .segments
                        .iter()
                        .map(|name| crate::symbols::Name(name.0.clone()))
                        .collect(),
                })
                .collect(),
        ),
    })
}

fn effect_subtractability_for_keep(keep: &ShiftKeep) -> Option<EffectSubtractability> {
    match keep {
        ShiftKeep::None | ShiftKeep::CallBoundary => Some(EffectSubtractability::Empty),
        ShiftKeep::Surface => None,
        ShiftKeep::Set(paths) => Some(EffectSubtractability::from_paths(paths.clone())),
    }
}

fn record_call_boundary_effect_metadata(
    state: &LowerState,
    call_eff: TypeVar,
    result_eff: TypeVar,
    keep: Option<&ShiftKeep>,
) -> bool {
    let Some(keep) = keep else {
        return false;
    };
    state
        .infer
        .record_effect_boundary_keep(call_eff, keep.clone());
    state
        .infer
        .record_effect_boundary_keep(result_eff, keep.clone());
    let Some(subtractability) = effect_subtractability_for_keep(keep) else {
        return false;
    };
    let subtract_id = state.infer.fresh_effect_subtract_id();
    state.infer.record_effect_subtractability_for_id(
        call_eff,
        subtract_id,
        subtractability.clone(),
    );
    state
        .infer
        .record_effect_subtractability_for_id(result_eff, subtract_id, subtractability);
    true
}

fn record_effect_subtractability_from_upper(
    state: &LowerState,
    effect: TypeVar,
    upper: crate::ids::NegId,
) -> bool {
    if let Neg::Var(source) = state.infer.arena.get_neg(upper) {
        if state.infer.effect_subtract_facts(source).is_empty()
            && state.infer.effect_non_subtract_ids(source).is_empty()
        {
            return false;
        }
        state.infer.copy_effect_subtractability(source, effect);
        return true;
    }
    let Neg::Row(items, _) = state.infer.arena.get_neg(upper) else {
        return false;
    };
    let atoms = items
        .into_iter()
        .filter_map(|item| match state.infer.arena.get_neg(item) {
            Neg::Atom(atom) => Some(atom),
            _ => None,
        })
        .collect::<Vec<_>>();
    if atoms.is_empty() {
        return false;
    }
    state
        .infer
        .record_effect_subtractability(effect, EffectSubtractability::Set(atoms));
    true
}

fn cross_owner_function_ref_owner(state: &LowerState, func: &TypedExpr) -> Option<DefId> {
    let ExprKind::Var(def) = &func.kind else {
        return None;
    };
    let owner = state.current_owner?;
    let def_owner = state.def_owner(*def)?;
    (owner != def_owner).then_some(owner)
}

fn register_role_method_call_spine(state: &mut LowerState, expr: &TypedExpr) {
    let (head, args) = collect_app_spine(expr);
    match &head.kind {
        ExprKind::Select { recv, name } => {
            state
                .infer
                .push_deferred_role_method_call(DeferredRoleMethodCall {
                    name: name.clone(),
                    role_path: None,
                    cast_coercion: false,
                    owner: state.current_owner,
                    recv_tv: recv.tv,
                    arg_tvs: args.iter().map(|arg| arg.tv).collect(),
                    result_tv: expr.tv,
                });
        }
        ExprKind::Var(def) => {
            let Some((info, role_path)) = role_method_info_for_direct_call_def(state, *def) else {
                return;
            };
            let Some((recv, rest)) = args.split_first() else {
                return;
            };
            state
                .infer
                .push_deferred_role_method_call(DeferredRoleMethodCall {
                    name: info.name,
                    role_path,
                    cast_coercion: false,
                    owner: state.current_owner,
                    recv_tv: recv.tv,
                    arg_tvs: rest.iter().map(|arg| arg.tv).collect(),
                    result_tv: expr.tv,
                });
        }
        ExprKind::Ref(ref_id) => {
            let Some((name, role_path)) = unresolved_role_method_path(state, *ref_id) else {
                return;
            };
            let Some((recv, rest)) = args.split_first() else {
                return;
            };
            state
                .infer
                .push_deferred_role_method_call(DeferredRoleMethodCall {
                    name,
                    role_path: Some(role_path),
                    cast_coercion: false,
                    owner: state.current_owner,
                    recv_tv: recv.tv,
                    arg_tvs: rest.iter().map(|arg| arg.tv).collect(),
                    result_tv: expr.tv,
                });
        }
        _ => {}
    }
}

fn role_method_info_for_direct_call_def(
    state: &LowerState,
    def: crate::ids::DefId,
) -> Option<(RoleMethodInfo, Option<crate::symbols::Path>)> {
    state
        .infer
        .role_method_info_for_def(def)
        .map(|info| (info, direct_call_path(state, def)))
        .or_else(|| {
            let path = direct_call_path(state, def)?;
            role_method_info_for_path(&state.infer.role_methods, &path)
                .map(|info| (info, Some(path)))
        })
}

fn direct_call_path(state: &LowerState, def: crate::ids::DefId) -> Option<crate::symbols::Path> {
    state
        .ctx
        .collect_all_binding_paths()
        .into_iter()
        .find_map(|(path, path_def)| (path_def == def).then_some(path))
}

fn unresolved_role_method_path(
    state: &LowerState,
    ref_id: crate::ids::RefId,
) -> Option<(crate::symbols::Name, crate::symbols::Path)> {
    let path = state.ctx.refs.unresolved_info(ref_id)?.path.clone();
    let name = path.segments.last()?.clone();
    (path.segments.len() > 1).then_some((name, path))
}

fn collect_app_spine<'a>(expr: &'a TypedExpr) -> (&'a TypedExpr, Vec<&'a TypedExpr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App { callee, arg, .. } = &current.kind {
        args.push(arg.as_ref());
        current = callee.as_ref();
    }
    args.reverse();
    (current, args)
}

fn argument_passing_style(state: &LowerState, func: &TypedExpr) -> ArgumentPassingStyle {
    if matches!(&func.kind, ExprKind::Var(def) if state.is_continuation_def(*def)) {
        return ArgumentPassingStyle::Computation;
    }
    if matches!(&func.kind, ExprKind::Var(def) if def_expects_computation_argument(state, *def)) {
        return ArgumentPassingStyle::Computation;
    }
    if func_expects_computation_argument(state, func) {
        return ArgumentPassingStyle::Computation;
    }
    if func_accepts_pure_argument(state, func) {
        return ArgumentPassingStyle::Value;
    }
    ArgumentPassingStyle::Value
}

fn func_expects_computation_argument(state: &LowerState, func: &TypedExpr) -> bool {
    let mut seen = HashSet::new();
    pos_var_expects_computation_argument(state, func.tv, &mut seen)
}

fn pos_var_expects_computation_argument(
    state: &LowerState,
    tv: TypeVar,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    if !seen.insert(tv) {
        return false;
    }
    for lower in state.infer.lower_refs_of(tv) {
        if pos_id_expects_computation_argument(state, lower, seen) {
            return true;
        }
    }
    for instance in state.infer.compact_lower_instances_of(tv) {
        let lower = state.infer.materialize_compact_lower_instance(&instance);
        if pos_id_expects_computation_argument(state, lower, seen) {
            return true;
        }
    }
    false
}

fn pos_id_expects_computation_argument(
    state: &LowerState,
    pos: PosId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_pos(pos) {
        Pos::Fun { arg_eff, .. } => {
            let mut row_seen = HashSet::new();
            neg_effect_has_computation_evidence(state, arg_eff, &mut row_seen)
        }
        Pos::Var(tv) | Pos::Raw(tv) => pos_var_expects_computation_argument(state, tv, seen),
        Pos::Forall(_, body) => pos_id_expects_computation_argument(state, body, seen),
        Pos::Union(lhs, rhs) => {
            pos_id_expects_computation_argument(state, lhs, &mut seen.clone())
                || pos_id_expects_computation_argument(state, rhs, &mut seen.clone())
        }
        _ => false,
    }
}

fn neg_effect_has_computation_evidence(
    state: &LowerState,
    neg: crate::ids::NegId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_neg(neg) {
        Neg::Row(items, tail) => {
            !items.is_empty() || neg_effect_has_computation_evidence(state, tail, seen)
        }
        Neg::Var(tv) => {
            if state.infer.effect_subtractability(tv).is_some() {
                return true;
            }
            if !seen.insert(tv) {
                return false;
            }
            state
                .infer
                .upper_refs_of(tv)
                .into_iter()
                .any(|upper| neg_effect_has_computation_evidence(state, upper, seen))
                || state
                    .infer
                    .lower_refs_of(tv)
                    .into_iter()
                    .any(|lower| pos_effect_has_computation_evidence(state, lower, seen))
        }
        Neg::Forall(_, body) => neg_effect_has_computation_evidence(state, body, seen),
        Neg::Intersection(lhs, rhs) => {
            neg_effect_has_computation_evidence(state, lhs, &mut seen.clone())
                || neg_effect_has_computation_evidence(state, rhs, &mut seen.clone())
        }
        _ => false,
    }
}

fn pos_effect_has_computation_evidence(
    state: &LowerState,
    pos: PosId,
    seen: &mut HashSet<TypeVar>,
) -> bool {
    match state.infer.arena.get_pos(pos) {
        Pos::Row(items, tail) => {
            !items.is_empty() || pos_effect_has_computation_evidence(state, tail, seen)
        }
        Pos::Var(tv) | Pos::Raw(tv) => {
            if state.infer.effect_subtractability(tv).is_some() {
                return true;
            }
            if !seen.insert(tv) {
                return false;
            }
            state
                .infer
                .lower_refs_of(tv)
                .into_iter()
                .any(|lower| pos_effect_has_computation_evidence(state, lower, seen))
                || state
                    .infer
                    .upper_refs_of(tv)
                    .into_iter()
                    .any(|upper| neg_effect_has_computation_evidence(state, upper, seen))
        }
        Pos::Forall(_, body) => pos_effect_has_computation_evidence(state, body, seen),
        Pos::Union(lhs, rhs) => {
            pos_effect_has_computation_evidence(state, lhs, &mut seen.clone())
                || pos_effect_has_computation_evidence(state, rhs, &mut seen.clone())
        }
        _ => false,
    }
}

fn func_accepts_pure_argument(state: &LowerState, func: &TypedExpr) -> bool {
    if matches!(&func.kind, ExprKind::Var(def) if def_expects_computation_argument(state, *def)) {
        return false;
    }
    if let ExprKind::Var(def) = &func.kind {
        if let Some(&def_tv) = state.def_tvs.get(def) {
            let mut seen = HashSet::new();
            if state
                .infer
                .lowers_of(def_tv)
                .into_iter()
                .any(|lower| lower_has_pure_fun_arg(state, &lower, &mut seen))
            {
                return true;
            }
        }
    }
    let mut seen = HashSet::new();
    state
        .infer
        .lowers_of(func.tv)
        .into_iter()
        .any(|lower| lower_has_pure_fun_arg(state, &lower, &mut seen))
}

fn selected_value_method_accepts_pure_next_arg(state: &LowerState, func: &TypedExpr) -> bool {
    let ExprKind::Select { recv, name } = &func.kind else {
        return false;
    };
    let Some(def) = state.infer.resolve_selection_def(recv.tv, name) else {
        return false;
    };
    let Some(body) = state.principal_bodies.get(&def) else {
        return false;
    };
    let mut body: &TypedExpr = body;
    for _ in 0..2 {
        match &body.kind {
            ExprKind::Coerce { expr, .. } | ExprKind::PackForall(_, expr) => {
                body = expr;
            }
            _ => break,
        }
    }
    let ExprKind::Lam(_, recv_body) = &body.kind else {
        return false;
    };
    let mut body = recv_body.as_ref();
    loop {
        match &body.kind {
            ExprKind::Coerce { expr, .. } | ExprKind::PackForall(_, expr) => {
                body = expr;
            }
            ExprKind::Lam(param_def, _) => {
                return !state
                    .lambda_param_effect_annotations
                    .contains_key(param_def);
            }
            _ => return false,
        }
    }
}

fn def_expects_computation_argument(state: &LowerState, def: crate::ids::DefId) -> bool {
    if state.binding_expects_computation_argument(def) {
        return true;
    }
    let Some(body) = state.principal_bodies.get(&def) else {
        return false;
    };
    let mut body: &TypedExpr = body;
    loop {
        match &body.kind {
            ExprKind::Coerce { expr, .. } | ExprKind::PackForall(_, expr) => {
                body = expr;
            }
            ExprKind::Lam(param_def, _) => {
                return state
                    .lambda_param_effect_annotations
                    .contains_key(param_def);
            }
            _ => return false,
        }
    }
}

fn lower_has_pure_fun_arg(state: &LowerState, pos: &Pos, seen: &mut HashSet<TypeVar>) -> bool {
    match pos {
        Pos::Fun { arg_eff, .. } => {
            let mut row_seen = HashSet::new();
            super::neg_id_is_pure_row(state, *arg_eff, &mut row_seen)
        }
        Pos::Union(a, b) => {
            lower_has_pure_fun_arg(state, &state.infer.arena.get_pos(*a), seen)
                || lower_has_pure_fun_arg(state, &state.infer.arena.get_pos(*b), seen)
        }
        Pos::Var(tv) | Pos::Raw(tv) => {
            if !seen.insert(*tv) {
                return false;
            }
            state
                .infer
                .lowers_of(*tv)
                .into_iter()
                .any(|lower| lower_has_pure_fun_arg(state, &lower, seen))
        }
        _ => false,
    }
}
