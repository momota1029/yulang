use std::collections::HashSet;
use std::sync::OnceLock;

use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{
    ConstraintCause, ExpectedAdapterEdgeKind, ExpectedEdgeKind, TypeErrorKind, TypeOrigin,
    TypeOriginKind,
};
use crate::ids::TypeVar;
use crate::lower::{FunctionSigEffectHint, LowerState};
use crate::solve::DeferredRoleMethodCall;
use crate::solve::RoleMethodInfo;
use crate::solve::ShiftKeep;
use crate::solve::role::role_method_info_for_path;
use crate::types::{Neg, Pos};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgumentPassingStyle {
    Value,
    Computation,
    Unknown,
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
    let debug_app = debug_app_enabled();
    let passing_style = argument_passing_style(state, &func);
    record_callee_dependency(state, &func);
    let result_ty = crate::ast::expr::ComputationTy::new(
        state.fresh_tv_with_origin(TypeOrigin {
            span: cause.span,
            file_span: None,
            kind: TypeOriginKind::ApplicationResult,
            label: None,
        }),
        state.fresh_tv(),
    );
    let expected_callee_tv = state.fresh_tv();
    let expected_arg_tv = state.fresh_tv();
    let call_eff = state.fresh_tv();
    if let Some(owner) = cross_owner_function_ref_owner(state, &func) {
        state.infer.add_non_generic_var(owner, result_ty.value);
        state.infer.add_non_generic_var(owner, expected_callee_tv);
        state.infer.add_non_generic_var(owner, expected_arg_tv);
        state.infer.add_non_generic_var(owner, call_eff);
        state.infer.add_non_generic_var(owner, result_ty.effect);
    }
    let pure_argument_slot = func_accepts_pure_argument(state, &func)
        || matches!(func.kind, ExprKind::Select { .. })
        || selected_value_method_accepts_pure_next_arg(state, &func);
    let anf_arg = matches!(passing_style, ArgumentPassingStyle::Value)
        && matches!(arg.kind, ExprKind::App { .. });
    let arg_eff_for_slot = if pure_argument_slot || anf_arg {
        state.fresh_exact_pure_eff_tv()
    } else if matches!(passing_style, ArgumentPassingStyle::Computation) {
        argument_effect_for_slot(state, &arg)
    } else {
        argument_effect_for_slot(state, &arg)
    };
    let mut demanded_ret_eff = Neg::Var(call_eff);
    if let ExprKind::Var(def) = &func.kind {
        if let Some(hint) = state.lambda_param_function_sig_hint(*def) {
            match hint {
                FunctionSigEffectHint::Pure => {
                    state
                        .infer
                        .constrain(state.infer.arena.empty_pos_row, Neg::Var(call_eff));
                    state
                        .infer
                        .constrain(Pos::Var(call_eff), state.infer.arena.empty_neg_row);
                    demanded_ret_eff = state
                        .infer
                        .arena
                        .get_neg(state.infer.arena.empty_neg_row)
                        .clone();
                }
                FunctionSigEffectHint::Through => {
                    state.infer.mark_through(call_eff);
                }
                FunctionSigEffectHint::LowerBound(lower) => {
                    state.infer.constrain(lower, Neg::Var(call_eff));
                }
                FunctionSigEffectHint::Bounds(lower, upper) => {
                    state.infer.constrain(lower, Neg::Var(call_eff));
                    state.infer.constrain(Pos::Var(call_eff), upper);
                    demanded_ret_eff = state.infer.arena.get_neg(upper).clone();
                }
            }
        } else if !state.effect_op_args.contains_key(def)
            && !state.is_let_bound_def(*def)
            && !state.is_continuation_def(*def)
        {
            state.infer.mark_through(call_eff);
        }
    }

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
    if matches!(&func.kind, ExprKind::Var(def) if state.effect_op_args.contains_key(def)) {
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
    if pure_argument_slot {
        state.infer.constrain(Pos::Var(arg.eff), Neg::Var(call_eff));
    }
    state
        .infer
        .constrain(Pos::Var(func.eff), Neg::Var(result_ty.effect));
    if let Some(keep) = thunk_boundary_keep_for_call(state, &func) {
        state
            .infer
            .record_effect_boundary_keep(call_eff, keep.clone());
        state
            .infer
            .record_effect_boundary_keep(result_ty.effect, keep);
    }
    state
        .infer
        .constrain(Pos::Var(call_eff), Neg::Var(result_ty.effect));
    if pure_argument_slot || anf_arg {
        state
            .infer
            .constrain(Pos::Var(arg.eff), Neg::Var(result_ty.effect));
    }
    if matches!(&func.kind, ExprKind::Var(def) if state.is_continuation_def(*def)) {
        state
            .infer
            .constrain(Pos::Var(arg.eff), Neg::Var(result_ty.effect));
    }

    if debug_app && matches!(func.kind, ExprKind::Lam(_, _)) {
        eprintln!("-- make_app_with_cause --");
        eprintln!("arg.kind = {:?}", arg.kind);
        eprintln!("arg.tv = {:?}", arg.tv);
        eprintln!("arg lowers = {:?}", state.infer.lowers_of(arg.tv));
        eprintln!("arg uppers = {:?}", state.infer.uppers_of(arg.tv));
        for upper in state.infer.uppers_of(arg.tv) {
            if let Neg::Fun { ret_eff, ret, .. } = upper {
                eprintln!(
                    "arg upper ret_eff node = {:?}",
                    state.infer.arena.get_neg(ret_eff)
                );
                eprintln!("arg upper ret node = {:?}", state.infer.arena.get_neg(ret));
                if let Neg::Var(ret_eff_tv) = state.infer.arena.get_neg(ret_eff) {
                    super::debug_dump_effect_tv(state, ret_eff_tv, 1, &mut HashSet::new());
                }
            }
        }
        eprintln!("call_eff = {:?}", call_eff);
        eprintln!("call_eff lowers = {:?}", state.infer.lowers_of(call_eff));
        eprintln!("call_eff uppers = {:?}", state.infer.uppers_of(call_eff));
    }
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

fn argument_effect_for_slot(state: &mut LowerState, arg: &TypedExpr) -> TypeVar {
    let ExprKind::Var(def) = &arg.kind else {
        return arg.eff;
    };
    let Some(source_eff) = state.lambda_param_source_eff_tvs.get(def).copied() else {
        return arg.eff;
    };
    source_eff
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
    if state.is_unannotated_current_lambda_param(*def) {
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

fn debug_app_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_DEBUG_APP").is_some())
}

fn cross_owner_function_ref_owner(
    state: &LowerState,
    func: &TypedExpr,
) -> Option<crate::ids::DefId> {
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
    if func_accepts_pure_argument(state, func) {
        return ArgumentPassingStyle::Value;
    }
    ArgumentPassingStyle::Unknown
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
