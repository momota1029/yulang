use std::collections::HashSet;
use std::sync::OnceLock;

use crate::ast::expr::{ExprKind, TypedExpr};
use crate::diagnostic::{
    ConstraintCause, ExpectedAdapterEdgeKind, ExpectedEdgeKind, TypeOrigin, TypeOriginKind,
};
use crate::ids::TypeVar;
use crate::lower::{FunctionSigEffectHint, LowerState};
use crate::solve::DeferredRoleMethodCall;
use crate::solve::RoleMethodInfo;
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
    let tv = state.fresh_tv_with_origin(TypeOrigin {
        span: cause.span,
        kind: TypeOriginKind::ApplicationResult,
        label: None,
    });
    let expected_callee_tv = state.fresh_tv();
    let expected_arg_tv = state.fresh_tv();
    let call_eff = state.fresh_tv();
    let eff = state.fresh_tv();
    if let Some(owner) = cross_owner_function_ref_owner(state, &func) {
        state.infer.add_non_generic_var(owner, tv);
        state.infer.add_non_generic_var(owner, expected_callee_tv);
        state.infer.add_non_generic_var(owner, expected_arg_tv);
        state.infer.add_non_generic_var(owner, call_eff);
        state.infer.add_non_generic_var(owner, eff);
    }
    let pure_argument_slot = func_accepts_pure_argument(state, &func)
        || matches!(func.kind, ExprKind::Select { .. })
        || selected_value_method_accepts_pure_next_arg(state, &func);
    let anf_arg = matches!(passing_style, ArgumentPassingStyle::Value)
        && matches!(arg.kind, ExprKind::App { .. });
    let arg_eff_for_slot = if pure_argument_slot || anf_arg {
        state.fresh_exact_pure_eff_tv()
    } else {
        arg.eff
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
            Neg::Var(tv),
        ),
        cause.clone(),
    );
    let callee_edge_id = state.expect_value(
        func.tv,
        expected_callee_tv,
        ExpectedEdgeKind::ApplicationCallee,
        cause.clone(),
    );
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
    state.infer.constrain(Pos::Var(func.eff), Neg::Var(eff));
    state.infer.constrain(Pos::Var(call_eff), Neg::Var(eff));
    if pure_argument_slot || anf_arg {
        state.infer.constrain(Pos::Var(arg.eff), Neg::Var(eff));
    }
    if matches!(&func.kind, ExprKind::Var(def) if state.is_continuation_def(*def)) {
        state.infer.constrain(Pos::Var(arg.eff), Neg::Var(eff));
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

    let result = TypedExpr {
        tv,
        eff,
        kind: ExprKind::App {
            callee: Box::new(func),
            arg: Box::new(arg),
            callee_edge_id: Some(callee_edge_id),
            expected_callee_tv,
            arg_edge_id: Some(arg_edge_id),
            expected_arg_tv,
        },
    };
    register_role_method_call_spine(state, &result);
    result
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
                    recv_tv: recv.tv,
                    arg_tvs: args.iter().map(|arg| arg.tv).collect(),
                    result_tv: expr.tv,
                });
        }
        ExprKind::Var(def) => {
            let Some(info) = role_method_info_for_direct_call_def(state, *def) else {
                return;
            };
            let Some((recv, rest)) = args.split_first() else {
                return;
            };
            state
                .infer
                .push_deferred_role_method_call(DeferredRoleMethodCall {
                    name: info.name,
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
) -> Option<RoleMethodInfo> {
    state
        .infer
        .role_method_info_for_def(def)
        .or_else(|| role_method_info_for_direct_call_path(state, def))
}

fn role_method_info_for_direct_call_path(
    state: &LowerState,
    def: crate::ids::DefId,
) -> Option<RoleMethodInfo> {
    let name = state.def_name(def)?;
    if !state.infer.role_methods.contains_key(name) {
        return None;
    }
    let path = state
        .ctx
        .collect_all_binding_paths()
        .into_iter()
        .find_map(|(path, path_def)| (path_def == def).then_some(path))?;
    role_method_info_for_path(&state.infer.role_methods, &path)
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
    let Some(mut body) = state.principal_bodies.get(&def) else {
        return false;
    };
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
    let Some(mut body) = state.principal_bodies.get(&def) else {
        return false;
    };
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
        Pos::Fun { arg_eff, .. } => super::neg_id_is_pure_row(state, *arg_eff, seen),
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
