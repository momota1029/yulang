use super::super::cast::{collect_cast_sig_vars, constrain_cast_arg_source};
use super::*;

use crate::types::{Neg, Pos};

pub(crate) fn lower_synthetic_error_wrap(
    state: &mut LowerState,
    error_sig: &SigType,
    variants: &[ErrorThrowVariant],
    visibility: crate::symbols::Visibility,
) {
    if variants.is_empty() {
        return;
    }
    let Some(result_ok_def) = resolve_std_result_constructor(state, "ok") else {
        return;
    };
    let Some(result_err_def) = resolve_std_result_constructor(state, "err") else {
        return;
    };

    let wrap_name = Name("wrap".to_string());
    let wrap_def = state.fresh_def();
    let wrap_tv = state.fresh_tv();
    state.register_def_tv(wrap_def, wrap_tv);
    state.mark_let_bound_def(wrap_def);
    state.register_def_name(wrap_def, wrap_name.clone());
    state.insert_value_with_visibility(state.ctx.current_module, wrap_name, wrap_def, visibility);

    let mut scope_names = Vec::new();
    collect_cast_sig_vars(error_sig, &mut scope_names);
    let impl_scope = fresh_type_scope(state, &scope_names);
    state.with_owner(wrap_def, |state| {
        lower_synthetic_error_wrap_body(
            state,
            wrap_def,
            wrap_tv,
            error_sig,
            variants,
            result_ok_def,
            result_err_def,
            &impl_scope,
        );
    });
}

fn lower_synthetic_error_wrap_body(
    state: &mut LowerState,
    wrap_def: crate::ids::DefId,
    wrap_tv: TypeVar,
    error_sig: &SigType,
    variants: &[ErrorThrowVariant],
    result_ok_def: crate::ids::DefId,
    result_err_def: crate::ids::DefId,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let action_def = state.fresh_def();
    let action_tv = state.fresh_tv();
    let action_eff = state.fresh_tv();
    let action_name = Name("action".to_string());
    state.register_def_tv(action_def, action_tv);
    state.register_def_eff_tv(action_def, action_eff);
    state.register_def_name(action_def, action_name.clone());
    state.register_def_owner(action_def, wrap_def);

    let result_tv = state.fresh_tv();
    let result_eff = state.fresh_tv();
    constrain_error_wrap_effect(state, action_eff, result_eff, error_sig, impl_scope);
    constrain_error_wrap_result(state, result_tv, error_sig, impl_scope);

    let comp = TypedExpr {
        tv: action_tv,
        eff: action_eff,
        kind: ExprKind::Var(action_def),
    };
    let mut arms = variants
        .iter()
        .filter_map(|variant| {
            synthetic_error_wrap_effect_arm(
                state,
                variant,
                result_tv,
                result_eff,
                result_err_def,
                wrap_def,
                impl_scope,
            )
        })
        .collect::<Vec<_>>();
    arms.push(synthetic_error_wrap_value_arm(
        state,
        action_tv,
        result_tv,
        result_eff,
        result_ok_def,
        wrap_def,
    ));
    let body = TypedExpr {
        tv: result_tv,
        eff: result_eff,
        kind: ExprKind::Catch(Box::new(comp), arms),
    };

    let principal_body = wrap_header_lambdas(
        state,
        body.clone(),
        vec![ArgPatInfo {
            def: action_def,
            tv: action_tv,
            arg_eff_tv: action_eff,
            read_eff_tv: Some(action_eff),
            pat: Some(TypedPat {
                tv: action_tv,
                kind: PatKind::UnresolvedName(action_name.clone()),
            }),
            local_bindings: vec![(action_name, action_def)],
            ann: None,
            unit_arg: false,
        }],
    );
    state.insert_principal_body(wrap_def, principal_body.clone());
    state
        .infer
        .constrain(Pos::Var(principal_body.tv), Neg::Var(wrap_tv));
    state
        .infer
        .constrain(Pos::Var(wrap_tv), Neg::Var(principal_body.tv));
}

fn synthetic_error_wrap_value_arm(
    state: &mut LowerState,
    action_tv: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
    result_ok_def: crate::ids::DefId,
    wrap_def: crate::ids::DefId,
) -> TypedCatchArm {
    let value_def = state.fresh_def();
    let value_tv = state.fresh_tv();
    let value_name = Name("value".to_string());
    state.register_def_tv(value_def, value_tv);
    state.register_def_name(value_def, value_name);
    state.register_def_owner(value_def, wrap_def);
    let pat = TypedPat {
        tv: value_tv,
        kind: PatKind::As(
            Box::new(TypedPat {
                tv: value_tv,
                kind: PatKind::Wild,
            }),
            value_def,
        ),
    };
    state.infer.constrain(Pos::Var(action_tv), Neg::Var(pat.tv));
    state.infer.constrain(Pos::Var(pat.tv), Neg::Var(action_tv));

    let ok = crate::lower::expr::resolve_bound_def_expr(state, result_ok_def);
    let value = TypedExpr {
        tv: value_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Var(value_def),
    };
    let body = crate::lower::expr::make_app(state, ok, value);
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            result_tv,
            result_eff,
            ExpectedEdgeKind::CatchBranch,
            ConstraintCause {
                span: None,
                reason: ConstraintReason::CatchBranch,
            },
            true,
        )
        .0;
    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, body.eff);

    TypedCatchArm {
        tv: state.fresh_tv(),
        guard: None,
        kind: CatchArmKind::Value(pat, body),
    }
}

fn synthetic_error_wrap_effect_arm(
    state: &mut LowerState,
    variant: &ErrorThrowVariant,
    result_tv: TypeVar,
    result_eff: TypeVar,
    result_err_def: crate::ids::DefId,
    wrap_def: crate::ids::DefId,
    impl_scope: &HashMap<String, TypeVar>,
) -> Option<TypedCatchArm> {
    let op_path = effect_operation_surface_path(state, variant.operation_def)?;
    let (pat, error_value) = if let Some(payload_sig) = &variant.payload_sig {
        let payload_def = state.fresh_def();
        let payload_tv = state.fresh_tv();
        state.register_def_tv(payload_def, payload_tv);
        state.register_def_name(payload_def, Name("payload".to_string()));
        state.register_def_owner(payload_def, wrap_def);
        constrain_cast_arg_source(state, payload_tv, payload_sig, impl_scope);
        let pat = TypedPat {
            tv: payload_tv,
            kind: PatKind::As(
                Box::new(TypedPat {
                    tv: payload_tv,
                    kind: PatKind::Wild,
                }),
                payload_def,
            ),
        };
        let payload = TypedExpr {
            tv: payload_tv,
            eff: state.fresh_exact_pure_eff_tv(),
            kind: ExprKind::Var(payload_def),
        };
        let constructor =
            crate::lower::expr::resolve_bound_def_expr(state, variant.constructor_def);
        (
            pat,
            crate::lower::expr::make_app(state, constructor, payload),
        )
    } else {
        (
            TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Lit(crate::ast::expr::Lit::Unit),
            },
            crate::lower::expr::resolve_bound_def_expr(state, variant.constructor_def),
        )
    };

    let err = crate::lower::expr::resolve_bound_def_expr(state, result_err_def);
    let body = crate::lower::expr::make_app(state, err, error_value);
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            result_tv,
            result_eff,
            ExpectedEdgeKind::CatchBranch,
            ConstraintCause {
                span: None,
                reason: ConstraintReason::CatchBranch,
            },
            true,
        )
        .0;
    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, body.eff);

    let k = state.fresh_def();
    let k_tv = state.fresh_tv();
    state.register_def_tv(k, k_tv);
    state.mark_continuation_def(k);
    state.register_def_owner(k, wrap_def);

    Some(TypedCatchArm {
        tv: state.fresh_tv(),
        guard: None,
        kind: CatchArmKind::Effect {
            op_path,
            pat,
            k,
            body,
        },
    })
}

fn constrain_error_wrap_effect(
    state: &mut LowerState,
    action_eff: TypeVar,
    result_eff: TypeVar,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let Some(atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    state.infer.constrain(
        state.pos_row(vec![Pos::Atom(atom.clone())], Pos::Bot),
        Neg::Var(action_eff),
    );
    state.infer.constrain(
        Pos::Var(action_eff),
        state.neg_row(vec![Neg::Atom(atom)], Neg::Top),
    );
    state
        .infer
        .constrain(state.pos_row(vec![], Pos::Bot), Neg::Var(result_eff));
    state
        .infer
        .constrain(Pos::Var(result_eff), state.neg_row(vec![], Neg::Top));
}

fn constrain_error_wrap_result(
    state: &mut LowerState,
    result_tv: TypeVar,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let mut result_scope = impl_scope.clone();
    let ok_var = "__wrap_ok".to_string();
    result_scope
        .entry(ok_var.clone())
        .or_insert_with(|| state.fresh_tv());
    let target = SigType::Apply {
        path: Path {
            segments: vec![
                Name("std".to_string()),
                Name("result".to_string()),
                Name("result".to_string()),
            ],
        },
        args: vec![
            SigType::Var(SigVar {
                name: ok_var,
                span: error_sig.span(),
            }),
            error_sig.clone(),
        ],
        span: error_sig.span(),
    };
    let mut pos_scope = result_scope.clone();
    let mut neg_scope = result_scope;
    let target_pos = lower_pure_sig_pos_id(state, &target, &mut pos_scope);
    let target_neg = lower_pure_sig_neg_id(state, &target, &mut neg_scope);
    state.infer.constrain(target_pos, Neg::Var(result_tv));
    state.infer.constrain(Pos::Var(result_tv), target_neg);
}

fn resolve_std_result_constructor(state: &LowerState, name: &str) -> Option<crate::ids::DefId> {
    let std_path = Path {
        segments: vec![
            Name("std".to_string()),
            Name("result".to_string()),
            Name("result".to_string()),
            Name(name.to_string()),
        ],
    };
    state.ctx.resolve_path_value(&std_path).or_else(|| {
        state.ctx.resolve_path_value(&Path {
            segments: vec![Name("result".to_string()), Name(name.to_string())],
        })
    })
}
