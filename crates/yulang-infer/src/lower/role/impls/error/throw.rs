use super::super::cast::{
    collect_cast_sig_vars, constrain_cast_arg_source, constrain_cast_result_target,
    render_cast_impl_args,
};
use super::*;

use crate::types::{Neg, Pos};

pub(crate) fn lower_synthetic_error_throw(
    state: &mut LowerState,
    error_sig: &SigType,
    variants: Vec<ErrorThrowVariant>,
) {
    if variants.is_empty() {
        return;
    }

    let impl_def = state.fresh_def();
    let role = throw_role_path(state);
    let role_infos = state.infer.role_arg_infos_of(&role);
    let mut impl_scope_names = Vec::new();
    collect_cast_sig_vars(error_sig, &mut impl_scope_names);
    for info in &role_infos {
        if !impl_scope_names.contains(&info.name) {
            impl_scope_names.push(info.name.clone());
        }
    }
    let impl_scope = fresh_type_scope(state, &impl_scope_names);
    let throw_name = Name("throw".to_string());
    let method_def = state.fresh_def();
    let method_tv = state.fresh_tv();
    state.register_def_tv(method_def, method_tv);
    state.mark_let_bound_def(method_def);
    state.register_def_owner(method_def, impl_def);
    state.register_def_name(method_def, throw_name.clone());

    let helper_module = state.ctx.modules.new_module();
    state.insert_module(
        state.ctx.current_module,
        Name(format!("&throw#{}", impl_def.0)),
        helper_module,
    );
    state.insert_value(helper_module, throw_name.clone(), method_def);

    state.with_type_scope(impl_scope.clone(), |state| {
        state.with_owner(impl_def, |state| {
            lower_synthetic_error_throw_body(
                state,
                method_def,
                method_tv,
                error_sig,
                &variants,
                &impl_scope,
            );
        });
    });

    let prerequisites = compact_role_constraints(&state.infer, impl_def);
    let throws_sig = SigType::Row {
        row: SigRow {
            items: vec![error_sig.clone()],
            tail: None,
        },
        span: error_sig.span(),
    };
    let assoc_eqs = HashMap::from([("throws".to_string(), throws_sig)]);
    let (args, compact_args) = render_cast_impl_args(
        state,
        &role_infos,
        std::slice::from_ref(error_sig),
        &assoc_eqs,
        &impl_scope,
    );
    state.infer.register_role_impl_candidate(RoleImplCandidate {
        role,
        args,
        compact_args,
        prerequisites,
        member_defs: HashMap::from([(throw_name, method_def)]),
    });
}

fn lower_synthetic_error_throw_body(
    state: &mut LowerState,
    method_def: crate::ids::DefId,
    method_tv: TypeVar,
    error_sig: &SigType,
    variants: &[ErrorThrowVariant],
    impl_scope: &HashMap<String, TypeVar>,
) {
    let arg_def = state.fresh_def();
    let arg_tv = state.fresh_tv();
    let arg_name = Name("error".to_string());
    state.register_def_tv(arg_def, arg_tv);
    state.register_def_name(arg_def, arg_name.clone());
    state.register_def_owner(arg_def, method_def);
    constrain_cast_arg_source(state, arg_tv, error_sig, impl_scope);

    let match_tv = state.fresh_tv();
    let match_eff = state.fresh_tv();
    constrain_exact_error_effect(state, match_eff, error_sig, impl_scope);
    let scrutinee = TypedExpr {
        tv: arg_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Var(arg_def),
    };
    let arms = variants
        .iter()
        .map(|variant| {
            synthetic_error_throw_arm(state, variant, arg_tv, match_tv, match_eff, method_def)
        })
        .collect::<Vec<_>>();
    let body = TypedExpr {
        tv: match_tv,
        eff: match_eff,
        kind: ExprKind::Match(Box::new(scrutinee), arms),
    };
    constrain_cast_result_target(state, body.tv, &never_sig(error_sig.span()), impl_scope);

    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    let principal_body = wrap_header_lambdas(
        state,
        body.clone(),
        vec![ArgPatInfo {
            def: arg_def,
            tv: arg_tv,
            arg_eff_tv,
            read_eff_tv: None,
            pat: Some(TypedPat {
                tv: arg_tv,
                kind: PatKind::UnresolvedName(arg_name.clone()),
            }),
            local_bindings: vec![(arg_name, arg_def)],
            ann: None,
            ann_non_generic_tvs: Vec::new(),
            unit_arg: false,
        }],
    );
    state.insert_principal_body(method_def, principal_body.clone());
    state
        .infer
        .constrain(Pos::Var(principal_body.tv), Neg::Var(method_tv));
    state
        .infer
        .constrain(Pos::Var(method_tv), Neg::Var(principal_body.tv));
    let constrained_sig = state.infer.alloc_pos(Pos::Fun {
        arg: state.infer.alloc_neg(Neg::Var(arg_tv)),
        arg_eff: state.infer.arena.empty_neg_row,
        ret_eff: state.infer.alloc_pos(Pos::Var(body.eff)),
        ret: state.infer.alloc_pos(Pos::Var(body.tv)),
    });
    state.infer.constrain(constrained_sig, Neg::Var(method_tv));
    state.infer.constrain(
        Pos::Var(method_tv),
        state.infer.alloc_neg(Neg::Fun {
            arg: state.infer.alloc_pos(Pos::Var(arg_tv)),
            arg_eff: state.infer.arena.empty_pos_row,
            ret_eff: state.infer.alloc_neg(Neg::Var(body.eff)),
            ret: state.infer.alloc_neg(Neg::Var(body.tv)),
        }),
    );
    store_synthetic_error_throw_scheme(state, method_def, error_sig, impl_scope);
    state.runtime_export_schemes.insert(
        method_def,
        synthetic_error_throw_runtime_scheme(state, error_sig),
    );
}

fn synthetic_error_throw_arm(
    state: &mut LowerState,
    variant: &ErrorThrowVariant,
    scrutinee_tv: TypeVar,
    match_tv: TypeVar,
    match_eff: TypeVar,
    method_def: crate::ids::DefId,
) -> TypedMatchArm {
    let pat_tv = state.fresh_tv();
    let ctor_ref =
        crate::lower::stmt::resolve_pattern_constructor_ref(state, variant.constructor_def);
    let (pat, body) = if variant.payload_sig.is_some() {
        let payload_def = state.fresh_def();
        let payload_tv = state.fresh_tv();
        let payload_name = Name("value".to_string());
        state.register_def_tv(payload_def, payload_tv);
        state.register_def_name(payload_def, payload_name);
        state.register_def_owner(payload_def, method_def);
        let payload_pat = TypedPat {
            tv: payload_tv,
            kind: PatKind::As(
                Box::new(TypedPat {
                    tv: payload_tv,
                    kind: PatKind::Wild,
                }),
                payload_def,
            ),
        };
        let pat = TypedPat {
            tv: pat_tv,
            kind: PatKind::Con(ctor_ref, Some(Box::new(payload_pat))),
        };
        let op = crate::lower::expr::resolve_bound_def_expr(state, variant.operation_def);
        let payload = TypedExpr {
            tv: payload_tv,
            eff: state.fresh_exact_pure_eff_tv(),
            kind: ExprKind::Var(payload_def),
        };
        (pat, crate::lower::expr::make_app(state, op, payload))
    } else {
        (
            TypedPat {
                tv: pat_tv,
                kind: PatKind::Con(ctor_ref, None),
            },
            crate::lower::expr::resolve_bound_def_expr(state, variant.operation_def),
        )
    };

    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, match_eff);
    state
        .infer
        .constrain(Pos::Var(scrutinee_tv), Neg::Var(pat.tv));
    state
        .infer
        .constrain(Pos::Var(pat.tv), Neg::Var(scrutinee_tv));
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            match_tv,
            match_eff,
            ExpectedEdgeKind::MatchBranch,
            ConstraintCause::unknown(),
            true,
        )
        .0;

    TypedMatchArm {
        pat,
        guard: None,
        body,
    }
}

fn constrain_exact_error_effect(
    state: &mut LowerState,
    eff_tv: TypeVar,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let Some(atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    state.infer.constrain(
        state.pos_row(vec![Pos::Atom(atom.clone())], Pos::Bot),
        Neg::Var(eff_tv),
    );
    state.infer.constrain(
        Pos::Var(eff_tv),
        state.neg_row(vec![Neg::Atom(atom)], Neg::Top),
    );
}

fn store_synthetic_error_throw_scheme(
    state: &mut LowerState,
    method_def: crate::ids::DefId,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let Some(atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    let mut pos_scope = impl_scope.clone();
    let mut neg_scope = impl_scope.clone();
    let arg = lower_pure_sig_neg_id(state, error_sig, &mut neg_scope);
    let ret = lower_pure_sig_pos_id(state, &never_sig(error_sig.span()), &mut pos_scope);
    let scheme_pos = state.infer.alloc_pos(Pos::Fun {
        arg,
        arg_eff: state.infer.arena.empty_neg_row,
        ret_eff: state
            .infer
            .alloc_pos(state.pos_row(vec![Pos::Atom(atom)], Pos::Bot)),
        ret,
    });
    state.infer.store_frozen_scheme(
        method_def,
        crate::scheme::freeze_pos_scheme(&state.infer, scheme_pos),
    );
}

fn synthetic_error_throw_runtime_scheme(
    state: &LowerState,
    error_sig: &SigType,
) -> typed_ir::Scheme {
    typed_ir::Scheme {
        requirements: Vec::new(),
        body: typed_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, error_sig)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(core_error_effect_type(state, error_sig)),
            ret: Box::new(export_runtime_sig_type(state, &never_sig(error_sig.span()))),
        },
    }
}

fn core_error_effect_type(state: &LowerState, error_sig: &SigType) -> typed_ir::Type {
    typed_ir::Type::Row {
        items: vec![export_runtime_sig_type(state, error_sig)],
        tail: Box::new(typed_ir::Type::Never),
    }
}

fn throw_role_path(state: &LowerState) -> Path {
    canonical_role_path(
        state,
        &Path {
            segments: vec![Name("Throw".to_string())],
        },
    )
}
