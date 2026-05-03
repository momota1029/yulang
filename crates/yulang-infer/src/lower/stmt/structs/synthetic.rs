use crate::ast::expr::{ExprKind, PatKind, TypedExpr, TypedPat};
use crate::ids::{DefId, TypeVar};
use crate::lower::LowerState;
use crate::symbols::{Name, Path};
use crate::types::RecordField;
use crate::types::{Neg, Pos};

pub(crate) fn synthetic_struct_constructor_body(
    state: &mut LowerState,
    ctor_def: DefId,
) -> TypedExpr {
    let arg_def = state.fresh_def();
    let arg_tv = state.fresh_tv();
    let ret_tv = state.fresh_tv();
    let arg_name = Name("value".to_string());
    state.register_def_tv(arg_def, arg_tv);
    state.register_def_name(arg_def, arg_name.clone());
    state.register_def_owner(arg_def, ctor_def);

    let body_eff = state.fresh_exact_pure_eff_tv();
    let arg_expr_eff = state.fresh_exact_pure_eff_tv();
    let body = state.representation_coerce(
        arg_tv,
        ret_tv,
        body_eff,
        TypedExpr {
            tv: arg_tv,
            eff: arg_expr_eff,
            kind: ExprKind::Var(arg_def),
        },
    );
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    super::super::wrap_header_lambdas(
        state,
        body,
        vec![super::super::ArgPatInfo {
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
            unit_arg: false,
        }],
    )
}

pub(crate) fn synthetic_struct_field_body(
    state: &mut LowerState,
    struct_path: &Path,
    type_arg_tvs: &[TypeVar],
    record_fields: &[(Name, Pos, Neg)],
    field_def: DefId,
    field_name: &Name,
) -> TypedExpr {
    let recv_def = state.fresh_def();
    let recv_tv = state.fresh_tv();
    let record_tv = state.fresh_tv();
    let recv_name = Name("recv".to_string());
    state.register_def_tv(recv_def, recv_tv);
    state.register_def_name(recv_def, recv_name.clone());
    state.register_def_owner(recv_def, field_def);
    state.infer.constrain(
        state.pos_con(
            struct_path.clone(),
            super::super::invariant_args(type_arg_tvs),
        ),
        Neg::Var(recv_tv),
    );
    state.infer.constrain(
        Pos::Var(recv_tv),
        state.neg_con(
            struct_path.clone(),
            super::super::invariant_args(type_arg_tvs),
        ),
    );
    state.infer.constrain(
        state.pos_record(
            record_fields
                .iter()
                .map(|(name, pos, _)| RecordField::required(name.clone(), pos.clone()))
                .collect(),
        ),
        Neg::Var(record_tv),
    );
    state.infer.constrain(
        Pos::Var(record_tv),
        state.neg_record(
            record_fields
                .iter()
                .map(|(name, _, neg)| RecordField::required(name.clone(), neg.clone()))
                .collect(),
        ),
    );

    let recv_coerce_eff = state.fresh_exact_pure_eff_tv();
    let recv_expr_eff = state.fresh_exact_pure_eff_tv();
    let recv = state.representation_coerce(
        recv_tv,
        record_tv,
        recv_coerce_eff,
        TypedExpr {
            tv: recv_tv,
            eff: recv_expr_eff,
            kind: ExprKind::Var(recv_def),
        },
    );

    let body = TypedExpr {
        tv: state.fresh_tv(),
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Select {
            recv: Box::new(recv),
            name: field_name.clone(),
        },
    };
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    super::super::wrap_header_lambdas(
        state,
        body,
        vec![super::super::ArgPatInfo {
            def: recv_def,
            tv: recv_tv,
            arg_eff_tv,
            read_eff_tv: None,
            pat: Some(TypedPat {
                tv: recv_tv,
                kind: PatKind::UnresolvedName(recv_name.clone()),
            }),
            local_bindings: vec![(recv_name, recv_def)],
            ann: None,
            unit_arg: false,
        }],
    )
}
