use crate::profile::ProfileClock as Instant;

use super::super::{direct_param_source_eff_tv, lambda_expr_eff_tv};
use super::arg::{ArgPatInfo, configure_read_effect_from_ann};
use crate::ast::expr::{ExprKind, TypedExpr};
use crate::lower::LowerState;
use crate::types::{Neg, Pos};

pub(crate) fn wrap_header_lambdas(
    state: &mut LowerState,
    raw_body: TypedExpr,
    arg_pats: Vec<ArgPatInfo>,
) -> TypedExpr {
    let start = Instant::now();
    let header_local_defs = arg_pats
        .iter()
        .flat_map(|arg_pat| {
            std::iter::once(arg_pat.def).chain(
                arg_pat
                    .local_bindings
                    .iter()
                    .map(|(_, local_def)| *local_def),
            )
        })
        .collect::<Vec<_>>();
    let result = arg_pats.into_iter().rev().fold(raw_body, |body, arg_pat| {
        let def = arg_pat.def;
        let param_tv = arg_pat.tv;
        let tv = state.fresh_tv();
        let arg_eff_tv = arg_pat.arg_eff_tv;
        if arg_pat.unit_arg {
            state
                .infer
                .constrain(super::super::prim_type("unit"), Neg::Var(param_tv));
            state
                .infer
                .constrain(Pos::Var(param_tv), super::super::neg_prim_type("unit"));
        }
        super::super::configure_arg_effect_from_ann(state, arg_eff_tv, arg_pat.ann.as_ref());
        if let Some(read_eff_tv) = arg_pat.read_eff_tv {
            if read_eff_tv != arg_eff_tv {
                if let Some(ann) = arg_pat.ann.as_ref() {
                    configure_read_effect_from_ann(state, read_eff_tv, ann);
                }
            }
        }
        if let Some(pat) = &arg_pat.pat {
            state.infer.constrain(Pos::Var(param_tv), Neg::Var(pat.tv));
            state.infer.constrain(Pos::Var(pat.tv), Neg::Var(param_tv));
            state.register_lambda_param_pat(def, pat.clone());
            state.register_lambda_local_defs(
                def,
                arg_pat
                    .local_bindings
                    .iter()
                    .map(|(_, local_def)| *local_def)
                    .collect(),
            );
            state.ctx.push_local();
            for (name, def) in &arg_pat.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
            }
            super::super::connect_pat_shape_and_locals(state, pat, body.eff);
            state.ctx.pop_local();
        }
        if matches!(
            arg_pat.ann.as_ref().and_then(|ann| ann.eff.as_ref()),
            Some(super::super::LoweredEffAnn::Opaque)
        ) {
            let source_eff = direct_param_source_eff_tv(&body, def).unwrap_or(body.eff);
            state
                .infer
                .constrain(Pos::Var(source_eff), Neg::Var(arg_eff_tv));
            state
                .infer
                .constrain(Pos::Var(arg_eff_tv), Neg::Var(source_eff));
        }
        let ret_eff_tv = if matches!(body.kind, ExprKind::Lam(_, _)) {
            state.fresh_exact_pure_eff_tv()
        } else {
            body.eff
        };
        state.infer.constrain(
            state.pos_fun(
                Neg::Var(param_tv),
                Neg::Var(arg_eff_tv),
                Pos::Var(ret_eff_tv),
                Pos::Var(body.tv),
            ),
            Neg::Var(tv),
        );
        let mut local_defs = vec![def];
        local_defs.extend(
            arg_pat
                .local_bindings
                .iter()
                .map(|(_, local_def)| *local_def),
        );
        local_defs.extend(header_local_defs.iter().copied());
        let eff = lambda_expr_eff_tv(state, &body, &local_defs);
        TypedExpr {
            tv,
            eff,
            kind: ExprKind::Lam(def, Box::new(body)),
        }
    });
    state.lower_detail.wrap_header_lambdas += start.elapsed();
    result
}
