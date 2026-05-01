use std::collections::HashSet;

use crate::ids::DefId;
use crate::lower::LowerState;
use crate::types::{Neg, Pos};

use super::ArgPatInfo;

pub(crate) fn preconstrain_recursive_binding_header_shape(
    state: &mut LowerState,
    owner: DefId,
    arg_pats: &[ArgPatInfo],
) {
    if arg_pats.is_empty() {
        return;
    }
    let Some(&owner_tv) = state.def_tvs.get(&owner) else {
        return;
    };
    let non_generic_roots = arg_pats
        .iter()
        .flat_map(|arg_pat| {
            std::iter::once(arg_pat.tv)
                .chain(std::iter::once(arg_pat.arg_eff_tv))
                .chain(arg_pat.read_eff_tv)
        })
        .collect::<HashSet<_>>();

    let mut ret_tv = state.fresh_tv();
    let mut ret_eff = state.fresh_tv();
    for arg_pat in arg_pats.iter().rev() {
        let fun_tv = state.fresh_tv();
        state.infer.constrain(
            state.pos_fun(
                Neg::Var(arg_pat.tv),
                Neg::Var(arg_pat.arg_eff_tv),
                Pos::Var(ret_eff),
                Pos::Var(ret_tv),
            ),
            Neg::Var(fun_tv),
        );
        ret_tv = fun_tv;
        ret_eff = state.fresh_exact_pure_eff_tv();
    }

    state.infer.constrain(Pos::Var(owner_tv), Neg::Var(ret_tv));
    state.infer.constrain(Pos::Var(ret_tv), Neg::Var(owner_tv));
    state.provisional_self_root_tvs.insert(owner, ret_tv);
    let frozen =
        crate::scheme::freeze_type_var_with_non_generic(&state.infer, ret_tv, &non_generic_roots);
    state.provisional_self_schemes.insert(owner, frozen);
}
