use crate::ids::{PosId, TypeVar};
use crate::scheme::FrozenScheme;
use crate::simplify::compact::CompactTypeScheme;
use crate::types::arena::TypeArena;
use crate::types::{Neg, Pos};

use super::Infer;
use super::compact_var::{common_compact_var, single_compact_var};

pub(super) fn first_fun_arg_var_in_scheme(
    _infer: &Infer,
    scheme: &FrozenScheme,
) -> Option<TypeVar> {
    first_fun_arg_var_in_compact(&scheme.compact)
        .or_else(|| first_fun_arg_var_in_arena(&scheme.arena, scheme.body))
}

fn first_fun_arg_var_in_compact(scheme: &CompactTypeScheme) -> Option<TypeVar> {
    let [lower_fun] = scheme.cty.lower.funs.as_slice() else {
        return None;
    };
    let [upper_fun] = scheme.cty.upper.funs.as_slice() else {
        return single_compact_var(&lower_fun.arg);
    };
    common_compact_var(&lower_fun.arg, &upper_fun.arg)
        .or_else(|| single_compact_var(&lower_fun.arg))
}

fn first_fun_arg_var_in_arena(arena: &TypeArena, pos: PosId) -> Option<TypeVar> {
    match arena.get_pos(pos) {
        Pos::Fun { arg, .. } => match arena.get_neg(arg) {
            Neg::Var(tv) => Some(tv),
            _ => None,
        },
        Pos::Union(lhs, rhs) => first_fun_arg_var_in_arena(arena, lhs)
            .or_else(|| first_fun_arg_var_in_arena(arena, rhs)),
        _ => None,
    }
}
