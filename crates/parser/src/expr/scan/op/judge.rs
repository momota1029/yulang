use crate::op::{OpKindSet, OpUse};

pub fn judge_nud(
    mut kinds: OpKindSet,
    pre_ws: bool,
    post_ws: bool,
    probe_value_start: bool,
) -> Option<OpUse> {
    kinds -= OpKindSet::INFIX | OpKindSet::SUFFIX;
    if !probe_value_start {
        kinds -= OpKindSet::PREFIX;
    }
    table(kinds, pre_ws, post_ws)
}

pub fn judge_led(
    mut kinds: OpKindSet,
    pre_ws: bool,
    post_ws: bool,
    probe_value_start: bool,
) -> Option<OpUse> {
    if !probe_value_start {
        kinds -= OpKindSet::PREFIX | OpKindSet::INFIX;
    }
    let mut ml_arg_kinds = kinds;
    if post_ws {
        ml_arg_kinds -= OpKindSet::PREFIX;
    }
    table(ml_arg_kinds, pre_ws, post_ws).or_else(|| table(kinds, pre_ws, post_ws))
}

fn table(kinds: OpKindSet, pre_ws: bool, post_ws: bool) -> Option<OpUse> {
    const P: Option<OpUse> = Some(OpUse::Prefix);
    const I: Option<OpUse> = Some(OpUse::Infix);
    const S: Option<OpUse> = Some(OpUse::Suffix);
    const N: Option<OpUse> = Some(OpUse::Nullfix);
    const X: Option<OpUse> = None;

    const NORMAL_TABLE: [[Option<OpUse>; 4]; 16] = [
        [X, X, X, X],
        [P, P, P, P],
        [I, I, I, I],
        [I, I, P, I],
        [S, S, S, S],
        [X, S, P, X],
        [I, S, I, I],
        [I, S, P, I],
        [N, N, N, N],
        [P, N, P, N],
        [I, I, I, N],
        [I, I, P, N],
        [N, S, N, N],
        [N, S, P, N],
        [I, S, I, N],
        [I, S, P, N],
    ];

    fn kinds_bits(kinds: OpKindSet) -> usize {
        let mut bits = 0u8;
        if kinds.contains(OpKindSet::PREFIX) {
            bits |= 1 << 0;
        }
        if kinds.contains(OpKindSet::INFIX) {
            bits |= 1 << 1;
        }
        if kinds.contains(OpKindSet::SUFFIX) {
            bits |= 1 << 2;
        }
        if kinds.contains(OpKindSet::NULLFIX) {
            bits |= 1 << 3;
        }
        bits as usize
    }

    fn ws_bits(pre_ws: bool, post_ws: bool) -> usize {
        ((pre_ws as usize) << 1) | (post_ws as usize)
    }

    NORMAL_TABLE[kinds_bits(kinds)][ws_bits(pre_ws, post_ws)]
}
