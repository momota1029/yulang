use crate::lower::builtin_types::builtin_source_type_path;
use crate::types::{Neg, Pos};

/// プリミティブ型名から Pos::Con を作る。
pub(in crate::lower::expr) fn prim_type(name: &str) -> Pos {
    if name == "never" {
        return Pos::Bot;
    }
    Pos::Con(builtin_source_type_path(name), vec![])
}

pub(in crate::lower::expr) fn neg_prim_type(name: &str) -> Neg {
    if name == "never" {
        return Neg::Top;
    }
    Neg::Con(builtin_source_type_path(name), vec![])
}
