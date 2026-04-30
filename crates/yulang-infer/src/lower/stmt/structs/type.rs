use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};
use crate::types::{Neg, Pos};

pub(crate) fn lower_struct_field_type(
    state: &mut LowerState,
    field: &SyntaxNode,
    type_scope: &HashMap<String, TypeVar>,
) -> Option<(Pos, Neg)> {
    let type_expr = super::super::child_node(field, SyntaxKind::TypeExpr)?;
    let sig = crate::lower::signature::parse_sig_type_expr(&type_expr)?;
    let mut pos_vars = type_scope.clone();
    let mut neg_vars = type_scope.clone();
    Some((
        crate::lower::signature::lower_pure_sig_type(state, &sig, &mut pos_vars),
        crate::lower::signature::lower_pure_sig_neg_type(state, &sig, &mut neg_vars),
    ))
}

pub(crate) fn invariant_args(vars: &[TypeVar]) -> Vec<(Pos, Neg)> {
    vars.iter()
        .map(|tv| (Pos::Var(*tv), Neg::Var(*tv)))
        .collect()
}
