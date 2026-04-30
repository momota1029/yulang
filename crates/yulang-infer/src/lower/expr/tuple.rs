use crate::ast::expr::{ExprKind, TypedExpr};
use crate::lower::{LowerState, SyntaxNode};
use crate::types::{Neg, Pos};

use super::lower_expr;

pub(super) fn lower_tuple_expr(state: &mut LowerState, items: Vec<SyntaxNode>) -> TypedExpr {
    let fields = items
        .into_iter()
        .map(|item| lower_expr(state, &item))
        .collect::<Vec<_>>();
    let tv = state.fresh_tv();
    let eff = state.fresh_tv();
    state.infer.constrain(
        state.pos_tuple(fields.iter().map(|field| Pos::Var(field.tv)).collect()),
        Neg::Var(tv),
    );
    state
        .infer
        .constrain(state.infer.arena.empty_pos_row, Neg::Var(eff));
    for field in &fields {
        state.infer.constrain(Pos::Var(field.eff), Neg::Var(eff));
    }
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Tuple(fields),
    }
}
