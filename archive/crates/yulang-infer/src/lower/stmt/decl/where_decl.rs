use crate::lower::{LowerState, SyntaxNode};

pub(crate) fn lower_where_clause(state: &mut LowerState, node: &SyntaxNode) {
    crate::lower::where_clause::lower_where_clause(state, node);
}
