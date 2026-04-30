use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, Lit, TypedExpr};
use crate::lower::{LowerState, SyntaxNode};

/// BindingBody ノードの中身を lower する。
/// IndentBlock / BraceGroup / Expr のいずれかを含む。
pub(crate) fn lower_binding_body(state: &mut LowerState, body: &SyntaxNode) -> TypedExpr {
    let start = Instant::now();
    let result = (|| {
        let block_node = super::super::child_node(body, SyntaxKind::IndentBlock)
            .or_else(|| super::super::child_node(body, SyntaxKind::BraceGroup));
        if let Some(block_node) = block_node {
            let typed_block = super::super::lower_block(state, &block_node);
            return TypedExpr {
                tv: typed_block.tv,
                eff: typed_block.eff,
                kind: ExprKind::Block(typed_block),
            };
        }
        if let Some(expr_node) = super::super::child_node(body, SyntaxKind::Expr) {
            return crate::lower::expr::lower_expr(state, &expr_node);
        }
        let tv = state.fresh_tv();
        let eff = state.fresh_tv();
        TypedExpr {
            tv,
            eff,
            kind: ExprKind::Lit(Lit::Unit),
        }
    })();
    state.lower_detail.lower_binding_body += start.elapsed();
    result
}
