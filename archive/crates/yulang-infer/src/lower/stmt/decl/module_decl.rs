use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{TypedBlock, TypedStmt};

use super::super::{child_node, ident_name, lower_block};
use crate::lower::{LowerState, SyntaxNode};

/// `mod foo:` / `mod foo { ... }` を TypedStmt::Module に lower する。
pub(crate) fn lower_mod_decl(state: &mut LowerState, node: &SyntaxNode) -> Option<TypedStmt> {
    let name = ident_name(node)?;
    let def = state.fresh_def();
    let mod_tv = state.fresh_tv();
    state.register_def_tv(def, mod_tv);

    let saved = state.ctx.enter_module(name);
    let block = if let Some(block_node) = child_node(node, SyntaxKind::IndentBlock)
        .or_else(|| child_node(node, SyntaxKind::BraceGroup))
    {
        lower_block(state, &block_node)
    } else {
        TypedBlock {
            tv: state.fresh_tv(),
            eff: state.fresh_tv(),
            stmts: vec![],
            tail: None,
        }
    };
    state.ctx.leave_module(saved);

    Some(TypedStmt::Module(def, block))
}
