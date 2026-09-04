//! Direct normal-expression statements and their indented sequence owner.

use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn,
    driver::{
        Either, TailExit, expr_from_nud, handoff, indentation_after_newline, is_normal_core_item,
    },
    emit::emit_leading_trivia,
    item::Item,
    lexer::{scan_trivia, tail_item_after_trivia},
};

/// The first reusable direct `Statement` callee. Its current normal subset is
/// deliberately the same direct core accepted by C1/C2 entry evidence.
pub(super) fn expression_statement(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: u8,
) -> TailExit {
    debug_assert!(is_normal_core_item(&item));
    i.state.start_node(SyntaxKind::Statement.into());
    let exit = expr_from_nud(
        i.rb(),
        item,
        None,
        baseline,
        stops,
        super::driver::MlMode::All,
    );
    i.state.finish_node();
    exit
}

/// A normal-only construction callee for the future canonical statement
/// sequence. It owns its opening trivia and equal-indent separators; dedent
/// and unimplemented statement starts remain complete pending Items.
pub(super) fn indented_statement_block(
    mut i: RewriteIn,
    base_indent: usize,
    stops: u8,
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let block_indent = indentation_after_newline(&opening)
        .filter(|&indentation| indentation > base_indent)
        .expect("C2 admission proved a strictly indented block opening");

    i.state
        .start_node(SyntaxKind::IndentedStatementBlock.into());
    emit_leading_trivia(&mut i, &opening);
    let item = statement_item_after_opening(i.rb(), block_indent, stops);
    let exit = expression_statement(i.rb(), item, block_indent, stops);
    let exit = indented_statement_successor(i.rb(), exit, block_indent, stops);
    i.state.finish_node();
    exit
}

fn indented_statement_successor(
    mut i: RewriteIn,
    mut exit: TailExit,
    block_indent: usize,
    stops: u8,
) -> TailExit {
    loop {
        let Err(Either::Left(mut item)) = exit else {
            return exit;
        };
        if indentation_after_newline(&item.leading) != Some(block_indent)
            || !is_normal_core_item(&item)
        {
            return handoff(item);
        }

        i.state
            .start_node(SyntaxKind::BlockStatementSeparator.into());
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        i.state.finish_node();
        exit = expression_statement(i.rb(), item, block_indent, stops);
    }
}

fn statement_item_after_opening(mut i: RewriteIn, baseline: usize, stops: u8) -> Item {
    tail_item_after_trivia(
        i.rb(),
        super::item::LeadingTrivia::default(),
        OperatorSite::Nud,
        baseline,
        stops,
    )
}
