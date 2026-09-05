//! Gate 3's isolated one-builder Yulang-cell construction witness.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_end, emit_fragmented_item, emit_token_item},
    item::{Item, PendingBoundary, TokenKind},
    lexer::{scan_trivia, statement_item_after_trivia},
    statement::{is_canonical_statement_nud, statement_from_item},
};

/// Composes the currently closed canonical statement surface beneath one cell
/// node, then returns the caller-injected fence boundary without emitting it.
/// The ordinary lexer remains unaware of Yumark boundaries at this gate.
pub(super) fn yulang_code_cell_witness(
    mut i: RewriteIn,
    terminal: Item,
) -> Result<PendingBoundary, TailExit> {
    i.state.start_node(SyntaxKind::YmYulangCodeCell.into());
    let leading = scan_trivia(i.rb());
    let mut item = statement_item_after_trivia(i.rb(), leading, 0, 0);

    loop {
        if item.payload_view().is_boundary() {
            return Ok(finish_at_boundary(i, item));
        }

        if item.payload_view().is_eof() {
            let mut end = super::driver::End { item };
            emit_end(&mut *i.state, &mut end);
            return Ok(finish_at_boundary(i, terminal));
        }

        let exit = statement_from_item(i.rb(), item, 0, 0);
        match exit {
            Ok(()) => {
                let leading = scan_trivia(i.rb());
                item = statement_item_after_trivia(i.rb(), leading, 0, 0);
            }
            Err(Either::Right(mut end)) => {
                emit_end(&mut *i.state, &mut end);
                return Ok(finish_at_boundary(i, terminal));
            }
            Err(Either::Left(next)) if next.payload_view().is_boundary() => {
                return Ok(finish_at_boundary(i, next));
            }
            Err(Either::Left(next)) => match cell_successor(&mut i, next) {
                Ok(()) => {
                    let leading = scan_trivia(i.rb());
                    item = statement_item_after_trivia(i.rb(), leading, 0, 0);
                }
                Err(exit) => return Err(exit),
            },
        }
    }
}

/// Exercises an already-accepted segmented identifier statement followed by
/// the same successor path used by the cell loop. This remains a Gate 3 test
/// seam until the fence-aware lexical owner exists.
pub(super) fn accepted_identifier_statement_witness(
    mut i: RewriteIn,
    item: Item,
    successor: Item,
) -> Result<PendingBoundary, TailExit> {
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert!(is_canonical_statement_nud(i.rb(), &item, 0));

    i.state.start_node(SyntaxKind::YmYulangCodeCell.into());
    i.state.start_node(SyntaxKind::Statement.into());
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    emit_fragmented_item(&mut i, item);
    i.state.finish_node();
    i.state.finish_node();

    if successor.payload_view().is_boundary() {
        return Ok(finish_at_boundary(i, successor));
    }
    match cell_successor(&mut i, successor) {
        Ok(()) => unreachable!("the Gate 3 successor fixture requires a boundary"),
        Err(exit) => Err(exit),
    }
}

/// A boundary is classified before any ordinary token predicate can observe
/// it. `Ok(())` means that a statement separator was accepted and the caller
/// may scan the next statement.
fn cell_successor(i: &mut RewriteIn, next: Item) -> Result<(), TailExit> {
    debug_assert!(!next.payload_view().is_boundary());

    if token_kind(&next) == Some(TokenKind::Semicolon) {
        emit_token_item(i, next);
        Ok(())
    } else {
        i.state.finish_node();
        Err(handoff(next))
    }
}

fn finish_at_boundary(i: RewriteIn, item: Item) -> PendingBoundary {
    let boundary = item.emit_terminal_boundary(&mut *i.state);
    i.state.finish_node();
    boundary
}
