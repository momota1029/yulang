//! Isolated StringInterpolation virtual canonical-Statement sequence.
//!
//! The enclosing interpolation owns the braces. This owner emits only the
//! root-style Statement sequence and its separators, then returns the exact
//! borrowed close or boundary Item.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    ParserIn, Stops,
    ambient_claim::AmbientClaimContext,
    current_item::LineEntry,
    driver::{Either, NormalizedExit, advanced_origin, suffix_marker, token_kind},
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    operator::{STOP_COMMA, STOP_SEMICOLON, stops_for},
    statement::{
        StatementAdmission, StatementLineHandoff, canonical_statement_from_admission_normalized,
        classify_statement_item_normalized, statement_item_normalized,
    },
    yumark::FenceBoundary,
};

pub(super) enum VirtualStatementBlockExit {
    Close(Item, LineEntry),
    Boundary(Item, LineEntry),
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum SequencePosition {
    Initial,
    AfterStatement,
    AfterSeparator,
}

enum RetryExit {
    Candidate {
        item: Item,
        admission: StatementAdmission,
        item_origin: usize,
        line_entry: LineEntry,
    },
    Incomplete {
        item: Item,
        item_origin: usize,
        line_entry: LineEntry,
    },
}

pub(super) fn virtual_statement_block_normalized(
    mut i: ParserIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> VirtualStatementBlockExit {
    let sequence = Some(super::sequence::SequenceOwner::VirtualStatement);
    let baseline = 0;
    let stops: Stops = stops_for(TokenKind::RBrace) | STOP_COMMA | STOP_SEMICOLON;
    let (mut item, mut item_origin, mut line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    let mut position = SequencePosition::Initial;
    let mut known_admission = None;

    loop {
        if item.payload_view().is_boundary() || item.payload_view().is_eof() {
            return VirtualStatementBlockExit::Boundary(item, line_entry);
        }
        if token_kind(&item) == Some(TokenKind::RBrace) {
            return VirtualStatementBlockExit::Close(item, line_entry);
        }

        if matches!(
            token_kind(&item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        ) {
            if position != SequencePosition::AfterStatement {
                emit_missing_statement(&mut i);
            }
            let (next, next_origin, next_entry, admission) = emit_explicit_separator(
                i.rb(),
                item,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            item = next;
            item_origin = next_origin;
            line_entry = next_entry;
            known_admission = admission;
            position = SequencePosition::AfterSeparator;
            continue;
        }

        let admission = known_admission.take().unwrap_or_else(|| {
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        });

        if position == SequencePosition::AfterStatement {
            if item.leading_view().has_ordinary_newline() {
                emit_newline_separator(&mut i, &mut item);
                position = SequencePosition::AfterSeparator;
            } else if admission.is_some() {
                emit_missing(&mut i, LeadingTrivia::default());
                position = SequencePosition::AfterSeparator;
            } else {
                match retry_statement(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                ) {
                    RetryExit::Candidate {
                        item: next,
                        admission,
                        item_origin: next_origin,
                        line_entry: next_entry,
                    } => {
                        item = next;
                        item_origin = next_origin;
                        line_entry = next_entry;
                        known_admission = Some(Some(admission));
                        position = SequencePosition::AfterSeparator;
                    }
                    RetryExit::Incomplete {
                        item: next,
                        item_origin: next_origin,
                        line_entry: next_entry,
                    } => {
                        item = next;
                        item_origin = next_origin;
                        line_entry = next_entry;
                        position = SequencePosition::AfterStatement;
                    }
                }
                continue;
            }
        }

        if let Some(admission) = admission {
            let entry = suffix_marker(i.rb());
            let exit = canonical_statement_from_admission_normalized(
                i.rb(),
                item,
                admission,
                baseline,
                stops,
                StatementLineHandoff::BracedStatementSequence,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            item_origin = advanced_origin(item_origin, entry, i.rb());
            (item, item_origin, line_entry) =
                statement_successor(i.rb(), exit, item_origin, fence, baseline, stops);
            position = SequencePosition::AfterStatement;
            known_admission = None;
            continue;
        }

        match retry_statement(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        ) {
            RetryExit::Candidate {
                item: next,
                admission,
                item_origin: next_origin,
                line_entry: next_entry,
            } => {
                item = next;
                item_origin = next_origin;
                line_entry = next_entry;
                known_admission = Some(Some(admission));
            }
            RetryExit::Incomplete {
                item: next,
                item_origin: next_origin,
                line_entry: next_entry,
            } => {
                item = next;
                item_origin = next_origin;
                line_entry = next_entry;
                position = SequencePosition::AfterStatement;
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_statement(
    mut i: ParserIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> RetryExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        if retry_boundary(&item) {
            i.state.finish_node();
            return RetryExit::Incomplete {
                item,
                item_origin,
                line_entry,
            };
        }
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
            return RetryExit::Candidate {
                item,
                admission,
                item_origin,
                line_entry,
            };
        }
    }
}

fn retry_boundary(item: &Item) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || item.leading_view().has_ordinary_newline()
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon | TokenKind::RBrace)
        )
}

#[allow(clippy::too_many_arguments)]
fn emit_explicit_separator(
    mut i: ParserIn,
    mut separator: Item,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry, Option<Option<StatementAdmission>>) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    separator.emit_all_remaining_leading(&mut *i.state);
    emit_token_item(&mut i, separator);
    let (mut item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    let admission = if separator_successor_terminal(&item) {
        None
    } else {
        let admission =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence);
        item.emit_all_remaining_leading(&mut *i.state);
        Some(admission)
    };
    i.state.finish_node();
    (item, item_origin, line_entry, admission)
}

fn separator_successor_terminal(item: &Item) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon | TokenKind::RBrace)
        )
}

fn emit_newline_separator(i: &mut ParserIn, item: &mut Item) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.finish_node();
}

fn emit_missing_statement(i: &mut ParserIn) {
    i.state.start_node(SyntaxKind::Statement.into());
    emit_missing(i, LeadingTrivia::default());
    i.state.finish_node();
}

fn statement_successor(
    i: ParserIn,
    exit: NormalizedExit,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            statement_item_normalized(i, item_origin, line_entry, fence, baseline, stops)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized canonical statements do not defer virtual-block owners")
        }
    }
}
