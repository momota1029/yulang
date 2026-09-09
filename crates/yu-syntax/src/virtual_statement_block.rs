//! Isolated StringInterpolation virtual canonical-Statement sequence.
//!
//! The enclosing interpolation owns the braces. This owner emits only the
//! root-style Statement sequence and its separators, then returns the exact
//! borrowed close or boundary Item.

use std::{ops::Range, sync::Arc};

use crate::syntax_kind::SyntaxKind;

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    cursor::recovery::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    handoff::{Either, NormalizedExit},
    lexical::{
        current_item::LineEntry,
        item::{Item, LeadingTrivia, TokenKind},
        observation::token_kind,
        position::{advanced_origin, suffix_marker},
        stops::{STOP_COMMA, STOP_SEMICOLON, Stops, stops_for},
        yumark::FenceBoundary,
    },
    recovery_record::{
        ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind, RecoverySiteKey,
        StatementRole, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    statement::{
        StatementAdmission, StatementLineHandoff, canonical_statement_from_admission_normalized,
        classify_statement_item_lexical, classify_statement_item_normalized,
        scan_statement_item_lexical, statement_item_normalized,
    },
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
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> VirtualStatementBlockExit {
    let sequence = Some(crate::sequence::SequenceOwner::VirtualStatement);
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
                emit_missing_statement(&mut i, item.extent(item_origin).recovery_range().start);
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
                emit_virtual_missing(
                    i.rb(),
                    StatementRole::Separator,
                    item.extent(item_origin).recovery_range().start,
                );
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
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> RetryExit {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            loop {
                let kind = token_syntax_kind(
                    token_kind(&item).expect("a Virtual Statement Error emits a token"),
                );
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                (item, item_origin, line_entry) = run.lexical(|lex| {
                    scan_statement_item_lexical(
                        lex,
                        item_origin,
                        line_entry,
                        fence,
                        baseline,
                        stops,
                    )
                });
                let boundary = retry_boundary(&item);
                let admission = if boundary {
                    None
                } else {
                    run.lexical(|lex| {
                        classify_statement_item_lexical(
                            lex.remainder(),
                            &item,
                            baseline,
                            item_origin,
                            fence,
                        )
                    })
                };
                if boundary || admission.is_some() {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return match admission {
                        Some(admission) => RetryExit::Candidate {
                            item,
                            admission,
                            item_origin,
                            line_entry,
                        },
                        None => RetryExit::Incomplete {
                            item,
                            item_origin,
                            line_entry,
                        },
                    };
                }
            }
        },
        |range, unexpected| {
            virtual_recovery_draft(
                StatementRole::Starter,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    )
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
    mut i: SyntaxIn,
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

fn emit_newline_separator(i: &mut SyntaxIn, item: &mut Item) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.finish_node();
}

fn emit_missing_statement(i: &mut SyntaxIn, at: usize) {
    i.state.start_node(SyntaxKind::Statement.into());
    emit_virtual_missing(i.rb(), StatementRole::Starter, at);
    i.state.finish_node();
}

fn emit_virtual_missing(i: SyntaxIn, role: StatementRole, at: usize) {
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        virtual_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn virtual_recovery_draft(
    role: StatementRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        StatementRole::Starter => ExpectedSyntax::Statement,
        StatementRole::Separator => ExpectedSyntax::StatementSeparator,
        _ => unreachable!("Virtual owns only Statement starter and separator recovery"),
    };
    let role = GrammarRole::Statement(role);
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn statement_successor(
    i: SyntaxIn,
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
