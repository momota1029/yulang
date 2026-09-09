//! Rule-owned ordinary expression lists for bracket atoms, calls, and indices.

use crate::ambient_claim::AmbientClaimContext;
use std::{ops::Range, sync::Arc};

use crate::{
    lexical::operator_scan::OperatorSite,
    recovery_record::{
        ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, ExpressionListRole,
        GrammarRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cursor::SyntaxIn,
    cursor::recovery::{
        RecoveryDraft,
        emit::{emit_recovery_error_item, emit_recovery_missing, token_syntax_kind},
    },
    expression::{expr_from_nud_normalized, is_nud_item},
    handoff::{Either, MlMode, NormalizedExit},
    lexical::{
        current_item::LineEntry,
        expression_item::expression_item,
        item::{Item, LeadingTrivia, TokenKind},
        observation::is_close,
        position::{advanced_origin, suffix_marker},
        stops::{STOP_LINE_BREAK, stops_for},
        yumark::FenceBoundary,
    },
    rule::{emit_item_as, is_token},
    statement::StatementLineHandoff,
};

pub(super) enum ExpressionListExit {
    Close(Item, LineEntry),
    Returned(Item, LineEntry),
    Deferred(Item, LineEntry),
}

/// Parses the ordinary expression interior without introducing a CST wrapper.
/// The RuleCall/RuleIndex/RuleItem caller owns and emits the returned close.
pub(super) fn expression_list(
    mut i: SyntaxIn,
    mut current: Item,
    close: TokenKind,
    origin: &mut usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> ExpressionListExit {
    let sequence = Some(crate::sequence::SequenceOwner::RuleExpressionList);
    let stops = stops_for(close) | STOP_LINE_BREAK;
    let mut needs_expression = true;
    let mut recovery_requires_expression = false;

    loop {
        if current.payload_view().is_boundary()
            || current.payload_view().is_eof()
            || (is_unread_close(&current) && token_kind_or_boundary(&current) != Some(close))
        {
            if recovery_requires_expression {
                missing(
                    i.rb(),
                    &current,
                    *origin,
                    GrammarRole::ExpressionList(ExpressionListRole::Item),
                );
            }
            missing(i.rb(), &current, *origin, close_role(close));
            return ExpressionListExit::Returned(current, line_entry);
        }

        if emit_leading_newline_separators(
            &mut i,
            &mut current,
            *origin,
            &mut needs_expression,
            &mut recovery_requires_expression,
        ) {
            continue;
        }

        if token_kind_or_boundary(&current) == Some(close) {
            if recovery_requires_expression {
                missing(
                    i.rb(),
                    &current,
                    *origin,
                    GrammarRole::ExpressionList(ExpressionListRole::Item),
                );
            }
            return ExpressionListExit::Close(current, line_entry);
        }

        if is_token(&current, TokenKind::Comma) {
            if needs_expression {
                missing(
                    i.rb(),
                    &current,
                    *origin,
                    GrammarRole::ExpressionList(ExpressionListRole::Item),
                );
            }
            emit_item_as(&mut i, current, SyntaxKind::Comma);
            (current, line_entry) = next_item(i.rb(), stops, origin, line_entry, fence);
            needs_expression = true;
            recovery_requires_expression = false;
            continue;
        }

        if needs_expression {
            if !is_nud_item(&current) {
                error(i.rb(), current, *origin, ExpressionListRole::Item);
                (current, line_entry) = next_item(i.rb(), stops, origin, line_entry, fence);
                recovery_requires_expression = true;
                continue;
            }

            let entry = suffix_marker(i.rb());
            let exit = expr_from_nud_normalized(
                i.rb(),
                current,
                None,
                0,
                stops,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                *origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            *origin = advanced_origin(*origin, entry, i.rb());
            (current, line_entry) = match exit {
                NormalizedExit::Complete(Ok(()), line_entry) => {
                    next_item(i.rb(), stops, origin, line_entry, fence)
                }
                NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => (item, line_entry),
                NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
                    (end.item, line_entry)
                }
                NormalizedExit::Deferred(item, line_entry) => {
                    return ExpressionListExit::Deferred(item, line_entry);
                }
            };
            needs_expression = false;
            recovery_requires_expression = false;
            continue;
        }

        error(i.rb(), current, *origin, ExpressionListRole::Separator);
        (current, line_entry) = next_item(i.rb(), stops, origin, line_entry, fence);
    }
}

pub(super) fn first_item(
    mut i: SyntaxIn,
    close: TokenKind,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, LineEntry) {
    next_item(
        i.rb(),
        stops_for(close) | STOP_LINE_BREAK,
        origin,
        line_entry,
        fence,
    )
}

fn next_item(
    mut i: SyntaxIn,
    stops: u16,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, LineEntry) {
    let (item, next_origin, next_line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        *origin,
        line_entry,
        fence,
        0,
        stops,
    );
    *origin = next_origin;
    (item, next_line_entry)
}

fn emit_leading_newline_separators(
    i: &mut SyntaxIn,
    item: &mut Item,
    origin: usize,
    needs_expression: &mut bool,
    recovery_requires_expression: &mut bool,
) -> bool {
    let Some(end_part) = item.leading_view().cut_after_last_ordinary_newline() else {
        return false;
    };
    crate::cursor::recovery::emit::emit_required_slots_before_newlines(
        i,
        item,
        end_part,
        origin,
        needs_expression,
        recovery_requires_expression,
        |at| {
            draft(
                GrammarRole::ExpressionList(ExpressionListRole::Item),
                RecoveryKind::Missing,
                at..at,
                Arc::from([]),
            )
        },
    );
    true
}

fn close_role(close: TokenKind) -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ExpressionList,
        delimiter: match close {
            TokenKind::RParen => Delimiter::Parenthesis,
            TokenKind::RBracket => Delimiter::Bracket,
            _ => unreachable!("Rule expression lists use parentheses or brackets"),
        },
    }
}

fn draft(
    role: GrammarRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        GrammarRole::ExpressionList(ExpressionListRole::Item) => ExpectedSyntax::Expression,
        GrammarRole::ExpressionList(ExpressionListRole::Separator) => {
            ExpectedSyntax::DelimitedSequenceSeparator
        }
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        _ => unreachable!(),
    };
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

fn missing(i: SyntaxIn, item: &Item, origin: usize, role: GrammarRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || {
            if item.payload_view().is_eof() {
                origin
            } else {
                item.extent(origin).recovery_range().start
            }
        },
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn error(i: SyntaxIn, item: Item, origin: usize, slot: ExpressionListRole) {
    let payload = item.payload_view();
    let kind = if payload.operator_use().is_some() {
        SyntaxKind::Operator
    } else {
        token_syntax_kind(
            payload
                .token_kind()
                .expect("a rejected list Item is lexical"),
        )
    };
    let unexpected = UnexpectedSyntax::Token {
        range: item.extent(origin).recovery_range(),
        category: UnexpectedCategory::OtherCharacter,
    };
    emit_recovery_error_item(i, item, origin, kind, unexpected, |range, unexpected| {
        draft(
            GrammarRole::ExpressionList(slot),
            RecoveryKind::Error,
            range,
            unexpected,
        )
    });
}

fn is_unread_close(item: &Item) -> bool {
    item.payload_view().token_kind().is_some() && is_close(item)
}

fn token_kind_or_boundary(item: &Item) -> Option<TokenKind> {
    item.payload_view().token_kind()
}
