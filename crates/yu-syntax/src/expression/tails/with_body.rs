//! With-body introducer, Statement admission and terminal handoff.

use super::inline_slot::{
    emit_inline_leading, emit_inline_slot_missing, inline_boundary, inline_slot_draft,
    is_inline_slot_boundary,
};
use crate::ambient_claim::AmbientClaimContext;
use crate::cursor::SyntaxIn;
use crate::cursor::recovery::emit::{
    emit_recovery_error_run, emit_token_item, emit_with_keyword, token_syntax_kind,
};
use crate::handoff::{Either, NormalizedExit, complete, handoff};
use crate::lexical::current_item::LineEntry;
use crate::lexical::expression_item::expression_item;
use crate::lexical::item::{Item, TokenKind};
use crate::lexical::lexer::introduced_body_indentation_normalized;
use crate::lexical::observation::{is_active_stop_lex, is_line_stop, token_kind};
use crate::lexical::operator_scan::OperatorSite;
use crate::lexical::position::{advanced_origin, suffix_marker};
use crate::lexical::stops::Stops;
use crate::lexical::trivia::lone_colon_after_fenced_trivia;
use crate::lexical::yumark::FenceBoundary;
use crate::recovery_record::{
    ExpectedSyntax, GrammarRole, PunctuationEvidence as Punctuation, RecoveryKind,
    UnexpectedCategory, UnexpectedSyntax, WithBodyRole,
};
use crate::statement::{
    StatementAdmission, StatementLineHandoff, canonical_statement_from_admission_normalized,
    classify_statement_item_lexical, classify_statement_item_normalized,
    indented_statement_block_normalized, scan_statement_item_lexical, statement_item_normalized,
};
use crate::syntax_kind::SyntaxKind;

/// The terminal generic `with:` continuation. Its body is an existing direct
/// Statement callee, never a target-owning or replayed expression parser.
#[allow(clippy::too_many_arguments)]
pub(crate) fn with_tail_normalized(
    mut i: SyntaxIn,
    mut keyword: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::WithBodyTail.into());
    emit_with_keyword(&mut i, keyword);

    let has_colon = i
        .rb()
        .map(
            |lex: crate::cursor::LexIn| {
                Some(lone_colon_after_fenced_trivia(
                    lex.remainder(),
                    item_origin,
                    LineEntry::InLine,
                    fence,
                ))
            },
            |follower| follower,
        )
        .unwrap_or(false);
    let exit = if has_colon {
        let (colon, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Led,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        debug_assert_eq!(token_kind(&colon), Some(TokenKind::Colon));
        emit_token_item(&mut i, colon);
        if introduced_body_indentation_normalized(i.rb(), item_origin, fence)
            .is_some_and(|indentation| indentation > baseline)
        {
            indented_statement_block_normalized(
                i.rb(),
                baseline,
                GrammarRole::WithBody(WithBodyRole::IndentedStatement),
                stops,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else {
            let entry = suffix_marker(i.rb());
            let exit = with_inline_body_normalized(
                i.rb(),
                baseline,
                stops,
                true,
                true,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            with_inline_terminal_normalized(i.rb(), exit, baseline, stops, item_origin, fence)
        }
    } else {
        let (mut item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        emit_inline_slot_missing(
            i.rb(),
            &mut item,
            item_origin,
            GrammarRole::WithBody(WithBodyRole::Introducer),
            ExpectedSyntax::Punctuation(Punctuation::Colon),
            stops,
        );
        with_inline_item_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            false,
            false,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    };

    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn with_inline_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    with_inline_item_normalized(
        i,
        item,
        baseline,
        stops,
        missing_on_boundary,
        allow_braced,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn with_inline_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        if missing_on_boundary {
            emit_inline_slot_missing(
                i.rb(),
                &mut item,
                item_origin,
                GrammarRole::WithBody(WithBodyRole::Body),
                ExpectedSyntax::Statement,
                stops,
            );
        }
        return complete(handoff(item), line_entry);
    }
    if !item.payload_view().is_boundary()
        && !allow_braced
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::PathSeparator)
        )
    {
        return complete(handoff(item), line_entry);
    }
    if with_inline_boundary(i.rb(), &item, baseline, stops) {
        if missing_on_boundary {
            emit_inline_slot_missing(
                i.rb(),
                &mut item,
                item_origin,
                GrammarRole::WithBody(WithBodyRole::Body),
                ExpectedSyntax::Statement,
                stops,
            );
        }
        return complete(handoff(item), line_entry);
    }
    if allow_braced || token_kind(&item) != Some(TokenKind::LBrace) {
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            return canonical_statement_from_admission_normalized(
                i,
                item,
                admission,
                baseline,
                stops,
                line_handoff.through_inline_statement(),
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
        }
    }

    emit_inline_leading(&mut i, &mut item);
    let admission;
    (item, admission, item_origin, line_entry) = retry_with_inline_body_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        allow_braced,
        item_origin,
        line_entry,
        fence,
    );
    if !item.payload_view().is_boundary()
        && !allow_braced
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::PathSeparator)
        )
    {
        return complete(handoff(item), line_entry);
    }
    if with_inline_boundary(i.rb(), &item, baseline, stops) {
        if item.payload_view().is_eof() && !is_line_stop(&item, stops) {
            item.emit_eof_leading(&mut *i.state);
        }
        return complete(handoff(item), line_entry);
    }
    canonical_statement_from_admission_normalized(
        i,
        item,
        admission.expect("inline-body retry returned an admitted canonical Statement"),
        baseline,
        stops,
        line_handoff.through_inline_statement(),
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_with_inline_body_normalized(
    i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    allow_braced: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, Option<StatementAdmission>, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            loop {
                let kind =
                    token_syntax_kind(token_kind(&item).expect("a With Error emits a token"));
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
                let boundary = inline_boundary(&item, baseline, stops)
                    || (!allow_braced
                        && matches!(
                            token_kind(&item),
                            Some(TokenKind::LBrace | TokenKind::PathSeparator)
                        ))
                    || run.lexical(|lex| is_active_stop_lex(lex, &item, stops));
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
                    return (item, admission, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| {
            inline_slot_draft(
                GrammarRole::WithBody(WithBodyRole::Body),
                ExpectedSyntax::Statement,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    )
}

fn with_inline_boundary(i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    is_inline_slot_boundary(i, item, baseline, stops)
}

fn with_inline_terminal_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let NormalizedExit::Complete(Err(Either::Left(semicolon)), line_entry) = exit else {
        return exit;
    };
    if semicolon.payload_view().is_boundary() {
        return complete(handoff(semicolon), line_entry);
    }
    if token_kind(&semicolon) != Some(TokenKind::Semicolon) {
        return complete(handoff(semicolon), line_entry);
    }
    emit_token_item(&mut i, semicolon);
    let (item, _, line_entry) = expression_item(
        i,
        OperatorSite::Led,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    complete(handoff(item), line_entry)
}
