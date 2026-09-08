//! Direct canonical `for` statement construction.

use crate::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{
    lexical::operator_scan::OperatorSite,
    recovery_record::{
        Delimiter, ExpectationSources, ExpectedSyntax, ForStatementRole, GrammarRole,
        KeywordEvidence, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    cursor::{LexIn, SyntaxIn},
    expression::{is_required_operand_boundary, required_expr_item_normalized},
    handoff::{Either, MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{CurrentItem, LineEntry, current_item},
        expression_item::{expression_item, scan_expression_item_lexical},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_case_label_payload,
            scan_pattern_nud_payload, scan_statement_payload,
        },
        observation::{
            implicit_delimited_newline, is_active_stop_lex, is_close, is_line_stop, is_separator,
            token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_COLON, STOP_COMMA, STOP_LBRACE, STOP_SEMICOLON, Stops},
        yumark::FenceBoundary,
    },
    pattern::{
        PATTERN_STOP_IN, PATTERN_STOP_LBRACE, PATTERN_STOP_PRIMARY_COLON, PatternCompletion,
        pattern_from_entry_item_with_completion_normalized, pattern_stops_from_owner,
    },
    statement::{
        StatementLineHandoff, braced_statement_block_normalized,
        indented_statement_block_normalized,
    },
};

pub(crate) fn for_statement_selected(item: &Item) -> bool {
    item_word(item) == Some("for")
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn for_statement_normalized(
    mut i: SyntaxIn,
    keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    debug_assert!(for_statement_selected(&keyword));
    i.state.start_node(SyntaxKind::ForStatement.into());
    emit_keyword(&mut i, keyword, SyntaxKind::ForKw, "for");
    (item_origin, line_entry) = emit_optional_label_normalized(
        i.rb(),
        baseline,
        outer_stops,
        item_origin,
        line_entry,
        fence,
    );
    let exit = pattern_slot_normalized(
        i.rb(),
        baseline,
        outer_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn emit_optional_label_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    outer_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (usize, LineEntry) {
    let mut accepted = false;
    let rolled_back: Option<()> = i.token(|mut probe: LexIn| {
        let (label, text) = probe.rb().with_str(|label| {
            current_item(label, item_origin, line_entry, fence, |lex, _, _, _, _| {
                scan_case_label_payload(lex)
            })
        });
        let Some(CurrentItem {
            item: label,
            next_line_entry,
        }) = label
        else {
            return None;
        };
        if label.payload_view().is_boundary()
            || label.payload_view().is_eof()
            || implicit_gap(baseline, label.leading_view())
        {
            return None;
        }
        let next_origin = item_origin
            .checked_add(text.len())
            .expect("a tentative For label coordinate must fit usize");
        let Some(CurrentItem { item: next, .. }) = current_item(
            probe.rb(),
            next_origin,
            next_line_entry,
            fence,
            |lex, leading, origin, fence, _| {
                scan_statement_payload(lex, leading, origin, fence, baseline, outer_stops)
            },
        ) else {
            return None;
        };
        accepted = !label_following_boundary(probe.rb(), &next, baseline, outer_stops)
            && item_word(&next) != Some("in");
        None
    });
    debug_assert!(rolled_back.is_none());
    if !accepted {
        return (item_origin, line_entry);
    }

    let entry = suffix_marker(i.rb());
    let CurrentItem {
        mut item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(lex, item_origin, line_entry, fence, |lex, _, _, _, _| {
                scan_case_label_payload(lex)
            })
        })
        .expect("an accepted For label must reacquire identically");
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    debug_assert!(!item.payload_view().is_boundary());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::ForLabel.into());
    emit_token_item(&mut i, item);
    i.state.finish_node();
    (item_origin, next_line_entry)
}

#[allow(clippy::too_many_arguments)]
fn pattern_slot_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let stops = pattern_stops_from_owner(outer_stops)
        | PATTERN_STOP_PRIMARY_COLON
        | PATTERN_STOP_LBRACE
        | PATTERN_STOP_IN;
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        mut item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_pattern_nud_payload(lex, leading, origin, fence, stops)
                },
            )
        })
        .expect("For Pattern payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        i.state.start_node(SyntaxKind::Pattern.into());
        emit_for_missing(i.rb(), &mut item, item_origin, ForStatementRole::Pattern);
        i.state.finish_node();
        return complete(handoff(item), next_line_entry);
    }
    let missing_at_in = item_word(&item) == Some("in");
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
    }
    let missing_at_body = matches!(
        token_kind(&item),
        Some(TokenKind::Colon | TokenKind::LBrace)
    );
    if (!outer_boundary(i.rb(), &item, baseline, outer_stops)
        || token_kind(&item) == Some(TokenKind::LBracket))
        && !missing_at_in
        && !missing_at_body
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, completion) = pattern_from_entry_item_with_completion_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        next_line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    match exit {
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => match completion {
            PatternCompletion::Complete => in_slot_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            ),
            PatternCompletion::Incomplete if missing_at_in => in_slot_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            ),
            PatternCompletion::Incomplete if missing_at_body => body_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            ),
            PatternCompletion::Incomplete => complete(handoff(item), line_entry),
        },
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            if completion == PatternCompletion::Complete {
                emit_for_missing(
                    i.rb(),
                    &mut end.item,
                    item_origin,
                    ForStatementRole::InKeyword,
                );
            }
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("a Pattern leaves its successor Item")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn in_slot_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        emit_for_missing(i.rb(), &mut item, item_origin, ForStatementRole::InKeyword);
        return complete(handoff(item), line_entry);
    }
    if item_word(&item) == Some("in") {
        emit_keyword(&mut i, item, SyntaxKind::InKw, "in");
        return iterable_normalized(
            i,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }

    if !outer_boundary(i.rb(), &item, baseline, outer_stops)
        && !matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        )
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_for_missing(i.rb(), &mut item, item_origin, ForStatementRole::InKeyword);
    if matches!(
        token_kind(&item),
        Some(TokenKind::Colon | TokenKind::LBrace)
    ) {
        return body_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if outer_boundary(i.rb(), &item, baseline, outer_stops) {
        return complete(handoff(item), line_entry);
    }
    iterable_from_item_normalized(
        i,
        item,
        baseline,
        outer_stops,
        false,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn iterable_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        iterable_stops(outer_stops),
    );
    let missing = implicit_delimited_newline(baseline, item.leading_view())
        || is_required_operand_boundary(i.rb(), &item, iterable_stops(outer_stops));
    if !item.payload_view().is_boundary()
        && !implicit_delimited_newline(baseline, item.leading_view())
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    iterable_from_item_normalized(
        i,
        item,
        baseline,
        outer_stops,
        missing,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn iterable_from_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    missing: bool,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if !item.payload_view().is_boundary()
        && !implicit_delimited_newline(baseline, item.leading_view())
        && !item.leading_view().is_grammar_empty()
    {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.start_node(SyntaxKind::ForIterable.into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let child_entry = suffix_marker(i.rb());
    let exit = if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        crate::expression::emit_required_expression_missing(
            &mut i,
            &mut item,
            item_origin,
            iterable_stops(outer_stops),
            GrammarRole::ForStatement(ForStatementRole::Iterable),
        );
        complete(handoff(item), line_entry)
    } else {
        required_expr_item_normalized(
            i.rb(),
            item,
            GrammarRole::ForStatement(ForStatementRole::Iterable),
            None,
            baseline,
            iterable_stops(outer_stops),
            MlMode::All,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    };
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    i.state.finish_node();
    i.state.finish_node();

    match exit {
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if !item.payload_view().is_boundary()
                && matches!(
                    token_kind(&item),
                    Some(TokenKind::Colon | TokenKind::LBrace)
                ) =>
        {
            body_normalized(
                i,
                item,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) if missing => {
            complete(handoff(item), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => body_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) if missing => {
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            emit_for_missing(
                i.rb(),
                &mut end.item,
                item_origin,
                ForStatementRole::BodyIntroducer,
            );
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("an iterable leaves its successor Item")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn body_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        emit_for_missing(
            i.rb(),
            &mut item,
            item_origin,
            ForStatementRole::BodyIntroducer,
        );
        return complete(handoff(item), line_entry);
    }
    match token_kind(&item) {
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_body_normalized(
                i,
                baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        Some(TokenKind::LBrace) => {
            item.emit_all_remaining_leading(&mut *i.state);
            braced_statement_block_normalized(
                i,
                item,
                baseline,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        _ if outer_boundary(i.rb(), &item, baseline, outer_stops) => {
            emit_for_missing(
                i.rb(),
                &mut item,
                item_origin,
                ForStatementRole::BodyIntroducer,
            );
            complete(handoff(item), line_entry)
        }
        _ => recover_body_introducer_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn colon_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            GrammarRole::ForStatement(ForStatementRole::IndentedStatement),
            outer_stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            let (mut item, item_origin, line_entry) = statement_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                outer_stops,
            );
            emit_for_missing(i.rb(), &mut item, item_origin, ForStatementRole::Body);
            complete(handoff(item), line_entry)
        }
        None => inline_body_normalized(
            i,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_body_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let stops = outer_stops | STOP_COMMA | STOP_SEMICOLON;
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item_normalized(
        i.rb(),
        item,
        GrammarRole::ForStatement(ForStatementRole::Body),
        None,
        baseline,
        stops,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let kind =
                token_syntax_kind(token_kind(&item).expect("For introducer Error owns tokens"));
            let range = run.emit_item_as(item, item_origin, kind).recovery_range();
            run.append_unexpected(UnexpectedSyntax::Token {
                range,
                category: UnexpectedCategory::OtherCharacter,
            });
            (item, item_origin, line_entry) = run.lexical(|lex| {
                scan_expression_item_lexical(
                    lex,
                    OperatorSite::Nud,
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    outer_stops,
                )
            });
            if run.lexical(|lex| outer_boundary_lex(lex, &item, baseline, outer_stops))
                || matches!(
                    token_kind(&item),
                    Some(TokenKind::Colon | TokenKind::LBrace)
                )
            {
                return (item, item_origin, line_entry);
            }
        },
        |range, unexpected| {
            for_recovery_draft(
                ForStatementRole::BodyIntroducer,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    );
    if !item.payload_view().is_boundary()
        && !implicit_delimited_newline(baseline, item.leading_view())
        && matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        )
    {
        body_normalized(
            i,
            item,
            baseline,
            outer_stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

fn statement_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("For recovery Statement payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}

fn iterable_stops(outer_stops: Stops) -> Stops {
    outer_stops | STOP_COLON | STOP_LBRACE | STOP_COMMA | STOP_SEMICOLON
}

fn outer_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, outer_stops: Stops) -> bool {
    i.token(|lex| Some(outer_boundary_lex(lex, item, baseline, outer_stops)))
        .expect("For boundary observation is total")
}

fn outer_boundary_lex(i: LexIn, item: &Item, baseline: usize, outer_stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || implicit_delimited_newline(baseline, item.leading_view())
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop_lex(i, item, outer_stops)
        || is_line_stop(item, outer_stops)
        || is_close(item)
        || matches!(token_kind(item), Some(TokenKind::LBracket))
}

fn emit_for_missing(i: SyntaxIn, item: &mut Item, origin: usize, role: ForStatementRole) {
    if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
        item.emit_eof_leading(&mut *i.state);
    }
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        for_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn for_recovery_draft(
    role: ForStatementRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        ForStatementRole::Pattern => ExpectedSyntax::Pattern,
        ForStatementRole::InKeyword => ExpectedSyntax::Keyword(KeywordEvidence::In),
        ForStatementRole::BodyIntroducer => ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ForStatementRole::Body => ExpectedSyntax::Statement,
        _ => unreachable!("only For structural slots publish here"),
    };
    let expectation = |expected| SyntaxExpectation {
        role: GrammarRole::ForStatement(role),
        expected,
        range: range.clone(),
        sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
    };
    let expectations: Arc<[SyntaxExpectation]> = if role == ForStatementRole::BodyIntroducer {
        Arc::from([
            expectation(expected),
            expectation(ExpectedSyntax::Punctuation(PunctuationEvidence::Open(
                Delimiter::Brace,
            ))),
        ])
    } else {
        Arc::from([expectation(expected)])
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role: GrammarRole::ForStatement(role),
            range,
        },
        kind,
        unexpected,
        expectations,
        0,
    )
}

fn label_following_boundary(
    mut i: LexIn,
    item: &Item,
    baseline: usize,
    outer_stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || implicit_gap(baseline, item.leading_view())
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop_lex(i.rb(), item, outer_stops)
        || matches!(token_kind(item), Some(TokenKind::Colon | TokenKind::LBrace))
}

fn implicit_gap(baseline: usize, leading: crate::lexical::item::LeadingView<'_>) -> bool {
    implicit_delimited_newline(baseline, leading)
}

fn item_word(item: &Item) -> Option<&str> {
    let payload = item.payload_view();
    assert!(!payload.is_boundary(), "a boundary is not a word");
    (payload.token_kind() == Some(TokenKind::Identifier))
        .then(|| payload.spelling())
        .flatten()
}

fn emit_keyword(i: &mut SyntaxIn, item: Item, kind: SyntaxKind, spelling: &str) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    debug_assert_eq!(item.payload_view().spelling(), Some(spelling));
    item.emit_remaining(&mut *i.state, kind);
}
