//! Direct fixed continuations over already-owned Items.

use super::ambient_claim::AmbientClaimContext;
use crate::session::{
    ColonApplicationRole, ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole,
    PunctuationEvidence as Punctuation, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
    UnexpectedCategory, UnexpectedSyntax, WithBodyRole,
};
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use crate::{operator::BindingPower, rewrite::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{LineEntry, current_item},
    delimited::{DelimitedOwner, delimited_items_normalized},
    driver::{
        Either, MlMode, NormalizedExit, advanced_origin, chain_continuation, complete,
        continue_normalized_tail, expr_from_nud_normalized, expression_item, handoff,
        implicit_delimited_newline, is_active_stop, is_active_stop_lex, is_close, is_led_operator,
        is_line_stop, is_nud_item, is_separator, scan_expression_item_lexical,
        scan_tail_after_accept_normalized, suffix_marker, tail_normalized, token_kind,
    },
    emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, emit_with_keyword,
        token_syntax_kind,
    },
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{introduced_body_indentation_normalized, scan_path_segment_payload},
    operator::{STOP_COMMA, STOP_LINE_BREAK, lone_colon_after_fenced_trivia},
    output::RecoveryDraft,
    statement::{
        StatementAdmission, StatementLineHandoff, canonical_statement_from_admission_normalized,
        classify_statement_item_lexical, classify_statement_item_normalized,
        indented_statement_block_normalized, scan_statement_item_lexical,
        statement_item_normalized,
    },
    yumark::FenceBoundary,
};

/// A lone eligible colon is terminal and owns its mandatory RHS, including
/// recovery. Inline RHSs use the direct expression vocabulary; indented RHSs
/// use canonical Statements.
#[allow(clippy::too_many_arguments)]
pub(super) fn colon_tail_normalized(
    mut i: RewriteIn,
    mut colon: Item,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    if matches!(ml_mode, MlMode::None) || !chain_continuation(colon.leading_view(), baseline) {
        return complete(handoff(colon), line_entry);
    }
    let indentation = introduced_body_indentation_normalized(i.rb(), item_origin, fence);
    let indented = indentation.is_some_and(|indentation| indentation > baseline);

    colon.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::ColonApplicationTail.into());
    emit_token_item(&mut i, colon);

    let exit = if !indented {
        let (mut item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops | STOP_COMMA,
        );
        if indentation.is_some() {
            emit_inline_slot_missing(
                i.rb(),
                &mut item,
                item_origin,
                GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
                ExpectedSyntax::Expression,
                stops | STOP_LINE_BREAK,
            );
            complete(handoff(item), line_entry)
        } else {
            inline_colon_argument_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                ml_mode,
                ColonApplicationRole::Rhs,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
    } else {
        indented_statement_block_normalized(
            i.rb(),
            baseline,
            GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    };
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn inline_colon_argument_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    role: ColonApplicationRole,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        emit_inline_slot_missing(
            i.rb(),
            &mut item,
            item_origin,
            GrammarRole::ColonApplication(role),
            ExpectedSyntax::Expression,
            stops,
        );
        return complete(handoff(item), line_entry);
    }
    if is_colon_owned_boundary(i.rb(), &item, baseline, stops, sequence) {
        emit_inline_slot_missing(
            i.rb(),
            &mut item,
            item_origin,
            GrammarRole::ColonApplication(role),
            ExpectedSyntax::Expression,
            stops,
        );
        return inline_colon_successor_normalized(
            i,
            complete(handoff(item), line_entry),
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            fence,
            ambient,
            sequence,
        );
    }
    if inline_colon_boundary(i.rb(), &item, baseline, stops) {
        emit_inline_slot_missing(
            i.rb(),
            &mut item,
            item_origin,
            GrammarRole::ColonApplication(role),
            ExpectedSyntax::Expression,
            stops,
        );
        return complete(handoff(item), line_entry);
    }

    emit_inline_leading(&mut i, &mut item);
    if !is_nud_item(&item) {
        (item, item_origin, line_entry) = retry_inline_colon_argument_normalized(
            i.rb(),
            item,
            role,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
        if is_colon_owned_boundary(i.rb(), &item, baseline, stops, sequence) {
            return inline_colon_successor_normalized(
                i,
                complete(handoff(item), line_entry),
                baseline,
                stops,
                ml_mode,
                line_handoff,
                item_origin,
                fence,
                ambient,
                sequence,
            );
        }
        if inline_colon_boundary(i.rb(), &item, baseline, stops) {
            if item.payload_view().is_eof() && !is_line_stop(&item, stops) {
                item.emit_eof_leading(&mut *i.state);
            }
            return complete(handoff(item), line_entry);
        }
        emit_inline_leading(&mut i, &mut item);
    }

    let entry = suffix_marker(i.rb());
    let exit = expr_from_nud_normalized(
        i.rb(),
        item,
        None,
        baseline,
        stops | STOP_COMMA,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence.or(Some(super::sequence::SequenceOwner::Colon)),
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    inline_colon_successor_normalized(
        i,
        exit,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn inline_colon_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry)
            if is_colon_owned_boundary(i.rb(), &end.item, baseline, stops, sequence) =>
        {
            end.item.emit_all_remaining_leading(&mut *i.state);
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            complete(handoff(item), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Left(mut item)), line_entry)
            if is_colon_owned_boundary(i.rb(), &item, baseline, stops, sequence) =>
        {
            let (mut item, item_origin, line_entry) = if token_kind(&item) == Some(TokenKind::Comma)
            {
                emit_token_item(&mut i, item);
                expression_item(
                    i.rb(),
                    OperatorSite::Nud,
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops | STOP_COMMA,
                )
            } else {
                item.emit_all_remaining_leading(&mut *i.state);
                (item, item_origin, line_entry)
            };
            // A comma and its following qualifying newline form one boundary.
            // Protected Items retain their leading for the enclosing owner.
            if !item.payload_view().is_boundary()
                && !is_close(&item)
                && !is_active_stop(i.rb(), &item, stops)
                && !is_line_stop(&item, stops)
                && implicit_delimited_newline(baseline, item.leading_view())
            {
                item.emit_all_remaining_leading(&mut *i.state);
            }
            inline_colon_argument_normalized(
                i,
                item,
                baseline,
                stops,
                ml_mode,
                ColonApplicationRole::InlineArgument,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        exit => exit,
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_inline_colon_argument_normalized(
    i: RewriteIn,
    mut item: Item,
    role: ColonApplicationRole,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            loop {
                let kind =
                    token_syntax_kind(token_kind(&item).expect("a Colon Error emits a token"));
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                (item, item_origin, line_entry) = run.lexical(|lex| {
                    scan_expression_item_lexical(
                        lex,
                        OperatorSite::Nud,
                        item_origin,
                        line_entry,
                        fence,
                        baseline,
                        stops | STOP_COMMA,
                    )
                });
                if inline_boundary(&item, baseline, stops)
                    || run.lexical(|lex| is_active_stop_lex(lex, &item, stops))
                    || is_nud_item(&item)
                {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| {
            inline_slot_draft(
                GrammarRole::ColonApplication(role),
                ExpectedSyntax::Expression,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    )
}

fn is_colon_owned_boundary(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    sequence: super::sequence::SequenceContext,
) -> bool {
    sequence.is_none()
        && !item.payload_view().is_boundary()
        && !is_close(item)
        && !is_active_stop(i.rb(), item, stops)
        && !is_line_stop(item, stops)
        && (token_kind(item) == Some(TokenKind::Comma)
            || implicit_delimited_newline(baseline, item.leading_view()))
}

fn inline_colon_boundary(i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    inline_boundary(item, baseline, stops)
        || i.map(
            |lex: LexIn| Some(is_active_stop_lex(lex, item, stops)),
            |stop| stop,
        )
        .unwrap_or(false)
}

fn inline_boundary(item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn emit_inline_leading(i: &mut RewriteIn, item: &mut Item) {
    if !item.leading_view().is_grammar_empty() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

fn emit_inline_slot_missing(
    i: RewriteIn,
    item: &mut Item,
    origin: usize,
    role: GrammarRole,
    expected: ExpectedSyntax,
    stops: Stops,
) {
    let at = if item.payload_view().is_boundary() {
        item.payload_view()
            .pending_boundary()
            .expect("boundary coordinate")
            .coordinate()
    } else {
        if item.payload_view().is_eof() && !is_line_stop(item, stops) {
            item.emit_eof_leading(&mut *i.state);
        }
        item.extent(origin).recovery_range().start
    };
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        inline_slot_draft(role, expected, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn inline_slot_draft(
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
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

/// The terminal generic `with:` continuation. Its body is an existing direct
/// Statement callee, never a target-owning or replayed expression parser.
#[allow(clippy::too_many_arguments)]
pub(super) fn with_tail_normalized(
    mut i: RewriteIn,
    mut keyword: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::WithBodyTail.into());
    emit_with_keyword(&mut i, keyword);

    let has_colon = i
        .rb()
        .map(
            |lex: super::LexIn| {
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
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
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
    mut i: RewriteIn,
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
    sequence: super::sequence::SequenceContext,
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
    i: RewriteIn,
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

fn with_inline_boundary(i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    inline_colon_boundary(i, item, baseline, stops)
}

fn with_inline_terminal_normalized(
    mut i: RewriteIn,
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

#[allow(clippy::too_many_arguments)]
pub(super) fn call_tail_normalized(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Call,
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn index_tail_normalized(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Index,
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn dot_tail_normalized(
    mut i: RewriteIn,
    dot: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    let (next, item_origin, line_entry) = super::driver::expression_item(
        i.rb(),
        OperatorSite::Led,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if !next.payload_view().is_boundary() && next.leading_view().is_grammar_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => {
                return projection_tail_normalized(
                    i,
                    dot,
                    next,
                    SyntaxKind::ProjectionTupleTail,
                    false,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                    sequence,
                );
            }
            Some(TokenKind::LBrace) => {
                return projection_tail_normalized(
                    i,
                    dot,
                    next,
                    SyntaxKind::ProjectionRecordTail,
                    true,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                    sequence,
                );
            }
            _ => {}
        }
    }
    field_tail_normalized(
        i,
        dot,
        next,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn field_tail_normalized(
    mut i: RewriteIn,
    dot: Item,
    mut name: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    let boundary = is_fixed_tail_boundary(&name)
        || is_line_stop(&name, stops)
        || is_active_stop(i.rb(), &name, stops);
    if !boundary
        && token_kind(&name) == Some(TokenKind::Identifier)
        && name.leading_view().is_grammar_empty()
    {
        emit_token_item(&mut i, name);
        i.state.finish_node();
        return scan_tail_after_accept_normalized(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if boundary || !name.leading_view().is_grammar_empty() {
        emit_fixed_tail_missing(
            i.rb(),
            &mut name,
            item_origin,
            ExpressionRole::FieldName,
            false,
        );
    } else {
        name.emit_all_remaining_leading(&mut *i.state);
        (name, item_origin, line_entry) = retry_fixed_tail_item_normalized(
            i.rb(),
            name,
            ExpressionRole::FieldName,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    i.state.finish_node();
    tail_normalized(
        i,
        name,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn projection_tail_normalized(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    node: SyntaxKind,
    record_spread: bool,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(node.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        if record_spread {
            DelimitedOwner::ProjectionRecord
        } else {
            DelimitedOwner::ProjectionTuple
        },
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn path_tail_normalized(
    mut i: RewriteIn,
    separator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let (mut segment, next_origin, next_line_entry) =
        path_segment_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    item_origin = next_origin;
    line_entry = next_line_entry;
    let boundary = is_fixed_tail_boundary(&segment)
        || is_line_stop(&segment, stops)
        || is_active_stop(i.rb(), &segment, stops);
    if !boundary
        && matches!(
            token_kind(&segment),
            Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
        )
    {
        emit_token_item(&mut i, segment);
        i.state.finish_node();
        return scan_tail_after_accept_normalized(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if boundary {
        let eof_leading = !is_line_stop(&segment, stops);
        emit_fixed_tail_missing(
            i.rb(),
            &mut segment,
            item_origin,
            ExpressionRole::PathSegment,
            eof_leading,
        );
    } else {
        segment.emit_all_remaining_leading(&mut *i.state);
        (segment, item_origin, line_entry) = retry_fixed_tail_item_normalized(
            i.rb(),
            segment,
            ExpressionRole::PathSegment,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    i.state.finish_node();
    tail_normalized(
        i,
        segment,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

fn path_segment_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_path_item_lexical(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        ))
    })
    .expect("path-segment payload scanning is total")
}

fn scan_path_item_lexical(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let (current, consumed) = i.with_str(|lex| {
        current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |lex, leading, origin, fence, _| {
                scan_path_segment_payload(lex, leading, origin, fence, baseline, stops)
            },
        )
        .expect("path-segment payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("a path coordinate fits usize"),
        current.next_line_entry,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_fixed_tail_item_normalized(
    i: RewriteIn,
    mut item: Item,
    role: ExpressionRole,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            loop {
                let kind =
                    token_syntax_kind(token_kind(&item).expect("a fixed-tail Error emits a token"));
                let end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                (item, item_origin, line_entry) = run.lexical(|lex| {
                    if role == ExpressionRole::PathSegment {
                        scan_path_item_lexical(lex, item_origin, line_entry, fence, baseline, stops)
                    } else {
                        scan_expression_item_lexical(
                            lex,
                            OperatorSite::Led,
                            item_origin,
                            line_entry,
                            fence,
                            baseline,
                            stops,
                        )
                    }
                });
                if is_fixed_tail_boundary(&item)
                    || is_line_stop(&item, stops)
                    || !item.leading_view().is_grammar_empty()
                    || matches!(
                        token_kind(&item),
                        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
                    )
                    || run.lexical(|lex| is_active_stop_lex(lex, &item, stops))
                {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| fixed_tail_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn emit_fixed_tail_missing(
    i: RewriteIn,
    item: &mut Item,
    origin: usize,
    role: ExpressionRole,
    eof_leading: bool,
) {
    let at = if item.payload_view().is_boundary() {
        item.payload_view()
            .pending_boundary()
            .expect("a boundary retains its coordinate")
            .coordinate()
    } else {
        if eof_leading && item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
        }
        item.extent(origin).recovery_range().start
    };
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        fixed_tail_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn fixed_tail_draft(
    role: ExpressionRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Expression(role);
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Identifier,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn is_fixed_tail_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || item.payload_view().is_boundary()
        || is_separator(item)
        || is_close(item)
        || is_led_operator(item)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::LParen
                    | TokenKind::LBracket
                    | TokenKind::Dot
                    | TokenKind::PathSeparator
                    | TokenKind::Colon
            )
        )
}
