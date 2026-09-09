//! Shared direct-delimited owner and local item recovery.

use std::{ops::Range, sync::Arc};

use crate::{
    lexical::operator_scan::OperatorSite,
    operator_table::BindingPower,
    recovery_record::{
        ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    cursor::recovery::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_item, emit_recovery_error_run, emit_recovery_missing,
            emit_token_item, token_syntax_kind,
        },
    },
    expression::{continue_normalized_tail, expr_from_nud_normalized, is_nud_item},
    handoff::{Either, MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        expression_item::{expression_item, scan_expression_item_lexical},
        item::{Item, LeadingTrivia, Payload, TokenKind},
        lexer::{is_operator_shaped_unknown, scan_operator_shaped_unknown},
        observation::{implicit_delimited_newline, is_close, is_separator, token_kind},
        position::{advanced_origin, suffix_marker},
        stops::{
            STOP_CLOSES, STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, Stops,
            active_stop_item, stops_for,
        },
        trivia::newline_indentation_after_fenced_trivia,
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
};

#[derive(Clone, Copy)]
pub(crate) enum DelimitedOwner {
    Parenthesized,
    Call,
    Index,
    ProjectionTuple,
    ProjectionRecord,
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn parenthesized_nud_normalized(
    mut i: SyntaxIn,
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
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Parenthesized,
        stops,
        baseline,
        MlMode::LayoutOnly,
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
pub(crate) fn delimited_items_normalized(
    mut i: SyntaxIn,
    owner: DelimitedOwner,
    inherited_stops: Stops,
    incoming_baseline: usize,
    item_ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let inherited_closes = inherited_stops & STOP_CLOSES;
    let sequence = Some(match owner {
        DelimitedOwner::Parenthesized => crate::sequence::SequenceOwner::Parenthesized,
        DelimitedOwner::Call => crate::sequence::SequenceOwner::Call,
        DelimitedOwner::Index => crate::sequence::SequenceOwner::Index,
        DelimitedOwner::ProjectionTuple => crate::sequence::SequenceOwner::ProjectionTuple,
        DelimitedOwner::ProjectionRecord => crate::sequence::SequenceOwner::ProjectionRecord,
    });
    // Nested delimiters shield contextual and separator stops, but retain every
    // enclosing close capability. The local close is checked first below.
    let stops = stops_for(owner.close())
        | inherited_closes
        | if owner.is_record() {
            STOP_RECORD_SPREAD
        } else {
            0
        };
    let baseline =
        delimited_baseline_from_source(i.rb(), incoming_baseline, item_origin, line_entry, fence);
    let (mut item, next_origin, next_line) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    item_origin = next_origin;
    line_entry = next_line;
    let mut phase = Phase::Item;
    loop {
        if item.payload_view().is_boundary() || item.payload_view().is_eof() {
            return missing_close(i, item, owner, item_origin, line_entry);
        }
        if token_kind(&item) == Some(owner.close()) {
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }
        if is_close(&item) {
            if active_stop_item(token_kind(&item).unwrap(), inherited_closes) {
                return missing_close(i, item, owner, item_origin, line_entry);
            }
            let actual = delimiter_for_close(token_kind(&item).unwrap());
            error_item(
                i.rb(),
                item,
                item_origin,
                owner.close_role(),
                UnexpectedCategory::Punctuation(PunctuationEvidence::Close(actual)),
            );
            (item, item_origin, line_entry) = expression_item(
                i.rb(),
                OperatorSite::Nud,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            continue;
        }
        if matches!(owner, DelimitedOwner::Parenthesized)
            && token_kind(&item) == Some(TokenKind::Semicolon)
        {
            error_item(
                i.rb(),
                item,
                item_origin,
                owner.separator_role(),
                UnexpectedCategory::Punctuation(PunctuationEvidence::Semicolon),
            );
            phase = Phase::Item;
            (item, item_origin, line_entry) = expression_item(
                i.rb(),
                OperatorSite::Nud,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            continue;
        }
        if is_separator(&item) {
            if matches!(phase, Phase::Item) {
                emit_missing(i.rb(), &mut item, item_origin, owner.item_role(), false);
            }
            emit_token_item(&mut i, item);
            phase = Phase::Item;
            (item, item_origin, line_entry) = expression_item(
                i.rb(),
                OperatorSite::Nud,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            continue;
        }
        // A returned newline-bearing malformed Item must change phase once;
        // the fresh Item phase consumes it, preventing a same-Item retry loop.
        if !matches!(phase, Phase::Item)
            && implicit_delimited_newline(baseline, item.leading_view())
        {
            phase = Phase::Item;
        }
        let spread = owner.is_record() && is_record_spread_item(&item);
        if !is_nud_item(&item) && !spread {
            let role = if matches!(phase, Phase::Separator) {
                owner.separator_role()
            } else {
                owner.item_role()
            };
            item.emit_all_remaining_leading(&mut *i.state);
            (item, item_origin, line_entry) = error_run(
                i.rb(),
                item,
                role,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
                owner.is_record(),
            );
            phase = Phase::Recovered;
            continue;
        }
        if matches!(phase, Phase::Separator) {
            emit_missing(
                i.rb(),
                &mut item,
                item_origin,
                owner.separator_role(),
                false,
            );
        }
        let entry = suffix_marker(i.rb());
        let exit = if spread {
            record_spread_item_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        } else {
            if matches!(owner, DelimitedOwner::Index) {
                i.state.start_node(SyntaxKind::IndexItem.into());
            }
            let exit = expr_from_nud_normalized(
                i.rb(),
                item,
                None,
                baseline,
                stops,
                item_ml_mode,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            );
            if matches!(owner, DelimitedOwner::Index) {
                i.state.finish_node();
            }
            exit
        };
        item_origin = advanced_origin(item_origin, entry, i.rb());
        phase = Phase::Separator;
        match exit {
            NormalizedExit::Complete(Err(Either::Left(next)), line) => {
                item = next;
                line_entry = line;
            }
            NormalizedExit::Complete(Err(Either::Right(end)), line) => {
                item = end.item;
                line_entry = line;
            }
            NormalizedExit::Complete(Ok(()), line) => {
                (item, item_origin, line_entry) = expression_item(
                    i.rb(),
                    OperatorSite::Nud,
                    item_origin,
                    line,
                    fence,
                    baseline,
                    stops,
                );
            }
            exit @ NormalizedExit::Deferred(_, _) => return exit,
        }
    }
}

#[derive(Clone, Copy)]
enum Phase {
    Item,
    Separator,
    Recovered,
}

impl DelimitedOwner {
    fn close(self) -> TokenKind {
        match self {
            Self::Index => TokenKind::RBracket,
            Self::ProjectionRecord => TokenKind::RBrace,
            _ => TokenKind::RParen,
        }
    }
    fn is_record(self) -> bool {
        matches!(self, Self::ProjectionRecord)
    }
    fn item_role(self) -> GrammarRole {
        GrammarRole::Expression(match self {
            Self::Parenthesized => ExpressionRole::Nud,
            Self::Call => ExpressionRole::CallArgument,
            Self::Index => ExpressionRole::IndexItem,
            Self::ProjectionTuple => ExpressionRole::ProjectionTupleItem,
            Self::ProjectionRecord => ExpressionRole::ProjectionRecordItem,
        })
    }
    fn separator_role(self) -> GrammarRole {
        GrammarRole::Expression(match self {
            Self::Parenthesized => ExpressionRole::ParenthesizedSeparator,
            Self::Call => ExpressionRole::CallArgumentSeparator,
            Self::Index => ExpressionRole::IndexSeparator,
            Self::ProjectionTuple => ExpressionRole::ProjectionTupleSeparator,
            Self::ProjectionRecord => ExpressionRole::ProjectionRecordSeparator,
        })
    }
    fn close_role(self) -> GrammarRole {
        let (owner, delimiter) = match self {
            Self::Parenthesized => (ConstructRole::ExpressionGroup, Delimiter::Parenthesis),
            Self::Call => (ConstructRole::ArgumentList, Delimiter::Parenthesis),
            Self::Index => (ConstructRole::IndexTail, Delimiter::Bracket),
            Self::ProjectionTuple => (ConstructRole::ProjectionTupleTail, Delimiter::Parenthesis),
            Self::ProjectionRecord => (ConstructRole::ProjectionRecordTail, Delimiter::Brace),
        };
        GrammarRole::ClosingDelimiter { owner, delimiter }
    }
}

fn delimiter_for_close(close: TokenKind) -> Delimiter {
    match close {
        TokenKind::RParen => Delimiter::Parenthesis,
        TokenKind::RBracket => Delimiter::Bracket,
        TokenKind::RBrace => Delimiter::Brace,
        _ => unreachable!("only close tokens have a close delimiter"),
    }
}

fn delimited_baseline_from_source(
    mut i: SyntaxIn,
    incoming: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> usize {
    i.token(|lex| {
        Some(newline_indentation_after_fenced_trivia(
            lex.remainder(),
            item_origin,
            line_entry,
            fence,
        ))
    })
    .expect("the direct delimiter layout probe is total")
    .filter(|&indentation| indentation > incoming)
    .unwrap_or(incoming)
}

#[allow(clippy::too_many_arguments)]
fn record_spread_item_normalized(
    mut i: SyntaxIn,
    marker: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::ProjectionRecordSpreadItem.into());
    emit_token_item(&mut i, marker);
    let role = GrammarRole::Expression(ExpressionRole::ProjectionRecordSpreadRhs);
    let rhs_stops = (stops & !STOP_RECORD_SPREAD) | STOP_RECORD_SPREAD_AFTER_OPERATOR;
    let (mut rhs, origin, line) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        rhs_stops,
    );
    item_origin = origin;
    line_entry = line;
    let mut recovered = false;
    if !is_run_boundary(&rhs, baseline, true, false) && !is_nud_item(&rhs) {
        rhs.emit_all_remaining_leading(&mut *i.state);
        (rhs, item_origin, line_entry) = error_run(
            i.rb(),
            rhs,
            role,
            baseline,
            rhs_stops,
            item_origin,
            line_entry,
            fence,
            true,
        );
        recovered = true;
    }
    let exit = if !rhs.payload_view().is_boundary() && is_nud_item(&rhs) {
        expr_from_nud_normalized(
            i.rb(),
            rhs,
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
        )
    } else {
        if !recovered {
            emit_missing(i.rb(), &mut rhs, item_origin, role, true);
        }
        complete(handoff(rhs), line_entry)
    };
    i.state.finish_node();
    exit
}

fn missing_close(
    mut i: SyntaxIn,
    mut item: Item,
    owner: DelimitedOwner,
    item_origin: usize,
    line_entry: LineEntry,
) -> NormalizedExit {
    emit_missing(i.rb(), &mut item, item_origin, owner.close_role(), true);
    complete(handoff(item), line_entry)
}

fn emit_missing(
    i: SyntaxIn,
    item: &mut Item,
    item_origin: usize,
    role: GrammarRole,
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
        item.extent(item_origin).recovery_range().start
    };
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn error_item(
    i: SyntaxIn,
    item: Item,
    item_origin: usize,
    role: GrammarRole,
    category: UnexpectedCategory,
) {
    let kind = token_syntax_kind(token_kind(&item).expect("one-Item Errors have a token"));
    let range = item.extent(item_origin).recovery_range();
    emit_recovery_error_item(
        i,
        item,
        item_origin,
        kind,
        UnexpectedSyntax::Token { range, category },
        |range, unexpected| recovery_draft(role, RecoveryKind::Error, range, unexpected),
    );
}

#[allow(clippy::too_many_arguments)]
fn error_run(
    i: SyntaxIn,
    mut item: Item,
    role: GrammarRole,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    record_spread: bool,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let start = item.extent(item_origin).recovery_range().start;
            loop {
                let continues_operator_spelling =
                    record_spread && is_operator_shaped_unknown(&item);
                let kind =
                    token_syntax_kind(token_kind(&item).expect("a lexical Error emits a token"));
                let mut end = run
                    .emit_item_as(item, item_origin, kind)
                    .recovery_range()
                    .end;
                if continues_operator_spelling {
                    while let Some(token) =
                        run.lexical(|mut lex| lex.token(scan_operator_shaped_unknown))
                    {
                        item_origin = item_origin
                            .checked_add(token.text.len())
                            .expect("a lexical successor coordinate fits usize");
                        end = run
                            .emit_item_as(
                                Item::plain(LeadingTrivia::default(), Payload::Token(token)),
                                item_origin,
                                SyntaxKind::Unknown,
                            )
                            .recovery_range()
                            .end;
                    }
                }
                (item, item_origin, line_entry) = run.lexical(|lex| {
                    scan_expression_item_lexical(
                        lex,
                        OperatorSite::Nud,
                        item_origin,
                        line_entry,
                        fence,
                        baseline,
                        stops,
                    )
                });
                if is_run_boundary(&item, baseline, record_spread, true) || is_nud_item(&item) {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| recovery_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn is_run_boundary(item: &Item, baseline: usize, record_spread: bool, newline: bool) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || (record_spread && is_record_spread_item(item))
        || (newline && implicit_delimited_newline(baseline, item.leading_view()))
}

fn is_record_spread_item(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::DotDot)
}

fn recovery_draft(
    role: GrammarRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        GrammarRole::Expression(
            ExpressionRole::ParenthesizedSeparator
            | ExpressionRole::CallArgumentSeparator
            | ExpressionRole::IndexSeparator
            | ExpressionRole::ProjectionTupleSeparator
            | ExpressionRole::ProjectionRecordSeparator,
        ) => ExpectedSyntax::DelimitedSequenceSeparator,
        GrammarRole::Expression(_) => ExpectedSyntax::Expression,
        _ => unreachable!("a delimited owner selects its finite slot roles"),
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
