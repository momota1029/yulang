//! Direct expression ownership and Item handoff for the isolated rewrite.

use super::ambient_claim::{AmbientClaimContext, AmbientClaimView};
use std::sync::Arc;

use reborrow_generic::Reborrow as _;

use crate::{
    operator::BindingPower,
    scan::operator::OperatorSite,
    session::{
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use super::{
    LexIn, RewriteIn, Stops,
    case_like::{CaseLikeFamily, case_like_nud_normalized},
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    delimited::parenthesized_nud_normalized,
    emit::{
        ErrorRunOutput, emit_identifier_core, emit_integer_core, emit_operator_use,
        emit_recovery_error_run, emit_recovery_missing, token_syntax_kind,
    },
    if_expr::if_nud_normalized,
    item::{Item, LeadingTrivia, LeadingView, OperatorUse, TokenKind},
    lexer::{
        contextual_word_suffix_follower, scan_expression_payload, scan_nud_payload,
        scan_operator_shaped_unknown,
    },
    literal::{
        NormalizedRuleLiteralExit, NormalizedStringLiteralExit, quote_run, rule_literal_normalized,
        scan_expression_rule_literal_opener_token, scan_pattern_literal_opener_token,
        scan_string_opener_token, string_literal_with_virtual_statements_normalized,
        string_mode_from_opener,
    },
    operator::{
        STOP_LINE_BREAK, STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, active_stop_item,
    },
    output::RecoveryDraft,
    statement::{StatementLineHandoff, braced_nud_normalized},
    tails::{
        call_tail_normalized, colon_tail_normalized, dot_tail_normalized, index_tail_normalized,
        path_tail_normalized, with_tail_normalized,
    },
    yumark::FenceBoundary,
};

#[derive(Debug, Eq, PartialEq)]
pub(super) enum Either<L, R> {
    Left(L),
    Right(R),
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct End {
    pub(super) item: Item,
}

/// `Ok(())` lets the caller scan its successor after it closes its own node.
pub(super) type TailExit = Result<(), Either<Item, End>>;

#[derive(Clone, Copy)]
pub(super) enum MlMode {
    All,
    LayoutOnly,
    None,
}

pub(super) enum NormalizedExit {
    Complete(TailExit, LineEntry),
    Deferred(Item, LineEntry),
}

pub(super) fn expr(i: RewriteIn) -> Option<TailExit> {
    expr_normalized(
        i,
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .map(ordinary_exit)
}

pub(super) fn expr_normalized(
    mut i: RewriteIn,
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
) -> Option<NormalizedExit> {
    let (nud, item_origin, line_entry) =
        optional_nud_item(i.rb(), item_origin, line_entry, fence, baseline, stops)?;
    Some(expr_from_nud_normalized(
        i,
        nud,
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
    ))
}

pub(super) fn expr_from_nud(
    i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(expr_from_nud_normalized(
        i,
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
        None,
    ))
}

pub(super) fn expr_from_nud_normalized(
    mut i: RewriteIn,
    nud: Item,
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
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = append_nud(
        i.rb(),
        nud,
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
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn append_nud(
    mut i: RewriteIn,
    nud: Item,
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
    if is_expression_rule_literal_opener(&nud) {
        return append_rule_literal_nud(
            i,
            nud,
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
    if let Some(mode) = string_mode_from_opener(&nud) {
        return append_string_literal_nud(
            i,
            nud,
            mode,
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
    if is_contextual_word(i.rb(), &nud, "case") {
        return case_like_nud_normalized(
            i,
            CaseLikeFamily::Case,
            nud,
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
    if is_contextual_word(i.rb(), &nud, "catch") {
        return case_like_nud_normalized(
            i,
            CaseLikeFamily::Catch,
            nud,
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
    if is_contextual_word(i.rb(), &nud, "if") {
        return if_nud_normalized(
            i,
            nud,
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
    match token_kind(&nud) {
        Some(TokenKind::Identifier) => {
            emit_identifier_core(&mut i, nud);
            scan_tail_after_accept_normalized(
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
            )
        }
        Some(TokenKind::Integer) => {
            emit_integer_core(&mut i, nud);
            scan_tail_after_accept_normalized(
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
            )
        }
        Some(TokenKind::LParen) => parenthesized_nud_normalized(
            i,
            nud,
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
        ),
        Some(TokenKind::LBrace) => braced_nud_normalized(
            i,
            nud,
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
        ),
        Some(TokenKind::Operator) => operator_nud(
            i,
            nud,
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
        ),
        _ => unreachable!("the NUD scanner accepts only normal core items and `(`"),
    }
}

#[allow(clippy::too_many_arguments)]
fn append_string_literal_nud(
    mut i: RewriteIn,
    opener: Item,
    mode: super::literal::StringMode,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    _line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = string_literal_with_virtual_statements_normalized(
        i.rb(),
        opener,
        mode,
        item_origin,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedStringLiteralExit::Complete(line_entry) => scan_tail_after_accept_normalized(
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
        ),
        NormalizedStringLiteralExit::Boundary(item, line_entry) => {
            complete(handoff(item), line_entry)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn append_rule_literal_nud(
    mut i: RewriteIn,
    opener: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    _line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = rule_literal_normalized(
        i.rb(),
        opener,
        item_origin,
        LineEntry::InLine,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedRuleLiteralExit::Complete(line_entry) => scan_tail_after_accept_normalized(
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
        ),
        NormalizedRuleLiteralExit::Boundary(item, line_entry) => {
            complete(handoff(item), line_entry)
        }
    }
}

/// An accepted prefix or infix always owns its mandatory right operand. A pure
/// local absence is Missing; malformed source is one Error sentinel and never
/// receives a second Missing at the same boundary.
pub(super) fn required_expr_after_accept(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(required_expr_after_accept_normalized(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn required_expr_after_accept_normalized(
    mut i: RewriteIn,
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
    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
    );
    required_expr_item_normalized(
        i,
        item,
        GrammarRole::Expression(ExpressionRole::Nud),
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

pub(super) fn required_expr_item(
    i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(required_expr_item_normalized(
        i,
        item,
        GrammarRole::Expression(ExpressionRole::Nud),
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn required_expr_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    initial_role: GrammarRole,
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
    if is_required_operand_boundary(i.rb(), &item, stops) {
        emit_required_expression_missing(&mut i, &mut item, item_origin, stops, initial_role);
        return complete(handoff(item), line_entry);
    }
    if is_nud_item(&item) {
        return append_nud(
            i,
            item,
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
    item.emit_all_remaining_leading(&mut *i.state);
    (item, item_origin, line_entry) = emit_required_expression_error_run(
        i.rb(),
        item,
        initial_role,
        stops,
        item_origin,
        line_entry,
        fence,
        baseline,
    );
    if is_required_operand_boundary(i.rb(), &item, stops) {
        return complete(handoff(item), line_entry);
    }
    debug_assert!(is_nud_item(&item));
    append_nud(
        i,
        item,
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

pub(super) fn is_required_operand_boundary(mut i: RewriteIn, item: &Item, stops: Stops) -> bool {
    (item.payload_view().is_eof() || item.payload_view().is_boundary())
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || is_unread_operand_boundary(item)
}

fn is_unread_operand_boundary(item: &Item) -> bool {
    !is_nud_item(item)
        && (is_close(item)
            || matches!(
                token_kind(item),
                Some(TokenKind::LBracket | TokenKind::LBrace)
            ))
}

fn is_required_operand_boundary_in_error_run(
    run: &mut ErrorRunOutput<'_, '_, '_, '_, '_, '_>,
    item: &Item,
    stops: Stops,
) -> bool {
    (item.payload_view().is_eof() || item.payload_view().is_boundary())
        || is_line_stop(item, stops)
        || is_unread_operand_boundary(item)
        || run.lexical(|lex| is_active_stop_lex(lex, item, stops))
}

pub(super) fn emit_required_expression_missing(
    i: &mut RewriteIn,
    item: &mut Item,
    item_origin: usize,
    stops: Stops,
    role: GrammarRole,
) {
    let at = if item.payload_view().is_boundary() {
        item.payload_view()
            .pending_boundary()
            .expect("a boundary Item retains its inspected boundary")
            .coordinate()
    } else if is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || is_unread_operand_boundary(item)
    {
        item.extent(item_origin).recovery_range().start
    } else if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        item.extent(item_origin).recovery_range().start
    } else {
        item.extent(item_origin).recovery_range().start
    };
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        required_expression_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

#[allow(clippy::too_many_arguments)]
fn emit_required_expression_error_run(
    i: RewriteIn,
    mut item: Item,
    role: GrammarRole,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(
        i,
        |run| {
            let run_start = item.extent(item_origin).recovery_range().start;
            loop {
                let kind = required_expression_error_syntax_kind(&item);
                let run_end = run
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
                        stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
                    )
                });
                if is_required_operand_boundary_in_error_run(run, &item, stops)
                    || is_nud_item(&item)
                {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: run_start..run_end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (item, item_origin, line_entry);
                }
            }
        },
        |range, unexpected| {
            required_expression_recovery_draft(role, RecoveryKind::Error, range, unexpected)
        },
    )
}

fn required_expression_error_syntax_kind(item: &Item) -> SyntaxKind {
    match token_kind(item).expect("a required-expression Error contains lexical Items") {
        TokenKind::Operator => SyntaxKind::Operator,
        kind => token_syntax_kind(kind),
    }
}

fn required_expression_recovery_draft(
    role: GrammarRole,
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
            expected: ExpectedSyntax::Expression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

pub(super) fn scan_tail_after_accept(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(scan_tail_after_accept_normalized(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn scan_tail_after_accept_normalized(
    mut i: RewriteIn,
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
    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Led,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    tail_normalized(
        i,
        item,
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

pub(super) fn continue_completed_tail(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    exit: TailExit,
) -> TailExit {
    match exit {
        Ok(()) => scan_tail_after_accept(i, threshold, baseline, stops, ml_mode, line_handoff),
        Err(Either::Left(item)) => tail(i, item, threshold, baseline, stops, ml_mode, line_handoff),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn continue_normalized_tail(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    exit: NormalizedExit,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => scan_tail_after_accept_normalized(
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
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => tail_normalized(
            i,
            item,
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
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Deferred(item, line_entry) => NormalizedExit::Deferred(item, line_entry),
    }
}

pub(super) fn tail(
    i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(tail_normalized(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(baseline)).into(),
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn tail_normalized(
    mut i: RewriteIn,
    item: Item,
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
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if is_active_stop(i.rb(), &item, stops) || is_line_stop(&item, stops) {
        return complete(handoff(item), line_entry);
    }
    if is_with_tail_item(i.rb(), &item, baseline, ml_mode) {
        return with_tail_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if item.leading_view().is_grammar_empty() {
        match token_kind(&item) {
            Some(TokenKind::LParen) => {
                return call_tail_normalized(
                    i,
                    item,
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
            Some(TokenKind::LBracket) => {
                return index_tail_normalized(
                    i,
                    item,
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
    match token_kind(&item) {
        Some(TokenKind::Dot) => {
            return dot_tail_normalized(
                i,
                item,
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
        Some(TokenKind::PathSeparator) => {
            return path_tail_normalized(
                i,
                item,
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
        Some(TokenKind::Operator) if is_led_operator(&item) => {
            return operator_tail(
                i,
                item,
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
    if is_ml_argument(&item, baseline, ml_mode) {
        return ml_argument(
            i,
            item,
            threshold,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if token_kind(&item) == Some(TokenKind::Colon) {
        return colon_tail_normalized(
            i,
            item,
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
    complete(handoff(item), line_entry)
}

fn is_with_tail_item(mut i: RewriteIn, item: &Item, baseline: usize, ml_mode: MlMode) -> bool {
    !matches!(ml_mode, MlMode::None)
        && chain_continuation(item.leading_view(), baseline)
        && is_contextual_word(i.rb(), item, "with")
}

fn is_ml_argument(item: &Item, baseline: usize, mode: MlMode) -> bool {
    if !is_nud_item(item) || item.leading_view().is_grammar_empty() || matches!(mode, MlMode::None)
    {
        return false;
    }
    let indentation = indentation_after_newline(item.leading_view());
    match mode {
        MlMode::All => indentation.is_none_or(|indentation| indentation > baseline),
        MlMode::LayoutOnly => indentation.is_some_and(|indentation| indentation > baseline),
        MlMode::None => false,
    }
}

pub(super) fn chain_continuation(leading: LeadingView<'_>, baseline: usize) -> bool {
    indentation_after_newline(leading).is_none_or(|indentation| indentation > baseline)
}

pub(super) fn is_led_operator(item: &Item) -> bool {
    matches!(
        operator_use(item),
        Some(OperatorUse::Infix { .. } | OperatorUse::Suffix(_))
    )
}

#[allow(clippy::too_many_arguments)]
fn ml_argument(
    mut i: RewriteIn,
    argument: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::MlArgument.into());
    let entry = suffix_marker(i.rb());
    let exit = expr_from_nud_normalized(
        i.rb(),
        argument,
        threshold,
        baseline,
        stops,
        MlMode::None,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    let child_origin = advanced_origin(item_origin, entry, i.rb());
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        MlMode::All,
        line_handoff,
        exit,
        child_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn operator_nud(
    mut i: RewriteIn,
    operator: Item,
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
    match operator_use(&operator) {
        Some(OperatorUse::Prefix(right)) => {
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::PrefixOperatorUse);
            let entry = suffix_marker(i.rb());
            let rhs = required_expr_after_accept_normalized(
                i.rb(),
                Some(&right),
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
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            continue_normalized_tail(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                rhs,
                item_origin,
                fence,
                ambient,
                sequence,
            )
        }
        Some(OperatorUse::Nullfix) => {
            emit_operator_use(&mut i, operator, SyntaxKind::NullfixOperatorUse);
            scan_tail_after_accept_normalized(
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
            )
        }
        _ => unreachable!("the NUD scanner accepts only prefix and nullfix operators"),
    }
}

#[allow(clippy::too_many_arguments)]
fn operator_tail(
    mut i: RewriteIn,
    operator: Item,
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
    match operator_use(&operator) {
        Some(OperatorUse::Infix { left, right }) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return complete(handoff(operator), line_entry);
            }
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::InfixOperatorUse);
            let entry = suffix_marker(i.rb());
            let rhs = required_expr_after_accept_normalized(
                i.rb(),
                Some(&right),
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
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            continue_normalized_tail(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                rhs,
                item_origin,
                fence,
                ambient,
                sequence,
            )
        }
        Some(OperatorUse::Suffix(left)) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return complete(handoff(operator), line_entry);
            }
            emit_operator_use(&mut i, operator, SyntaxKind::SuffixOperatorUse);
            scan_tail_after_accept_normalized(
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
            )
        }
        _ => unreachable!("the LED scanner accepts only infix and suffix operators"),
    }
}

fn optional_nud_item(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<(Item, usize, LineEntry)> {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i.token(|lex| {
        let current = current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |mut lex, leading, origin, fence, _| {
                scan_expression_literal_payload(lex.rb(), OperatorSite::Nud)
                    .or_else(|| scan_nud_payload(lex, leading, origin, fence, baseline, stops))
            },
        )?;
        let payload = current.item.payload_view();
        if payload.is_boundary() || payload.is_eof() || !is_nud_item(&current.item) {
            return None;
        }
        Some(current)
    })?;
    let item_origin = advanced_origin(item_origin, entry, i);
    Some((item, item_origin, next_line_entry))
}

pub(super) fn expression_item(
    mut i: RewriteIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_expression_item_lexical(
            lex,
            site,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        ))
    })
    .expect("expression payload scanning is total")
}

/// One total lexical operation shared by ordinary and sealed Error-run paths.
#[allow(clippy::too_many_arguments)]
pub(super) fn scan_expression_item_lexical(
    i: LexIn,
    site: OperatorSite,
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
                scan_expression_payload_with_literals(
                    lex, site, leading, origin, fence, baseline, stops,
                )
            },
        )
        .expect("expression payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("a direct expression coordinate must fit usize"),
        current.next_line_entry,
    )
}

pub(super) fn scan_expression_payload_with_literals(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    if let Some(literal) = i.token(|lex| scan_expression_literal_payload(lex, site)) {
        return Some(literal);
    }
    scan_expression_payload(
        i,
        site,
        has_leading_trivia,
        payload_origin,
        fence,
        baseline,
        stops,
    )
}

pub(super) fn scan_expression_literal_payload(
    mut i: LexIn,
    site: OperatorSite,
) -> Option<AcceptedPayload> {
    if matches!(site, OperatorSite::Nud)
        && let Some(token) = i.token(scan_expression_rule_literal_opener_token)
    {
        return Some(literal_payload(token));
    }
    i.token(scan_string_opener_token)
        .map(|(token, _)| literal_payload(token))
}

pub(super) fn scan_pattern_literal_payload(mut i: LexIn) -> Option<AcceptedPayload> {
    // Pattern reserves one quote for RuleLiteral and three or more for String;
    // keep the rejected two-quote run maximal as one ordinary recovery Item.
    if quote_run(i.remainder()) == 2 {
        return i.token(scan_operator_shaped_unknown).map(literal_payload);
    }
    i.token(scan_pattern_literal_opener_token)
        .map(literal_payload)
}

fn literal_payload(token: super::item::Token) -> AcceptedPayload {
    AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    }
}

pub(super) fn complete(exit: TailExit, line_entry: LineEntry) -> NormalizedExit {
    NormalizedExit::Complete(exit, line_entry)
}

pub(super) fn ordinary_exit(exit: NormalizedExit) -> TailExit {
    match exit {
        NormalizedExit::Complete(exit, _) => exit,
        NormalizedExit::Deferred(_, _) => {
            unreachable!("ordinary expressions enter every direct-rewrite owner")
        }
    }
}

pub(super) fn suffix_marker(mut i: RewriteIn) -> (usize, usize) {
    i.token(|lex| Some((lex.remainder().as_ptr() as usize, lex.remainder().len())))
        .expect("the live expression suffix probe is total")
}

pub(super) fn advanced_origin(
    item_origin: usize,
    (entry_pointer, entry_length): (usize, usize),
    i: RewriteIn,
) -> usize {
    let (suffix_pointer, suffix_length) = suffix_marker(i);
    let consumed = entry_length
        .checked_sub(suffix_length)
        .expect("a direct expression child cannot lengthen its live suffix");
    assert_eq!(
        entry_pointer.wrapping_add(consumed),
        suffix_pointer,
        "a direct expression child keeps the input on one source suffix",
    );
    item_origin
        .checked_add(consumed)
        .expect("a direct expression coordinate must fit usize")
}

pub(super) fn is_nud_item(item: &Item) -> bool {
    is_statement_nud(item)
        || matches!(
            operator_use(item),
            Some(OperatorUse::Prefix(_) | OperatorUse::Nullfix)
        )
}

/// A local stop is determined from the complete Item, not only punctuation.
/// Dynamic word operators need the live suffix probe to retain `elsif?` and
/// `else!` as operators rather than splitting them into contextual words.
pub(super) fn is_active_stop(i: RewriteIn, item: &Item, stops: Stops) -> bool {
    i.map(
        |lex: LexIn| Some(is_active_stop_lex(lex, item, stops)),
        |active| active,
    )
    .expect("typed stop observation is total")
}

pub(super) fn is_active_stop_lex(mut i: LexIn, item: &Item, stops: Stops) -> bool {
    if token_kind(item).is_some_and(|kind| active_stop_item(kind, stops)) {
        return true;
    }
    (stops & super::operator::STOP_ELSIF != 0 && is_contextual_word_lex(i.rb(), item, "elsif"))
        || (stops & super::operator::STOP_ELSE != 0 && is_contextual_word_lex(i, item, "else"))
}

pub(super) fn is_contextual_word(mut i: RewriteIn, item: &Item, word: &str) -> bool {
    let payload = item.payload_view();
    if payload.token_kind() == Some(TokenKind::Identifier) {
        return payload.spelling() == Some(word);
    }
    if payload.operator_use().is_some() {
        return payload.spelling() == Some(word)
            && i.rb()
                .map(contextual_word_suffix_follower, |follower| follower)
                .unwrap_or(false);
    }
    assert!(
        !payload.is_boundary(),
        "a boundary is not a contextual word"
    );
    false
}

fn is_contextual_word_lex(mut i: LexIn, item: &Item, word: &str) -> bool {
    let payload = item.payload_view();
    if payload.token_kind() == Some(TokenKind::Identifier) {
        return payload.spelling() == Some(word);
    }
    if payload.operator_use().is_some() {
        return payload.spelling() == Some(word)
            && i.token(contextual_word_suffix_follower)
                .expect("contextual suffix observation is total");
    }
    assert!(
        !payload.is_boundary(),
        "a boundary is not a contextual word"
    );
    false
}

pub(super) fn is_statement_nud(item: &Item) -> bool {
    is_normal_core_item(item)
        || token_kind(item) == Some(TokenKind::LBrace)
        || string_mode_from_opener(item).is_some()
        || is_expression_rule_literal_opener(item)
}

fn is_expression_rule_literal_opener(item: &Item) -> bool {
    item.payload_view().spelling() == Some("~\"")
}

pub(super) fn is_normal_core_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::Integer | TokenKind::LParen)
    )
}

pub(super) fn is_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

pub(super) fn is_close(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    )
}

pub(super) fn handoff(item: Item) -> TailExit {
    if item.payload_view().is_eof() {
        Err(Either::Right(End { item }))
    } else {
        Err(Either::Left(item))
    }
}

pub(super) fn token_kind(item: &Item) -> Option<TokenKind> {
    let payload = item.payload_view();
    if let Some(kind) = payload.token_kind() {
        return Some(kind);
    }
    if payload.operator_use().is_some() {
        return Some(TokenKind::Operator);
    }
    assert!(!payload.is_boundary(), "a boundary has no token kind");
    None
}

fn operator_use(item: &Item) -> Option<&OperatorUse> {
    item.payload_view().operator_use()
}

pub(super) fn delimited_baseline(incoming: usize, leading: LeadingView<'_>) -> usize {
    indentation_after_newline(leading)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

pub(super) fn implicit_delimited_newline(baseline: usize, leading: LeadingView<'_>) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

pub(super) fn indentation_after_newline(leading: LeadingView<'_>) -> Option<usize> {
    leading.indentation_after_newline()
}

pub(super) fn is_line_stop(item: &Item, stops: Stops) -> bool {
    stops & STOP_LINE_BREAK != 0 && indentation_after_newline(item.leading_view()).is_some()
}
