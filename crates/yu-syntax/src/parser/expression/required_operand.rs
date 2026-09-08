//! Mandatory operands: boundary publication, lexical Error runs and NUD retry.

use std::sync::Arc;

use reborrow_generic::Reborrow as _;

use super::operator_chain::{append_nud, is_nud_item};
use crate::{
    operator::BindingPower,
    parser::{
        ParserIn, Stops,
        context::ambient_claim::AmbientClaimContext,
        handoff::{MlMode, NormalizedExit, complete, handoff},
        input::{
            current_item::LineEntry,
            expression::{expression_item, scan_expression_item_lexical},
            item::{Item, LeadingTrivia, TokenKind},
            observation::{is_active_stop, is_active_stop_lex, is_close, is_line_stop, token_kind},
            operator::{OperatorSite, STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR},
            yumark::FenceBoundary,
        },
        output::{
            RecoveryDraft,
            emit::{
                ErrorRunOutput, emit_recovery_error_run, emit_recovery_missing, token_syntax_kind,
            },
        },
        statement::StatementLineHandoff,
    },
    session::{
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn required_expr_after_accept_normalized(
    mut i: ParserIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::parser::context::sequence::SequenceContext,
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

#[allow(clippy::too_many_arguments)]
pub(in crate::parser) fn required_expr_item_normalized(
    mut i: ParserIn,
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
    sequence: crate::parser::context::sequence::SequenceContext,
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

pub(in crate::parser) fn is_required_operand_boundary(
    mut i: ParserIn,
    item: &Item,
    stops: Stops,
) -> bool {
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

pub(in crate::parser) fn emit_required_expression_missing(
    i: &mut ParserIn,
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
    i: ParserIn,
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
            expected: match role {
                GrammarRole::ForStatement(crate::session::ForStatementRole::Body) => {
                    ExpectedSyntax::Statement
                }
                _ => ExpectedSyntax::Expression,
            },
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}
