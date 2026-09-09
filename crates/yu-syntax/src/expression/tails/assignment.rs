//! Assignment owns one required RHS and returns its terminal handoff.

use super::inline_slot::{emit_inline_slot_missing, inline_boundary, inline_slot_draft};
use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    cursor::recovery::emit::{emit_recovery_error_run, emit_token_item, token_syntax_kind},
    expression::{expr_from_nud_normalized, is_nud_item},
    handoff::{MlMode, NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        expression_item::{expression_item, scan_expression_item_lexical},
        item::{Item, TokenKind},
        lexer::introduced_body_indentation_normalized,
        observation::{implicit_delimited_newline, is_active_stop, is_active_stop_lex, token_kind},
        operator_scan::OperatorSite,
        stops::{STOP_COMMA, STOP_LINE_BREAK, STOP_SEMICOLON, Stops},
        yumark::FenceBoundary,
    },
    recovery_record::{
        AssignmentRole, ExpectedSyntax, GrammarRole, RecoveryKind, UnexpectedCategory,
        UnexpectedSyntax,
    },
    statement::{StatementLineHandoff, indented_statement_block_normalized},
    syntax_kind::SyntaxKind,
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn assignment_tail_normalized(
    mut i: SyntaxIn,
    mut equals: Item,
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
    let indentation = introduced_body_indentation_normalized(i.rb(), item_origin, fence);
    equals.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::AssignmentTail.into());
    emit_token_item(&mut i, equals);
    let exit = if indentation.is_some_and(|indentation| indentation > baseline) {
        indented_statement_block_normalized(
            i.rb(),
            baseline,
            GrammarRole::Assignment(AssignmentRole::IndentedStatement),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        inline_rhs(
            i.rb(),
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
    };
    i.state.finish_node();
    exit
}

fn boundary(item: &Item, baseline: usize, stops: Stops) -> bool {
    inline_boundary(item, baseline, stops)
        || (!is_nud_item(item)
            && matches!(
                token_kind(item),
                Some(TokenKind::LBracket | TokenKind::LBrace)
            ))
}

#[allow(clippy::too_many_arguments)]
fn inline_rhs(
    mut i: SyntaxIn,
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
    let stops = stops | STOP_COMMA | STOP_SEMICOLON;
    let (mut item, mut item_origin, mut line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    let role = GrammarRole::Assignment(AssignmentRole::Rhs);
    if boundary(&item, baseline, stops) || is_active_stop(i.rb(), &item, stops) {
        // A layout boundary protects even EOF leading; only horizontal EOF
        // belongs to this missing slot's ordinary EOF publication.
        let missing_stops = if implicit_delimited_newline(baseline, item.leading_view()) {
            stops | STOP_LINE_BREAK
        } else {
            stops
        };
        emit_inline_slot_missing(
            i.rb(),
            &mut item,
            item_origin,
            role,
            ExpectedSyntax::Expression,
            missing_stops,
        );
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if !is_nud_item(&item) {
        (item, item_origin, line_entry) = emit_recovery_error_run(
            i.rb(),
            |run| {
                let start = item.extent(item_origin).recovery_range().start;
                loop {
                    let kind =
                        token_syntax_kind(token_kind(&item).expect("assignment Error token"));
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
                            stops,
                        )
                    });
                    if boundary(&item, baseline, stops)
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
                    role,
                    ExpectedSyntax::Expression,
                    RecoveryKind::Error,
                    range,
                    unexpected,
                )
            },
        );
        if boundary(&item, baseline, stops) || is_active_stop(i.rb(), &item, stops) {
            return complete(handoff(item), line_entry);
        }
    }
    expr_from_nud_normalized(
        i,
        item,
        None,
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
