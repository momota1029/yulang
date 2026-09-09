//! Colon application RHS and local inline sequence ownership.

use super::inline_slot::{
    emit_inline_leading, emit_inline_slot_missing, inline_boundary, inline_slot_draft,
    is_inline_slot_boundary,
};
use crate::ambient_claim::AmbientClaimContext;
use crate::cursor::SyntaxIn;
use crate::cursor::recovery::emit::{emit_recovery_error_run, emit_token_item, token_syntax_kind};
use crate::expression::{chain_continuation, expr_from_nud_normalized, is_nud_item};
use crate::handoff::{Either, MlMode, NormalizedExit, complete, handoff};
use crate::lexical::current_item::LineEntry;
use crate::lexical::expression_item::{expression_item, scan_expression_item_lexical};
use crate::lexical::item::{Item, TokenKind};
use crate::lexical::lexer::introduced_body_indentation_normalized;
use crate::lexical::observation::{
    implicit_delimited_newline, is_active_stop, is_active_stop_lex, is_close, is_line_stop,
    token_kind,
};
use crate::lexical::operator_scan::OperatorSite;
use crate::lexical::position::{advanced_origin, suffix_marker};
use crate::lexical::stops::{STOP_COMMA, STOP_LINE_BREAK, Stops};
use crate::lexical::yumark::FenceBoundary;
use crate::recovery_record::{
    ColonApplicationRole, ExpectedSyntax, GrammarRole, RecoveryKind, UnexpectedCategory,
    UnexpectedSyntax,
};
use crate::statement::{StatementLineHandoff, indented_statement_block_normalized};
use crate::syntax_kind::SyntaxKind;

/// A lone eligible colon is terminal and owns its mandatory RHS, including
/// recovery. Inline RHSs use the direct expression vocabulary; indented RHSs
/// use canonical Statements.
#[allow(clippy::too_many_arguments)]
pub(crate) fn colon_tail_normalized(
    mut i: SyntaxIn,
    mut colon: Item,
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
    mut i: SyntaxIn,
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
    sequence: crate::sequence::SequenceContext,
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
    if is_inline_slot_boundary(i.rb(), &item, baseline, stops) {
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
        if is_inline_slot_boundary(i.rb(), &item, baseline, stops) {
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
        sequence.or(Some(crate::sequence::SequenceOwner::Colon)),
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
    mut i: SyntaxIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
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
    i: SyntaxIn,
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
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    sequence: crate::sequence::SequenceContext,
) -> bool {
    sequence.is_none()
        && !item.payload_view().is_boundary()
        && !is_close(item)
        && !is_active_stop(i.rb(), item, stops)
        && !is_line_stop(item, stops)
        && (token_kind(item) == Some(TokenKind::Comma)
            || implicit_delimited_newline(baseline, item.leading_view()))
}
