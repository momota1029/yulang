//! Dot dispatch and fixed field/path access recovery.

use super::delimited_tail::projection_tail_normalized;
use crate::ambient_claim::AmbientClaimContext;
use crate::cst_output::RecoveryDraft;
use crate::cst_output::emit::{
    emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
};
use crate::cursor::{LexIn, SyntaxIn};
use crate::expression::{is_led_operator, scan_tail_after_accept_normalized, tail_normalized};
use crate::handoff::{MlMode, NormalizedExit};
use crate::lexical::current_item::{LineEntry, current_item};
use crate::lexical::expression_item::scan_expression_item_lexical;
use crate::lexical::item::{Item, LeadingTrivia, TokenKind};
use crate::lexical::lexer::scan_path_segment_payload;
use crate::lexical::observation::{
    is_active_stop, is_active_stop_lex, is_close, is_line_stop, is_separator, token_kind,
};
use crate::lexical::operator_scan::OperatorSite;
use crate::lexical::stops::Stops;
use crate::lexical::yumark::FenceBoundary;
use crate::operator_table::BindingPower;
use crate::recovery_record::{
    ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, RecoveryKind, RecoverySiteKey,
    SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
};
use crate::statement::StatementLineHandoff;
use crate::syntax_kind::SyntaxKind;
use reborrow_generic::Reborrow as _;
use std::sync::Arc;

pub(crate) fn dot_tail_normalized(
    mut i: SyntaxIn,
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
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (next, item_origin, line_entry) = crate::lexical::expression_item::expression_item(
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
    mut i: SyntaxIn,
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
    sequence: crate::sequence::SequenceContext,
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
pub(crate) fn path_tail_normalized(
    mut i: SyntaxIn,
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
    sequence: crate::sequence::SequenceContext,
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
    mut i: SyntaxIn,
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
    i: SyntaxIn,
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
    i: SyntaxIn,
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
