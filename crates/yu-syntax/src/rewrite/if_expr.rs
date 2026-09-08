//! Direct ownership for NUD `if` expressions and their arm boundaries.

use super::ambient_claim::{AmbientClaimContext, AmbientClaimView};
use reborrow_generic::Reborrow as _;

use crate::{
    operator::BindingPower,
    rewrite::operator::OperatorSite,
    session::{GrammarRole, IfExpressionRole},
    syntax_kind::SyntaxKind,
};

use super::{
    RewriteIn, Stops,
    current_item::LineEntry,
    driver::{
        Either, MlMode, NormalizedExit, TailExit, advanced_origin, complete,
        continue_normalized_tail, expr_from_nud_normalized, expression_item, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, is_contextual_word,
        is_nud_item, is_required_operand_boundary, ordinary_exit, required_expr_item_normalized,
        suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::introduced_body_indentation_normalized,
    operator::{STOP_COLON, STOP_ELSE, STOP_ELSIF, STOP_LBRACE},
    statement::{StatementLineHandoff, indented_statement_block_normalized},
    yumark::FenceBoundary,
};

pub(super) fn if_nud(
    i: RewriteIn,
    keyword: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    outer_stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(if_nud_normalized(
        i,
        keyword,
        threshold,
        baseline,
        outer_stops,
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
pub(super) fn if_nud_normalized(
    mut i: RewriteIn,
    mut keyword: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    outer_stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    let companion = ambient.view.map(|view| view.if_companion(baseline));
    let arm_ambient = ambient.map(|view| view.with_if(companion.as_ref().unwrap()));
    i.state.start_node(SyntaxKind::IfExpression.into());
    let entry = suffix_marker(i.rb());
    let exit = if_arm_normalized(
        i.rb(),
        keyword,
        SyntaxKind::IfKw,
        baseline,
        outer_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        arm_ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    let entry = suffix_marker(i.rb());
    let exit = if_continuations_normalized(
        i.rb(),
        exit,
        baseline,
        outer_stops,
        line_handoff,
        item_origin,
        fence,
        arm_ambient,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        outer_stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient.if_outer_tail(),
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn if_continuations_normalized(
    mut i: RewriteIn,
    mut exit: NormalizedExit,
    if_baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    fence: Option<&FenceBoundary>,
    arm_ambient: AmbientClaimContext<'_>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    loop {
        let NormalizedExit::Complete(Err(Either::Left(mut keyword)), line_entry) = exit else {
            return exit;
        };
        if keyword.payload_view().is_boundary() {
            return complete(handoff(keyword), line_entry);
        }
        let Some(kind) = arm_keyword(i.rb(), &keyword, if_baseline) else {
            return complete(handoff(keyword), line_entry);
        };
        keyword.emit_all_remaining_leading(&mut *i.state);
        let entry = suffix_marker(i.rb());
        exit = match kind {
            SyntaxKind::ElsifKw => if_arm_normalized(
                i.rb(),
                keyword,
                kind,
                if_baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                arm_ambient,
            ),
            SyntaxKind::ElseKw => else_arm_normalized(
                i.rb(),
                keyword,
                if_baseline,
                outer_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            ),
            _ => unreachable!("only if-continuation keyword kinds are selected"),
        };
        item_origin = advanced_origin(item_origin, entry, i.rb());
        if kind == SyntaxKind::ElseKw {
            return exit;
        }
    }
}

fn arm_keyword(i: RewriteIn, item: &Item, if_baseline: usize) -> Option<SyntaxKind> {
    match active_statement_companion(i, item, if_baseline, STOP_ELSIF | STOP_ELSE) {
        Some(ActiveStatementCompanion::Elsif) => Some(SyntaxKind::ElsifKw),
        Some(ActiveStatementCompanion::Else) => Some(SyntaxKind::ElseKw),
        None => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ActiveStatementCompanion {
    Elsif,
    Else,
}

pub(super) fn active_statement_companion(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> Option<ActiveStatementCompanion> {
    if item.payload_view().is_boundary() {
        return None;
    }
    let continuation = indentation_after_newline(item.leading_view())
        .is_none_or(|indentation| indentation >= baseline);
    continuation.then_some(())?;
    if stops & STOP_ELSIF != 0 && is_contextual_word(i.rb(), item, "elsif") {
        Some(ActiveStatementCompanion::Elsif)
    } else if stops & STOP_ELSE != 0 && is_contextual_word(i, item, "else") {
        Some(ActiveStatementCompanion::Else)
    } else {
        None
    }
}

#[allow(clippy::too_many_arguments)]
fn if_arm_normalized(
    mut i: RewriteIn,
    keyword: Item,
    keyword_kind: SyntaxKind,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let sequence = Some(super::sequence::SequenceOwner::If);
    i.state.start_node(SyntaxKind::IfArm.into());
    emit_contextual_keyword(&mut i, keyword, keyword_kind);

    let condition_stops = outer_stops | STOP_COLON | STOP_LBRACE | STOP_ELSIF | STOP_ELSE;
    let entry = suffix_marker(i.rb());
    let (exit, condition_missing) = condition_normalized(
        i.rb(),
        baseline,
        condition_stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());

    let exit = match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            missing_if_arm_normalized(
                i.rb(),
                complete(handoff(item), line_entry),
                condition_missing,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(colon)), line_entry)
            if token_kind(&colon) == Some(TokenKind::Colon) =>
        {
            emit_token_item(&mut i, colon);
            colon_body_normalized(
                i.rb(),
                baseline,
                outer_stops | STOP_ELSIF | STOP_ELSE,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        exit => missing_if_arm_normalized(i.rb(), exit, condition_missing),
    };
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn condition_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> (NormalizedExit, bool) {
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
    let missing = is_required_operand_boundary(i.rb(), &item, stops);
    i.state.start_node(SyntaxKind::Condition.into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item_normalized(
        i.rb(),
        item,
        GrammarRole::IfExpression(IfExpressionRole::Condition),
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
    i.state.finish_node();
    (exit, missing)
}

fn missing_if_arm_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    condition_missing: bool,
) -> NormalizedExit {
    if condition_missing {
        return exit;
    }
    match exit {
        NormalizedExit::Complete(Err(Either::Left(mut item)), line_entry) => {
            if !item.payload_view().is_boundary() {
                item.emit_all_remaining_leading(&mut *i.state);
            }
            emit_missing(&mut i, LeadingTrivia::default());
            complete(handoff(item), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            end.item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Ok(()), _) => {
            unreachable!("a direct condition always returns a boundary item")
        }
        deferred @ NormalizedExit::Deferred(..) => deferred,
    }
}

#[allow(clippy::too_many_arguments)]
fn else_arm_normalized(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let sequence = Some(super::sequence::SequenceOwner::If);
    #[cfg(test)]
    ambient.observe(super::ambient_claim::ProofSite::ElseBody);
    i.state.start_node(SyntaxKind::ElseArm.into());
    emit_contextual_keyword(&mut i, keyword, SyntaxKind::ElseKw);

    let (item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        outer_stops,
    );
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let exit = if token_kind(&item) == Some(TokenKind::Colon) {
        emit_token_item(&mut i, item);
        colon_body_normalized(
            i.rb(),
            baseline,
            outer_stops | STOP_ELSIF | STOP_ELSE,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    } else {
        inline_body_item_normalized(
            i.rb(),
            item,
            baseline,
            outer_stops | STOP_ELSIF | STOP_ELSE,
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
fn colon_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    if introduced_body_indentation_normalized(i.rb(), item_origin, fence)
        .is_some_and(|indentation| indentation > baseline)
    {
        indented_statement_block_normalized(
            i,
            baseline,
            GrammarRole::IfExpression(IfExpressionRole::IndentedStatement),
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        inline_body_normalized(
            i,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        )
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
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
        stops,
    );
    inline_body_item_normalized(
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
    )
}

#[allow(clippy::too_many_arguments)]
fn inline_body_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: super::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if inline_boundary(i.rb(), &item, baseline, stops) {
        emit_inline_missing(&mut i, &mut item, baseline);
        return complete(handoff(item), line_entry);
    }

    emit_inline_leading(&mut i, &mut item);
    if is_nud_item(&item) {
        return expr_from_nud_normalized(
            i,
            item,
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
    }

    (item, item_origin, line_entry) = retry_inline_body_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if inline_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            emit_inline_leading(&mut i, &mut item);
        }
        return complete(handoff(item), line_entry);
    }
    emit_inline_leading(&mut i, &mut item);
    debug_assert!(is_nud_item(&item));
    expr_from_nud_normalized(
        i,
        item,
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
}

#[allow(clippy::too_many_arguments)]
fn retry_inline_body_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        if item.payload_view().is_boundary()
            || inline_boundary(i.rb(), &item, baseline, stops)
            || is_nud_item(&item)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn inline_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || super::driver::is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
        || token_kind(item) == Some(TokenKind::LBrace)
}

fn emit_inline_leading(i: &mut RewriteIn, item: &mut Item) {
    if !item.leading_view().is_grammar_empty() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

fn emit_inline_missing(i: &mut RewriteIn, item: &mut Item, baseline: usize) {
    if !implicit_delimited_newline(baseline, item.leading_view()) {
        emit_inline_leading(i, item);
    }
    emit_missing(i, LeadingTrivia::default());
}

fn emit_contextual_keyword(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let spelling = match kind {
        SyntaxKind::IfKw => "if",
        SyntaxKind::ElsifKw => "elsif",
        SyntaxKind::ElseKw => "else",
        _ => unreachable!("only if-expression keyword kinds are emitted here"),
    };
    debug_assert_eq!(item.payload_view().spelling(), Some(spelling));
    item.emit_remaining(&mut *i.state, kind);
}
