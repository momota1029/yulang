//! Direct ownership for NUD `if` expressions and their arm boundaries.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    driver::{
        Either, MlMode, TailExit, continue_completed_tail, expr_from_nud, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, is_contextual_word,
        is_nud_item, is_required_operand_boundary, required_expr_item, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{introduced_body_indentation, scan_trivia, tail_item_after_trivia},
    operator::{STOP_COLON, STOP_ELSE, STOP_ELSIF, STOP_LBRACE},
    statement::{StatementLineHandoff, indented_statement_block},
};

pub(super) fn if_nud(
    mut i: RewriteIn,
    mut keyword: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    outer_stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    emit_leading_trivia(&mut i, &keyword.leading);
    keyword.leading = LeadingTrivia::default();
    i.state.start_node(SyntaxKind::IfExpression.into());
    let exit = if_arm(
        i.rb(),
        keyword,
        SyntaxKind::IfKw,
        baseline,
        outer_stops,
        line_handoff,
    );
    let exit = if_continuations(i.rb(), exit, baseline, outer_stops, line_handoff);
    i.state.finish_node();
    continue_completed_tail(
        i,
        threshold,
        baseline,
        outer_stops,
        ml_mode,
        line_handoff,
        exit,
    )
}

fn if_continuations(
    mut i: RewriteIn,
    mut exit: TailExit,
    if_baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    loop {
        let Err(Either::Left(mut keyword)) = exit else {
            return exit;
        };
        let Some(kind) = arm_keyword(i.rb(), &keyword, if_baseline) else {
            return handoff(keyword);
        };
        emit_leading_trivia(&mut i, &keyword.leading);
        keyword.leading = LeadingTrivia::default();
        exit = match kind {
            SyntaxKind::ElsifKw => if_arm(
                i.rb(),
                keyword,
                kind,
                if_baseline,
                outer_stops,
                line_handoff,
            ),
            SyntaxKind::ElseKw => else_arm(i.rb(), keyword, if_baseline, outer_stops, line_handoff),
            _ => unreachable!("only if-continuation keyword kinds are selected"),
        };
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
    let continuation =
        indentation_after_newline(&item.leading).is_none_or(|indentation| indentation >= baseline);
    continuation.then_some(())?;
    if stops & STOP_ELSIF != 0 && is_contextual_word(i.rb(), item, "elsif") {
        Some(ActiveStatementCompanion::Elsif)
    } else if stops & STOP_ELSE != 0 && is_contextual_word(i, item, "else") {
        Some(ActiveStatementCompanion::Else)
    } else {
        None
    }
}

fn if_arm(
    mut i: RewriteIn,
    keyword: Item,
    keyword_kind: SyntaxKind,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::IfArm.into());
    emit_contextual_keyword(&mut i, keyword, keyword_kind);

    let condition_stops = outer_stops | STOP_COLON | STOP_LBRACE | STOP_ELSIF | STOP_ELSE;
    let (exit, condition_missing) = condition(i.rb(), baseline, condition_stops, line_handoff);

    let exit = match exit {
        Err(Either::Left(colon)) if token_kind(&colon) == Some(TokenKind::Colon) => {
            emit_token_item(&mut i, colon);
            colon_body(
                i.rb(),
                baseline,
                outer_stops | STOP_ELSIF | STOP_ELSE,
                line_handoff,
            )
        }
        exit => missing_if_arm(i.rb(), exit, condition_missing),
    };
    i.state.finish_node();
    exit
}

fn condition(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> (TailExit, bool) {
    let leading = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &leading);
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    item.leading = LeadingTrivia::default();
    let missing = is_required_operand_boundary(i.rb(), &item, stops);
    i.state.start_node(SyntaxKind::Condition.into());
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = required_expr_item(
        i.rb(),
        item,
        None,
        baseline,
        stops,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    i.state.finish_node();
    (exit, missing)
}

fn missing_if_arm(mut i: RewriteIn, exit: TailExit, condition_missing: bool) -> TailExit {
    if condition_missing {
        return exit;
    }
    match exit {
        Err(Either::Left(mut item)) => {
            let leading = std::mem::take(&mut item.leading);
            emit_missing(&mut i, leading);
            handoff(item)
        }
        Err(Either::Right(mut end)) => {
            let leading = std::mem::take(&mut end.item.leading);
            emit_missing(&mut i, leading);
            Err(Either::Right(end))
        }
        Ok(()) => unreachable!("a direct condition always returns a boundary item"),
    }
}

fn else_arm(
    mut i: RewriteIn,
    keyword: Item,
    baseline: usize,
    outer_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::ElseArm.into());
    emit_contextual_keyword(&mut i, keyword, SyntaxKind::ElseKw);

    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, outer_stops);
    let exit = if token_kind(&item) == Some(TokenKind::Colon) {
        emit_token_item(&mut i, item);
        colon_body(
            i.rb(),
            baseline,
            outer_stops | STOP_ELSIF | STOP_ELSE,
            line_handoff,
        )
    } else {
        inline_body_item(
            i.rb(),
            item,
            baseline,
            outer_stops | STOP_ELSIF | STOP_ELSE,
            line_handoff,
        )
    };
    i.state.finish_node();
    exit
}

fn colon_body(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if introduced_body_indentation(i.rb()).is_some_and(|indentation| indentation > baseline) {
        indented_statement_block(i, baseline, stops)
    } else {
        inline_body(i, baseline, stops, line_handoff)
    }
}

fn inline_body(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    inline_body_item(i, item, baseline, stops, line_handoff)
}

fn inline_body_item(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if inline_boundary(i.rb(), &item, baseline, stops) {
        emit_inline_missing(&mut i, &mut item, baseline);
        return handoff(item);
    }

    emit_inline_leading(&mut i, &mut item);
    if is_nud_item(&item) {
        return expr_from_nud(i, item, None, baseline, stops, MlMode::All, line_handoff);
    }

    item = retry_inline_body(i.rb(), item, baseline, stops);
    if inline_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, &item.leading) {
            emit_inline_leading(&mut i, &mut item);
        }
        return handoff(item);
    }
    emit_inline_leading(&mut i, &mut item);
    debug_assert!(is_nud_item(&item));
    expr_from_nud(i, item, None, baseline, stops, MlMode::All, line_handoff)
}

fn retry_inline_body(mut i: RewriteIn, mut item: Item, baseline: usize, stops: Stops) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
        if inline_boundary(i.rb(), &item, baseline, stops) || is_nud_item(&item) {
            i.state.finish_node();
            return item;
        }
    }
}

fn inline_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || super::driver::is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || implicit_delimited_newline(baseline, &item.leading)
        || token_kind(item) == Some(TokenKind::LBrace)
}

fn emit_inline_leading(i: &mut RewriteIn, item: &mut Item) {
    if !item.leading.0.is_empty() {
        emit_leading_trivia(i, &std::mem::take(&mut item.leading));
    }
}

fn emit_inline_missing(i: &mut RewriteIn, item: &mut Item, baseline: usize) {
    if !implicit_delimited_newline(baseline, &item.leading) {
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
    emit_leading_trivia(i, &item.leading);
    match item.payload {
        Payload::Token(token) => {
            debug_assert_eq!(token.kind, TokenKind::Identifier);
            debug_assert_eq!(&*token.text, spelling);
            i.state.token(kind.into(), &token.text);
        }
        Payload::Operator(operator) => {
            debug_assert_eq!(&*operator.text, spelling);
            i.state.token(kind.into(), &operator.text);
        }
        Payload::Eof => unreachable!("an accepted contextual keyword is lexical"),
        Payload::Boundary(_) => unreachable!("Gate 2 boundaries are not emitted by a scanner"),
    }
}
