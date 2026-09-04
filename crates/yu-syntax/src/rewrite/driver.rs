//! Direct expression ownership and Item handoff for the isolated rewrite.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    LexIn, RewriteIn, Stops,
    case_like::{CaseLikeFamily, case_like_nud},
    delimited::parenthesized_nud,
    emit::{
        emit_identifier_core, emit_integer_core, emit_missing, emit_operator_use, emit_token_item,
    },
    if_expr::if_nud,
    item::{Item, LeadingTrivia, OperatorUse, Payload, TokenKind, TriviaKind},
    lexer::{contextual_word_suffix_follower, scan_nud_item, scan_trivia, tail_item_after_trivia},
    operator::{
        STOP_LINE_BREAK, STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, active_stop_item,
    },
    statement::braced_nud,
    tails::{call_tail, colon_tail, dot_tail, index_tail, path_tail, with_tail},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Either<L, R> {
    Left(L),
    Right(R),
}

#[derive(Clone, Debug, Eq, PartialEq)]
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

pub(super) fn expr(mut i: RewriteIn) -> Option<TailExit> {
    expr_at(i.rb(), None, 0, 0, MlMode::All)
}

fn expr_at(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> Option<TailExit> {
    let nud = i.token(|lex| scan_nud_item(lex, baseline, stops))?;
    Some(expr_from_nud(i, nud, threshold, baseline, stops, ml_mode))
}

pub(super) fn expr_from_nud(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = append_nud(i.rb(), nud, threshold, baseline, stops, ml_mode);
    i.state.finish_node();
    exit
}

fn append_nud(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    if is_contextual_word(i.rb(), &nud, "case") {
        return case_like_nud(
            i,
            CaseLikeFamily::Case,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
        );
    }
    if is_contextual_word(i.rb(), &nud, "catch") {
        return case_like_nud(
            i,
            CaseLikeFamily::Catch,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
        );
    }
    if is_contextual_word(i.rb(), &nud, "if") {
        return if_nud(i, nud, threshold, baseline, stops, ml_mode);
    }
    match token_kind(&nud) {
        Some(TokenKind::Identifier) => {
            emit_identifier_core(&mut i, nud);
            scan_tail_after_accept(i.rb(), threshold, baseline, stops, ml_mode)
        }
        Some(TokenKind::Integer) => {
            emit_integer_core(&mut i, nud);
            scan_tail_after_accept(i.rb(), threshold, baseline, stops, ml_mode)
        }
        Some(TokenKind::LParen) => {
            parenthesized_nud(i.rb(), nud, threshold, baseline, stops, ml_mode)
        }
        Some(TokenKind::LBrace) => braced_nud(i.rb(), nud, threshold, baseline, stops, ml_mode),
        Some(TokenKind::Operator) => operator_nud(i.rb(), nud, threshold, baseline, stops, ml_mode),
        _ => unreachable!("the NUD scanner accepts only normal core items and `(`"),
    }
}

/// An accepted prefix or infix always owns its mandatory right operand.  A
/// pure local absence is Missing; malformed source is one Error sentinel and
/// never receives a second Missing at the same boundary.
pub(super) fn required_expr_after_accept(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(
        i.rb(),
        leading,
        OperatorSite::Nud,
        baseline,
        stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
    );
    required_expr_item(i, item, threshold, baseline, stops, ml_mode)
}

pub(super) fn required_expr_item(
    mut i: RewriteIn,
    mut item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    if is_required_operand_boundary(i.rb(), &item, stops) {
        let leading = std::mem::take(&mut item.leading);
        emit_missing(&mut i, leading);
        return handoff(item);
    }
    if is_nud_item(&item) {
        return append_nud(i, item, threshold, baseline, stops, ml_mode);
    }
    if is_unread_operand_boundary(&item) {
        return handoff(item);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(
            i.rb(),
            leading,
            OperatorSite::Nud,
            baseline,
            stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
        );
        if is_required_operand_boundary(i.rb(), &item, stops) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_nud_item(&item) {
            i.state.finish_node();
            return append_nud(i, item, threshold, baseline, stops, ml_mode);
        }
        if is_unread_operand_boundary(&item) {
            i.state.finish_node();
            return handoff(item);
        }
    }
}

pub(super) fn is_required_operand_boundary(mut i: RewriteIn, item: &Item, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
}

fn is_unread_operand_boundary(item: &Item) -> bool {
    is_close(item)
        || matches!(
            token_kind(item),
            Some(TokenKind::LBracket | TokenKind::LBrace)
        )
}

pub(super) fn scan_tail_after_accept(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    tail(i, item, threshold, baseline, stops, ml_mode)
}

pub(super) fn continue_completed_tail(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    exit: TailExit,
) -> TailExit {
    match exit {
        Ok(()) => scan_tail_after_accept(i, threshold, baseline, stops, ml_mode),
        Err(Either::Left(item)) => tail(i, item, threshold, baseline, stops, ml_mode),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

pub(super) fn tail(
    mut i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    if is_active_stop(i.rb(), &item, stops) || is_line_stop(&item, stops) {
        return handoff(item);
    }
    if is_with_tail_item(i.rb(), &item, baseline, ml_mode) {
        return with_tail(i, item, baseline, stops);
    }
    if item.leading.0.is_empty() {
        match token_kind(&item) {
            Some(TokenKind::LParen) => {
                return call_tail(i.rb(), item, threshold, baseline, stops, ml_mode);
            }
            Some(TokenKind::LBracket) => {
                return index_tail(i.rb(), item, threshold, baseline, stops, ml_mode);
            }
            _ => {}
        }
    }
    match token_kind(&item) {
        Some(TokenKind::Dot) => {
            return dot_tail(i.rb(), item, threshold, baseline, stops, ml_mode);
        }
        Some(TokenKind::PathSeparator) => {
            return path_tail(i.rb(), item, threshold, baseline, stops, ml_mode);
        }
        Some(TokenKind::Operator) if is_led_operator(&item) => {
            return operator_tail(i.rb(), item, threshold, baseline, stops, ml_mode);
        }
        _ => {}
    }
    if is_ml_argument(&item, baseline, ml_mode) {
        return ml_argument(i.rb(), item, threshold, baseline, stops);
    }
    if token_kind(&item) == Some(TokenKind::Colon) {
        return colon_tail(i, item, baseline, stops, ml_mode);
    }
    handoff(item)
}

fn is_with_tail_item(mut i: RewriteIn, item: &Item, baseline: usize, ml_mode: MlMode) -> bool {
    !matches!(ml_mode, MlMode::None)
        && chain_continuation(&item.leading, baseline)
        && is_contextual_word(i.rb(), item, "with")
}

fn is_ml_argument(item: &Item, baseline: usize, mode: MlMode) -> bool {
    if !is_nud_item(item) || item.leading.0.is_empty() || matches!(mode, MlMode::None) {
        return false;
    }
    let indentation = indentation_after_newline(&item.leading);
    match mode {
        MlMode::All => indentation.is_none_or(|indentation| indentation > baseline),
        MlMode::LayoutOnly => indentation.is_some_and(|indentation| indentation > baseline),
        MlMode::None => false,
    }
}

pub(super) fn chain_continuation(leading: &LeadingTrivia, baseline: usize) -> bool {
    indentation_after_newline(leading).is_none_or(|indentation| indentation > baseline)
}

pub(super) fn is_led_operator(item: &Item) -> bool {
    matches!(
        operator_use(item),
        Some(OperatorUse::Infix { .. } | OperatorUse::Suffix(_))
    )
}

fn ml_argument(
    mut i: RewriteIn,
    argument: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::MlArgument.into());
    let exit = expr_from_nud(i.rb(), argument, threshold, baseline, stops, MlMode::None);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, MlMode::All, exit)
}

fn operator_nud(
    mut i: RewriteIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    match operator_use(&operator) {
        Some(OperatorUse::Prefix(right)) => {
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::PrefixOperatorUse);
            let rhs = required_expr_after_accept(i.rb(), Some(&right), baseline, stops, ml_mode);
            continue_completed_tail(i, threshold, baseline, stops, ml_mode, rhs)
        }
        Some(OperatorUse::Nullfix) => {
            emit_operator_use(&mut i, operator, SyntaxKind::NullfixOperatorUse);
            scan_tail_after_accept(i, threshold, baseline, stops, ml_mode)
        }
        _ => unreachable!("the NUD scanner accepts only prefix and nullfix operators"),
    }
}

fn operator_tail(
    mut i: RewriteIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
) -> TailExit {
    match operator_use(&operator) {
        Some(OperatorUse::Infix { left, right }) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return handoff(operator);
            }
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::InfixOperatorUse);
            let rhs = required_expr_after_accept(i.rb(), Some(&right), baseline, stops, ml_mode);
            continue_completed_tail(i, threshold, baseline, stops, ml_mode, rhs)
        }
        Some(OperatorUse::Suffix(left)) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return handoff(operator);
            }
            emit_operator_use(&mut i, operator, SyntaxKind::SuffixOperatorUse);
            scan_tail_after_accept(i, threshold, baseline, stops, ml_mode)
        }
        _ => unreachable!("the LED scanner accepts only infix and suffix operators"),
    }
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
    match &item.payload {
        Payload::Token(token) => token.kind == TokenKind::Identifier && &*token.text == word,
        Payload::Operator(operator) => {
            &*operator.text == word
                && i.rb()
                    .map(contextual_word_suffix_follower, |follower| follower)
                    .unwrap_or(false)
        }
        Payload::Eof => false,
    }
}

fn is_contextual_word_lex(mut i: LexIn, item: &Item, word: &str) -> bool {
    match &item.payload {
        Payload::Token(token) => token.kind == TokenKind::Identifier && &*token.text == word,
        Payload::Operator(operator) => {
            &*operator.text == word
                && i.token(contextual_word_suffix_follower)
                    .expect("contextual suffix observation is total")
        }
        Payload::Eof => false,
    }
}

pub(super) fn is_statement_nud(item: &Item) -> bool {
    is_normal_core_item(item) || token_kind(item) == Some(TokenKind::LBrace)
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
    match item.payload {
        Payload::Eof => Err(Either::Right(End { item })),
        Payload::Token(_) | Payload::Operator(_) => Err(Either::Left(item)),
    }
}

pub(super) fn token_kind(item: &Item) -> Option<TokenKind> {
    match &item.payload {
        Payload::Token(token) => Some(token.kind),
        Payload::Operator(_) => Some(TokenKind::Operator),
        Payload::Eof => None,
    }
}

fn operator_use(item: &Item) -> Option<&OperatorUse> {
    let Payload::Operator(operator) = &item.payload else {
        return None;
    };
    Some(&operator.use_)
}

pub(super) fn delimited_baseline(incoming: usize, leading: &LeadingTrivia) -> usize {
    indentation_after_newline(leading)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

pub(super) fn implicit_delimited_newline(baseline: usize, leading: &LeadingTrivia) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

pub(super) fn indentation_after_newline(leading: &LeadingTrivia) -> Option<usize> {
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;
    for part in &leading.0 {
        match part.kind {
            TriviaKind::Newline => {
                saw_newline = true;
                at_line_start = true;
                indentation = 0;
            }
            TriviaKind::Whitespace if at_line_start => indentation += part.text.chars().count(),
            _ => at_line_start = false,
        }
    }
    saw_newline.then_some(indentation)
}

pub(super) fn is_line_stop(item: &Item, stops: Stops) -> bool {
    stops & STOP_LINE_BREAK != 0 && indentation_after_newline(&item.leading).is_some()
}
