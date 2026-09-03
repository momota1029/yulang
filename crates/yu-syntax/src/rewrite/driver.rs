//! Direct expression ownership and Item handoff for the isolated rewrite.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn,
    emit::{
        emit_error_item, emit_identifier_core, emit_integer_core, emit_missing, emit_operator_use,
        emit_token_item,
    },
    item::{Item, LeadingTrivia, OperatorUse, Payload, TokenKind, TriviaKind},
    lexer::{scan_nud_item, scan_trivia, tail_item_after_trivia},
    operator::stops_for,
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
enum MlMode {
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
    stops: u8,
    ml_mode: MlMode,
) -> Option<TailExit> {
    let nud = i.token(|lex| scan_nud_item(lex, baseline, stops))?;
    Some(expr_from_nud(i, nud, threshold, baseline, stops, ml_mode))
}

fn expr_from_nud(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
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
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
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
        Some(TokenKind::Operator) => operator_nud(i.rb(), nud, threshold, baseline, stops, ml_mode),
        _ => unreachable!("the NUD scanner accepts only normal core items and `(`"),
    }
}

fn expr_after_accept(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    if is_nud_item(&item) {
        append_nud(i, item, threshold, baseline, stops, ml_mode)
    } else {
        handoff(item)
    }
}

fn scan_tail_after_accept(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    tail(i, item, threshold, baseline, stops, ml_mode)
}

fn continue_completed_tail(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
    exit: TailExit,
) -> TailExit {
    match exit {
        Ok(()) => scan_tail_after_accept(i, threshold, baseline, stops, ml_mode),
        Err(Either::Left(item)) => tail(i, item, threshold, baseline, stops, ml_mode),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn tail(
    mut i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
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
    handoff(item)
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

fn is_led_operator(item: &Item) -> bool {
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
    stops: u8,
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
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    match operator_use(&operator) {
        Some(OperatorUse::Prefix(right)) => {
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::PrefixOperatorUse);
            let rhs = expr_after_accept(i.rb(), Some(&right), baseline, stops, ml_mode);
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
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    match operator_use(&operator) {
        Some(OperatorUse::Infix { left, right }) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return handoff(operator);
            }
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::InfixOperatorUse);
            let rhs = expr_after_accept(i.rb(), Some(&right), baseline, stops, ml_mode);
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

fn parenthesized_nud(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RParen,
        None,
        baseline,
        MlMode::LayoutOnly,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

fn delimited_items(
    mut i: RewriteIn,
    close: TokenKind,
    item_node: Option<SyntaxKind>,
    incoming_baseline: usize,
    item_ml_mode: MlMode,
) -> TailExit {
    let stops = stops_for(close);
    let leading = scan_trivia(i.rb());
    let baseline = delimited_baseline(incoming_baseline, &leading);
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) {
            return missing_close(i, item);
        }
        if is_separator(&item) {
            item = missing_item(i.rb(), item);
            emit_token_item(&mut i, item);
            let leading = scan_trivia(i.rb());
            item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
            continue;
        }
        if is_close(&item) {
            item = wrong_close_item(i.rb(), item, baseline, stops);
            continue;
        }
        if !is_nud_item(&item) {
            return handoff(item);
        }
        if let Some(kind) = item_node {
            i.state.start_node(kind.into());
        }
        let exit = expr_from_nud(i.rb(), item, None, baseline, stops, item_ml_mode);
        if item_node.is_some() {
            i.state.finish_node();
        }
        item = match exit {
            Err(Either::Left(next)) if is_separator(&next) => {
                emit_token_item(&mut i, next);
                let leading = scan_trivia(i.rb());
                tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops)
            }
            Err(Either::Left(next)) if token_kind(&next) == Some(close) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            Err(Either::Left(next)) if is_close(&next) => {
                wrong_close_item(i.rb(), next, baseline, stops)
            }
            Err(Either::Left(next))
                if is_nud_item(&next) && implicit_delimited_newline(baseline, &next.leading) =>
            {
                next
            }
            Err(Either::Left(next))
                if matches!(item_ml_mode, MlMode::LayoutOnly) && is_nud_item(&next) =>
            {
                missing_item(i.rb(), next)
            }
            Err(Either::Right(end)) => return missing_close(i, end.item),
            exit => return exit,
        };
    }
}

fn missing_close(mut i: RewriteIn, mut end: Item) -> TailExit {
    let leading = std::mem::take(&mut end.leading);
    emit_missing(&mut i, leading);
    handoff(end)
}

fn missing_item(mut i: RewriteIn, mut item: Item) -> Item {
    let leading = std::mem::take(&mut item.leading);
    emit_missing(&mut i, leading);
    item
}

fn wrong_close_item(mut i: RewriteIn, item: Item, baseline: usize, stops: u8) -> Item {
    emit_error_item(&mut i, item);
    let leading = scan_trivia(i.rb());
    tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops)
}

fn is_nud_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::Integer | TokenKind::LParen)
    ) || matches!(
        operator_use(item),
        Some(OperatorUse::Prefix(_) | OperatorUse::Nullfix)
    )
}

fn call_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, baseline, MlMode::All);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

fn index_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RBracket,
        Some(SyntaxKind::IndexItem),
        baseline,
        MlMode::All,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

fn dot_tail(
    mut i: RewriteIn,
    dot: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let next = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    if next.leading.0.is_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => {
                return projection_tuple_tail(i, dot, next, threshold, baseline, stops, ml_mode);
            }
            Some(TokenKind::LBrace) => {
                return projection_record_tail(i, dot, next, threshold, baseline, stops, ml_mode);
            }
            _ => {}
        }
    }
    field_tail(i, dot, next, threshold, baseline, stops, ml_mode)
}

fn field_tail(
    mut i: RewriteIn,
    dot: Item,
    name: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if token_kind(&name) != Some(TokenKind::Identifier) || !name.leading.0.is_empty() {
        i.state.finish_node();
        return handoff(name);
    }
    emit_token_item(&mut i, name);
    i.state.finish_node();
    scan_tail_after_accept(i, threshold, baseline, stops, ml_mode)
}

fn projection_tuple_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionTupleTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, baseline, MlMode::All);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

fn projection_record_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionRecordTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RBrace, None, baseline, MlMode::All);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, exit)
}

fn path_tail(
    mut i: RewriteIn,
    separator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    ml_mode: MlMode,
) -> TailExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let leading = scan_trivia(i.rb());
    let segment = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    if token_kind(&segment) != Some(TokenKind::Identifier) {
        i.state.finish_node();
        return handoff(segment);
    }
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_tail_after_accept(i, threshold, baseline, stops, ml_mode)
}

fn is_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

fn is_close(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    )
}

fn handoff(item: Item) -> TailExit {
    match item.payload {
        Payload::Eof => Err(Either::Right(End { item })),
        Payload::Token(_) | Payload::Operator(_) => Err(Either::Left(item)),
    }
}

fn token_kind(item: &Item) -> Option<TokenKind> {
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

fn delimited_baseline(incoming: usize, leading: &LeadingTrivia) -> usize {
    indentation_after_newline(leading)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

fn implicit_delimited_newline(baseline: usize, leading: &LeadingTrivia) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

fn indentation_after_newline(leading: &LeadingTrivia) -> Option<usize> {
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
