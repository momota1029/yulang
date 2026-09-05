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
    item::{Item, LeadingTrivia, LeadingView, OperatorUse, TokenKind},
    lexer::{
        contextual_word_suffix_follower, path_segment_item_after_trivia, scan_nud_item,
        scan_trivia, tail_item_after_trivia,
    },
    operator::{
        STOP_LINE_BREAK, STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, active_stop_item,
    },
    statement::{StatementLineHandoff, braced_nud},
    tails::{call_tail, colon_tail, dot_tail, index_tail, path_tail, with_tail},
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

/// L5a keeps an unentered owner frontier distinct from an ordinary Pratt
/// handoff. The deferred Item has not affected Rowan or recovery.
pub(super) enum L5aExit {
    Complete(TailExit),
    Deferred(Item),
}

#[derive(Clone, Copy)]
pub(super) enum CompleteItemSite {
    Nud,
    Led,
    PathSegment,
}

fn ordinary_complete_item(
    i: &mut RewriteIn,
    site: CompleteItemSite,
    baseline: usize,
    stops: Stops,
) -> Item {
    let leading = scan_trivia(i.rb());
    match site {
        CompleteItemSite::Nud => {
            tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops)
        }
        CompleteItemSite::Led => {
            tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops)
        }
        CompleteItemSite::PathSegment => {
            path_segment_item_after_trivia(i.rb(), leading, baseline, stops)
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum MlMode {
    All,
    LayoutOnly,
    None,
}

pub(super) fn expr(mut i: RewriteIn) -> Option<TailExit> {
    expr_at(
        i.rb(),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
    )
}

fn expr_at(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> Option<TailExit> {
    let nud = i.token(|lex| scan_nud_item(lex, baseline, stops))?;
    Some(expr_from_nud(
        i,
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
    ))
}

pub(super) fn expr_from_nud(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let mut acquire = ordinary_complete_item;
    match expr_from_nud_with(
        i,
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        false,
        &mut acquire,
    ) {
        L5aExit::Complete(exit) => exit,
        L5aExit::Deferred(_) => unreachable!("ordinary expressions enter every existing owner"),
    }
}

pub(super) fn expr_from_nud_l5a<F>(
    i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    expr_from_nud_with(
        i,
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        true,
        acquire,
    )
}

fn expr_from_nud_with<F>(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    if defer_distinct_owner && is_distinct_owner_nud(i.rb(), &nud) {
        return L5aExit::Deferred(nud);
    }
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = append_nud_with(
        i.rb(),
        nud,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        defer_distinct_owner,
        acquire,
    );
    i.state.finish_node();
    exit
}

fn append_nud_with<F>(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    if is_contextual_word(i.rb(), &nud, "case") {
        return L5aExit::Complete(case_like_nud(
            i,
            CaseLikeFamily::Case,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
        ));
    }
    if is_contextual_word(i.rb(), &nud, "catch") {
        return L5aExit::Complete(case_like_nud(
            i,
            CaseLikeFamily::Catch,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
        ));
    }
    if is_contextual_word(i.rb(), &nud, "if") {
        return L5aExit::Complete(if_nud(
            i,
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
        ));
    }
    match token_kind(&nud) {
        Some(TokenKind::Identifier) => {
            emit_identifier_core(&mut i, nud);
            scan_tail_after_accept_with(
                i.rb(),
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            )
        }
        Some(TokenKind::Integer) => {
            emit_integer_core(&mut i, nud);
            scan_tail_after_accept_with(
                i.rb(),
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            )
        }
        Some(TokenKind::LParen) => {
            if defer_distinct_owner {
                super::delimited::parenthesized_nud_with(
                    i.rb(),
                    nud,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    true,
                    acquire,
                )
            } else {
                L5aExit::Complete(parenthesized_nud(
                    i.rb(),
                    nud,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                ))
            }
        }
        Some(TokenKind::LBrace) => L5aExit::Complete(braced_nud(
            i.rb(),
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
        )),
        Some(TokenKind::Operator) => operator_nud_with(
            i.rb(),
            nud,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            defer_distinct_owner,
            acquire,
        ),
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
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let mut acquire = ordinary_complete_item;
    match required_expr_after_accept_with(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        false,
        &mut acquire,
    ) {
        L5aExit::Complete(exit) => exit,
        L5aExit::Deferred(_) => unreachable!("ordinary operands enter every existing owner"),
    }
}

pub(super) fn required_expr_item(
    mut i: RewriteIn,
    mut item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let mut acquire = ordinary_complete_item;
    match required_expr_item_with(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        false,
        &mut acquire,
    ) {
        L5aExit::Complete(exit) => exit,
        L5aExit::Deferred(_) => unreachable!("ordinary operands enter every existing owner"),
    }
}

fn required_expr_after_accept_with<F>(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    let item = acquire(
        &mut i,
        CompleteItemSite::Nud,
        baseline,
        stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
    );
    required_expr_item_with(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        defer_distinct_owner,
        acquire,
    )
}

fn required_expr_item_with<F>(
    mut i: RewriteIn,
    mut item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    if defer_distinct_owner && is_distinct_owner_nud(i.rb(), &item) {
        return L5aExit::Deferred(item);
    }
    if is_required_operand_boundary(i.rb(), &item, stops) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return L5aExit::Complete(handoff(item));
    }
    if is_nud_item(&item) {
        return append_nud_with(
            i,
            item,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            defer_distinct_owner,
            acquire,
        );
    }
    if is_unread_operand_boundary(&item) {
        return L5aExit::Complete(handoff(item));
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        item = acquire(
            &mut i,
            CompleteItemSite::Nud,
            baseline,
            stops & !(STOP_RECORD_SPREAD | STOP_RECORD_SPREAD_AFTER_OPERATOR),
        );
        if defer_distinct_owner && is_distinct_owner_nud(i.rb(), &item) {
            i.state.finish_node();
            return L5aExit::Deferred(item);
        }
        if is_required_operand_boundary(i.rb(), &item, stops) {
            i.state.finish_node();
            return L5aExit::Complete(handoff(item));
        }
        if is_nud_item(&item) {
            i.state.finish_node();
            return append_nud_with(
                i,
                item,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            );
        }
        if is_unread_operand_boundary(&item) {
            i.state.finish_node();
            return L5aExit::Complete(handoff(item));
        }
    }
}

pub(super) fn is_required_operand_boundary(mut i: RewriteIn, item: &Item, stops: Stops) -> bool {
    (item.payload_view().is_eof() || item.payload_view().is_boundary())
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
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let mut acquire = ordinary_complete_item;
    match scan_tail_after_accept_with(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        false,
        &mut acquire,
    ) {
        L5aExit::Complete(exit) => exit,
        L5aExit::Deferred(_) => unreachable!("ordinary tails enter every existing owner"),
    }
}

fn scan_tail_after_accept_with<F>(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    let item = acquire(&mut i, CompleteItemSite::Led, baseline, stops);
    tail_with(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        defer_distinct_owner,
        acquire,
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

pub(super) fn continue_l5a_tail<F>(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    exit: L5aExit,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    match exit {
        L5aExit::Complete(Ok(())) => scan_tail_after_accept_with(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            true,
            acquire,
        ),
        L5aExit::Complete(Err(Either::Left(item))) => tail_with(
            i,
            item,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            true,
            acquire,
        ),
        L5aExit::Complete(Err(Either::Right(end))) => L5aExit::Complete(Err(Either::Right(end))),
        L5aExit::Deferred(item) => L5aExit::Deferred(item),
    }
}

pub(super) fn tail(
    mut i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let mut acquire = ordinary_complete_item;
    match tail_with(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        false,
        &mut acquire,
    ) {
        L5aExit::Complete(exit) => exit,
        L5aExit::Deferred(_) => unreachable!("ordinary tails enter every existing owner"),
    }
}

pub(super) fn tail_l5a<F>(
    i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    tail_with(
        i,
        item,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        true,
        acquire,
    )
}

fn tail_with<F>(
    mut i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    if item.payload_view().is_boundary() {
        return L5aExit::Complete(handoff(item));
    }
    if is_active_stop(i.rb(), &item, stops) || is_line_stop(&item, stops) {
        return L5aExit::Complete(handoff(item));
    }
    if is_with_tail_item(i.rb(), &item, baseline, ml_mode) {
        return if defer_distinct_owner {
            L5aExit::Deferred(item)
        } else {
            L5aExit::Complete(with_tail(i, item, baseline, stops, line_handoff))
        };
    }
    if item.leading_view().is_grammar_empty() {
        match token_kind(&item) {
            Some(TokenKind::LParen) => {
                return if defer_distinct_owner {
                    super::tails::call_tail_with(
                        i.rb(),
                        item,
                        threshold,
                        baseline,
                        stops,
                        ml_mode,
                        line_handoff,
                        true,
                        acquire,
                    )
                } else {
                    L5aExit::Complete(call_tail(
                        i,
                        item,
                        threshold,
                        baseline,
                        stops,
                        ml_mode,
                        line_handoff,
                    ))
                };
            }
            Some(TokenKind::LBracket) => {
                return if defer_distinct_owner {
                    super::tails::index_tail_with(
                        i.rb(),
                        item,
                        threshold,
                        baseline,
                        stops,
                        ml_mode,
                        line_handoff,
                        true,
                        acquire,
                    )
                } else {
                    L5aExit::Complete(index_tail(
                        i,
                        item,
                        threshold,
                        baseline,
                        stops,
                        ml_mode,
                        line_handoff,
                    ))
                };
            }
            _ => {}
        }
    }
    match token_kind(&item) {
        Some(TokenKind::Dot) => {
            return if defer_distinct_owner {
                super::tails::dot_tail_with(
                    i.rb(),
                    item,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    true,
                    acquire,
                )
            } else {
                L5aExit::Complete(dot_tail(
                    i,
                    item,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                ))
            };
        }
        Some(TokenKind::PathSeparator) => {
            return if defer_distinct_owner {
                super::tails::path_tail_with(
                    i.rb(),
                    item,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    true,
                    acquire,
                )
            } else {
                L5aExit::Complete(path_tail(
                    i,
                    item,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                ))
            };
        }
        Some(TokenKind::Operator) if is_led_operator(&item) => {
            return operator_tail_with(
                i.rb(),
                item,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            );
        }
        _ => {}
    }
    if is_ml_argument(&item, baseline, ml_mode) {
        return ml_argument_with(
            i.rb(),
            item,
            threshold,
            baseline,
            stops,
            line_handoff,
            defer_distinct_owner,
            acquire,
        );
    }
    if token_kind(&item) == Some(TokenKind::Colon) {
        return if defer_distinct_owner {
            L5aExit::Deferred(item)
        } else {
            L5aExit::Complete(colon_tail(i, item, baseline, stops, ml_mode, line_handoff))
        };
    }
    L5aExit::Complete(handoff(item))
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

fn ml_argument_with<F>(
    mut i: RewriteIn,
    argument: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    i.state.start_node(SyntaxKind::MlArgument.into());
    let exit = expr_from_nud_with(
        i.rb(),
        argument,
        threshold,
        baseline,
        stops,
        MlMode::None,
        line_handoff,
        defer_distinct_owner,
        acquire,
    );
    i.state.finish_node();
    if defer_distinct_owner {
        continue_l5a_tail(
            i,
            threshold,
            baseline,
            stops,
            MlMode::All,
            line_handoff,
            exit,
            acquire,
        )
    } else {
        match exit {
            L5aExit::Complete(exit) => L5aExit::Complete(continue_completed_tail(
                i,
                threshold,
                baseline,
                stops,
                MlMode::All,
                line_handoff,
                exit,
            )),
            L5aExit::Deferred(_) => unreachable!("ordinary ML arguments enter every owner"),
        }
    }
}

fn operator_nud_with<F>(
    mut i: RewriteIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    match operator_use(&operator) {
        Some(OperatorUse::Prefix(right)) => {
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::PrefixOperatorUse);
            let rhs = required_expr_after_accept_with(
                i.rb(),
                Some(&right),
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            );
            continue_tail_by_mode(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                rhs,
                defer_distinct_owner,
                acquire,
            )
        }
        Some(OperatorUse::Nullfix) => {
            emit_operator_use(&mut i, operator, SyntaxKind::NullfixOperatorUse);
            scan_tail_after_accept_with(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            )
        }
        _ => unreachable!("the NUD scanner accepts only prefix and nullfix operators"),
    }
}

fn operator_tail_with<F>(
    mut i: RewriteIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    match operator_use(&operator) {
        Some(OperatorUse::Infix { left, right }) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return L5aExit::Complete(handoff(operator));
            }
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::InfixOperatorUse);
            let rhs = required_expr_after_accept_with(
                i.rb(),
                Some(&right),
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            );
            continue_tail_by_mode(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                rhs,
                defer_distinct_owner,
                acquire,
            )
        }
        Some(OperatorUse::Suffix(left)) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return L5aExit::Complete(handoff(operator));
            }
            emit_operator_use(&mut i, operator, SyntaxKind::SuffixOperatorUse);
            scan_tail_after_accept_with(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                defer_distinct_owner,
                acquire,
            )
        }
        _ => unreachable!("the LED scanner accepts only infix and suffix operators"),
    }
}

fn continue_tail_by_mode<F>(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    exit: L5aExit,
    defer_distinct_owner: bool,
    acquire: &mut F,
) -> L5aExit
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    if defer_distinct_owner {
        continue_l5a_tail(
            i,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            exit,
            acquire,
        )
    } else {
        match exit {
            L5aExit::Complete(exit) => L5aExit::Complete(continue_completed_tail(
                i,
                threshold,
                baseline,
                stops,
                ml_mode,
                line_handoff,
                exit,
            )),
            L5aExit::Deferred(_) => unreachable!("ordinary tails enter every owner"),
        }
    }
}

pub(super) fn is_distinct_owner_nud(mut i: RewriteIn, item: &Item) -> bool {
    !(item.payload_view().is_boundary() || item.payload_view().is_eof())
        && (token_kind(item) == Some(TokenKind::LBrace)
            || is_contextual_word(i.rb(), item, "case")
            || is_contextual_word(i.rb(), item, "catch")
            || is_contextual_word(i, item, "if"))
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
