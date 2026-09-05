//! Direct fixed continuations over already-owned Items.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    delimited::delimited_items,
    driver::{
        CompleteItemSite, Either, L5aExit, MlMode, TailExit, chain_continuation,
        continue_completed_tail, continue_l5a_tail, expr_from_nud, expr_from_nud_l5a, handoff,
        implicit_delimited_newline, is_active_stop, is_close, is_led_operator, is_nud_item,
        is_separator, scan_tail_after_accept, tail, tail_l5a, token_kind,
    },
    emit::{emit_missing, emit_token_item, emit_with_keyword},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation, path_segment_item_after_trivia, scan_trivia,
        statement_item_after_trivia, tail_item_after_trivia, with_colon_follower,
    },
    operator::STOP_COMMA,
    statement::{
        StatementLineHandoff, canonical_statement, indented_statement_block,
        is_canonical_statement_nud,
    },
};

/// A lone eligible colon is terminal and owns its mandatory RHS, including
/// recovery. Inline RHSs use the direct expression vocabulary; indented RHSs
/// use canonical Statements.
pub(super) fn colon_tail(
    mut i: RewriteIn,
    mut colon: Item,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if matches!(ml_mode, MlMode::None) || !chain_continuation(colon.leading_view(), baseline) {
        return handoff(colon);
    }
    let indented =
        introduced_body_indentation(i.rb()).is_some_and(|indentation| indentation > baseline);

    colon.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::ColonApplicationTail.into());
    emit_token_item(&mut i, colon);

    let exit = if !indented {
        let leading = scan_trivia(i.rb());
        let item = tail_item_after_trivia(
            i.rb(),
            leading,
            OperatorSite::Nud,
            baseline,
            stops | STOP_COMMA,
        );
        inline_colon_argument(i.rb(), item, baseline, stops, ml_mode, true, line_handoff)
    } else {
        indented_statement_block(i.rb(), baseline, stops)
    };
    i.state.finish_node();
    exit
}

fn inline_colon_argument(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    missing_on_boundary: bool,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if is_colon_owned_comma(&item, stops) {
        emit_inline_leading(&mut i, &mut item);
        if missing_on_boundary {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return inline_colon_successor(i, handoff(item), baseline, stops, ml_mode, line_handoff);
    }
    if inline_colon_boundary(i.rb(), &item, baseline, stops) {
        if missing_on_boundary {
            emit_inline_missing(&mut i, &mut item, baseline);
        }
        return handoff(item);
    }

    emit_inline_leading(&mut i, &mut item);
    if !is_nud_item(&item) {
        item = retry_inline_colon_argument(i.rb(), item, baseline, stops);
        if is_colon_owned_comma(&item, stops) {
            return inline_colon_successor(
                i,
                handoff(item),
                baseline,
                stops,
                ml_mode,
                line_handoff,
            );
        }
        if inline_colon_boundary(i.rb(), &item, baseline, stops) {
            if !implicit_delimited_newline(baseline, item.leading_view()) {
                emit_inline_leading(&mut i, &mut item);
            }
            return handoff(item);
        }
        emit_inline_leading(&mut i, &mut item);
    }

    let exit = expr_from_nud(
        i.rb(),
        item,
        None,
        baseline,
        stops | STOP_COMMA,
        ml_mode,
        line_handoff,
    );
    inline_colon_successor(i, exit, baseline, stops, ml_mode, line_handoff)
}

fn inline_colon_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    match exit {
        Ok(()) => Ok(()),
        Err(Either::Left(comma))
            if token_kind(&comma) == Some(TokenKind::Comma) && stops & STOP_COMMA == 0 =>
        {
            emit_token_item(&mut i, comma);
            let leading = scan_trivia(i.rb());
            let item = tail_item_after_trivia(
                i.rb(),
                leading,
                OperatorSite::Nud,
                baseline,
                stops | STOP_COMMA,
            );
            inline_colon_argument(i, item, baseline, stops, ml_mode, true, line_handoff)
        }
        exit => exit,
    }
}

fn retry_inline_colon_argument(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(
            i.rb(),
            leading,
            OperatorSite::Nud,
            baseline,
            stops | STOP_COMMA,
        );
        if is_colon_owned_comma(&item, stops)
            || inline_colon_boundary(i.rb(), &item, baseline, stops)
            || is_nud_item(&item)
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn is_colon_owned_comma(item: &Item, stops: Stops) -> bool {
    token_kind(item) == Some(TokenKind::Comma) && stops & STOP_COMMA == 0
}

fn inline_colon_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
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

/// The terminal generic `with:` continuation. Its body is an existing direct
/// Statement callee, never a target-owning or replayed expression parser.
pub(super) fn with_tail(
    mut i: RewriteIn,
    mut keyword: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::WithBodyTail.into());
    emit_with_keyword(&mut i, keyword);

    let exit = if i
        .rb()
        .map(with_colon_follower, |follower| follower)
        .unwrap_or(false)
    {
        let leading = scan_trivia(i.rb());
        let colon = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
        debug_assert_eq!(token_kind(&colon), Some(TokenKind::Colon));
        emit_token_item(&mut i, colon);
        if introduced_body_indentation(i.rb()).is_some_and(|indentation| indentation > baseline) {
            indented_statement_block(i.rb(), baseline, stops)
        } else {
            let exit = with_inline_body(i.rb(), baseline, stops, true, true, line_handoff);
            with_inline_terminal(i.rb(), exit, baseline, stops)
        }
    } else {
        let leading = scan_trivia(i.rb());
        let mut item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if implicit_delimited_newline(baseline, item.leading_view()) {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return handoff(item);
        }
        emit_inline_leading(&mut i, &mut item);
        emit_missing(&mut i, LeadingTrivia::default());
        let exit = with_inline_item(i.rb(), item, baseline, stops, false, false, line_handoff);
        exit
    };

    i.state.finish_node();
    exit
}

fn with_inline_body(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
    with_inline_item(
        i,
        item,
        baseline,
        stops,
        missing_on_boundary,
        allow_braced,
        line_handoff,
    )
}

fn with_inline_item(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if !allow_braced
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::PathSeparator)
        )
    {
        return handoff(item);
    }
    if with_inline_boundary(i.rb(), &item, baseline, stops) {
        if missing_on_boundary {
            emit_with_inline_missing(&mut i, &mut item, baseline);
        }
        return handoff(item);
    }
    emit_inline_leading(&mut i, &mut item);
    if is_canonical_statement_nud(i.rb(), &item, baseline)
        && (allow_braced || token_kind(&item) != Some(TokenKind::LBrace))
    {
        return canonical_statement(
            i,
            item,
            baseline,
            stops,
            line_handoff.through_inline_statement(),
        );
    }

    item = retry_with_inline_body(i.rb(), item, baseline, stops, allow_braced);
    if !allow_braced
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::PathSeparator)
        )
    {
        return handoff(item);
    }
    if with_inline_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            emit_inline_leading(&mut i, &mut item);
        }
        return handoff(item);
    }
    emit_inline_leading(&mut i, &mut item);
    debug_assert!(is_canonical_statement_nud(i.rb(), &item, baseline));
    canonical_statement(
        i,
        item,
        baseline,
        stops,
        line_handoff.through_inline_statement(),
    )
}

fn retry_with_inline_body(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    allow_braced: bool,
) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if with_inline_boundary(i.rb(), &item, baseline, stops)
            || (!allow_braced
                && matches!(
                    token_kind(&item),
                    Some(TokenKind::LBrace | TokenKind::PathSeparator)
                ))
            || (is_canonical_statement_nud(i.rb(), &item, baseline)
                && (allow_braced || token_kind(&item) != Some(TokenKind::LBrace)))
        {
            i.state.finish_node();
            return item;
        }
    }
}

fn with_inline_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn emit_with_inline_missing(i: &mut RewriteIn, item: &mut Item, baseline: usize) {
    if !implicit_delimited_newline(baseline, item.leading_view()) {
        emit_inline_leading(i, item);
    }
    emit_missing(i, LeadingTrivia::default());
}

fn with_inline_terminal(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    let Err(Either::Left(semicolon)) = exit else {
        return exit;
    };
    if token_kind(&semicolon) != Some(TokenKind::Semicolon) {
        return handoff(semicolon);
    }
    emit_token_item(&mut i, semicolon);
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i, leading, OperatorSite::Led, baseline, stops);
    handoff(item)
}

pub(super) fn call_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, line_handoff, exit)
}

pub(super) fn call_tail_with<F>(
    mut i: RewriteIn,
    open: Item,
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
    debug_assert!(defer_distinct_owner);
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let exit = super::delimited::delimited_items_l5a(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::All,
        line_handoff,
        acquire,
    );
    i.state.finish_node();
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
}

pub(super) fn index_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RBracket,
        Some(SyntaxKind::IndexItem),
        false,
        baseline,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, line_handoff, exit)
}

pub(super) fn index_tail_with<F>(
    mut i: RewriteIn,
    open: Item,
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
    debug_assert!(defer_distinct_owner);
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let exit = super::delimited::delimited_items_l5a(
        i.rb(),
        TokenKind::RBracket,
        Some(SyntaxKind::IndexItem),
        false,
        baseline,
        MlMode::All,
        line_handoff,
        acquire,
    );
    i.state.finish_node();
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
}

pub(super) fn dot_tail(
    mut i: RewriteIn,
    dot: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let next = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    if next.leading_view().is_grammar_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => {
                return projection_tuple_tail(
                    i,
                    dot,
                    next,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                );
            }
            Some(TokenKind::LBrace) => {
                return projection_record_tail(
                    i,
                    dot,
                    next,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                );
            }
            _ => {}
        }
    }
    field_tail(
        i,
        dot,
        next,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
    )
}

pub(super) fn dot_tail_with<F>(
    mut i: RewriteIn,
    dot: Item,
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
    debug_assert!(defer_distinct_owner);
    let next = acquire(&mut i, CompleteItemSite::Led, baseline, stops);
    if next.leading_view().is_grammar_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => {
                return projection_tail_with(
                    i,
                    dot,
                    next,
                    SyntaxKind::ProjectionTupleTail,
                    TokenKind::RParen,
                    false,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    acquire,
                );
            }
            Some(TokenKind::LBrace) => {
                return projection_tail_with(
                    i,
                    dot,
                    next,
                    SyntaxKind::ProjectionRecordTail,
                    TokenKind::RBrace,
                    true,
                    threshold,
                    baseline,
                    stops,
                    ml_mode,
                    line_handoff,
                    acquire,
                );
            }
            _ => {}
        }
    }
    field_tail_with(
        i,
        dot,
        next,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        acquire,
    )
}

fn field_tail_with<F>(
    mut i: RewriteIn,
    dot: Item,
    mut name: Item,
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
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if token_kind(&name) == Some(TokenKind::Identifier) && name.leading_view().is_grammar_empty() {
        emit_token_item(&mut i, name);
        i.state.finish_node();
        let next = acquire(&mut i, CompleteItemSite::Led, baseline, stops);
        return tail_l5a(
            i,
            next,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            acquire,
        );
    }
    if !name.leading_view().is_grammar_empty() || is_fixed_tail_boundary(&name) {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        name = retry_fixed_tail_item_l5a(i.rb(), name, baseline, stops, acquire);
    }
    i.state.finish_node();
    tail_l5a(
        i,
        name,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        acquire,
    )
}

#[allow(clippy::too_many_arguments)]
fn projection_tail_with<F>(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    node: SyntaxKind,
    close: TokenKind,
    record_spread: bool,
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
    i.state.start_node(node.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = super::delimited::delimited_items_l5a(
        i.rb(),
        close,
        None,
        record_spread,
        baseline,
        MlMode::All,
        line_handoff,
        acquire,
    );
    i.state.finish_node();
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
}

fn field_tail(
    mut i: RewriteIn,
    dot: Item,
    mut name: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if token_kind(&name) == Some(TokenKind::Identifier) && name.leading_view().is_grammar_empty() {
        emit_token_item(&mut i, name);
        i.state.finish_node();
        return scan_tail_after_accept(i, threshold, baseline, stops, ml_mode, line_handoff);
    }
    if !name.leading_view().is_grammar_empty() || is_fixed_tail_boundary(&name) {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        name = retry_fixed_tail_item(i.rb(), name, baseline, stops);
    }
    i.state.finish_node();
    tail(i, name, threshold, baseline, stops, ml_mode, line_handoff)
}

fn projection_tuple_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionTupleTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RParen,
        None,
        false,
        baseline,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, line_handoff, exit)
}

fn projection_record_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionRecordTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RBrace,
        None,
        true,
        baseline,
        MlMode::All,
        line_handoff,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, ml_mode, line_handoff, exit)
}

pub(super) fn path_tail(
    mut i: RewriteIn,
    separator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let leading = scan_trivia(i.rb());
    let mut segment = path_segment_item_after_trivia(i.rb(), leading, baseline, stops);
    if matches!(
        token_kind(&segment),
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
    ) {
        emit_token_item(&mut i, segment);
        i.state.finish_node();
        return scan_tail_after_accept(i, threshold, baseline, stops, ml_mode, line_handoff);
    }
    if is_fixed_tail_boundary(&segment) {
        segment.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        segment = retry_fixed_tail_item(i.rb(), segment, baseline, stops);
    }
    i.state.finish_node();
    tail(
        i,
        segment,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
    )
}

pub(super) fn path_tail_with<F>(
    mut i: RewriteIn,
    separator: Item,
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
    debug_assert!(defer_distinct_owner);
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let mut segment = acquire(&mut i, CompleteItemSite::PathSegment, baseline, stops);
    if matches!(
        token_kind(&segment),
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
    ) {
        emit_token_item(&mut i, segment);
        i.state.finish_node();
        let next = acquire(&mut i, CompleteItemSite::Led, baseline, stops);
        return tail_l5a(
            i,
            next,
            threshold,
            baseline,
            stops,
            ml_mode,
            line_handoff,
            acquire,
        );
    }
    if is_fixed_tail_boundary(&segment) {
        segment.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        segment = retry_fixed_tail_item_l5a(i.rb(), segment, baseline, stops, acquire);
    }
    i.state.finish_node();
    tail_l5a(
        i,
        segment,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        acquire,
    )
}

fn retry_fixed_tail_item(mut i: RewriteIn, mut item: Item, baseline: usize, stops: Stops) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
        if !item.leading_view().is_grammar_empty() || is_fixed_tail_boundary(&item) {
            i.state.finish_node();
            return item;
        }
    }
}

fn retry_fixed_tail_item_l5a<F>(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    acquire: &mut F,
) -> Item
where
    F: FnMut(&mut RewriteIn, CompleteItemSite, usize, Stops) -> Item,
{
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        item = acquire(&mut i, CompleteItemSite::Led, baseline, stops);
        if !item.leading_view().is_grammar_empty() || is_fixed_tail_boundary(&item) {
            i.state.finish_node();
            return item;
        }
    }
}

fn is_fixed_tail_boundary(item: &Item) -> bool {
    (item.payload_view().is_eof() || item.payload_view().is_boundary())
        || is_separator(item)
        || is_close(item)
        || is_led_operator(item)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::LParen | TokenKind::LBracket | TokenKind::Dot | TokenKind::PathSeparator
            )
        )
}
