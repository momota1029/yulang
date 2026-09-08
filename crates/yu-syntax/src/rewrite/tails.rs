//! Direct fixed continuations over already-owned Items.

use super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    current_item::{CurrentItem, LineEntry, current_item},
    delimited::{DelimitedOwner, delimited_items_normalized},
    driver::{
        Either, MlMode, NormalizedExit, advanced_origin, chain_continuation, complete,
        continue_normalized_tail, expr_from_nud_normalized, expression_item, handoff,
        implicit_delimited_newline, is_active_stop, is_close, is_led_operator, is_nud_item,
        is_separator, scan_tail_after_accept_normalized, suffix_marker, tail_normalized,
        token_kind,
    },
    emit::{emit_missing, emit_token_item, emit_with_keyword},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, scan_path_segment_payload, scan_statement_payload,
    },
    operator::{STOP_COMMA, lone_colon_after_fenced_trivia},
    statement::{
        StatementAdmission, StatementLineHandoff, canonical_statement_from_admission_normalized,
        classify_statement_item_normalized, indented_statement_block_normalized,
    },
    yumark::FenceBoundary,
};

/// A lone eligible colon is terminal and owns its mandatory RHS, including
/// recovery. Inline RHSs use the direct expression vocabulary; indented RHSs
/// use canonical Statements.
#[allow(clippy::too_many_arguments)]
pub(super) fn colon_tail_normalized(
    mut i: RewriteIn,
    mut colon: Item,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if matches!(ml_mode, MlMode::None) || !chain_continuation(colon.leading_view(), baseline) {
        return complete(handoff(colon), line_entry);
    }
    let indented = introduced_body_indentation_normalized(i.rb(), item_origin, fence)
        .is_some_and(|indentation| indentation > baseline);

    colon.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::ColonApplicationTail.into());
    emit_token_item(&mut i, colon);

    let exit = if !indented {
        let (item, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops | STOP_COMMA,
        );
        inline_colon_argument_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            ml_mode,
            true,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        )
    } else {
        indented_statement_block_normalized(
            i.rb(),
            baseline,
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
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    missing_on_boundary: bool,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        if missing_on_boundary {
            emit_inline_missing(&mut i, &mut item, baseline);
        }
        return complete(handoff(item), line_entry);
    }
    if is_colon_owned_comma(&item, stops) {
        emit_inline_leading(&mut i, &mut item);
        if missing_on_boundary {
            emit_missing(&mut i, LeadingTrivia::default());
        }
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
        );
    }
    if inline_colon_boundary(i.rb(), &item, baseline, stops) {
        if missing_on_boundary {
            emit_inline_missing(&mut i, &mut item, baseline);
        }
        return complete(handoff(item), line_entry);
    }

    emit_inline_leading(&mut i, &mut item);
    if !is_nud_item(&item) {
        (item, item_origin, line_entry) = retry_inline_colon_argument_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
        if is_colon_owned_comma(&item, stops) {
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
            );
        }
        if inline_colon_boundary(i.rb(), &item, baseline, stops) {
            if !implicit_delimited_newline(baseline, item.leading_view()) {
                emit_inline_leading(&mut i, &mut item);
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
    )
}

#[allow(clippy::too_many_arguments)]
fn inline_colon_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            complete(handoff(item), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Left(comma)), line_entry)
            if token_kind(&comma) == Some(TokenKind::Comma) && stops & STOP_COMMA == 0 =>
        {
            emit_token_item(&mut i, comma);
            let (item, item_origin, line_entry) = expression_item(
                i.rb(),
                OperatorSite::Nud,
                item_origin,
                line_entry,
                fence,
                baseline,
                stops | STOP_COMMA,
            );
            inline_colon_argument_normalized(
                i,
                item,
                baseline,
                stops,
                ml_mode,
                true,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        exit => exit,
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_inline_colon_argument_normalized(
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
            stops | STOP_COMMA,
        );
        if is_colon_owned_comma(&item, stops)
            || inline_colon_boundary(i.rb(), &item, baseline, stops)
            || is_nud_item(&item)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn is_colon_owned_comma(item: &Item, stops: Stops) -> bool {
    token_kind(item) == Some(TokenKind::Comma) && stops & STOP_COMMA == 0
}

fn inline_colon_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
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
#[allow(clippy::too_many_arguments)]
pub(super) fn with_tail_normalized(
    mut i: RewriteIn,
    mut keyword: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::WithBodyTail.into());
    emit_with_keyword(&mut i, keyword);

    let has_colon = i
        .rb()
        .map(
            |lex: super::LexIn| {
                Some(lone_colon_after_fenced_trivia(
                    lex.remainder(),
                    item_origin,
                    LineEntry::InLine,
                    fence,
                ))
            },
            |follower| follower,
        )
        .unwrap_or(false);
    let exit = if has_colon {
        let (colon, item_origin, line_entry) = expression_item(
            i.rb(),
            OperatorSite::Led,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        debug_assert_eq!(token_kind(&colon), Some(TokenKind::Colon));
        emit_token_item(&mut i, colon);
        if introduced_body_indentation_normalized(i.rb(), item_origin, fence)
            .is_some_and(|indentation| indentation > baseline)
        {
            indented_statement_block_normalized(
                i.rb(),
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        } else {
            let entry = suffix_marker(i.rb());
            let exit = with_inline_body_normalized(
                i.rb(),
                baseline,
                stops,
                true,
                true,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            let item_origin = advanced_origin(item_origin, entry, i.rb());
            with_inline_terminal_normalized(i.rb(), exit, baseline, stops, item_origin, fence)
        }
    } else {
        let (mut item, item_origin, line_entry) = statement_item_for_tail_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        if item.payload_view().is_boundary() {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if implicit_delimited_newline(baseline, item.leading_view()) {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        emit_inline_leading(&mut i, &mut item);
        emit_missing(&mut i, LeadingTrivia::default());
        with_inline_item_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            false,
            false,
            line_handoff,
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
fn with_inline_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) =
        statement_item_for_tail_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    with_inline_item_normalized(
        i,
        item,
        baseline,
        stops,
        missing_on_boundary,
        allow_braced,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn with_inline_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    missing_on_boundary: bool,
    allow_braced: bool,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        if missing_on_boundary {
            emit_with_inline_missing(&mut i, &mut item, baseline);
        }
        return complete(handoff(item), line_entry);
    }
    if !allow_braced
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::PathSeparator)
        )
    {
        return complete(handoff(item), line_entry);
    }
    if with_inline_boundary(i.rb(), &item, baseline, stops) {
        if missing_on_boundary {
            emit_with_inline_missing(&mut i, &mut item, baseline);
        }
        return complete(handoff(item), line_entry);
    }
    if allow_braced || token_kind(&item) != Some(TokenKind::LBrace) {
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            return canonical_statement_from_admission_normalized(
                i,
                item,
                admission,
                baseline,
                stops,
                line_handoff.through_inline_statement(),
                item_origin,
                line_entry,
                fence,
                ambient,
            );
        }
    }

    emit_inline_leading(&mut i, &mut item);
    let admission;
    (item, admission, item_origin, line_entry) = retry_with_inline_body_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        allow_braced,
        item_origin,
        line_entry,
        fence,
    );
    if !allow_braced
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::PathSeparator)
        )
    {
        return complete(handoff(item), line_entry);
    }
    if with_inline_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, item.leading_view()) {
            emit_inline_leading(&mut i, &mut item);
        }
        return complete(handoff(item), line_entry);
    }
    canonical_statement_from_admission_normalized(
        i,
        item,
        admission.expect("inline-body retry returned an admitted canonical Statement"),
        baseline,
        stops,
        line_handoff.through_inline_statement(),
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_with_inline_body_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    allow_braced: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, Option<StatementAdmission>, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = statement_item_for_tail_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        if with_inline_boundary(i.rb(), &item, baseline, stops)
            || (!allow_braced
                && matches!(
                    token_kind(&item),
                    Some(TokenKind::LBrace | TokenKind::PathSeparator)
                ))
        {
            i.state.finish_node();
            return (item, None, item_origin, line_entry);
        }
        if (allow_braced || token_kind(&item) != Some(TokenKind::LBrace))
            && let Some(admission) =
                classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
            return (item, Some(admission), item_origin, line_entry);
        }
    }
}

fn with_inline_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
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

fn with_inline_terminal_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let NormalizedExit::Complete(Err(Either::Left(semicolon)), line_entry) = exit else {
        return exit;
    };
    if semicolon.payload_view().is_boundary() {
        return complete(handoff(semicolon), line_entry);
    }
    if token_kind(&semicolon) != Some(TokenKind::Semicolon) {
        return complete(handoff(semicolon), line_entry);
    }
    emit_token_item(&mut i, semicolon);
    let (item, _, line_entry) = expression_item(
        i,
        OperatorSite::Led,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    complete(handoff(item), line_entry)
}

fn statement_item_for_tail_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("statement payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn call_tail_normalized(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Call,
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn index_tail_normalized(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Index,
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn dot_tail_normalized(
    mut i: RewriteIn,
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
) -> NormalizedExit {
    let (next, item_origin, line_entry) = super::driver::expression_item(
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
    )
}

#[allow(clippy::too_many_arguments)]
fn field_tail_normalized(
    mut i: RewriteIn,
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
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if !name.payload_view().is_boundary()
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
        );
    }
    if name.payload_view().is_boundary()
        || !name.leading_view().is_grammar_empty()
        || is_fixed_tail_boundary(&name)
    {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        (name, item_origin, line_entry) = retry_fixed_tail_item_normalized(
            i.rb(),
            name,
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
    )
}

#[allow(clippy::too_many_arguments)]
fn projection_tail_normalized(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    node: SyntaxKind,
    record_spread: bool,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(node.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        if record_spread {
            DelimitedOwner::ProjectionRecord
        } else {
            DelimitedOwner::ProjectionTuple
        },
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn path_tail_normalized(
    mut i: RewriteIn,
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
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let (mut segment, next_origin, next_line_entry) =
        path_segment_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    item_origin = next_origin;
    line_entry = next_line_entry;
    if !segment.payload_view().is_boundary()
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
        );
    }
    if segment.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
    } else if is_fixed_tail_boundary(&segment) {
        segment.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        (segment, item_origin, line_entry) = retry_fixed_tail_item_normalized(
            i.rb(),
            segment,
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
    )
}

fn path_segment_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_path_segment_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("path-segment payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_fixed_tail_item_normalized(
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
        debug_assert!(!item.payload_view().is_boundary());
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = super::driver::expression_item(
            i.rb(),
            OperatorSite::Led,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        );
        if item.payload_view().is_boundary()
            || !item.leading_view().is_grammar_empty()
            || is_fixed_tail_boundary(&item)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
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
                TokenKind::LParen | TokenKind::LBracket | TokenKind::Dot | TokenKind::PathSeparator
            )
        )
}
