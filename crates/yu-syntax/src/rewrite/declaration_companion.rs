//! Isolated direct declaration-companion construction.
//!
//! The declaration shell selects the exact contextual `with` Item.  This
//! owner starts after that decision and owns only the companion form, its
//! direct canonical Statement and Derives-run items, and its local
//! separators/brace close.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    derives::{derives_clause_normalized, is_word},
    driver::{
        Either, NormalizedExit, advanced_origin, complete, delimited_baseline, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, is_close,
        is_contextual_word, is_separator, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item, emit_with_keyword},
    if_expr::active_statement_companion,
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{scan_statement_payload, scan_unknown},
    operator::{STOP_COMMA, STOP_SEMICOLON, stops_for},
    statement::{
        StatementAdmission, StatementLineHandoff,
        canonical_statement_contents_from_admission_normalized, classify_statement_item_normalized,
    },
    type_expr::TypeOuterBoundary,
    yumark::FenceBoundary,
};

#[derive(Clone, Copy)]
enum CompanionLayout {
    Inline,
    Indented { block_indent: usize },
    Braced { baseline: usize },
}

struct SlotExit {
    exit: NormalizedExit,
    item_origin: usize,
    complete: bool,
    pending_admission: Option<CompanionItemAdmission>,
}

#[derive(Clone, Copy)]
enum CompanionItemAdmission {
    Derives,
    Statement(StatementAdmission),
    Rejected,
}

/// Construct one already-selected declaration companion.  Attachment gap,
/// owner priority, and the declaration shell remain outside this isolated
/// owner until their later Gate 6 gates.
#[allow(clippy::too_many_arguments)]
pub(super) fn declaration_companion_normalized(
    mut i: RewriteIn,
    mut with_keyword: Item,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    debug_assert!(is_contextual_word(i.rb(), &with_keyword, "with"));

    i.state.start_node(SyntaxKind::DeclarationCompanion.into());
    with_keyword.emit_all_remaining_leading(&mut *i.state);
    emit_with_keyword(&mut i, with_keyword);
    let (item, item_origin, line_entry) = companion_form_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        caller_stops,
    );
    let exit = companion_after_keyword(
        i.rb(),
        item,
        baseline,
        caller_stops,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn companion_after_keyword(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if introducer_boundary(i.rb(), &item, baseline, caller_stops) {
        if !item.payload_view().is_boundary() && !item.leading_view().has_ordinary_newline() {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    let admission = classify_companion_item(i.rb(), &item, baseline, item_origin, fence);
    match token_kind(&item) {
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            colon_form(i, baseline, caller_stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => {
            emit_token_item(&mut i, item);
            braced_form(i, baseline, caller_stops, item_origin, line_entry, fence)
        }
        _ if !matches!(admission, CompanionItemAdmission::Rejected) => {
            emit_missing(&mut i, LeadingTrivia::default());
            inline_form_from_item(
                i,
                item,
                admission,
                baseline,
                caller_stops,
                item_origin,
                line_entry,
                fence,
            )
        }
        _ => retry_introducer(
            i,
            item,
            baseline,
            caller_stops,
            item_origin,
            line_entry,
            fence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_introducer(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    caller_stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(&mut i, item);
    let mut item;
    loop {
        (item, item_origin, line_entry) = companion_form_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            caller_stops,
        );
        if introducer_boundary(i.rb(), &item, baseline, caller_stops) {
            if !item.payload_view().is_boundary() {
                if item.leading_view().has_ordinary_newline() {
                    emit_leading_before_first_newline(&mut i, &mut item);
                } else {
                    item.emit_all_remaining_leading(&mut *i.state);
                }
            }
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }

        let starter = matches!(
            token_kind(&item),
            Some(TokenKind::Colon | TokenKind::LBrace)
        );
        let admission = classify_companion_item(i.rb(), &item, baseline, item_origin, fence);
        if starter || !matches!(admission, CompanionItemAdmission::Rejected) {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            return match token_kind(&item) {
                Some(TokenKind::Colon) => {
                    emit_token_item(&mut i, item);
                    colon_form(i, baseline, caller_stops, item_origin, line_entry, fence)
                }
                Some(TokenKind::LBrace) => {
                    emit_token_item(&mut i, item);
                    braced_form(i, baseline, caller_stops, item_origin, line_entry, fence)
                }
                _ => inline_form_from_item(
                    i,
                    item,
                    admission,
                    baseline,
                    caller_stops,
                    item_origin,
                    line_entry,
                    fence,
                ),
            };
        }
        emit_token_item(&mut i, item);
    }
}

#[allow(clippy::too_many_arguments)]
fn colon_form(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) = statement_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        caller_stops | STOP_COMMA | STOP_SEMICOLON,
    );
    let indentation = indentation_after_newline(item.leading_view());
    if let Some(block_indent) = indentation {
        if block_indent <= baseline
            || companion_body_boundary(i.rb(), &item, baseline, caller_stops)
        {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }
        return indented_form_from_item(
            i,
            item,
            block_indent,
            caller_stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    if companion_body_boundary(i.rb(), &item, baseline, caller_stops) {
        if !item.payload_view().is_boundary() {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    let admission = classify_companion_item(i.rb(), &item, baseline, item_origin, fence);
    inline_form_from_item(
        i,
        item,
        admission,
        baseline,
        caller_stops,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn inline_form_from_item(
    mut i: RewriteIn,
    item: Item,
    admission: CompanionItemAdmission,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let slot = companion_item_slot(
        i.rb(),
        item,
        admission,
        CompanionLayout::Inline,
        baseline,
        caller_stops | STOP_COMMA | STOP_SEMICOLON,
        item_origin,
        line_entry,
        fence,
    );
    if !slot.complete {
        return slot.exit;
    }
    let (mut item, _, line_entry, _) = successor_item(
        i.rb(),
        slot.exit,
        slot.pending_admission,
        slot.item_origin,
        fence,
        baseline,
        caller_stops | STOP_COMMA | STOP_SEMICOLON,
    );
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if token_kind(&item) == Some(TokenKind::Semicolon)
        && !item.leading_view().has_ordinary_newline()
    {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_token_item(&mut i, item);
        complete(Ok(()), line_entry)
    } else {
        complete(handoff(item), line_entry)
    }
}

#[allow(clippy::too_many_arguments)]
fn indented_form_from_item(
    mut i: RewriteIn,
    mut item: Item,
    block_indent: usize,
    caller_stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::DeclarationCompanionIndentedBody.into());
    item.emit_all_remaining_leading(&mut *i.state);
    let mut after_separator = false;
    let mut admission = classify_companion_item(i.rb(), &item, block_indent, item_origin, fence);
    loop {
        if indented_terminal(i.rb(), &item, block_indent, caller_stops) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }

        if token_kind(&item) == Some(TokenKind::Semicolon) {
            if after_separator {
                emit_missing_statement(&mut i);
            }
            (item, item_origin, line_entry) = consume_explicit_separator(
                i.rb(),
                item,
                item_origin,
                line_entry,
                fence,
                block_indent,
                caller_stops | STOP_SEMICOLON,
                Some(block_indent),
            );
            after_separator = true;
            admission = classify_companion_item(i.rb(), &item, block_indent, item_origin, fence);
            continue;
        }

        if indentation_after_newline(item.leading_view()) == Some(block_indent) {
            emit_separator_leading(&mut i, &mut item);
        }

        let slot = companion_item_slot(
            i.rb(),
            item,
            admission,
            CompanionLayout::Indented { block_indent },
            block_indent,
            caller_stops | STOP_SEMICOLON,
            item_origin,
            line_entry,
            fence,
        );
        item_origin = slot.item_origin;
        if !slot.complete {
            i.state.finish_node();
            return slot.exit;
        }
        let (next, next_origin, next_entry, carried_admission) = successor_item(
            i.rb(),
            slot.exit,
            slot.pending_admission,
            item_origin,
            fence,
            block_indent,
            caller_stops | STOP_SEMICOLON,
        );
        item = next;
        item_origin = next_origin;
        line_entry = next_entry;
        admission = carried_admission.unwrap_or_else(|| {
            classify_companion_item(i.rb(), &item, block_indent, item_origin, fence)
        });
        after_separator = false;

        if !matches!(admission, CompanionItemAdmission::Rejected)
            && indentation_after_newline(item.leading_view()).is_none()
        {
            emit_missing(&mut i, LeadingTrivia::default());
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum BracedSlot {
    Initial,
    AfterItem,
    AfterSeparator,
}

#[allow(clippy::too_many_arguments)]
fn braced_form(
    mut i: RewriteIn,
    incoming_baseline: usize,
    caller_stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let local_stops = caller_stops | stops_for(TokenKind::RBrace);
    let (mut item, next_origin, next_entry) = statement_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        incoming_baseline,
        local_stops,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    let baseline = delimited_baseline(incoming_baseline, item.leading_view());
    let mut slot = BracedSlot::Initial;
    let mut admission = classify_companion_item(i.rb(), &item, baseline, item_origin, fence);

    loop {
        if !item.payload_view().is_boundary() && !item.payload_view().is_eof() {
            match token_kind(&item) {
                Some(TokenKind::RBrace) => {
                    item.emit_all_remaining_leading(&mut *i.state);
                    emit_token_item(&mut i, item);
                    return complete(Ok(()), line_entry);
                }
                Some(TokenKind::Comma | TokenKind::Semicolon) => {
                    if matches!(slot, BracedSlot::Initial | BracedSlot::AfterSeparator) {
                        emit_missing_statement(&mut i);
                    }
                    (item, item_origin, line_entry) = consume_explicit_separator(
                        i.rb(),
                        item,
                        item_origin,
                        line_entry,
                        fence,
                        baseline,
                        local_stops,
                        None,
                    );
                    admission =
                        classify_companion_item(i.rb(), &item, baseline, item_origin, fence);
                    slot = BracedSlot::AfterSeparator;
                    continue;
                }
                _ => {}
            }
        }

        if item.payload_view().is_boundary() || item.payload_view().is_eof() {
            if item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            }
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }

        if is_active_stop(i.rb(), &item, caller_stops)
            || active_statement_companion(i.rb(), &item, baseline, caller_stops).is_some()
        {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(item), line_entry);
        }

        match token_kind(&item) {
            Some(TokenKind::RParen | TokenKind::RBracket) => {
                item.emit_all_remaining_leading(&mut *i.state);
                i.state.start_node(SyntaxKind::Error.into());
                emit_token_item(&mut i, item);
                i.state.finish_node();
                (item, item_origin, line_entry) = statement_item_normalized(
                    i.rb(),
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    local_stops,
                );
                admission = classify_companion_item(i.rb(), &item, baseline, item_origin, fence);
                continue;
            }
            _ => {}
        }

        if matches!(slot, BracedSlot::AfterItem)
            && implicit_delimited_newline(baseline, item.leading_view())
        {
            emit_separator_leading(&mut i, &mut item);
            slot = BracedSlot::AfterSeparator;
        } else if matches!(slot, BracedSlot::Initial) {
            item.emit_all_remaining_leading(&mut *i.state);
        }

        let candidate = !matches!(admission, CompanionItemAdmission::Rejected);
        if matches!(slot, BracedSlot::AfterItem) && candidate {
            emit_missing(&mut i, LeadingTrivia::default());
        }

        let parsed = companion_item_slot(
            i.rb(),
            item,
            admission,
            CompanionLayout::Braced { baseline },
            baseline,
            local_stops,
            item_origin,
            line_entry,
            fence,
        );
        item_origin = parsed.item_origin;
        let (next, next_origin, next_entry, carried_admission) = successor_item(
            i.rb(),
            parsed.exit,
            parsed.pending_admission,
            item_origin,
            fence,
            baseline,
            local_stops,
        );
        item = next;
        item_origin = next_origin;
        line_entry = next_entry;
        admission = carried_admission.unwrap_or_else(|| {
            classify_companion_item(i.rb(), &item, baseline, item_origin, fence)
        });
        slot = if parsed.complete {
            BracedSlot::AfterItem
        } else {
            BracedSlot::AfterSeparator
        };
    }
}

#[allow(clippy::too_many_arguments)]
fn companion_item_slot(
    i: RewriteIn,
    item: Item,
    admission: CompanionItemAdmission,
    layout: CompanionLayout,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> SlotExit {
    if matches!(admission, CompanionItemAdmission::Derives) {
        return derives_run_slot(
            i,
            item,
            layout,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
    }
    statement_slot(
        i,
        item,
        match admission {
            CompanionItemAdmission::Statement(admission) => Some(admission),
            CompanionItemAdmission::Derives | CompanionItemAdmission::Rejected => None,
        },
        layout,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn derives_run_slot(
    mut i: RewriteIn,
    mut item: Item,
    layout: CompanionLayout,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> SlotExit {
    loop {
        // A comma after a role belongs to DerivesClause even where the outer
        // companion sequence also accepts comma as an item separator.
        (item, item_origin, line_entry) = derives_clause_normalized(
            i.rb(),
            item,
            baseline,
            stops & !STOP_COMMA,
            derives_line_handoff(layout),
            TypeOuterBoundary::DERIVES.with(TypeOuterBoundary::VIA),
            item_origin,
            line_entry,
            fence,
        );
        if !is_word(&item, "derives") || derives_separator_before(&item, layout) {
            let pending_admission = if let CompanionLayout::Indented { block_indent } = layout
                && indentation_after_newline(item.leading_view())
                    .is_some_and(|indentation| indentation > block_indent)
                && !indented_terminal(i.rb(), &item, block_indent, stops)
            {
                Some(classify_companion_item(
                    i.rb(),
                    &item,
                    block_indent,
                    item_origin,
                    fence,
                ))
            } else {
                None
            };
            if pending_admission
                .is_some_and(|admission| !matches!(admission, CompanionItemAdmission::Rejected))
            {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            return SlotExit {
                exit: complete(handoff(item), line_entry),
                item_origin,
                complete: true,
                pending_admission,
            };
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn statement_slot(
    mut i: RewriteIn,
    mut item: Item,
    admission: Option<StatementAdmission>,
    layout: CompanionLayout,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> SlotExit {
    i.state.start_node(SyntaxKind::Statement.into());
    if let Some(admission) = admission {
        let entry = suffix_marker(i.rb());
        let exit = canonical_statement_contents_from_admission_normalized(
            i.rb(),
            item,
            admission,
            baseline,
            stops,
            line_handoff(layout),
            item_origin,
            line_entry,
            fence,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        i.state.finish_node();
        return SlotExit {
            exit,
            item_origin,
            complete: true,
            pending_admission: None,
        };
    }

    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(&mut i, item);
    loop {
        (item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        if statement_slot_boundary(i.rb(), &item, layout, stops) {
            if !item.payload_view().is_boundary() && !item.leading_view().has_ordinary_newline() {
                item.emit_all_remaining_leading(&mut *i.state);
            }
            i.state.finish_node();
            i.state.finish_node();
            return SlotExit {
                exit: complete(handoff(item), line_entry),
                item_origin,
                complete: false,
                pending_admission: None,
            };
        }
        if is_word(&item, "derives") {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            i.state.finish_node();
            return derives_run_slot(
                i,
                item,
                layout,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
        }
        if let Some(admission) =
            classify_statement_item_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            let entry = suffix_marker(i.rb());
            let exit = canonical_statement_contents_from_admission_normalized(
                i.rb(),
                item,
                admission,
                baseline,
                stops,
                line_handoff(layout),
                item_origin,
                line_entry,
                fence,
            );
            item_origin = advanced_origin(item_origin, entry, i.rb());
            i.state.finish_node();
            return SlotExit {
                exit,
                item_origin,
                complete: true,
                pending_admission: None,
            };
        }
        emit_token_item(&mut i, item);
    }
}

fn classify_companion_item(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> CompanionItemAdmission {
    if is_word(item, "derives") {
        CompanionItemAdmission::Derives
    } else if let Some(admission) =
        classify_statement_item_normalized(i.rb(), item, baseline, item_origin, fence)
    {
        CompanionItemAdmission::Statement(admission)
    } else {
        CompanionItemAdmission::Rejected
    }
}

fn line_handoff(layout: CompanionLayout) -> StatementLineHandoff {
    match layout {
        CompanionLayout::Braced { .. } => StatementLineHandoff::BracedStatementSequence,
        CompanionLayout::Inline | CompanionLayout::Indented { .. } => {
            StatementLineHandoff::OrdinaryLayout
        }
    }
}

fn derives_line_handoff(layout: CompanionLayout) -> StatementLineHandoff {
    match layout {
        CompanionLayout::Indented { .. } => StatementLineHandoff::OrdinaryLayout,
        CompanionLayout::Inline | CompanionLayout::Braced { .. } => {
            StatementLineHandoff::BracedStatementSequence
        }
    }
}

fn derives_separator_before(item: &Item, layout: CompanionLayout) -> bool {
    match layout {
        CompanionLayout::Inline => item.leading_view().has_ordinary_newline(),
        CompanionLayout::Indented { block_indent } => {
            indentation_after_newline(item.leading_view()) == Some(block_indent)
        }
        CompanionLayout::Braced { baseline } => {
            implicit_delimited_newline(baseline, item.leading_view())
        }
    }
}

fn statement_slot_boundary(
    mut i: RewriteIn,
    item: &Item,
    layout: CompanionLayout,
    stops: Stops,
) -> bool {
    if item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || is_active_stop(i.rb(), item, stops)
    {
        return true;
    }
    let indentation = indentation_after_newline(item.leading_view());
    match layout {
        CompanionLayout::Inline => indentation.is_some(),
        CompanionLayout::Indented { block_indent } => {
            indentation.is_some_and(|indentation| indentation <= block_indent)
        }
        CompanionLayout::Braced { baseline } => {
            implicit_delimited_newline(baseline, item.leading_view())
        }
    }
}

fn introducer_boundary(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    caller_stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || item.leading_view().has_ordinary_newline()
        || is_separator(item)
        || is_close(item)
        || is_active_stop(i.rb(), item, caller_stops)
        || active_statement_companion(i, item, baseline, caller_stops).is_some()
}

fn companion_body_boundary(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    caller_stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || is_active_stop(i.rb(), item, caller_stops)
        || active_statement_companion(i, item, baseline, caller_stops).is_some()
}

fn indented_terminal(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    caller_stops: Stops,
) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || token_kind(item) == Some(TokenKind::Comma)
        || is_close(item)
        || is_active_stop(i.rb(), item, caller_stops)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

#[allow(clippy::too_many_arguments)]
fn consume_explicit_separator(
    mut i: RewriteIn,
    separator: Item,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    indented: Option<usize>,
) -> (Item, usize, LineEntry) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    emit_token_item(&mut i, separator);
    let (mut item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    let dedent = indented.is_some_and(|block_indent| {
        indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
    });
    if !item.payload_view().is_boundary() && !dedent {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    i.state.finish_node();
    (item, item_origin, line_entry)
}

fn emit_separator_leading(i: &mut RewriteIn, item: &mut Item) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.finish_node();
}

fn emit_leading_before_first_newline(i: &mut RewriteIn, item: &mut Item) {
    let newline_end = item
        .leading_view()
        .cut_after_first_ordinary_newline()
        .expect("a newline boundary has one remaining ordinary newline");
    let newline_part = newline_end
        .checked_sub(1)
        .expect("the first newline has a physical part");
    item.emit_leading_prefix_with(&mut *i.state, newline_part, |_, _| {});
}

fn emit_missing_statement(i: &mut RewriteIn) {
    i.state.start_node(SyntaxKind::Statement.into());
    emit_missing(i, LeadingTrivia::default());
    i.state.finish_node();
}

fn successor_item(
    i: RewriteIn,
    exit: NormalizedExit,
    pending_admission: Option<CompanionItemAdmission>,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry, Option<CompanionItemAdmission>) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            let (item, item_origin, line_entry) =
                statement_item_normalized(i, item_origin, line_entry, fence, baseline, stops);
            (item, item_origin, line_entry, None)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry, pending_admission)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry, None)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized canonical statements do not defer declaration owners")
        }
    }
}

fn companion_form_item_normalized(
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
                |mut lex: LexIn, leading, origin, fence, _| {
                    if lex.remainder().starts_with("::") {
                        return lex.token(scan_unknown).map(|token| AcceptedPayload {
                            payload: CurrentPayload::Token(token),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                },
            )
        })
        .expect("declaration companion form scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn statement_item_normalized(
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
        .expect("declaration companion statement scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(super) fn declaration_companion_witness(
    mut i: RewriteIn,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    use crate::scan::operator::OperatorSite;

    use super::lexer::{contextual_word_suffix_follower, scan_expression_payload};

    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item: with_keyword,
        next_line_entry,
    } = i.token(|mut lex| {
        let current = current_item(
            lex.rb(),
            item_origin,
            line_entry,
            fence,
            |lex: LexIn, leading, origin, fence, _| {
                scan_expression_payload(
                    lex,
                    OperatorSite::Led,
                    leading,
                    origin,
                    fence,
                    baseline,
                    caller_stops,
                )
            },
        )?;
        let payload = current.item.payload_view();
        let accepted = payload.spelling() == Some("with")
            && (payload.token_kind() == Some(TokenKind::Identifier)
                || (payload.operator_use().is_some()
                    && lex
                        .token(contextual_word_suffix_follower)
                        .expect("contextual suffix observation is total")));
        accepted.then_some(current)
    })?;
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    Some(declaration_companion_normalized(
        i,
        with_keyword,
        baseline,
        caller_stops,
        item_origin,
        next_line_entry,
        fence,
    ))
}
