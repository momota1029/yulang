//! Direct canonical statements and their closed sequence owners.

use reborrow_generic::Reborrow as _;

use crate::{operator::BindingPower, syntax_kind::SyntaxKind};

use super::{
    RewriteIn, Stops,
    binding::{
        binding_statement_normalized, binding_statement_selected_normalized, is_binding_visibility,
    },
    current_item::{CurrentItem, LineEntry, current_item},
    driver::{
        Either, MlMode, NormalizedExit, TailExit, advanced_origin, complete,
        continue_normalized_tail, delimited_baseline, expr_from_nud_normalized, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, is_separator,
        is_statement_nud, ordinary_exit, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    for_decl::{for_statement_normalized, for_statement_selected},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::scan_statement_payload,
    mod_decl::{mod_declaration, mod_declaration_selected_normalized},
    operator::stops_for,
    struct_decl::{struct_declaration, struct_declaration_selected_normalized},
    type_decl::{type_declaration, type_declaration_selected_normalized},
    use_decl::{use_declaration, use_declaration_selected_normalized},
    yumark::FenceBoundary,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StatementLineHandoff {
    OrdinaryLayout,
    BracedStatementSequence,
    CatchBracedArm,
    CatchArmSequenceThroughInlineCanonicalStatement,
}

impl StatementLineHandoff {
    pub(super) fn through_inline_statement(self) -> Self {
        match self {
            Self::CatchBracedArm | Self::CatchArmSequenceThroughInlineCanonicalStatement => {
                Self::CatchArmSequenceThroughInlineCanonicalStatement
            }
            other => other,
        }
    }
}

pub(super) fn statement(i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    ordinary_exit(statement_normalized(
        i,
        baseline,
        stops,
        0,
        LineEntry::InLine,
        None,
    ))
}

pub(super) fn statement_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    statement_from_item_normalized(i, item, baseline, stops, item_origin, line_entry, fence)
}

pub(super) fn statement_from_item(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    ordinary_exit(statement_from_item_normalized(
        i,
        item,
        baseline,
        stops,
        0,
        LineEntry::InLine,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn statement_from_item_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if is_canonical_statement_nud_normalized(i.rb(), &item, baseline, item_origin, fence) {
        canonical_statement_normalized(
            i,
            item,
            baseline,
            stops,
            StatementLineHandoff::OrdinaryLayout,
            item_origin,
            line_entry,
            fence,
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

pub(super) fn canonical_statement(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(canonical_statement_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn canonical_statement_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    debug_assert!(!item.payload_view().is_boundary());
    debug_assert!(is_canonical_statement_nud_normalized(
        i.rb(),
        &item,
        baseline,
        item_origin,
        fence,
    ));
    let family = selected_declaration_family(i.rb(), &item, baseline, item_origin, fence);
    if declaration_family_is_deferred(family, fence) {
        return NormalizedExit::Deferred(item, line_entry);
    }
    i.state.start_node(SyntaxKind::Statement.into());
    let exit = match family {
        Some(DeclarationFamily::Struct) => struct_declaration(i.rb(), item, baseline, stops),
        Some(DeclarationFamily::Mod) => {
            mod_declaration(i.rb(), item, baseline, stops, line_handoff)
        }
        Some(DeclarationFamily::Use) => use_declaration(i.rb(), item, baseline, stops),
        Some(DeclarationFamily::Type) => {
            type_declaration(i.rb(), item, baseline, stops, line_handoff)
        }
        Some(DeclarationFamily::For) => {
            let exit = for_statement_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
            );
            i.state.finish_node();
            return exit;
        }
        Some(DeclarationFamily::Binding) => {
            let exit = binding_statement_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
            );
            i.state.finish_node();
            return exit;
        }
        None => {
            let exit = expr_from_nud_normalized(
                i.rb(),
                item,
                None,
                baseline,
                stops,
                MlMode::All,
                line_handoff,
                item_origin,
                line_entry,
                fence,
            );
            i.state.finish_node();
            return exit;
        }
    };
    i.state.finish_node();
    complete(exit, line_entry)
}

pub(super) fn is_canonical_statement_nud(i: RewriteIn, item: &Item, baseline: usize) -> bool {
    is_canonical_statement_nud_normalized(i, item, baseline, 0, None)
}

pub(super) fn is_canonical_statement_nud_normalized(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item.payload_view().is_boundary() {
        return false;
    }
    selected_declaration_family(i.rb(), item, baseline, item_origin, fence).is_some()
        || (!is_binding_visibility(item) && is_statement_nud(item))
}

#[derive(Clone, Copy)]
enum DeclarationFamily {
    Struct,
    Mod,
    Use,
    Type,
    For,
    Binding,
}

fn declaration_family_is_deferred(
    family: Option<DeclarationFamily>,
    fence: Option<&FenceBoundary>,
) -> bool {
    fence.is_some()
        && matches!(
            family,
            Some(
                DeclarationFamily::Struct
                    | DeclarationFamily::Mod
                    | DeclarationFamily::Use
                    | DeclarationFamily::Type
            )
        )
}

fn selected_declaration_family(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<DeclarationFamily> {
    if struct_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
        Some(DeclarationFamily::Struct)
    } else if mod_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
        Some(DeclarationFamily::Mod)
    } else if use_declaration_selected_normalized(i.rb(), item, item_origin, fence) {
        Some(DeclarationFamily::Use)
    } else if type_declaration_selected_normalized(i.rb(), item, baseline, item_origin, fence) {
        Some(DeclarationFamily::Type)
    } else if for_statement_selected(item) {
        Some(DeclarationFamily::For)
    } else if is_binding_visibility(item)
        && binding_statement_selected_normalized(i, item, baseline, item_origin, fence)
    {
        Some(DeclarationFamily::Binding)
    } else {
        None
    }
}

#[derive(Clone, Copy)]
enum StatementSequencePolicy {
    Indented { block_indent: usize },
    Braced,
}

/// The canonical indented sequence owns its opening trivia and equal-indent
/// separators; dedent and unimplemented statement starts remain pending Items.
pub(super) fn indented_statement_block(i: RewriteIn, base_indent: usize, stops: Stops) -> TailExit {
    ordinary_exit(indented_statement_block_normalized(
        i,
        base_indent,
        stops,
        0,
        LineEntry::InLine,
        None,
    ))
}

pub(super) fn indented_statement_block_normalized(
    mut i: RewriteIn,
    base_indent: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, base_indent, stops);
    i.state
        .start_node(SyntaxKind::IndentedStatementBlock.into());
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let block_indent = indentation_after_newline(item.leading_view())
        .filter(|&indentation| indentation > base_indent)
        .expect("C2 admission proved a strictly indented block opening");

    let deferred_child = declaration_family_is_deferred(
        selected_declaration_family(i.rb(), &item, block_indent, item_origin, fence),
        fence,
    );

    if !deferred_child {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let exit = statement_sequence_normalized(
        i.rb(),
        item,
        StatementSequencePolicy::Indented { block_indent },
        block_indent,
        stops,
        item_origin,
        line_entry,
        fence,
        true,
    );
    i.state.finish_node();
    exit
}

/// The braced-primary wrapper owns its delimiters and local separator stops;
/// the closed sequence helper owns normal statement progression for both
/// current block forms.
#[allow(clippy::too_many_arguments)]
pub(super) fn braced_nud_normalized(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    incoming_baseline: usize,
    outer_stops: Stops,
    outer_ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = braced_statement_block_normalized(
        i.rb(),
        open,
        incoming_baseline,
        item_origin,
        line_entry,
        fence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    continue_normalized_tail(
        i,
        threshold,
        incoming_baseline,
        outer_stops,
        outer_ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
    )
}

/// Construct the existing braced canonical-statement owner without attaching
/// an expression tail. Declaration bodies reuse this exact delimiter scope.
pub(super) fn braced_statement_block(
    i: RewriteIn,
    open: Item,
    incoming_baseline: usize,
) -> TailExit {
    ordinary_exit(braced_statement_block_normalized(
        i,
        open,
        incoming_baseline,
        0,
        LineEntry::InLine,
        None,
    ))
}

pub(super) fn braced_statement_block_normalized(
    mut i: RewriteIn,
    open: Item,
    incoming_baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::BracedStatementBlockExpression.into());
    emit_token_item(&mut i, open);
    let stops = stops_for(TokenKind::RBrace);
    let (mut item, item_origin, line_entry) = statement_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        incoming_baseline,
        stops,
    );
    if item.payload_view().is_boundary() {
        let exit = braced_terminal_normalized(i.rb(), item, line_entry);
        i.state.finish_node();
        return exit;
    }
    let baseline = delimited_baseline(incoming_baseline, item.leading_view());
    let deferred_child = declaration_family_is_deferred(
        selected_declaration_family(i.rb(), &item, baseline, item_origin, fence),
        fence,
    );
    if !item.payload_view().is_boundary() && !deferred_child {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    let exit = statement_sequence_normalized(
        i.rb(),
        item,
        StatementSequencePolicy::Braced,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        true,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn statement_sequence_normalized(
    mut i: RewriteIn,
    mut item: Item,
    policy: StatementSequencePolicy,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    mut first: bool,
) -> NormalizedExit {
    loop {
        match policy {
            StatementSequencePolicy::Indented { block_indent } => {
                let entry = suffix_marker(i.rb());
                let exit = indented_statement_slot_normalized(
                    i.rb(),
                    item,
                    baseline,
                    block_indent,
                    stops,
                    true,
                    item_origin,
                    line_entry,
                    fence,
                    first,
                );
                item_origin = advanced_origin(item_origin, entry, i.rb());
                (item, line_entry) = match indented_statement_successor_normalized(
                    i.rb(),
                    exit,
                    block_indent,
                    stops,
                ) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
            }
            StatementSequencePolicy::Braced => {
                if item.payload_view().is_boundary()
                    || item.payload_view().is_eof()
                    || token_kind(&item) == Some(TokenKind::RBrace)
                {
                    if !first
                        && !item.payload_view().is_boundary()
                        && implicit_delimited_newline(baseline, item.leading_view())
                    {
                        emit_separator_leading(&mut i, &mut item);
                    }
                    return braced_terminal_normalized(i, item, line_entry);
                }
                let entry = suffix_marker(i.rb());
                let exit = braced_statement_slot_normalized(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                    first,
                );
                item_origin = advanced_origin(item_origin, entry, i.rb());
                (item, line_entry, item_origin) = match braced_statement_successor_normalized(
                    i.rb(),
                    exit,
                    baseline,
                    stops,
                    item_origin,
                    fence,
                ) {
                    Ok(next) => next,
                    Err(exit) => return exit,
                };
            }
        }
        first = false;
    }
}

fn indented_statement_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    block_indent: usize,
    stops: Stops,
) -> Result<(Item, LineEntry), NormalizedExit> {
    let NormalizedExit::Complete(Err(Either::Left(item)), line_entry) = exit else {
        return Err(exit);
    };
    if indentation_after_newline(item.leading_view()) != Some(block_indent)
        || indented_statement_outer_boundary(i.rb(), &item, block_indent, stops)
    {
        return Err(complete(handoff(item), line_entry));
    }
    Ok((item, line_entry))
}

#[allow(clippy::too_many_arguments)]
fn indented_statement_slot_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    missing_on_boundary: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    first: bool,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        if missing_on_boundary {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return complete(handoff(item), line_entry);
    }
    if indented_statement_slot_boundary(i.rb(), &item, block_indent, stops) {
        if missing_on_boundary {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
        }
        return complete(handoff(item), line_entry);
    }
    if is_canonical_statement_nud_normalized(i.rb(), &item, baseline, item_origin, fence) {
        let deferred_child = declaration_family_is_deferred(
            selected_declaration_family(i.rb(), &item, baseline, item_origin, fence),
            fence,
        );
        if !first && !deferred_child {
            emit_separator_leading(&mut i, &mut item);
        }
        return canonical_statement_normalized(
            i,
            item,
            baseline,
            stops,
            StatementLineHandoff::OrdinaryLayout,
            item_origin,
            line_entry,
            fence,
        );
    }

    if !first {
        emit_separator_leading(&mut i, &mut item);
    }

    let (next, next_origin, next_line_entry) = retry_indented_statement_normalized(
        i.rb(),
        item,
        baseline,
        block_indent,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    item = next;
    if indented_statement_retry_boundary(i.rb(), &item, block_indent, stops) {
        return complete(handoff(item), next_line_entry);
    }
    debug_assert!(is_canonical_statement_nud_normalized(
        i.rb(),
        &item,
        baseline,
        next_origin,
        fence
    ));
    canonical_statement_normalized(
        i,
        item,
        baseline,
        stops,
        StatementLineHandoff::OrdinaryLayout,
        next_origin,
        next_line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_indented_statement_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    block_indent: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        if indented_statement_retry_boundary(i.rb(), &item, block_indent, stops)
            || is_canonical_statement_nud_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn indented_statement_slot_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

fn indented_statement_retry_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    indented_statement_slot_boundary(i.rb(), item, block_indent, stops)
        || indentation_after_newline(item.leading_view()) == Some(block_indent)
}

fn indented_statement_outer_boundary(
    mut i: RewriteIn,
    item: &Item,
    block_indent: usize,
    stops: Stops,
) -> bool {
    is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation < block_indent)
}

fn braced_terminal_normalized(
    mut i: RewriteIn,
    item: Item,
    line_entry: LineEntry,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(missing_brace_close(i, item), line_entry);
    }
    if token_kind(&item) == Some(TokenKind::RBrace) {
        emit_token_item(&mut i, item);
        return complete(Ok(()), line_entry);
    }
    debug_assert!(item.payload_view().is_eof());
    complete(missing_brace_close(i, item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn braced_statement_slot_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    first: bool,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return braced_terminal_normalized(i, item, line_entry);
    }
    if is_canonical_statement_nud_normalized(i.rb(), &item, baseline, item_origin, fence) {
        let deferred_child = declaration_family_is_deferred(
            selected_declaration_family(i.rb(), &item, baseline, item_origin, fence),
            fence,
        );
        if !first && !deferred_child && implicit_delimited_newline(baseline, item.leading_view()) {
            emit_separator_leading(&mut i, &mut item);
        }
        return canonical_statement_normalized(
            i,
            item,
            baseline,
            stops,
            StatementLineHandoff::BracedStatementSequence,
            item_origin,
            line_entry,
            fence,
        );
    }

    if !first && implicit_delimited_newline(baseline, item.leading_view()) {
        emit_separator_leading(&mut i, &mut item);
    }

    let (item, item_origin, line_entry) = retry_braced_statement_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if braced_statement_boundary(&item, baseline) {
        complete(handoff(item), line_entry)
    } else if is_canonical_statement_nud_normalized(i.rb(), &item, baseline, item_origin, fence) {
        canonical_statement_normalized(
            i,
            item,
            baseline,
            stops,
            StatementLineHandoff::BracedStatementSequence,
            item_origin,
            line_entry,
            fence,
        )
    } else {
        complete(handoff(item), line_entry)
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_braced_statement_normalized(
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
        (item, item_origin, line_entry) =
            statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
        if braced_statement_boundary(&item, baseline)
            || is_canonical_statement_nud_normalized(i.rb(), &item, baseline, item_origin, fence)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn braced_statement_boundary(item: &Item, baseline: usize) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || token_kind(item) == Some(TokenKind::RBrace)
        || implicit_delimited_newline(baseline, item.leading_view())
}

fn braced_statement_successor_normalized(
    mut i: RewriteIn,
    exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Result<(Item, LineEntry, usize), NormalizedExit> {
    match exit {
        NormalizedExit::Deferred(item, line_entry) => {
            Err(NormalizedExit::Deferred(item, line_entry))
        }
        NormalizedExit::Complete(Ok(()), line_entry) => Err(complete(Ok(()), line_entry)),
        NormalizedExit::Complete(Err(Either::Right(mut end)), line_entry) => {
            if implicit_delimited_newline(baseline, end.item.leading_view()) {
                emit_separator_leading(&mut i, &mut end.item);
            }
            Err(complete(missing_brace_close(i, end.item), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if item.payload_view().is_boundary() =>
        {
            Err(complete(missing_brace_close(i, item), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if implicit_delimited_newline(baseline, item.leading_view()) =>
        {
            Ok((item, line_entry, item_origin))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if token_kind(&item) == Some(TokenKind::RBrace) =>
        {
            emit_token_item(&mut i, item);
            Err(complete(Ok(()), line_entry))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) if is_separator(&item) => {
            let (item, item_origin, line_entry) = braced_explicit_separator_normalized(
                i,
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
            Ok((item, line_entry, item_origin))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry)
            if is_canonical_statement_nud_normalized(
                i.rb(),
                &item,
                baseline,
                item_origin,
                fence,
            ) =>
        {
            emit_missing(&mut i, LeadingTrivia::default());
            Ok((item, line_entry, item_origin))
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            Ok((item, line_entry, item_origin))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn braced_explicit_separator_normalized(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state
        .start_node(SyntaxKind::BlockStatementSeparator.into());
    emit_token_item(&mut i, separator);
    let (mut item, item_origin, line_entry) =
        statement_item_normalized(i.rb(), item_origin, line_entry, fence, baseline, stops);
    let deferred_child = !item.payload_view().is_boundary()
        && declaration_family_is_deferred(
            selected_declaration_family(i.rb(), &item, baseline, item_origin, fence),
            fence,
        );
    if !item.payload_view().is_boundary() && !deferred_child {
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

fn missing_brace_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(&mut i, LeadingTrivia::default());
    handoff(item)
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
        .expect("statement payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i);
    (item, item_origin, next_line_entry)
}
