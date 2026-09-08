//! Direct canonical BindingStatement construction.

use super::ambient_claim::AmbientClaimContext;
use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{CurrentItem, LineEntry, current_item},
    driver::{
        Either, MlMode, NormalizedExit, advanced_origin, complete, expr_from_nud_normalized,
        expression_item, handoff, implicit_delimited_newline, is_active_stop, is_line_stop,
        is_nud_item, is_separator, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, is_exact_equals_source, scan_pattern_nud_payload,
        scan_statement_payload, source_declaration_head, source_identifier,
    },
    operator::{TriviaObservation, observe_fenced_trivia},
    pattern::{PATTERN_STOP_EQUALS, pattern_from_entry_item_normalized, pattern_stops_from_owner},
    statement::{StatementLineHandoff, indented_statement_block_normalized},
    yumark::FenceBoundary,
};

pub(super) fn binding_statement_selected_normalized(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(binding_statement_selected_lexical(
                lex.remainder(),
                item,
                baseline,
                item_origin,
                fence,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(super) fn binding_statement_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let Some(visibility) = visibility_word(item) else {
        return false;
    };
    if super::use_decl::use_declaration_selected_lexical(source, item, item_origin, fence) {
        return false;
    }
    if super::mod_decl::mod_declaration_selected_lexical(source, item, baseline, item_origin, fence)
    {
        return false;
    }
    if super::struct_decl::struct_declaration_selected_lexical(
        source,
        item,
        baseline,
        item_origin,
        fence,
    ) {
        return false;
    }
    if super::type_decl::type_declaration_selected_lexical(
        source,
        item,
        baseline,
        item_origin,
        fence,
    ) {
        return false;
    }
    binding_follower_normalized(source, visibility, baseline, item_origin, fence)
}

fn binding_follower_normalized(
    source: &str,
    visibility: &str,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(first) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return true;
    };
    if !first.present
        || first
            .indentation
            .is_some_and(|indentation| indentation <= baseline)
    {
        return true;
    }
    let Some((head, after_head)) = source_identifier(first.source) else {
        return true;
    };

    match head {
        "use" => true,
        "type" | "role" | "impl" | "cast" => false,
        "enum" | "error" | "act" => {
            visibility == "my"
                && !named_declaration_head_candidate_normalized(
                    source,
                    after_head,
                    baseline,
                    item_origin,
                    fence,
                )
        }
        "lazy" | "prefix" | "infix" | "suffix" | "nullfix" => {
            binding_definition_follows_normalized(source, after_head, baseline, item_origin, fence)
        }
        _ => true,
    }
}

fn observed_after_head<'a>(
    full_source: &'a str,
    after_head: &'a str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> TriviaObservation<'a> {
    let consumed = full_source.len() - after_head.len();
    let origin = item_origin
        .checked_add(consumed)
        .expect("a declaration admission coordinate must fit usize");
    observe_fenced_trivia(after_head, origin, LineEntry::InLine, fence)
}

fn named_declaration_head_candidate_normalized(
    full_source: &str,
    after_head: &str,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observed_after_head(full_source, after_head, item_origin, fence)
    else {
        return false;
    };
    if !observed.present
        || observed
            .indentation
            .is_some_and(|indentation| indentation <= baseline)
    {
        return false;
    }
    source_declaration_head(observed.source)
}

fn binding_definition_follows_normalized(
    full_source: &str,
    after_head: &str,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observed_after_head(full_source, after_head, item_origin, fence)
    else {
        return false;
    };
    observed.present
        && observed
            .indentation
            .is_none_or(|indentation| indentation > baseline)
        && is_exact_equals_source(observed.source)
}

pub(super) fn is_binding_visibility(item: &Item) -> bool {
    visibility_word(item).is_some()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn binding_statement_normalized(
    mut i: RewriteIn,
    visibility: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::BindingStatement.into());
    i.state.start_node(SyntaxKind::BindingHeader.into());
    emit_visibility(&mut i, visibility);

    let entry = suffix_marker(i.rb());
    let exit = binding_target_normalized(
        i.rb(),
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    let mut item = match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), next_line_entry) => {
            line_entry = next_line_entry;
            item
        }
        exit => {
            i.state.finish_node();
            i.state.finish_node();
            return exit;
        }
    };
    if item.payload_view().is_boundary() {
        i.state.finish_node();
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    if token_kind(&item) != Some(TokenKind::Equals)
        || implicit_delimited_newline(baseline, item.leading_view())
    {
        i.state.finish_node();
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    emit_token_item(&mut i, item);
    i.state.finish_node();

    i.state.start_node(SyntaxKind::BindingBody.into());
    let exit = binding_body_normalized(
        i.rb(),
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn binding_target_normalized(
    mut i: RewriteIn,
    baseline: usize,
    owner_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let stops = pattern_stops_from_owner(owner_stops)
        | super::pattern::PATTERN_STOP_COMMA
        | super::pattern::PATTERN_STOP_SEMICOLON
        | PATTERN_STOP_EQUALS;
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        mut item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_pattern_nud_payload(lex, leading, origin, fence, stops)
                },
            )
        })
        .expect("binding Pattern payload scanning is total");
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    if item.payload_view().is_boundary()
        || item
            .leading_view()
            .indentation_after_newline()
            .is_some_and(|indentation| indentation <= baseline)
    {
        i.state.start_node(SyntaxKind::Pattern.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), next_line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    pattern_from_entry_item_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        next_line_entry,
        fence,
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
fn binding_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    match introduced_body_indentation_normalized(i.rb(), item_origin, fence) {
        Some(indentation) if indentation > baseline => indented_statement_block_normalized(
            i,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
        Some(_) => {
            emit_missing(&mut i, LeadingTrivia::default());
            let (item, _, line_entry) = binding_statement_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
            );
            complete(handoff(item), line_entry)
        }
        None => inline_binding_body_normalized(
            i,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn inline_binding_body_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let (mut item, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if binding_body_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
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
        );
    }

    let (mut item, item_origin, line_entry) = retry_inline_binding_body_normalized(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if binding_body_boundary(i.rb(), &item, baseline, stops) {
        if !item.payload_view().is_boundary()
            && !implicit_delimited_newline(baseline, item.leading_view())
        {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
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
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_inline_binding_body_normalized(
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
        if binding_body_boundary(i.rb(), &item, baseline, stops) || is_nud_item(&item) {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

fn binding_body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

#[allow(clippy::too_many_arguments)]
fn binding_statement_item_normalized(
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
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn visibility_word(item: &Item) -> Option<&str> {
    let payload = item.payload_view();
    assert!(
        !payload.is_boundary(),
        "a boundary is not a visibility word"
    );
    match (payload.token_kind(), payload.spelling()) {
        (Some(TokenKind::Identifier), Some(text)) if matches!(text, "my" | "our" | "pub") => {
            Some(text)
        }
        _ => None,
    }
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("the binding judge accepted only visibility words"),
    };
    item.emit_remaining(&mut *i.state, kind);
}
