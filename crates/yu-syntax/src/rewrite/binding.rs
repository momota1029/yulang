//! Direct canonical BindingStatement construction.

use reborrow_generic::Reborrow as _;

use crate::{scan::operator::OperatorSite, syntax_kind::SyntaxKind};

use super::{
    LexIn, RewriteIn, Stops,
    driver::{
        Either, MlMode, TailExit, expr_from_nud, handoff, implicit_delimited_newline,
        is_active_stop, is_line_stop, is_nud_item, is_separator, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        introduced_body_indentation, is_exact_equals_source, pattern_nud_item_after_trivia,
        scan_trivia, source_identifier, statement_item_after_trivia, tail_item_after_trivia,
    },
    operator::source_after_trivia,
    pattern::{PATTERN_STOP_EQUALS, pattern_from_entry_item, pattern_stops_from_owner},
    statement::indented_statement_block,
};

pub(super) fn binding_statement_selected(i: RewriteIn, item: &Item, baseline: usize) -> bool {
    let Some(visibility) = visibility_word(item) else {
        return false;
    };
    i.map(
        |i: LexIn| Some(binding_follower(i, visibility, baseline)),
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(super) fn is_binding_visibility(item: &Item) -> bool {
    visibility_word(item).is_some()
}

pub(super) fn binding_statement(
    mut i: RewriteIn,
    visibility: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    debug_assert!(binding_statement_selected(i.rb(), &visibility, baseline));
    i.state.start_node(SyntaxKind::BindingStatement.into());
    i.state.start_node(SyntaxKind::BindingHeader.into());
    emit_visibility(&mut i, visibility);

    let exit = binding_target(i.rb(), baseline, stops);
    let Err(Either::Left(mut item)) = exit else {
        i.state.finish_node();
        i.state.finish_node();
        return exit;
    };
    if token_kind(&item) != Some(TokenKind::Equals)
        || implicit_delimited_newline(baseline, &item.leading)
    {
        i.state.finish_node();
        i.state.finish_node();
        return handoff(item);
    }

    emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    emit_token_item(&mut i, item);
    i.state.finish_node();

    i.state.start_node(SyntaxKind::BindingBody.into());
    let exit = binding_body(i.rb(), baseline, stops);
    i.state.finish_node();
    i.state.finish_node();
    exit
}

fn binding_target(mut i: RewriteIn, baseline: usize, owner_stops: Stops) -> TailExit {
    let indentation = introduced_body_indentation(i.rb());
    let mut leading = scan_trivia(i.rb());
    let stops = pattern_stops_from_owner(owner_stops)
        | super::pattern::PATTERN_STOP_COMMA
        | super::pattern::PATTERN_STOP_SEMICOLON
        | PATTERN_STOP_EQUALS;
    if indentation.is_some_and(|indentation| indentation <= baseline) {
        let item = pattern_nud_item_after_trivia(i.rb(), leading, stops);
        i.state.start_node(SyntaxKind::Pattern.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return handoff(item);
    }
    emit_leading_trivia(&mut i, &leading);
    leading = LeadingTrivia::default();
    let item = pattern_nud_item_after_trivia(i.rb(), leading, stops);
    pattern_from_entry_item(i, item, baseline, stops)
}

fn binding_body(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    match introduced_body_indentation(i.rb()) {
        Some(indentation) if indentation > baseline => indented_statement_block(i, baseline, stops),
        Some(_) => {
            emit_missing(&mut i, LeadingTrivia::default());
            let leading = scan_trivia(i.rb());
            let item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
            handoff(item)
        }
        None => inline_binding_body(i, baseline, stops),
    }
}

fn inline_binding_body(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    if binding_body_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    if is_nud_item(&item) {
        return expr_from_nud(i, item, None, baseline, stops, MlMode::All);
    }

    item = retry_inline_binding_body(i.rb(), item, baseline, stops);
    if binding_body_boundary(i.rb(), &item, baseline, stops) {
        if !implicit_delimited_newline(baseline, &item.leading) {
            emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
        }
        return handoff(item);
    }
    emit_leading_trivia(&mut i, &std::mem::take(&mut item.leading));
    debug_assert!(is_nud_item(&item));
    expr_from_nud(i, item, None, baseline, stops, MlMode::All)
}

fn retry_inline_binding_body(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
) -> Item {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
        if binding_body_boundary(i.rb(), &item, baseline, stops) || is_nud_item(&item) {
            i.state.finish_node();
            return item;
        }
    }
}

fn binding_body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || is_separator(item)
        || is_active_stop(i.rb(), item, stops)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, &item.leading)
}

fn binding_follower(i: LexIn, visibility: &str, baseline: usize) -> bool {
    let (source, gap, indentation) = source_after_trivia(i.remainder());
    if !gap || indentation.is_some_and(|indentation| indentation <= baseline) {
        return true;
    }
    let Some((head, after_head)) = source_identifier(source) else {
        return true;
    };

    match head {
        "use" => !use_tree_candidate(after_head),
        "mod" | "struct" | "type" | "role" | "impl" | "cast" => false,
        "enum" | "error" | "act" => {
            visibility == "my" && !named_declaration_head_candidate(after_head, baseline)
        }
        "lazy" | "prefix" | "infix" | "suffix" | "nullfix" => {
            binding_definition_follows(after_head, baseline)
        }
        _ => true,
    }
}

fn use_tree_candidate(source: &str) -> bool {
    let (source, gap, indentation) = source_after_trivia(source);
    gap && indentation.is_none() && use_tree_atom(source)
}

fn use_tree_atom(source: &str) -> bool {
    matches!(source.chars().next(), Some('{' | '(')) || source_identifier(source).is_some()
}

fn named_declaration_head_candidate(source: &str, baseline: usize) -> bool {
    let (source, gap, indentation) = source_after_trivia(source);
    if !gap || indentation.is_some_and(|indentation| indentation <= baseline) {
        return false;
    }
    if source_identifier(source).is_some() {
        return true;
    }
    matches!(source.chars().next(), Some('$' | '&' | '\''))
        && source
            .chars()
            .next()
            .and_then(|sigil| source.get(sigil.len_utf8()..))
            .is_some_and(|source| source_identifier(source).is_some())
}

fn binding_definition_follows(source: &str, baseline: usize) -> bool {
    let (source, gap, indentation) = source_after_trivia(source);
    gap && indentation.is_none_or(|indentation| indentation > baseline)
        && is_exact_equals_source(source)
}

fn visibility_word(item: &Item) -> Option<&str> {
    match &item.payload {
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) if matches!(&**text, "my" | "our" | "pub") => Some(text),
        Payload::Token(_) | Payload::Operator(_) | Payload::Eof => None,
    }
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let Payload::Token(Token {
        kind: TokenKind::Identifier,
        text,
    }) = item.payload
    else {
        unreachable!("the Statement head scanner accepted a visibility word")
    };
    emit_leading_trivia(i, &item.leading);
    let kind = match &*text {
        "my" => SyntaxKind::MyKw,
        "our" => SyntaxKind::OurKw,
        "pub" => SyntaxKind::PubKw,
        _ => unreachable!("the binding judge accepted only visibility words"),
    };
    i.state.token(kind.into(), &text);
}
