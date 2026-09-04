//! Direct canonical `mod` declaration construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    driver::{
        Either, TailExit, handoff, implicit_delimited_newline, indentation_after_newline,
        is_active_stop, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        introduced_body_indentation, scan_identifier, scan_statement_item, scan_trivia,
        source_identifier, statement_item_after_trivia,
    },
    operator::source_after_trivia,
    statement::{
        braced_statement_block, canonical_statement, indented_statement_block,
        is_canonical_statement_nud,
    },
};

type SlotResult<T> = Result<Option<T>, Item>;

/// Exact bare `mod` is authoritative immediately. A visibility-led form is
/// selected only when the same Gmod rule exposes an exact maximal `mod` word.
pub(super) fn mod_declaration_selected(i: RewriteIn, item: &Item, baseline: usize) -> bool {
    if item_word(item) == Some("mod") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    i.map(
        |lex: LexIn| Some(prefixed_mod_candidate(lex.remainder(), baseline)),
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(super) fn mod_declaration(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    debug_assert!(mod_declaration_selected(i.rb(), &intro, baseline));
    i.state.start_node(SyntaxKind::ModDeclaration.into());

    if item_word(&intro) == Some("mod") {
        emit_intro(&mut i, intro, SyntaxKind::ModKw);
    } else {
        emit_visibility(&mut i, intro);
        let accepted = emit_gmod(i.rb(), baseline);
        debug_assert!(accepted, "visibility-led selection proved Gmod");
        let keyword = i
            .token(|lex| scan_exact_identifier(lex, "mod"))
            .expect("visibility-led selection proved exact `mod`");
        i.state.token(SyntaxKind::ModKw.into(), &keyword.text);
    }

    let exit = if !emit_gmod(i.rb(), baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        handoff(scan_pending_item(i.rb(), baseline, stops))
    } else {
        match parse_identity(i.rb(), baseline, stops) {
            Ok(()) => {
                if !emit_gmod(i.rb(), baseline) {
                    emit_missing(&mut i, LeadingTrivia::default());
                    handoff(scan_pending_item(i.rb(), baseline, stops))
                } else {
                    parse_body(i.rb(), baseline, stops)
                }
            }
            Err(boundary) => handoff(boundary),
        }
    };

    i.state.finish_node();
    exit
}

fn parse_identity(mut i: RewriteIn, baseline: usize, stops: Stops) -> Result<(), Item> {
    let Some(first) = required_name(i.rb(), baseline, stops)? else {
        return Ok(());
    };
    if &*first.text != "test" {
        i.state.token(SyntaxKind::Identifier.into(), &first.text);
        return Ok(());
    }

    i.state.start_node(SyntaxKind::TestModuleMarker.into());
    i.state.token(SyntaxKind::Identifier.into(), &first.text);
    i.state.finish_node();
    if anonymous_test_follower(i.rb(), baseline) {
        return Ok(());
    }
    if !emit_gmod(i.rb(), baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(scan_pending_item(i, baseline, stops));
    }
    if let Some(name) = required_name(i.rb(), baseline, stops)? {
        i.state.token(SyntaxKind::Identifier.into(), &name.text);
    }
    Ok(())
}

/// A missing/error name slot either returns a recovered raw name or leaves a
/// local body starter pending. Caller boundaries retain their exact Item.
fn required_name(mut i: RewriteIn, baseline: usize, stops: Stops) -> SlotResult<Token> {
    if observes(i.rb(), body_starter) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(None);
    }
    if let Some(boundary) = take_boundary(i.rb(), baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(boundary);
    }
    if let Some(name) = i.token(scan_identifier) {
        return Ok(Some(name));
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let item = statement_item_after_trivia(i.rb(), LeadingTrivia::default(), baseline, stops);
        emit_token_item(&mut i, item);

        if continuation_has_body_starter(i.rb(), baseline) {
            let trivia = scan_trivia(i.rb());
            emit_leading_trivia(&mut i, &trivia);
            i.state.finish_node();
            return Ok(None);
        }
        if let Some(boundary) = take_boundary(i.rb(), baseline, stops) {
            i.state.finish_node();
            return Err(boundary);
        }
        if continuation_has_raw_name(i.rb(), baseline) {
            let trivia = scan_trivia(i.rb());
            emit_leading_trivia(&mut i, &trivia);
            i.state.finish_node();
            return Ok(Some(
                i.token(scan_identifier)
                    .expect("the name continuation probe was exact"),
            ));
        }

        let trivia = scan_trivia(i.rb());
        emit_leading_trivia(&mut i, &trivia);
    }
}

fn parse_body(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let item = statement_item_after_trivia(i.rb(), LeadingTrivia::default(), baseline, stops);
    parse_body_item(i, item, baseline, stops)
}

fn parse_body_item(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> TailExit {
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            scan_after_completed(i, baseline, stops)
        }
        Some(TokenKind::LBrace) => {
            let exit = braced_statement_block(i.rb(), item, baseline);
            match exit {
                Ok(()) => scan_after_completed(i, baseline, stops),
                Err(_) => exit,
            }
        }
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            parse_colon_body(i, baseline, stops)
        }
        _ if mod_boundary(i.rb(), &item, baseline, stops) => {
            emit_missing(&mut i, LeadingTrivia::default());
            handoff(item)
        }
        _ if is_canonical_statement_nud(i.rb(), &item, baseline) => {
            emit_missing(&mut i, LeadingTrivia::default());
            parse_inline_statement(i, item, baseline, stops)
        }
        _ => recover_body_introducer(i, item, baseline, stops),
    }
}

fn recover_body_introducer(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if implicit_delimited_newline(baseline, &item.leading) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_body_starter_item(&item) {
            i.state.finish_node();
            return parse_body_item(i, item, baseline, stops);
        }
        if mod_boundary(i.rb(), &item, baseline, stops) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_canonical_statement_nud(i.rb(), &item, baseline) {
            i.state.finish_node();
            return parse_inline_statement(i, item, baseline, stops);
        }
    }
}

fn parse_colon_body(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    match introduced_body_indentation(i.rb()) {
        Some(indentation) if indentation > baseline => indented_statement_block(i, baseline, stops),
        Some(_) => {
            emit_missing(&mut i, LeadingTrivia::default());
            handoff(scan_pending_item(i, baseline, stops))
        }
        None => {
            let leading = scan_trivia(i.rb());
            let item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
            parse_inline_body_item(i, item, baseline, stops)
        }
    }
}

fn parse_inline_body_item(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> TailExit {
    if inline_terminal_semicolon(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
        emit_token_item(&mut i, item);
        return scan_after_completed(i, baseline, stops);
    }
    if mod_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    if is_canonical_statement_nud(i.rb(), &item, baseline) {
        return parse_inline_statement(i, item, baseline, stops);
    }

    i.state.start_node(SyntaxKind::Error.into());
    let mut item = item;
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = statement_item_after_trivia(i.rb(), leading, baseline, stops);
        if inline_terminal_semicolon(&item) {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return scan_after_completed(i, baseline, stops);
        }
        if mod_boundary(i.rb(), &item, baseline, stops) {
            i.state.finish_node();
            return handoff(item);
        }
        if is_canonical_statement_nud(i.rb(), &item, baseline) {
            i.state.finish_node();
            return parse_inline_statement(i, item, baseline, stops);
        }
    }
}

fn parse_inline_statement(mut i: RewriteIn, item: Item, baseline: usize, stops: Stops) -> TailExit {
    let exit = canonical_statement(i.rb(), item, baseline, stops);
    match exit {
        Ok(()) => scan_after_completed(i, baseline, stops),
        Err(Either::Left(item)) if inline_terminal_semicolon(&item) => {
            emit_token_item(&mut i, item);
            scan_after_completed(i, baseline, stops)
        }
        Err(_) => exit,
    }
}

fn scan_after_completed(mut i: RewriteIn, baseline: usize, stops: Stops) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = statement_item_after_trivia(i, leading, baseline, stops);
    handoff(item)
}

fn scan_pending_item(mut i: RewriteIn, baseline: usize, stops: Stops) -> Item {
    let leading = scan_trivia(i.rb());
    statement_item_after_trivia(i, leading, baseline, stops)
}

fn take_boundary(mut i: RewriteIn, baseline: usize, stops: Stops) -> Option<Item> {
    i.token(|mut lex| {
        let item = scan_statement_item(lex.rb(), baseline, stops)?;
        mod_boundary_lex(lex, &item, baseline, stops).then_some(item)
    })
}

fn mod_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || implicit_delimited_newline(baseline, &item.leading)
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn mod_boundary_lex(mut i: LexIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || implicit_delimited_newline(baseline, &item.leading)
        || super::driver::is_active_stop_lex(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn emit_gmod(mut i: RewriteIn, baseline: usize) -> bool {
    if !gmod_allowed(i.rb(), baseline) {
        return false;
    }
    let trivia = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &trivia);
    true
}

fn gmod_allowed(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        source_after_trivia(source)
            .2
            .is_none_or(|indentation| indentation > baseline)
    })
}

fn anonymous_test_follower(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        let (after, _, indentation) = source_after_trivia(source);
        indentation.is_none_or(|indentation| indentation > baseline) && body_starter(after)
    })
}

fn continuation_has_raw_name(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        let (after, _, indentation) = source_after_trivia(source);
        indentation.is_none_or(|indentation| indentation > baseline)
            && source_identifier(after).is_some()
    })
}

fn continuation_has_body_starter(i: RewriteIn, baseline: usize) -> bool {
    observes(i, |source| {
        let (after, _, indentation) = source_after_trivia(source);
        indentation.is_none_or(|indentation| indentation > baseline) && body_starter(after)
    })
}

fn prefixed_mod_candidate(source: &str, baseline: usize) -> bool {
    let (source, _, indentation) = source_after_trivia(source);
    indentation.is_none_or(|indentation| indentation > baseline)
        && source_identifier(source).is_some_and(|(word, _)| word == "mod")
}

fn body_starter(source: &str) -> bool {
    source.starts_with(';')
        || source.starts_with('{')
        || source.starts_with(':') && !source.starts_with("::")
}

fn is_body_starter_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon)
    )
}

fn inline_terminal_semicolon(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Semicolon)
        && indentation_after_newline(&item.leading).is_none()
}

fn scan_exact_identifier(mut i: LexIn, expected: &str) -> Option<Token> {
    let token = scan_identifier(i.rb())?;
    (&*token.text == expected).then_some(token)
}

fn item_word(item: &Item) -> Option<&str> {
    match &item.payload {
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text,
        }) => Some(text),
        Payload::Token(_) | Payload::Operator(_) | Payload::Eof => None,
    }
}

fn emit_intro(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let Payload::Token(token) = item.payload else {
        unreachable!("an accepted Mod intro is a token")
    };
    emit_leading_trivia(i, &item.leading);
    i.state.token(kind.into(), &token.text);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("an accepted Mod visibility is a token")
    };
    emit_leading_trivia(i, &item.leading);
    let kind = match &*token.text {
        "my" => SyntaxKind::MyKw,
        "our" => SyntaxKind::OurKw,
        "pub" => SyntaxKind::PubKw,
        _ => unreachable!("Mod visibility was selected from exact words"),
    };
    i.state.token(kind.into(), &token.text);
}

fn observes<F>(i: RewriteIn, predicate: F) -> bool
where
    F: FnOnce(&str) -> bool,
{
    i.map(
        |lex: LexIn| Some(predicate(lex.remainder())),
        |observed| observed,
    )
    .expect("a source observation is total")
}
