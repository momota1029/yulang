//! Direct, source-free `use` declaration and recursive use-tree construction.

use reborrow_generic::Reborrow as _;
use unicode_ident::is_xid_continue;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    driver::{TailExit, handoff, indentation_after_newline, is_active_stop_lex, token_kind},
    emit::{emit_leading_trivia, emit_missing},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        scan_identifier, scan_statement_item, scan_trivia, source_identifier,
        statement_item_after_trivia,
    },
    operator::source_after_trivia,
};

#[derive(Clone, Copy, Eq, PartialEq)]
enum Terminal {
    Single,
    Group,
    Glob,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Separator {
    ColonColon,
    Slash,
}

struct Lexeme {
    text: Box<str>,
}

struct KeywordPrefix {
    leading: LeadingTrivia,
    keyword: Token,
}

type UseResult<T = ()> = Result<T, Item>;

/// Statement-only, source-backed declaration selection. Bare `use` is
/// authoritative immediately; visibility-prefixed `use` stays contextual
/// until its first use-tree starter is visible.
pub(super) fn use_declaration_selected(i: RewriteIn, item: &Item, _baseline: usize) -> bool {
    if item_word(item) == Some("use") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    i.map(
        |lex: LexIn| Some(prefixed_use_candidate(lex.remainder())),
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(super) fn use_declaration(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
) -> TailExit {
    debug_assert!(use_declaration_selected(i.rb(), &intro, baseline));
    i.state.start_node(SyntaxKind::UseDeclaration.into());

    if item_word(&intro) == Some("use") {
        emit_intro_keyword(&mut i, intro, SyntaxKind::UseKw);
    } else {
        emit_visibility(&mut i, intro);
        let gap = i
            .token(scan_required_inline_trivia)
            .expect("prefixed use selection proved inline trivia");
        emit_leading_trivia(&mut i, &gap);
        let keyword = i
            .token(|lex| scan_exact_word(lex, "use"))
            .expect("prefixed use selection proved exact `use`");
        i.state.token(SyntaxKind::UseKw.into(), &keyword.text);
    }

    let after_use = i.token(scan_required_inline_trivia);
    if let Some(trivia) = &after_use {
        emit_leading_trivia(&mut i, trivia);
    } else if observes(i.rb(), use_tree_starter) {
        emit_missing(&mut i, LeadingTrivia::default());
    }

    let result = if observes(i.rb(), use_tree_starter) {
        parse_use_tree(i.rb(), baseline, stops, None)
    } else if let Some(boundary) = take_declaration_boundary(i.rb(), baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        Err(boundary)
    } else {
        match recover_until(i.rb(), use_tree_starter, |_| false, baseline, stops, true) {
            Ok(true) => parse_use_tree(i.rb(), baseline, stops, None),
            Ok(false) => Ok(()),
            Err(boundary) => Err(boundary),
        }
    };

    i.state.finish_node();
    if let Err(boundary) = result {
        return handoff(boundary);
    }
    let leading = scan_trivia(i.rb());
    let item = statement_item_after_trivia(i, leading, baseline, stops);
    handoff(item)
}

fn parse_use_tree(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult {
    debug_assert!(observes(i.rb(), use_tree_starter));
    i.state.start_node(SyntaxKind::UseTree.into());
    let result = (|| -> UseResult {
        let terminal = if observes(i.rb(), |source| source.starts_with('{')) {
            let open = i
                .token(|lex| scan_character(lex, '{'))
                .expect("use-tree starter was an opening brace");
            parse_group(
                i.rb(),
                open,
                '}',
                SyntaxKind::UseGroup,
                baseline,
                stops,
                outer_close,
            )?;
            Terminal::Group
        } else if observes(i.rb(), |source| source.starts_with('(')) {
            i.state.start_node(SyntaxKind::UsePath.into());
            parse_operator_name(i.rb());
            parse_path_tail(i.rb(), None, baseline, stops, outer_close)?
        } else {
            let first = i
                .token(scan_identifier)
                .expect("use-tree starter was a word");
            if &*first.text == "mod" {
                i.state.token(SyntaxKind::ModKw.into(), &first.text);
                parse_mod_target(i.rb(), baseline, stops, outer_close)?
            } else {
                let pending = i.token(scan_separator);
                match (
                    &*first.text,
                    pending.as_ref().map(|(separator, _)| *separator),
                ) {
                    ("realm", Some(Separator::Slash)) => {
                        i.state.token(SyntaxKind::RealmKw.into(), &first.text);
                        emit_separator(
                            &mut i,
                            pending.expect("realm marker has its slash").1,
                            Separator::Slash,
                        );
                        parse_marker_target(i.rb(), baseline, stops, outer_close)?
                    }
                    ("band", Some(Separator::ColonColon)) => {
                        i.state.token(SyntaxKind::BandKw.into(), &first.text);
                        emit_separator(
                            &mut i,
                            pending.expect("band marker has its separator").1,
                            Separator::ColonColon,
                        );
                        parse_marker_target(i.rb(), baseline, stops, outer_close)?
                    }
                    _ => {
                        i.state.start_node(SyntaxKind::UsePath.into());
                        i.state.token(SyntaxKind::Identifier.into(), &first.text);
                        parse_path_tail(i.rb(), pending, baseline, stops, outer_close)?
                    }
                }
            }
        };

        if terminal != Terminal::Glob {
            parse_aliases(i.rb(), baseline, stops)?;
        }
        parse_qualifiers(i.rb(), baseline, stops)?;
        Ok(())
    })();
    i.state.finish_node();
    result
}

fn parse_mod_target(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult<Terminal> {
    if let Some(trivia) = i.token(scan_required_inline_trivia) {
        emit_leading_trivia(&mut i, &trivia);
    } else if observes(i.rb(), word_starter) {
        emit_missing(&mut i, LeadingTrivia::default());
    }

    i.state.start_node(SyntaxKind::UsePath.into());
    let first = required_word(i.rb(), baseline, stops);
    if matches!(first, Ok(false)) {
        i.state.finish_node();
        return Ok(Terminal::Single);
    }
    if let Err(boundary) = first {
        i.state.finish_node();
        return Err(boundary);
    }
    parse_path_tail(i, None, baseline, stops, outer_close)
}

fn parse_marker_target(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult<Terminal> {
    if observes(i.rb(), |source| source.starts_with('{')) {
        let open = i
            .token(|lex| scan_character(lex, '{'))
            .expect("marker target was a group");
        parse_group(
            i,
            open,
            '}',
            SyntaxKind::UseGroup,
            baseline,
            stops,
            outer_close,
        )?;
        return Ok(Terminal::Group);
    }
    if observes(i.rb(), |source| source.starts_with('*')) {
        let star = i
            .token(|lex| scan_character(lex, '*'))
            .expect("marker target was a glob");
        parse_glob(i, star, baseline, stops, outer_close)?;
        return Ok(Terminal::Glob);
    }

    i.state.start_node(SyntaxKind::UsePath.into());
    let first = required_path_segment(i.rb(), baseline, stops);
    if matches!(first, Ok(false)) {
        i.state.finish_node();
        return Ok(Terminal::Single);
    }
    if let Err(boundary) = first {
        i.state.finish_node();
        return Err(boundary);
    }
    parse_path_tail(i, None, baseline, stops, outer_close)
}

/// `UsePath` is open on entry. A terminal join closes it before the join is
/// emitted, keeping path separators and terminal joins observably distinct.
fn parse_path_tail(
    mut i: RewriteIn,
    mut pending: Option<(Separator, Lexeme)>,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult<Terminal> {
    loop {
        let Some((separator, text)) = pending.take().or_else(|| i.token(scan_separator)) else {
            i.state.finish_node();
            return Ok(Terminal::Single);
        };
        if observes(i.rb(), |source| source.starts_with('{')) {
            i.state.finish_node();
            emit_separator(&mut i, text, separator);
            let open = i
                .token(|lex| scan_character(lex, '{'))
                .expect("terminal group was visible");
            parse_group(
                i,
                open,
                '}',
                SyntaxKind::UseGroup,
                baseline,
                stops,
                outer_close,
            )?;
            return Ok(Terminal::Group);
        }
        if observes(i.rb(), |source| source.starts_with('*')) {
            i.state.finish_node();
            emit_separator(&mut i, text, separator);
            let star = i
                .token(|lex| scan_character(lex, '*'))
                .expect("terminal glob was visible");
            parse_glob(i, star, baseline, stops, outer_close)?;
            return Ok(Terminal::Glob);
        }

        emit_separator(&mut i, text, separator);
        let segment = required_path_segment(i.rb(), baseline, stops);
        if matches!(segment, Ok(false)) {
            i.state.finish_node();
            return Ok(Terminal::Single);
        }
        if let Err(boundary) = segment {
            i.state.finish_node();
            return Err(boundary);
        }
    }
}

fn required_path_segment(mut i: RewriteIn, baseline: usize, stops: Stops) -> UseResult<bool> {
    if observes(i.rb(), path_segment_starter) {
        parse_path_segment(i);
        return Ok(true);
    }
    if use_local_path_boundary(i.rb()) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(false);
    }
    if let Some(boundary) = take_declaration_boundary(i.rb(), baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(boundary);
    }
    let retry = recover_until(
        i.rb(),
        path_segment_starter,
        path_local_boundary_source,
        baseline,
        stops,
        true,
    )?;
    if retry {
        parse_path_segment(i);
    }
    Ok(retry)
}

fn required_word(mut i: RewriteIn, baseline: usize, stops: Stops) -> UseResult<bool> {
    if observes(i.rb(), word_starter) {
        emit_word(&mut i);
        return Ok(true);
    }
    if observes(i.rb(), reserved_use_atom) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(false);
    }
    if let Some(boundary) = take_declaration_boundary(i.rb(), baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(boundary);
    }
    let retry = recover_until(
        i.rb(),
        word_starter,
        reserved_use_atom,
        baseline,
        stops,
        true,
    )?;
    if retry {
        emit_word(&mut i);
    }
    Ok(retry)
}

fn parse_path_segment(mut i: RewriteIn) {
    if observes(i.rb(), operator_name_starter) {
        parse_operator_name(i);
    } else {
        emit_word(&mut i);
    }
}

fn emit_word(i: &mut RewriteIn) {
    let word = i
        .token(scan_use_identifier)
        .expect("word starter was checked before emission");
    i.state.token(SyntaxKind::Identifier.into(), &word.text);
}

fn parse_operator_name(mut i: RewriteIn) {
    let open = i
        .token(|lex| scan_character(lex, '('))
        .expect("operator-name starter has an opening parenthesis");
    i.state.start_node(SyntaxKind::OperatorName.into());
    i.state.token(SyntaxKind::LParen.into(), &open.text);
    let Some(operator) = i.token(scan_operator_spelling) else {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return;
    };
    i.state.token(SyntaxKind::Operator.into(), &operator.text);
    if let Some(close) = i.token(|lex| scan_character(lex, ')')) {
        i.state.token(SyntaxKind::RParen.into(), &close.text);
    } else {
        emit_missing(&mut i, LeadingTrivia::default());
    }
    i.state.finish_node();
}

fn parse_group(
    mut i: RewriteIn,
    open: Lexeme,
    close: char,
    kind: SyntaxKind,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult {
    i.state.start_node(kind.into());
    i.state.token(open_kind(close).into(), &open.text);

    loop {
        if let Some(boundary) = take_group_caller_boundary(i.rb(), close, baseline, stops) {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return Err(boundary);
        }
        let trivia = scan_trivia(i.rb());
        emit_leading_trivia(&mut i, &trivia);
        if emit_matching_close(i.rb(), close) {
            i.state.finish_node();
            return Ok(());
        }
        if observes(i.rb(), |source| source.starts_with(',')) {
            emit_missing(&mut i, LeadingTrivia::default());
            emit_comma(&mut i);
            continue;
        }
        if observes(i.rb(), |source| mismatched_close(source, close)) {
            if outer_close.is_some_and(|outer| observes(i.rb(), |source| source.starts_with(outer)))
            {
                emit_missing(&mut i, LeadingTrivia::default());
                i.state.finish_node();
                return Ok(());
            }
            emit_mismatched_close(&mut i);
            continue;
        }

        if observes(i.rb(), use_tree_starter) {
            if let Err(boundary) = parse_use_tree(i.rb(), baseline, stops, Some(close)) {
                i.state.finish_node();
                return Err(boundary);
            }
        } else {
            let retry = match recover_until(
                i.rb(),
                use_tree_starter,
                |source| source.starts_with(',') || source.starts_with(close),
                baseline,
                stops,
                false,
            ) {
                Ok(retry) => retry,
                Err(boundary) => {
                    i.state.finish_node();
                    return Err(boundary);
                }
            };
            if retry {
                if let Err(boundary) = parse_use_tree(i.rb(), baseline, stops, Some(close)) {
                    i.state.finish_node();
                    return Err(boundary);
                }
            }
        }

        if let Some(boundary) = take_group_caller_boundary(i.rb(), close, baseline, stops) {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return Err(boundary);
        }
        let trivia = scan_trivia(i.rb());
        let newline = trivia_has_newline(&trivia);
        emit_leading_trivia(&mut i, &trivia);
        if emit_matching_close(i.rb(), close) {
            i.state.finish_node();
            return Ok(());
        }
        if observes(i.rb(), |source| source.starts_with(',')) {
            emit_comma(&mut i);
            continue;
        }
        if newline {
            continue;
        }
        if observes(i.rb(), use_tree_starter) {
            emit_missing(&mut i, LeadingTrivia::default());
            continue;
        }
        if observes(i.rb(), |source| mismatched_close(source, close)) {
            if outer_close.is_some_and(|outer| observes(i.rb(), |source| source.starts_with(outer)))
            {
                emit_missing(&mut i, LeadingTrivia::default());
                i.state.finish_node();
                return Ok(());
            }
            emit_mismatched_close(&mut i);
            continue;
        }

        let retry = match recover_until(
            i.rb(),
            |source| use_tree_starter(source) || source.starts_with(','),
            |source| source.starts_with(close),
            baseline,
            stops,
            false,
        ) {
            Ok(retry) => retry,
            Err(boundary) => {
                i.state.finish_node();
                return Err(boundary);
            }
        };
        if retry && observes(i.rb(), |source| source.starts_with(',')) {
            emit_comma(&mut i);
        }
    }
}

fn parse_glob(
    mut i: RewriteIn,
    star: Lexeme,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult {
    i.state.start_node(SyntaxKind::UseGlob.into());
    let result = (|| -> UseResult {
        i.state.token(SyntaxKind::Star.into(), &star.text);
        parse_aliases(i.rb(), baseline, stops)?;

        if let Some(prefix) = i.token(|lex| scan_keyword_prefix(lex, "without")) {
            emit_leading_trivia(&mut i, &prefix.leading);
            i.state
                .token(SyntaxKind::WithoutKw.into(), &prefix.keyword.text);
            if let Some(trivia) = i.token(scan_required_inline_trivia) {
                emit_leading_trivia(&mut i, &trivia);
            } else if observes(i.rb(), exclusion_starter) {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            required_exclusion(i.rb(), baseline, stops, outer_close)?;

            while observes(i.rb(), |source| source.starts_with(',')) {
                emit_comma(&mut i);
                let trivia = scan_trivia(i.rb());
                emit_leading_trivia(&mut i, &trivia);
                if !required_exclusion(i.rb(), baseline, stops, outer_close)? {
                    break;
                }
            }
        }
        Ok(())
    })();
    i.state.finish_node();
    result
}

fn required_exclusion(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult<bool> {
    if observes(i.rb(), exclusion_starter) {
        parse_exclusion(i, baseline, stops, outer_close)?;
        return Ok(true);
    }
    if observes(i.rb(), reserved_use_atom) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(false);
    }
    if let Some(boundary) = take_declaration_boundary(i.rb(), baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(boundary);
    }
    let retry = recover_until(i.rb(), exclusion_starter, |_| false, baseline, stops, true)?;
    if retry {
        parse_exclusion(i, baseline, stops, outer_close)?;
    }
    Ok(retry)
}

fn parse_exclusion(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
) -> UseResult {
    i.state.start_node(SyntaxKind::UseExclusion.into());
    let result = (|| -> UseResult {
        if observes(i.rb(), operator_name_starter) {
            parse_operator_name(i.rb());
        } else if observes(i.rb(), |source| {
            matches!(source.chars().next(), Some('(' | '{'))
        }) {
            let opening = if observes(i.rb(), |source| source.starts_with('(')) {
                '('
            } else {
                '{'
            };
            let close = if opening == '(' { ')' } else { '}' };
            let open = i
                .token(|lex| scan_character(lex, opening))
                .expect("exclusion group opener was checked");
            parse_group(
                i.rb(),
                open,
                close,
                SyntaxKind::UseExclusionGroup,
                baseline,
                stops,
                outer_close,
            )?;
        } else if observes(i.rb(), |source| source.starts_with('*')) {
            let star = i
                .token(|lex| scan_character(lex, '*'))
                .expect("glob exclusion was checked");
            i.state.token(SyntaxKind::Star.into(), &star.text);
        } else {
            emit_word(&mut i);
        }
        Ok(())
    })();
    i.state.finish_node();
    result
}

fn parse_aliases(mut i: RewriteIn, baseline: usize, stops: Stops) -> UseResult {
    while let Some(prefix) = i.token(|lex| scan_keyword_prefix(lex, "as")) {
        emit_leading_trivia(&mut i, &prefix.leading);
        i.state.start_node(SyntaxKind::UseAlias.into());
        i.state.token(SyntaxKind::AsKw.into(), &prefix.keyword.text);
        if let Some(trivia) = i.token(scan_required_inline_trivia) {
            emit_leading_trivia(&mut i, &trivia);
        } else if observes(i.rb(), word_starter) {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        let name = required_word(i.rb(), baseline, stops);
        i.state.finish_node();
        name?;
    }
    Ok(())
}

fn parse_qualifiers(mut i: RewriteIn, baseline: usize, stops: Stops) -> UseResult {
    let version = i.token(scan_version_prefix);
    let anchor = if version.is_none() {
        i.token(|lex| scan_keyword_prefix(lex, "with"))
    } else {
        None
    };
    if version.is_none() && anchor.is_none() {
        return Ok(());
    }

    i.state.start_node(SyntaxKind::UseQualifiers.into());
    let result = (|| -> UseResult {
        if let Some((leading, version)) = version {
            emit_leading_trivia(&mut i, &leading);
            i.state.start_node(SyntaxKind::UseVersion.into());
            i.state.token(SyntaxKind::Version.into(), &version.text);
            i.state.finish_node();
            if let Some(prefix) = i.token(|lex| scan_keyword_prefix(lex, "with")) {
                parse_anchor(i.rb(), prefix, baseline, stops)?;
            }
        } else {
            parse_anchor(
                i.rb(),
                anchor.expect("anchor-only qualifier was selected"),
                baseline,
                stops,
            )?;
        }
        Ok(())
    })();
    i.state.finish_node();
    result
}

fn parse_anchor(
    mut i: RewriteIn,
    prefix: KeywordPrefix,
    baseline: usize,
    stops: Stops,
) -> UseResult {
    emit_leading_trivia(&mut i, &prefix.leading);
    i.state.start_node(SyntaxKind::UseAnchor.into());
    i.state
        .token(SyntaxKind::WithKw.into(), &prefix.keyword.text);
    if let Some(trivia) = i.token(scan_required_inline_trivia) {
        emit_leading_trivia(&mut i, &trivia);
    } else if observes(i.rb(), word_starter) {
        emit_missing(&mut i, LeadingTrivia::default());
    }

    i.state.start_node(SyntaxKind::UsePath.into());
    let result = (|| -> UseResult {
        if required_word(i.rb(), baseline, stops)? {
            while let Some((separator, text)) = i.token(scan_separator) {
                emit_separator(&mut i, text, separator);
                if !required_word(i.rb(), baseline, stops)? {
                    break;
                }
            }
        }
        Ok(())
    })();
    i.state.finish_node();
    i.state.finish_node();
    result
}

fn emit_matching_close(mut i: RewriteIn, close: char) -> bool {
    let Some(close_token) = i.token(|lex| scan_character(lex, close)) else {
        return false;
    };
    i.state.token(close_kind(close).into(), &close_token.text);
    true
}

fn emit_mismatched_close(i: &mut RewriteIn) {
    i.state.start_node(SyntaxKind::Error.into());
    let close = i
        .token(scan_raw_character)
        .expect("mismatched close was checked before recovery");
    i.state.token(SyntaxKind::Unknown.into(), &close.text);
    i.state.finish_node();
}

fn emit_comma(i: &mut RewriteIn) {
    let comma = i
        .token(|lex| scan_character(lex, ','))
        .expect("comma was checked before emission");
    i.state.token(SyntaxKind::Comma.into(), &comma.text);
}

fn emit_separator(i: &mut RewriteIn, token: Lexeme, separator: Separator) {
    let kind = match separator {
        Separator::ColonColon => SyntaxKind::ColonColon,
        Separator::Slash => SyntaxKind::Slash,
    };
    i.state.token(kind.into(), &token.text);
}

fn emit_intro_keyword(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let Payload::Token(token) = item.payload else {
        unreachable!("reserved statement keyword is a token")
    };
    emit_leading_trivia(i, &item.leading);
    i.state.token(kind.into(), &token.text);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("reserved visibility is a token")
    };
    emit_leading_trivia(i, &item.leading);
    let kind = match &*token.text {
        "my" => SyntaxKind::MyKw,
        "our" => SyntaxKind::OurKw,
        "pub" => SyntaxKind::PubKw,
        _ => unreachable!("use visibility was selected from exact words"),
    };
    i.state.token(kind.into(), &token.text);
}

fn recover_until<C, L>(
    mut i: RewriteIn,
    candidate: C,
    local_boundary: L,
    baseline: usize,
    stops: Stops,
    newline_boundary: bool,
) -> UseResult<bool>
where
    C: Fn(&str) -> bool,
    L: Fn(&str) -> bool,
{
    debug_assert!(!observes(i.rb(), |source| candidate(source)));
    if let Some(boundary) = take_caller_boundary(i.rb(), baseline, stops, newline_boundary) {
        return Err(boundary);
    }
    if observes(i.rb(), |source| local_boundary(source)) {
        return Ok(false);
    }
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let trivia = scan_trivia(i.rb());
        if trivia.0.is_empty() {
            let raw = i
                .token(scan_raw_character)
                .expect("recovery entered only on non-boundary source");
            i.state.token(SyntaxKind::Unknown.into(), &raw.text);
        } else {
            emit_leading_trivia(&mut i, &trivia);
        }
        if observes(i.rb(), |source| candidate(source)) {
            i.state.finish_node();
            return Ok(true);
        }
        if observes(i.rb(), |source| local_boundary(source)) {
            i.state.finish_node();
            return Ok(false);
        }
        if let Some(boundary) = take_caller_boundary(i.rb(), baseline, stops, newline_boundary) {
            i.state.finish_node();
            return Err(boundary);
        }
    }
}

fn take_declaration_boundary(mut i: RewriteIn, baseline: usize, stops: Stops) -> Option<Item> {
    take_caller_boundary(i.rb(), baseline, stops, true)
}

fn take_group_caller_boundary(
    mut i: RewriteIn,
    close: char,
    baseline: usize,
    stops: Stops,
) -> Option<Item> {
    i.token(|mut lex| {
        let item = scan_statement_item(lex.rb(), baseline, stops)?;
        if matches!(token_kind(&item), Some(TokenKind::Comma))
            || token_kind(&item) == Some(close_token_kind(close))
        {
            return None;
        }
        group_caller_boundary(lex, &item, baseline, stops).then_some(item)
    })
}

fn take_caller_boundary(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    newline_boundary: bool,
) -> Option<Item> {
    i.token(|mut lex| {
        let item = scan_statement_item(lex.rb(), baseline, stops)?;
        declaration_caller_boundary(lex, &item, stops, newline_boundary).then_some(item)
    })
}

fn declaration_caller_boundary(
    mut i: LexIn,
    item: &Item,
    stops: Stops,
    newline_boundary: bool,
) -> bool {
    matches!(item.payload, Payload::Eof)
        || newline_boundary && trivia_has_newline(&item.leading)
        || is_active_stop_lex(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::LBracket
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
}

fn group_caller_boundary(mut i: LexIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || is_active_stop_lex(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Semicolon | TokenKind::LBracket)
        )
        || indentation_after_newline(&item.leading)
            .is_some_and(|indentation| indentation <= baseline)
            && is_exact_canonical_statement_intro(item)
}

fn is_exact_canonical_statement_intro(item: &Item) -> bool {
    matches!(
        item_word(item),
        Some("use" | "mod" | "struct" | "type" | "my" | "our" | "pub")
    )
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

fn prefixed_use_candidate(source: &str) -> bool {
    let (source, gap, indentation) = source_after_trivia(source);
    if !gap || indentation.is_some() {
        return false;
    }
    let Some((head, after_head)) = source_identifier(source) else {
        return false;
    };
    if head != "use" {
        return false;
    }
    let (target, gap, indentation) = source_after_trivia(after_head);
    gap && indentation.is_none() && use_tree_starter(target)
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

fn use_tree_starter(source: &str) -> bool {
    matches!(source.chars().next(), Some('{' | '('))
        || source.starts_with("mod")
            && source_identifier(source).is_some_and(|(word, _)| word == "mod")
        || word_starter(source)
}

fn path_segment_starter(source: &str) -> bool {
    operator_name_starter(source) || word_starter(source)
}

fn exclusion_starter(source: &str) -> bool {
    matches!(source.chars().next(), Some('(' | '{' | '*')) || word_starter(source)
}

fn operator_name_starter(source: &str) -> bool {
    source.starts_with('(')
        && source[1..]
            .chars()
            .next()
            .is_some_and(is_use_operator_character)
}

fn word_starter(source: &str) -> bool {
    source_identifier(source).is_some_and(|(word, _)| use_identifier_spelling(word))
}

fn use_local_path_boundary(i: RewriteIn) -> bool {
    observes(i, path_local_boundary_source)
}

fn path_local_boundary_source(source: &str) -> bool {
    source.starts_with('/')
        || source.starts_with("::")
        || reserved_use_atom(source)
        || use_suffix_after_inline_trivia(source)
}

fn reserved_use_atom(source: &str) -> bool {
    source_identifier(source).is_some_and(|(word, _)| !use_identifier_spelling(word))
}

fn mismatched_close(source: &str, close: char) -> bool {
    matches!(source.chars().next(), Some(')' | '}')) && !source.starts_with(close)
}

fn use_suffix_after_inline_trivia(source: &str) -> bool {
    let (next, has_trivia, indentation) = source_after_trivia(source);
    if !has_trivia || indentation.is_some() {
        return false;
    }
    source_identifier(next)
        .is_some_and(|(word, _)| matches!(word, "as" | "with") || version_starter(word))
}

fn version_starter(word: &str) -> bool {
    word.strip_prefix('v')
        .and_then(|suffix| suffix.chars().next())
        .is_some_and(|character| character.is_ascii_digit())
}

fn trivia_has_newline(trivia: &LeadingTrivia) -> bool {
    trivia.0.iter().any(|part| part.text.contains(['\r', '\n']))
}

fn open_kind(close: char) -> SyntaxKind {
    match close {
        ')' => SyntaxKind::LParen,
        '}' => SyntaxKind::LBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
}

fn close_kind(close: char) -> SyntaxKind {
    match close {
        ')' => SyntaxKind::RParen,
        '}' => SyntaxKind::RBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
}

fn close_token_kind(close: char) -> TokenKind {
    match close {
        ')' => TokenKind::RParen,
        '}' => TokenKind::RBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
}

fn scan_keyword_prefix(mut i: LexIn, word: &str) -> Option<KeywordPrefix> {
    let leading = scan_required_inline_trivia(i.rb())?;
    let keyword = scan_exact_word(i.rb(), word)?;
    Some(KeywordPrefix { leading, keyword })
}

fn scan_version_prefix(mut i: LexIn) -> Option<(LeadingTrivia, Lexeme)> {
    let leading = scan_required_inline_trivia(i.rb())?;
    let version = scan_version(i)?;
    Some((leading, version))
}

fn scan_required_inline_trivia(mut i: LexIn) -> Option<LeadingTrivia> {
    let trivia = scan_trivia(i.rb());
    (!trivia.0.is_empty() && !trivia_has_newline(&trivia)).then_some(trivia)
}

fn scan_exact_word(mut i: LexIn, word: &str) -> Option<Token> {
    let token = scan_identifier(i.rb())?;
    (&*token.text == word).then_some(token)
}

fn scan_use_identifier(mut i: LexIn) -> Option<Token> {
    let token = scan_identifier(i.rb())?;
    use_identifier_spelling(&token.text).then_some(token)
}

fn use_identifier_spelling(word: &str) -> bool {
    !matches!(word, "mod" | "as" | "with" | "without") && !version_starter(word)
}

fn scan_separator(mut i: LexIn) -> Option<(Separator, Lexeme)> {
    if let Some(separator) = i.token(|lex| scan_pair(lex, ':', ':')) {
        return Some((Separator::ColonColon, separator));
    }
    i.token(|lex| scan_character(lex, '/'))
        .map(|separator| (Separator::Slash, separator))
}

fn scan_pair(mut i: LexIn, first: char, second: char) -> Option<Lexeme> {
    let (accepted, text) = i.rb().with_str(|mut pair| {
        (pair.next()? == first).then_some(())?;
        (pair.next()? == second).then_some(())
    });
    accepted?;
    Some(Lexeme { text: text.into() })
}

fn scan_character(mut i: LexIn, expected: char) -> Option<Lexeme> {
    let (accepted, text) = i
        .rb()
        .with_str(|mut one| (one.next()? == expected).then_some(()));
    accepted?;
    Some(Lexeme { text: text.into() })
}

fn scan_raw_character(mut i: LexIn) -> Option<Lexeme> {
    let (character, text) = i.rb().with_str(|mut one| one.next());
    character?;
    Some(Lexeme { text: text.into() })
}

fn scan_operator_spelling(mut i: LexIn) -> Option<Lexeme> {
    let (accepted, text) = i.rb().with_str(|mut spelling| {
        is_use_operator_character(spelling.next()?).then_some(())?;
        while spelling
            .remainder()
            .chars()
            .next()
            .is_some_and(is_use_operator_character)
        {
            spelling.next()?;
        }
        Some(())
    });
    accepted?;
    Some(Lexeme { text: text.into() })
}

fn scan_version(mut i: LexIn) -> Option<Lexeme> {
    let (accepted, text) = i.rb().with_str(|mut version| {
        (version.next()? == 'v').then_some(())?;
        version
            .remainder()
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_digit())
            .then_some(())?;
        version.next()?;
        while version.remainder().chars().next().is_some_and(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '+')
        }) {
            version.next()?;
        }
        Some(())
    });
    accepted?;
    Some(Lexeme { text: text.into() })
}

fn is_use_operator_character(character: char) -> bool {
    !character.is_whitespace()
        && character != '_'
        && !is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';'
        )
}
