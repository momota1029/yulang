//! Direct, fence-normalized `use` declaration and recursive use-tree construction.

use reborrow_generic::Reborrow as _;
use unicode_ident::is_xid_continue;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        NormalizedExit, advanced_origin, complete, handoff, indentation_after_newline,
        is_active_stop, suffix_marker, token_kind,
    },
    emit::emit_missing,
    item::{Item, LeadingTrivia, Token, TokenKind},
    lexer::{scan_arm_arrow, scan_identifier, scan_punctuation, scan_unknown, source_identifier},
    operator::{TriviaObservation, observe_fenced_trivia},
    yumark::FenceBoundary,
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

type UseResult<T = Item> = Result<T, Item>;

pub(super) fn use_declaration_selected_normalized(
    i: RewriteIn,
    item: &Item,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("use") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    i.map(
        |lex: LexIn| {
            Some(prefixed_use_candidate_normalized(
                lex.remainder(),
                item_origin,
                fence,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

fn prefixed_use_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    let TriviaObservation::Visible(first) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    if !first.present || first.indentation.is_some() {
        return false;
    }
    let Some((head, after_head)) = source_identifier(first.source) else {
        return false;
    };
    if head != "use" {
        return false;
    }
    let consumed = source.len() - after_head.len();
    let Some(after_head_origin) = item_origin.checked_add(consumed) else {
        return false;
    };
    let TriviaObservation::Visible(target) =
        observe_fenced_trivia(after_head, after_head_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    target.present && target.indentation.is_none() && use_tree_starter_source(target.source)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn use_declaration_normalized(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    debug_assert!(use_declaration_selected_normalized(
        i.rb(),
        &intro,
        item_origin,
        fence,
    ));
    i.state.start_node(SyntaxKind::UseDeclaration.into());

    if item_word(&intro) == Some("use") {
        emit_item_as(&mut i, intro, SyntaxKind::UseKw);
    } else {
        emit_visibility(&mut i, intro);
        let mut keyword = next_use_item(i.rb(), &mut item_origin, &mut line_entry, fence);
        debug_assert!(inline_gap(&keyword));
        debug_assert_eq!(item_word(&keyword), Some("use"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::UseKw);
    }

    let mut item = next_use_item(i.rb(), &mut item_origin, &mut line_entry, fence);
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    let had_inline_gap = inline_gap(&item);
    if had_inline_gap {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return complete(handoff(item), line_entry);
    }
    if use_tree_starter(&item) && !had_inline_gap {
        emit_missing(&mut i, LeadingTrivia::default());
    }

    if !use_tree_starter(&item) {
        match recover_until(
            i.rb(),
            item,
            |_, item, _, _, _| use_tree_starter(item),
            |_, _, _, _, _| false,
            baseline,
            stops,
            true,
            &mut item_origin,
            &mut line_entry,
            fence,
        ) {
            Ok((true, next)) => item = next,
            Ok((false, next)) | Err(next) => {
                i.state.finish_node();
                return complete(handoff(next), line_entry);
            }
        }
    }

    let item = match parse_use_tree(
        i.rb(),
        item,
        baseline,
        stops,
        None,
        &mut item_origin,
        &mut line_entry,
        fence,
    ) {
        Ok(item) | Err(item) => item,
    };
    i.state.finish_node();
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn parse_use_tree(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    debug_assert!(use_tree_starter(&item));
    i.state.start_node(SyntaxKind::UseTree.into());
    let result = (|| -> UseResult {
        let (terminal, item) = if exact_char(&item, '{') {
            (
                Terminal::Group,
                parse_group(
                    i.rb(),
                    item,
                    '}',
                    SyntaxKind::UseGroup,
                    baseline,
                    stops,
                    outer_close,
                    item_origin,
                    line_entry,
                    fence,
                )?,
            )
        } else if exact_char(&item, '(') {
            i.state.start_node(SyntaxKind::UsePath.into());
            let item = parse_operator_name(i.rb(), item, item_origin, line_entry, fence);
            parse_path_tail(
                i.rb(),
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?
        } else {
            let word = item_word(&item).expect("use-tree starter was a word");
            if word == "mod" {
                emit_item_as(&mut i, item, SyntaxKind::ModKw);
                let item = next_use_item(i.rb(), item_origin, line_entry, fence);
                parse_mod_target(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    outer_close,
                    item_origin,
                    line_entry,
                    fence,
                )?
            } else {
                let mut next = next_use_item(i.rb(), item_origin, line_entry, fence);
                match (word, separator(&next)) {
                    ("realm", Some(Separator::Slash)) => {
                        emit_item_as(&mut i, item, SyntaxKind::RealmKw);
                        emit_separator(&mut i, next, Separator::Slash);
                        next = next_use_item(i.rb(), item_origin, line_entry, fence);
                        parse_marker_target(
                            i.rb(),
                            next,
                            baseline,
                            stops,
                            outer_close,
                            item_origin,
                            line_entry,
                            fence,
                        )?
                    }
                    ("band", Some(Separator::ColonColon)) => {
                        emit_item_as(&mut i, item, SyntaxKind::BandKw);
                        emit_separator(&mut i, next, Separator::ColonColon);
                        next = next_use_item(i.rb(), item_origin, line_entry, fence);
                        parse_marker_target(
                            i.rb(),
                            next,
                            baseline,
                            stops,
                            outer_close,
                            item_origin,
                            line_entry,
                            fence,
                        )?
                    }
                    _ => {
                        i.state.start_node(SyntaxKind::UsePath.into());
                        emit_item_as(&mut i, item, SyntaxKind::Identifier);
                        parse_path_tail(
                            i.rb(),
                            next,
                            baseline,
                            stops,
                            outer_close,
                            item_origin,
                            line_entry,
                            fence,
                        )?
                    }
                }
            }
        };

        let item = if terminal != Terminal::Glob {
            parse_aliases(
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            )?
        } else {
            item
        };
        parse_qualifiers(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )
    })();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn parse_mod_target(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(Terminal, Item)> {
    i.state.start_node(SyntaxKind::UsePath.into());
    if declaration_boundary(i.rb(), &item, stops, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return Err(item);
    }
    if inline_gap(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
    } else if word_starter(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
    }
    let (present, item) = required_word(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    )?;
    if !present {
        i.state.finish_node();
        return Ok((Terminal::Single, item));
    }
    parse_path_tail(
        i,
        item,
        baseline,
        stops,
        outer_close,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_marker_target(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(Terminal, Item)> {
    if exact_char(&item, '{') {
        let item = parse_group(
            i,
            item,
            '}',
            SyntaxKind::UseGroup,
            baseline,
            stops,
            outer_close,
            item_origin,
            line_entry,
            fence,
        )?;
        return Ok((Terminal::Group, item));
    }
    if exact_char(&item, '*') {
        let item = parse_glob(
            i,
            item,
            baseline,
            stops,
            outer_close,
            item_origin,
            line_entry,
            fence,
        )?;
        return Ok((Terminal::Glob, item));
    }

    i.state.start_node(SyntaxKind::UsePath.into());
    let (present, item) = required_path_segment(
        i.rb(),
        item,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    )?;
    if !present {
        i.state.finish_node();
        return Ok((Terminal::Single, item));
    }
    parse_path_tail(
        i,
        item,
        baseline,
        stops,
        outer_close,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_path_tail(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(Terminal, Item)> {
    loop {
        let Some(separator_kind) = separator(&item) else {
            i.state.finish_node();
            return Ok((Terminal::Single, item));
        };
        emit_separator(&mut i, item, separator_kind);
        item = next_use_item(i.rb(), item_origin, line_entry, fence);
        if exact_char(&item, '{') {
            i.state.finish_node();
            item = parse_group(
                i,
                item,
                '}',
                SyntaxKind::UseGroup,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?;
            return Ok((Terminal::Group, item));
        }
        if exact_char(&item, '*') {
            i.state.finish_node();
            item = parse_glob(
                i,
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?;
            return Ok((Terminal::Glob, item));
        }

        let (present, next) = required_path_segment(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )?;
        item = next;
        if !present {
            i.state.finish_node();
            return Ok((Terminal::Single, item));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn required_path_segment(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(bool, Item)> {
    if path_segment_starter_normalized(i.rb(), &item, *item_origin, *line_entry, fence) {
        return Ok((
            true,
            parse_path_segment(i, item, item_origin, line_entry, fence),
        ));
    }
    if path_local_boundary(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok((false, item));
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    let (retry, item) = recover_until(
        i.rb(),
        item,
        path_segment_starter_normalized,
        |_, item, _, _, _| path_local_boundary(item),
        baseline,
        stops,
        true,
        item_origin,
        line_entry,
        fence,
    )?;
    if retry {
        Ok((
            true,
            parse_path_segment(i, item, item_origin, line_entry, fence),
        ))
    } else {
        Ok((false, item))
    }
}

#[allow(clippy::too_many_arguments)]
fn required_word(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(bool, Item)> {
    if word_starter(&item) {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        return Ok((true, next_use_item(i, item_origin, line_entry, fence)));
    }
    if reserved_use_atom(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok((false, item));
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    let (retry, item) = recover_until(
        i.rb(),
        item,
        |_, item, _, _, _| word_starter(item),
        |_, item, _, _, _| reserved_use_atom(item),
        baseline,
        stops,
        true,
        item_origin,
        line_entry,
        fence,
    )?;
    if retry {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        Ok((true, next_use_item(i, item_origin, line_entry, fence)))
    } else {
        Ok((false, item))
    }
}

fn parse_path_segment(
    mut i: RewriteIn,
    item: Item,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    if exact_char(&item, '(') {
        parse_operator_name(i, item, item_origin, line_entry, fence)
    } else {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        next_use_item(i, item_origin, line_entry, fence)
    }
}

fn parse_operator_name(
    mut i: RewriteIn,
    open: Item,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    i.state.start_node(SyntaxKind::OperatorName.into());
    emit_item_as(&mut i, open, SyntaxKind::LParen);
    let item = next_use_item(i.rb(), item_origin, line_entry, fence);
    if !item.leading_view().is_grammar_empty() || !operator_spelling(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return item;
    }
    emit_item_as(&mut i, item, SyntaxKind::Operator);
    let item = next_use_item(i.rb(), item_origin, line_entry, fence);
    if item.leading_view().is_grammar_empty() && exact_char(&item, ')') {
        emit_item_as(&mut i, item, SyntaxKind::RParen);
        let item = next_use_item(i.rb(), item_origin, line_entry, fence);
        i.state.finish_node();
        item
    } else {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        item
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_group(
    mut i: RewriteIn,
    open: Item,
    close: char,
    kind: SyntaxKind,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    i.state.start_node(kind.into());
    emit_item_as(&mut i, open, open_kind(close));
    let mut item = next_use_item(i.rb(), item_origin, line_entry, fence);
    let mut after_child = false;
    loop {
        if group_caller_boundary(i.rb(), &item, close, baseline, stops) {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return Err(item);
        }
        let newline = item.leading_view().contains_line_break();
        item.emit_all_remaining_leading(&mut *i.state);
        if exact_char(&item, close) {
            emit_item_as(&mut i, item, close_kind(close));
            let item = next_use_item(i.rb(), item_origin, line_entry, fence);
            i.state.finish_node();
            return Ok(item);
        }
        if exact_char(&item, ',') {
            if !after_child {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            emit_item_as(&mut i, item, SyntaxKind::Comma);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            after_child = false;
            continue;
        }
        if mismatched_close(&item, close) {
            if outer_close.is_some_and(|outer| exact_char(&item, outer)) {
                emit_missing(&mut i, LeadingTrivia::default());
                i.state.finish_node();
                return Ok(item);
            }
            emit_error_item(&mut i, item);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            continue;
        }
        if use_tree_starter(&item) {
            if after_child && !newline {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            item = match parse_use_tree(
                i.rb(),
                item,
                baseline,
                stops,
                Some(close),
                item_origin,
                line_entry,
                fence,
            ) {
                Ok(item) => item,
                Err(item) => {
                    i.state.finish_node();
                    return Err(item);
                }
            };
            after_child = true;
            continue;
        }

        item = match recover_group(
            i.rb(),
            item,
            close,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        ) {
            Ok(item) => item,
            Err(item) => {
                i.state.finish_node();
                return Err(item);
            }
        };
        if exact_char(&item, ',') {
            emit_item_as(&mut i, item, SyntaxKind::Comma);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            after_child = false;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_glob(
    mut i: RewriteIn,
    star: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    i.state.start_node(SyntaxKind::UseGlob.into());
    emit_item_as(&mut i, star, SyntaxKind::Star);
    let item = next_use_item(i.rb(), item_origin, line_entry, fence);
    let result = (|| -> UseResult {
        let mut item = parse_aliases(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )?;
        if inline_keyword(&item, "without") {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_item_as(&mut i, item, SyntaxKind::WithoutKw);
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            if declaration_boundary(i.rb(), &item, stops, true) {
                emit_missing(&mut i, LeadingTrivia::default());
                return Err(item);
            }
            if inline_gap(&item) {
                item.emit_all_remaining_leading(&mut *i.state);
            } else if exclusion_starter(&item) {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            let (present, next) = required_exclusion(
                i.rb(),
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?;
            item = next;
            if present {
                while item.leading_view().is_grammar_empty() && exact_char(&item, ',') {
                    emit_item_as(&mut i, item, SyntaxKind::Comma);
                    item = next_use_item(i.rb(), item_origin, line_entry, fence);
                    if declaration_boundary(i.rb(), &item, stops, true) {
                        emit_missing(&mut i, LeadingTrivia::default());
                        return Err(item);
                    }
                    item.emit_all_remaining_leading(&mut *i.state);
                    let (present, next) = required_exclusion(
                        i.rb(),
                        item,
                        baseline,
                        stops,
                        outer_close,
                        item_origin,
                        line_entry,
                        fence,
                    )?;
                    item = next;
                    if !present {
                        break;
                    }
                }
            }
        }
        Ok(item)
    })();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn required_exclusion(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult<(bool, Item)> {
    if exclusion_starter(&item) {
        return Ok((
            true,
            parse_exclusion(
                i,
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?,
        ));
    }
    if reserved_use_atom(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok((false, item));
    }
    if declaration_boundary(i.rb(), &item, stops, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    let (retry, item) = recover_until(
        i.rb(),
        item,
        |_, item, _, _, _| exclusion_starter(item),
        |_, _, _, _, _| false,
        baseline,
        stops,
        true,
        item_origin,
        line_entry,
        fence,
    )?;
    if retry {
        Ok((
            true,
            parse_exclusion(
                i,
                item,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )?,
        ))
    } else {
        Ok((false, item))
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_exclusion(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    outer_close: Option<char>,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    i.state.start_node(SyntaxKind::UseExclusion.into());
    let result = if exact_char(&item, '(') {
        if operator_name_follows(i.rb(), *item_origin, *line_entry, fence) {
            Ok(parse_operator_name(
                i.rb(),
                item,
                item_origin,
                line_entry,
                fence,
            ))
        } else {
            parse_group(
                i.rb(),
                item,
                ')',
                SyntaxKind::UseExclusionGroup,
                baseline,
                stops,
                outer_close,
                item_origin,
                line_entry,
                fence,
            )
        }
    } else if exact_char(&item, '{') {
        parse_group(
            i.rb(),
            item,
            '}',
            SyntaxKind::UseExclusionGroup,
            baseline,
            stops,
            outer_close,
            item_origin,
            line_entry,
            fence,
        )
    } else if exact_char(&item, '*') {
        emit_item_as(&mut i, item, SyntaxKind::Star);
        Ok(next_use_item(i.rb(), item_origin, line_entry, fence))
    } else {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        Ok(next_use_item(i.rb(), item_origin, line_entry, fence))
    };
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn parse_aliases(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    while inline_keyword(&item, "as") {
        item.emit_all_remaining_leading(&mut *i.state);
        i.state.start_node(SyntaxKind::UseAlias.into());
        emit_item_as(&mut i, item, SyntaxKind::AsKw);
        item = next_use_item(i.rb(), item_origin, line_entry, fence);
        if declaration_boundary(i.rb(), &item, stops, true) {
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            return Err(item);
        }
        if inline_gap(&item) {
            item.emit_all_remaining_leading(&mut *i.state);
        } else if word_starter(&item) {
            emit_missing(&mut i, LeadingTrivia::default());
        }
        let result = required_word(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
        i.state.finish_node();
        let (_, next) = result?;
        item = next;
    }
    Ok(item)
}

#[allow(clippy::too_many_arguments)]
fn parse_qualifiers(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    let version = inline_version(&item);
    let anchor = !version && inline_keyword(&item, "with");
    if !version && !anchor {
        return Ok(item);
    }

    i.state.start_node(SyntaxKind::UseQualifiers.into());
    let result = (|| -> UseResult {
        if version {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.start_node(SyntaxKind::UseVersion.into());
            emit_item_as(&mut i, item, SyntaxKind::Version);
            i.state.finish_node();
            item = next_use_item(i.rb(), item_origin, line_entry, fence);
            if inline_keyword(&item, "with") {
                item = parse_anchor(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                )?;
            }
        } else {
            item = parse_anchor(
                i.rb(),
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            )?;
        }
        Ok(item)
    })();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn parse_anchor(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::UseAnchor.into());
    emit_item_as(&mut i, item, SyntaxKind::WithKw);
    item = next_use_item(i.rb(), item_origin, line_entry, fence);
    i.state.start_node(SyntaxKind::UsePath.into());
    if declaration_boundary(i.rb(), &item, stops, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        i.state.finish_node();
        return Err(item);
    }
    if inline_gap(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
    } else if word_starter(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
    }
    let result = (|| -> UseResult {
        let (present, mut item) = required_word(
            i.rb(),
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        )?;
        if present {
            while let Some(separator_kind) = separator(&item) {
                emit_separator(&mut i, item, separator_kind);
                item = next_use_item(i.rb(), item_origin, line_entry, fence);
                let (present, next) = required_word(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    item_origin,
                    line_entry,
                    fence,
                )?;
                item = next;
                if !present {
                    break;
                }
            }
        }
        Ok(item)
    })();
    i.state.finish_node();
    i.state.finish_node();
    result
}

#[allow(clippy::too_many_arguments)]
fn recover_until<C, L>(
    mut i: RewriteIn,
    mut item: Item,
    candidate: C,
    local_boundary: L,
    _baseline: usize,
    stops: Stops,
    newline_boundary: bool,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<(bool, Item), Item>
where
    C: Fn(RewriteIn, &Item, usize, LineEntry, Option<&FenceBoundary>) -> bool,
    L: Fn(RewriteIn, &Item, usize, LineEntry, Option<&FenceBoundary>) -> bool,
{
    debug_assert!(!candidate(i.rb(), &item, *item_origin, *line_entry, fence,));
    if declaration_boundary(i.rb(), &item, stops, newline_boundary) {
        return Err(item);
    }
    if local_boundary(i.rb(), &item, *item_origin, *line_entry, fence) {
        return Ok((false, item));
    }
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if !item.leading_view().is_grammar_empty() {
            item.emit_all_remaining_leading(&mut *i.state);
            if candidate(i.rb(), &item, *item_origin, *line_entry, fence) {
                i.state.finish_node();
                return Ok((true, item));
            }
            if local_boundary(i.rb(), &item, *item_origin, *line_entry, fence) {
                i.state.finish_node();
                return Ok((false, item));
            }
        }
        emit_item_as(&mut i, item, SyntaxKind::Unknown);
        item = next_use_item(i.rb(), item_origin, line_entry, fence);
        if candidate(i.rb(), &item, *item_origin, *line_entry, fence) {
            i.state.finish_node();
            return Ok((true, item));
        }
        if local_boundary(i.rb(), &item, *item_origin, *line_entry, fence) {
            i.state.finish_node();
            return Ok((false, item));
        }
        if declaration_boundary(i.rb(), &item, stops, newline_boundary) {
            i.state.finish_node();
            return Err(item);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_group(
    mut i: RewriteIn,
    mut item: Item,
    close: char,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> UseResult {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if group_caller_boundary(i.rb(), &item, close, baseline, stops) {
            i.state.finish_node();
            emit_missing(&mut i, LeadingTrivia::default());
            return Err(item);
        }
        if !item.leading_view().is_grammar_empty() {
            item.emit_all_remaining_leading(&mut *i.state);
            if use_tree_starter(&item) || exact_char(&item, ',') || exact_char(&item, close) {
                i.state.finish_node();
                return Ok(item);
            }
        }
        emit_item_as(&mut i, item, SyntaxKind::Unknown);
        item = next_use_item(i.rb(), item_origin, line_entry, fence);
        if use_tree_starter(&item) || exact_char(&item, ',') || exact_char(&item, close) {
            i.state.finish_node();
            return Ok(item);
        }
    }
}

fn declaration_boundary(mut i: RewriteIn, item: &Item, stops: Stops, newline: bool) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || newline && item.leading_view().contains_line_break()
        || is_active_stop(i.rb(), item, stops)
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

fn group_caller_boundary(
    mut i: RewriteIn,
    item: &Item,
    close: char,
    baseline: usize,
    stops: Stops,
) -> bool {
    if exact_char(item, ',') || exact_char(item, close) {
        return false;
    }
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_active_stop(i.rb(), item, stops)
        || token_kind(item) == Some(TokenKind::Semicolon)
        || token_kind(item) == Some(TokenKind::LBracket)
        || indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation <= baseline)
            && is_exact_canonical_statement_intro(item)
}

fn is_exact_canonical_statement_intro(item: &Item) -> bool {
    matches!(
        item_word(item),
        Some("use" | "mod" | "struct" | "type" | "for" | "my" | "our" | "pub")
    )
}

fn next_use_item(
    mut i: RewriteIn,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Item {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(lex, *item_origin, *line_entry, fence, |lex, _, _, _, _| {
                scan_use_payload(lex)
            })
        })
        .expect("Use raw payload scanning is total");
    *item_origin = advanced_origin(*item_origin, entry, i);
    *line_entry = next_line_entry;
    item
}

fn scan_use_payload(mut i: LexIn) -> Option<AcceptedPayload> {
    let token = if let Some(version) = i.token(scan_version_token) {
        version
    } else if let Some(identifier) = i.token(scan_identifier) {
        identifier
    } else if let Some(arrow) = i.token(scan_arm_arrow) {
        arrow
    } else if let Some(separator) =
        i.token(|lex| scan_pair_token(lex, ':', ':', TokenKind::PathSeparator))
    {
        separator
    } else if let Some(punctuation) = i.token(scan_punctuation) {
        punctuation
    } else if let Some(slash) = i.token(|lex| scan_character_token(lex, '/', TokenKind::Operator)) {
        slash
    } else if let Some(operator) = i.token(scan_operator_token) {
        operator
    } else {
        i.token(scan_unknown)?
    };
    Some(AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    })
}

fn scan_version_token(mut i: LexIn) -> Option<Token> {
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
    Some(Token {
        kind: TokenKind::Identifier,
        text: text.into(),
    })
}

fn scan_pair_token(mut i: LexIn, first: char, second: char, kind: TokenKind) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut pair| {
        (pair.next()? == first).then_some(())?;
        (pair.next()? == second).then_some(())
    });
    accepted?;
    Some(Token {
        kind,
        text: text.into(),
    })
}

fn scan_character_token(mut i: LexIn, expected: char, kind: TokenKind) -> Option<Token> {
    let (accepted, text) = i
        .rb()
        .with_str(|mut one| (one.next()? == expected).then_some(()));
    accepted?;
    Some(Token {
        kind,
        text: text.into(),
    })
}

fn scan_operator_token(mut i: LexIn) -> Option<Token> {
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
    Some(Token {
        kind: TokenKind::Operator,
        text: text.into(),
    })
}

fn emit_item_as(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_error_item(i: &mut RewriteIn, item: Item) {
    i.state.start_node(SyntaxKind::Error.into());
    emit_item_as(i, item, SyntaxKind::Unknown);
    i.state.finish_node();
}

fn emit_separator(i: &mut RewriteIn, item: Item, separator: Separator) {
    let kind = match separator {
        Separator::ColonColon => SyntaxKind::ColonColon,
        Separator::Slash => SyntaxKind::Slash,
    };
    emit_item_as(i, item, kind);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("use visibility was selected from exact words"),
    };
    emit_item_as(i, item, kind);
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn exact_char(item: &Item, expected: char) -> bool {
    item.leading_view().is_grammar_empty()
        && item
            .payload_view()
            .spelling()
            .is_some_and(|text| text.len() == expected.len_utf8() && text.starts_with(expected))
}

fn inline_gap(item: &Item) -> bool {
    !item.leading_view().is_grammar_empty() && !item.leading_view().contains_line_break()
}

fn inline_keyword(item: &Item, expected: &str) -> bool {
    inline_gap(item) && item_word(item) == Some(expected)
}

fn inline_version(item: &Item) -> bool {
    inline_gap(item) && item_word(item).is_some_and(version_starter)
}

fn separator(item: &Item) -> Option<Separator> {
    if !item.leading_view().is_grammar_empty() {
        return None;
    }
    match item.payload_view().spelling() {
        Some("::") => Some(Separator::ColonColon),
        Some("/") => Some(Separator::Slash),
        _ => None,
    }
}

fn use_tree_starter(item: &Item) -> bool {
    exact_char(item, '{')
        || exact_char(item, '(')
        || item_word(item).is_some_and(|word| word == "mod" || use_identifier_spelling(word))
}

fn use_tree_starter_source(source: &str) -> bool {
    matches!(source.chars().next(), Some('{' | '('))
        || source.starts_with("mod")
            && source_identifier(source).is_some_and(|(word, _)| word == "mod")
        || source_identifier(source).is_some_and(|(word, _)| use_identifier_spelling(word))
}

fn path_segment_starter_normalized(
    i: RewriteIn,
    item: &Item,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    word_starter(item)
        || exact_char(item, '(') && operator_name_follows(i, item_origin, line_entry, fence)
}

fn operator_name_follows(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    let mut accepted = false;
    let _: Option<()> = i.token(|lex| {
        let CurrentItem { item, .. } =
            current_item(lex, item_origin, line_entry, fence, |lex, _, _, _, _| {
                scan_use_payload(lex)
            })?;
        accepted = operator_spelling(&item);
        None
    });
    accepted
}

fn exclusion_starter(item: &Item) -> bool {
    exact_char(item, '(') || exact_char(item, '{') || exact_char(item, '*') || word_starter(item)
}

fn word_starter(item: &Item) -> bool {
    item.leading_view().is_grammar_empty() && item_word(item).is_some_and(use_identifier_spelling)
}

fn reserved_use_atom(item: &Item) -> bool {
    item.leading_view().is_grammar_empty()
        && item_word(item).is_some_and(|word| !use_identifier_spelling(word))
}

fn path_local_boundary(item: &Item) -> bool {
    separator(item).is_some()
        || reserved_use_atom(item)
        || inline_keyword(item, "as")
        || inline_keyword(item, "with")
        || inline_version(item)
}

fn mismatched_close(item: &Item, close: char) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBrace)
    ) && !exact_char(item, close)
}

fn operator_spelling(item: &Item) -> bool {
    item.leading_view().is_grammar_empty()
        && item.payload_view().token_kind() == Some(TokenKind::Operator)
        && item
            .payload_view()
            .spelling()
            .is_some_and(|text| text.chars().all(is_use_operator_character))
}

fn version_starter(word: &str) -> bool {
    word.strip_prefix('v')
        .and_then(|suffix| suffix.chars().next())
        .is_some_and(|character| character.is_ascii_digit())
}

fn use_identifier_spelling(word: &str) -> bool {
    !matches!(word, "mod" | "as" | "with" | "without") && !version_starter(word)
}

fn close_kind(close: char) -> SyntaxKind {
    match close {
        ')' => SyntaxKind::RParen,
        '}' => SyntaxKind::RBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
}

fn open_kind(close: char) -> SyntaxKind {
    match close {
        ')' => SyntaxKind::LParen,
        '}' => SyntaxKind::LBrace,
        _ => unreachable!("use groups are parenthesized or braced"),
    }
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
