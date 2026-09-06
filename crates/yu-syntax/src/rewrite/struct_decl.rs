//! Direct canonical `struct` declaration construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, advanced_origin, complete, delimited_baseline, handoff,
        implicit_delimited_newline, indentation_after_newline, is_active_stop, suffix_marker,
        token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, scan_exact_pipe, scan_identifier,
        scan_statement_payload, scan_type_nud_payload, source_identifier,
    },
    operator::{TriviaObservation, observe_fenced_trivia},
    type_expr::{
        TypeApplyBoundary, required_type_expr_with_boundary_normalized, with_type_outer_close,
    },
    yumark::FenceBoundary,
};

pub(super) fn struct_declaration_selected_normalized(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("struct") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    i.map(
        |lex: LexIn| {
            Some(prefixed_struct_candidate_normalized(
                lex.remainder(),
                item_origin,
                fence,
                baseline,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

fn prefixed_struct_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    observed
        .indentation
        .is_none_or(|indentation| indentation > baseline)
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "struct")
}

#[allow(clippy::too_many_arguments)]
pub(super) fn struct_declaration_normalized(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    debug_assert!(struct_declaration_selected_normalized(
        i.rb(),
        &intro,
        baseline,
        item_origin,
        fence,
    ));
    i.state.start_node(SyntaxKind::StructDeclaration.into());
    if item_word(&intro) == Some("struct") {
        emit_item_as(&mut i, intro, SyntaxKind::StructKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = struct_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            true,
        );
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(gstruct_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("struct"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::StructKw);
    }

    let (first, next_origin, next_entry) = struct_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        true,
    );
    item_origin = next_origin;
    line_entry = next_entry;
    let body = match required_name_normalized(
        i.rb(),
        first,
        baseline,
        stops,
        &mut item_origin,
        &mut line_entry,
        fence,
    ) {
        Ok(Some(body)) => body,
        Ok(None) => {
            let (body, next_origin, next_entry) = struct_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                true,
            );
            item_origin = next_origin;
            line_entry = next_entry;
            body
        }
        Err(boundary) => {
            i.state.finish_node();
            return complete(handoff(boundary), line_entry);
        }
    };

    let exit = parse_body_item_normalized(
        i.rb(),
        body,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

/// `Ok(Some)` carries a local body starter. `Err` is an unchanged caller
/// boundary. An accepted raw name returns `Ok(None)` at the live suffix.
#[allow(clippy::too_many_arguments)]
fn required_name_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<Option<Item>, Item> {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    if !gstruct_allowed(&item, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    if body_starter_item(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(Some(item));
    }
    if header_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if raw_name(&item) {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        return Ok(None);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let (mut next, next_origin, next_entry) = struct_item_normalized(
            i.rb(),
            *item_origin,
            *line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        *item_origin = next_origin;
        *line_entry = next_entry;
        if next.payload_view().is_boundary() {
            i.state.finish_node();
            return Err(next);
        }
        if next.payload_view().is_eof() {
            next.emit_eof_leading(&mut *i.state);
            i.state.finish_node();
            return Err(next);
        }
        if !gstruct_allowed(&next, baseline) {
            i.state.finish_node();
            return Err(next);
        }
        if body_starter_item(&next) {
            next.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            return Ok(Some(next));
        }
        if header_boundary(i.rb(), &next, baseline, stops) {
            i.state.finish_node();
            return Err(next);
        }
        if raw_name(&next) {
            next.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            emit_item_as(&mut i, next, SyntaxKind::Identifier);
            return Ok(None);
        }
        item = next;
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_body_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if !gstruct_allowed(&item, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => parse_delimited_fields_normalized(
            i,
            item,
            baseline,
            stops,
            FieldList::NamedBrace,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::LParen) => parse_delimited_fields_normalized(
            i,
            item,
            baseline,
            stops,
            FieldList::Tuple,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            parse_indented_fields_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        _ if body_boundary(i.rb(), &item, baseline, stops) || type_starter(&item) => {
            emit_missing(&mut i, LeadingTrivia::default());
            complete(handoff(item), line_entry)
        }
        _ => recover_body_introducer_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = struct_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            true,
            false,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if !gstruct_allowed(&item, baseline) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if body_starter_item(&item) {
            i.state.finish_node();
            return parse_body_item_normalized(
                i,
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            );
        }
        if body_boundary(i.rb(), &item, baseline, stops) || type_starter(&item) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum FieldList {
    NamedBrace,
    Tuple,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum FieldOuterClose {
    Recover,
    Borrow,
}

pub(super) struct DeclarationFieldExit {
    pub(super) exit: NormalizedExit,
    pub(super) item_origin: usize,
}

impl FieldList {
    fn close(self) -> TokenKind {
        match self {
            Self::NamedBrace => TokenKind::RBrace,
            Self::Tuple => TokenKind::RParen,
        }
    }

    fn type_boundary(self) -> Option<TypeApplyBoundary> {
        match self {
            Self::NamedBrace => Some(TypeApplyBoundary::DeclarationNamedFields),
            Self::Tuple => None,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_delimited_fields_normalized(
    mut i: RewriteIn,
    open: Item,
    owner_baseline: usize,
    stops: Stops,
    list: FieldList,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let result = declaration_fields_normalized(
        i.rb(),
        open,
        owner_baseline,
        stops,
        list,
        FieldOuterClose::Recover,
        false,
        item_origin,
        line_entry,
        fence,
    );
    match result.exit {
        NormalizedExit::Complete(Ok(()), line_entry) => after_completed_normalized(
            i,
            owner_baseline,
            stops,
            result.item_origin,
            line_entry,
            fence,
        ),
        exit => exit,
    }
}

/// Shared direct named/tuple declaration-field owner.  It consumes exactly
/// its own matching close; the enclosing declaration owner decides how to
/// acquire the successor after `Ok(())`.
#[allow(clippy::too_many_arguments)]
pub(super) fn declaration_fields_normalized(
    mut i: RewriteIn,
    open: Item,
    owner_baseline: usize,
    stops: Stops,
    list: FieldList,
    outer_close: FieldOuterClose,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> DeclarationFieldExit {
    emit_token_item(&mut i, open);
    let (mut item, item_origin, line_entry) = field_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        owner_baseline,
        stops,
        Some(list),
        pipe_lexical,
    );
    let list_base = delimited_baseline(owner_baseline, item.leading_view());
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
    } else if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    field_sequence_normalized(
        i,
        item,
        list_base,
        stops,
        Some(list),
        outer_close,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_indented_fields_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let Some(block_indent) = introduced_body_indentation_normalized(i.rb(), item_origin, fence)
    else {
        let (item, _, next_entry) = struct_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        emit_missing_field(&mut i, LeadingTrivia::default(), false);
        return complete(handoff(item), next_entry);
    };
    if block_indent <= baseline {
        let (item, _, next_entry) = struct_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        emit_missing_field(&mut i, LeadingTrivia::default(), false);
        return complete(handoff(item), next_entry);
    }
    let (mut item, item_origin, line_entry) = struct_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        block_indent,
        stops,
        true,
        false,
    );
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
    } else if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    field_sequence_normalized(
        i,
        item,
        block_indent,
        stops,
        None,
        FieldOuterClose::Recover,
        false,
        item_origin,
        line_entry,
        fence,
    )
    .exit
}

#[allow(clippy::too_many_arguments)]
fn field_sequence_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    outer_close: FieldOuterClose,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> DeclarationFieldExit {
    let mut need_field = true;
    let mut after_comma = false;
    loop {
        if item.payload_view().is_boundary() {
            if let Some(list) = delimited {
                if after_comma
                    || (!need_field && implicit_delimited_newline(baseline, item.leading_view()))
                {
                    emit_missing_field_item(&mut i, &mut item, list == FieldList::Tuple);
                }
                emit_missing(&mut i, LeadingTrivia::default());
            } else if need_field && !after_comma {
                emit_missing_field(&mut i, LeadingTrivia::default(), false);
            }
            return DeclarationFieldExit {
                exit: complete(handoff(item), line_entry),
                item_origin,
            };
        }
        if item.payload_view().is_eof() {
            if let Some(list) = delimited {
                if after_comma
                    || (!need_field && implicit_delimited_newline(baseline, item.leading_view()))
                {
                    emit_missing_field_item(&mut i, &mut item, list == FieldList::Tuple);
                } else {
                    item.emit_eof_leading(&mut *i.state);
                }
                emit_missing(&mut i, LeadingTrivia::default());
            } else {
                item.emit_eof_leading(&mut *i.state);
                if need_field && !after_comma {
                    emit_missing_field(&mut i, LeadingTrivia::default(), false);
                }
            }
            return DeclarationFieldExit {
                exit: complete(handoff(item), line_entry),
                item_origin,
            };
        }

        if let Some(list) = delimited {
            if token_kind(&item) == Some(list.close()) {
                emit_token_item(&mut i, item);
                return DeclarationFieldExit {
                    exit: complete(Ok(()), line_entry),
                    item_origin,
                };
            }
            if is_active_stop(i.rb(), &item, stops) {
                if after_comma
                    || (!need_field && implicit_delimited_newline(baseline, item.leading_view()))
                {
                    emit_missing_field_item(&mut i, &mut item, list == FieldList::Tuple);
                }
                emit_missing(&mut i, LeadingTrivia::default());
                return DeclarationFieldExit {
                    exit: complete(handoff(item), line_entry),
                    item_origin,
                };
            }
        } else if indented_end(i.rb(), &item, baseline, stops) {
            if need_field && !after_comma {
                emit_missing_field(&mut i, LeadingTrivia::default(), false);
            }
            return DeclarationFieldExit {
                exit: complete(handoff(item), line_entry),
                item_origin,
            };
        }

        if delimited.is_some_and(|list| mismatched_close(&item, list.close())) {
            if outer_close == FieldOuterClose::Borrow {
                emit_missing(&mut i, LeadingTrivia::default());
                return DeclarationFieldExit {
                    exit: complete(handoff(item), line_entry),
                    item_origin,
                };
            }
            i.state.start_node(SyntaxKind::Error.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            (item, item_origin, line_entry) = field_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                delimited,
                pipe_lexical,
            );
            continue;
        }

        if token_kind(&item) == Some(TokenKind::Comma) {
            if need_field {
                emit_missing_field_item(&mut i, &mut item, delimited == Some(FieldList::Tuple));
            }
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) = field_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                delimited,
                pipe_lexical,
            );
            need_field = true;
            after_comma = true;
            continue;
        }
        if !need_field && implicit_delimited_newline(baseline, item.leading_view()) {
            item.emit_all_remaining_leading(&mut *i.state);
            need_field = true;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            (item, item_origin, line_entry) = recover_separator_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                delimited,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
            need_field = true;
            after_comma = false;
            continue;
        }
        if !need_field {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            need_field = true;
        }
        if need_field && !item.leading_view().is_grammar_empty() {
            item.emit_all_remaining_leading(&mut *i.state);
        }

        let valid_start = match delimited {
            Some(FieldList::Tuple) => true,
            Some(FieldList::NamedBrace) | None => {
                raw_name(&item) || token_kind(&item) == Some(TokenKind::Colon)
            }
        };
        if !valid_start {
            if matches!(delimited, Some(FieldList::NamedBrace) | None) {
                let exit = recover_named_field_normalized(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    delimited,
                    pipe_lexical,
                    item_origin,
                    line_entry,
                    fence,
                );
                (item, item_origin, line_entry) = match exit {
                    (
                        NormalizedExit::Complete(Err(Either::Left(item)), next_entry),
                        next_origin,
                    ) => (item, next_origin, next_entry),
                    (exit, next_origin) => {
                        return DeclarationFieldExit {
                            exit,
                            item_origin: next_origin,
                        };
                    }
                };
                need_field = false;
                after_comma = false;
            } else {
                unreachable!("tuple fields admit the ordinary mandatory Type entry")
            }
        }

        if need_field {
            let (exit, next_origin) = match delimited {
                Some(FieldList::Tuple) => tuple_field_normalized(
                    i.rb(),
                    item,
                    baseline,
                    pipe_lexical,
                    item_origin,
                    line_entry,
                    fence,
                ),
                Some(FieldList::NamedBrace) | None => named_field_normalized(
                    i.rb(),
                    item,
                    baseline,
                    stops,
                    delimited,
                    pipe_lexical,
                    item_origin,
                    line_entry,
                    fence,
                ),
            };
            (item, item_origin, line_entry) = match exit {
                NormalizedExit::Complete(Err(Either::Left(item)), next_entry) => {
                    (item, next_origin, next_entry)
                }
                exit => {
                    return DeclarationFieldExit {
                        exit,
                        item_origin: next_origin,
                    };
                }
            };
            need_field = false;
            after_comma = false;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn named_field_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, usize) {
    i.state.start_node(SyntaxKind::StructField.into());
    if raw_name(&item) {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = struct_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            0,
            true,
            false,
            pipe_lexical,
        );
    } else {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
    }

    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }
    if token_kind(&item) == Some(TokenKind::Colon)
        && indentation_after_newline(item.leading_view()).is_none()
    {
        emit_token_item(&mut i, item);
        return named_field_rhs_normalized(
            i,
            baseline,
            delimited,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }

    if indentation_after_newline(item.leading_view()).is_some() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }

    if type_starter(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        let (exit, item_origin) = named_type_normalized(
            i.rb(),
            item,
            baseline,
            delimited,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
        i.state.finish_node();
        return (exit, item_origin);
    }

    if field_boundary(i.rb(), &item, baseline, stops, delimited) {
        item.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = struct_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
            pipe_lexical,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return (complete(handoff(item), line_entry), item_origin);
        }
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            i.state.finish_node();
            i.state.finish_node();
            return (complete(handoff(item), line_entry), item_origin);
        }
        if token_kind(&item) == Some(TokenKind::Colon)
            && indentation_after_newline(item.leading_view()).is_none()
        {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return named_field_rhs_normalized(
                i,
                baseline,
                delimited,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if type_starter(&item)
            && indentation_after_newline(item.leading_view()).is_none_or(|indent| indent > baseline)
        {
            i.state.finish_node();
            let (exit, item_origin) = named_type_normalized(
                i.rb(),
                item,
                baseline,
                delimited,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
            i.state.finish_node();
            return (exit, item_origin);
        }
        if field_boundary(i.rb(), &item, baseline, stops, delimited) {
            i.state.finish_node();
            i.state.finish_node();
            return (complete(handoff(item), line_entry), item_origin);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_named_field_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, usize) {
    i.state.start_node(SyntaxKind::StructField.into());
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = struct_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
            pipe_lexical,
        );
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return (complete(handoff(item), line_entry), item_origin);
        }
        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            i.state.finish_node();
            i.state.finish_node();
            return (complete(handoff(item), line_entry), item_origin);
        }
        if token_kind(&item) == Some(TokenKind::Colon)
            && indentation_after_newline(item.leading_view()).is_none()
        {
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return named_field_rhs_normalized(
                i,
                baseline,
                delimited,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if raw_name(&item) || field_boundary(i.rb(), &item, baseline, stops, delimited) {
            i.state.finish_node();
            i.state.finish_node();
            return (complete(handoff(item), line_entry), item_origin);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn named_field_rhs_normalized(
    mut i: RewriteIn,
    baseline: usize,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, usize) {
    let (mut primary, item_origin, line_entry) = struct_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        0,
        false,
        true,
        pipe_lexical,
    );
    if !primary.payload_view().is_boundary()
        && indentation_after_newline(primary.leading_view()).is_none_or(|indent| indent > baseline)
    {
        if primary.payload_view().is_eof() {
            primary.emit_eof_leading(&mut *i.state);
        } else {
            primary.emit_all_remaining_leading(&mut *i.state);
        }
    }
    let (exit, item_origin) = named_type_normalized(
        i.rb(),
        primary,
        baseline,
        delimited,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    (exit, item_origin)
}

#[allow(clippy::too_many_arguments)]
fn named_type_normalized(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, usize) {
    let close = delimited.map_or(0, |list| with_type_outer_close(0, list.close()));
    let entry = suffix_marker(i.rb());
    let exit = required_type_expr_with_boundary_normalized(
        i.rb(),
        primary,
        baseline,
        Some(TypeApplyBoundary::DeclarationNamedFields),
        close,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    (exit, advanced_origin(item_origin, entry, i))
}

#[allow(clippy::too_many_arguments)]
fn tuple_field_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, usize) {
    i.state.start_node(SyntaxKind::StructField.into());
    let entry = suffix_marker(i.rb());
    let exit = required_type_expr_with_boundary_normalized(
        i.rb(),
        item,
        baseline,
        None,
        1,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    (exit, item_origin)
}

#[allow(clippy::too_many_arguments)]
fn recover_separator_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = field_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            delimited,
            pipe_lexical,
        );
        if item.payload_view().is_boundary()
            || item.payload_view().is_eof()
            || token_kind(&item) == Some(TokenKind::Comma)
            || delimited.is_some_and(|list| token_kind(&item) == Some(list.close()))
            || token_kind(&item) == Some(TokenKind::Colon)
            || raw_name(&item)
            || delimited == Some(FieldList::Tuple) && type_starter(&item)
            || is_active_stop(i.rb(), &item, stops)
            || implicit_delimited_newline(baseline, item.leading_view())
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn field_item_normalized(
    i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
) -> (Item, usize, LineEntry) {
    match delimited {
        Some(FieldList::Tuple) => struct_item_with_pipe_lexical_normalized(
            i,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            true,
            pipe_lexical,
        ),
        Some(FieldList::NamedBrace) | None => struct_item_with_pipe_lexical_normalized(
            i,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
            pipe_lexical,
        ),
    }
}

/// Scope-local pre-TypeApply candidate for shared named declaration fields.
/// The Item is already complete; only its bounded live suffix is observed.
pub(super) fn named_declaration_fields_next_field_candidate(
    i: RewriteIn,
    item: &Item,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || item.leading_view().is_grammar_empty()
        || indentation_after_newline(item.leading_view()).is_some()
        || !raw_name(item)
    {
        return false;
    }
    i.map(
        |lex: LexIn| {
            let TriviaObservation::Visible(observed) =
                observe_fenced_trivia(lex.remainder(), item_origin, line_entry, fence)
            else {
                return Some(false);
            };
            Some(
                observed.indentation.is_none()
                    && observed.source.starts_with(':')
                    && !observed.source.starts_with("::"),
            )
        },
        |candidate| candidate,
    )
    .unwrap_or(false)
}

fn indented_end(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || indentation_after_newline(item.leading_view()).is_some_and(|indent| indent < baseline)
        || is_active_stop(i.rb(), item, stops)
}

fn emit_missing_field(i: &mut RewriteIn, leading: LeadingTrivia, tuple: bool) {
    i.state.start_node(SyntaxKind::StructField.into());
    if tuple {
        i.state.start_node(SyntaxKind::TypeExpression.into());
    }
    emit_missing(i, leading);
    if tuple {
        i.state.finish_node();
    }
    i.state.finish_node();
}

fn emit_missing_field_item(i: &mut RewriteIn, item: &mut Item, tuple: bool) {
    i.state.start_node(SyntaxKind::StructField.into());
    if tuple {
        i.state.start_node(SyntaxKind::TypeExpression.into());
    }
    if !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    emit_missing(i, LeadingTrivia::default());
    if tuple {
        i.state.finish_node();
    }
    i.state.finish_node();
}

fn after_completed_normalized(
    i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = struct_item_normalized(
        i,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        false,
    );
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn struct_item_normalized(
    i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    struct_item_with_pipe_lexical_normalized(
        i,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        raw_identifier,
        type_vocabulary,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn struct_item_with_pipe_lexical_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
    pipe_lexical: bool,
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
                |mut lex, leading, origin, fence, _| {
                    if pipe_lexical && let Some(pipe) = lex.token(scan_exact_pipe) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(pipe),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    if raw_identifier && let Some(identifier) = lex.token(scan_identifier) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(identifier),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    if type_vocabulary {
                        scan_type_nud_payload(lex, leading, origin, fence)
                    } else {
                        scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                    }
                },
            )
        })
        .expect("Struct payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn header_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn body_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn field_boundary(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_active_stop(i.rb(), item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
        || delimited.is_some_and(|list| {
            matches!(
                token_kind(item),
                Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
            ) || token_kind(item) == Some(list.close())
        })
}

fn gstruct_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn body_starter_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::LParen | TokenKind::Colon)
    )
}

fn type_starter(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBrace
                | TokenKind::LBracket
                | TokenKind::Forall
                | TokenKind::EffectRowApostrophe
                | TokenKind::PolymorphicVariantColon
        )
    )
}

fn mismatched_close(item: &Item, expected: TokenKind) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && token_kind(item) != Some(expected)
}

fn raw_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn item_word(item: &Item) -> Option<&str> {
    let payload = item.payload_view();
    assert!(!payload.is_boundary(), "a boundary is not a word");
    (payload.token_kind() == Some(TokenKind::Identifier))
        .then(|| payload.spelling())
        .flatten()
}

fn emit_item_as(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Struct visibility was selected from exact words"),
    };
    emit_item_as(i, item, kind);
}
