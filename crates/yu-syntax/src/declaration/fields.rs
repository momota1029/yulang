//! Shared named and tuple field-list protocol for declaration owners.
//!
//! Struct, Enum, and Error select their recovery identities at this boundary;
//! nested Type recovery stays with the Type owner.

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::recovery::emit::{emit_recovery_error_run, emit_recovery_missing, emit_token_item},
    cursor::{LexIn, SyntaxIn},
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_exact_pipe, scan_identifier,
            scan_statement_payload, scan_type_nud_payload,
        },
        observation::{
            delimited_baseline, implicit_delimited_newline, indentation_after_newline,
            is_active_stop, is_active_stop_lex, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    syntax_kind::SyntaxKind,
    type_expr::{
        TypeApplyBoundary, required_type_expr_with_boundary_normalized, with_type_outer_close,
    },
};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum FieldList {
    NamedBrace,
    Tuple,
}

impl FieldList {
    pub(crate) fn close(self) -> TokenKind {
        match self {
            Self::NamedBrace => TokenKind::RBrace,
            Self::Tuple => TokenKind::RParen,
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum FieldOuterClose {
    Recover,
    Borrow,
}

pub(crate) struct DeclarationFieldExit {
    pub(crate) exit: NormalizedExit,
    pub(crate) item_origin: usize,
}

fn declaration_field_missing(i: &mut SyntaxIn, item: &Item, origin: usize) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at);
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum FieldErrorSlot {
    Start,
    Colon,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum FieldErrorExit {
    Colon,
    Type,
    Other,
}

#[allow(clippy::too_many_arguments)]
fn declaration_field_error_run(
    mut i: SyntaxIn,
    mut item: Item,
    slot: FieldErrorSlot,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry, FieldErrorExit) {
    let (item, item_origin, line_entry, exit) = emit_recovery_error_run(i.rb(), |run| {
        let exit = loop {
            run.emit_item_as(item, item_origin);
            (item, item_origin, line_entry) = run.lexical(|lex| {
                scan_declaration_item_lexical(
                    lex,
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops,
                    true,
                    false,
                    pipe_lexical,
                )
            });
            let colon = token_kind(&item) == Some(TokenKind::Colon)
                && indentation_after_newline(item.leading_view()).is_none();
            let type_retry =
                type_starter(&item) && indentation_after_newline(item.leading_view()).is_none();
            let boundary = item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || run.lexical(|lex| is_active_stop_lex(lex, &item, stops))
                || implicit_delimited_newline(baseline, item.leading_view())
                || matches!(
                    token_kind(&item),
                    Some(TokenKind::Comma | TokenKind::Semicolon)
                )
                || delimited.is_some_and(|list| {
                    matches!(
                        token_kind(&item),
                        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
                    ) || token_kind(&item) == Some(list.close())
                });
            if boundary {
                break FieldErrorExit::Other;
            }
            let stop = match slot {
                FieldErrorSlot::Start => colon || raw_name(&item),
                FieldErrorSlot::Colon => colon || type_retry,
            };
            if stop {
                if slot == FieldErrorSlot::Start && colon {
                    break FieldErrorExit::Colon;
                }
                if slot == FieldErrorSlot::Colon {
                    break if colon {
                        FieldErrorExit::Colon
                    } else if type_retry {
                        FieldErrorExit::Type
                    } else {
                        FieldErrorExit::Other
                    };
                }
                break FieldErrorExit::Other;
            }
        };
        (item, item_origin, line_entry, exit)
    });
    (item, item_origin, line_entry, exit)
}

/// Shared direct named/tuple declaration-field owner.  It consumes exactly
/// its own matching close; the enclosing declaration owner decides how to
/// acquire the successor after `Ok(())`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn declaration_fields_normalized(
    mut i: SyntaxIn,
    open: Item,
    owner_baseline: usize,
    stops: Stops,
    list: FieldList,
    outer_close: FieldOuterClose,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
        ambient,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn parse_indented_fields_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let Some(block_indent) = introduced_body_indentation_normalized(i.rb(), item_origin, fence)
    else {
        let (mut item, next_origin, next_entry) = declaration_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        emit_missing_field_item(&mut i, &mut item, next_origin, false, false);
        return complete(handoff(item), next_entry);
    };
    if block_indent <= baseline {
        let (mut item, next_origin, next_entry) = declaration_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        emit_missing_field_item(&mut i, &mut item, next_origin, false, false);
        return complete(handoff(item), next_entry);
    }
    let (mut item, item_origin, line_entry) = declaration_item_normalized(
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
        ambient,
    )
    .exit
}

#[allow(clippy::too_many_arguments)]
fn field_sequence_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    outer_close: FieldOuterClose,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> DeclarationFieldExit {
    let mut need_field = true;
    let mut after_comma = false;
    loop {
        if item.payload_view().is_boundary() {
            if let Some(list) = delimited {
                if after_comma
                    || (!need_field && implicit_delimited_newline(baseline, item.leading_view()))
                {
                    emit_missing_field_item(
                        &mut i,
                        &mut item,
                        item_origin,
                        list == FieldList::Tuple,
                        true,
                    );
                }
                emit_missing_close(&mut i, &item, item_origin);
            } else if need_field && !after_comma {
                emit_missing_field_item(&mut i, &mut item, item_origin, false, true);
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
                    emit_missing_field_item(
                        &mut i,
                        &mut item,
                        item_origin,
                        list == FieldList::Tuple,
                        true,
                    );
                } else {
                    item.emit_eof_leading(&mut *i.state);
                }
                emit_missing_close(&mut i, &item, item_origin);
            } else {
                item.emit_eof_leading(&mut *i.state);
                if need_field && !after_comma {
                    emit_missing_field_item(&mut i, &mut item, item_origin, false, true);
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
                    emit_missing_field_item(
                        &mut i,
                        &mut item,
                        item_origin,
                        list == FieldList::Tuple,
                        false,
                    );
                }
                emit_missing_close(&mut i, &item, item_origin);
                return DeclarationFieldExit {
                    exit: complete(handoff(item), line_entry),
                    item_origin,
                };
            }
        } else if indented_end(i.rb(), &item, baseline, stops) {
            if need_field && !after_comma {
                let emit_leading = item.payload_view().is_eof();
                emit_missing_field_item(&mut i, &mut item, item_origin, false, emit_leading);
            }
            return DeclarationFieldExit {
                exit: complete(handoff(item), line_entry),
                item_origin,
            };
        }

        if delimited.is_some_and(|list| mismatched_close(&item, list.close())) {
            if outer_close == FieldOuterClose::Borrow {
                emit_missing_close(&mut i, &item, item_origin);
                return DeclarationFieldExit {
                    exit: complete(handoff(item), line_entry),
                    item_origin,
                };
            }
            item.emit_all_remaining_leading(&mut *i.state);
            (item, item_origin, line_entry) = recover_close_normalized(
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
            continue;
        }

        if token_kind(&item) == Some(TokenKind::Comma) {
            if need_field {
                emit_missing_field_item(
                    &mut i,
                    &mut item,
                    item_origin,
                    delimited == Some(FieldList::Tuple),
                    true,
                );
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
            item.emit_all_remaining_leading(&mut *i.state);
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
            emit_missing_separator(&mut i, &item, item_origin);
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
                    ambient,
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
                    ambient,
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
                    ambient,
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
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (NormalizedExit, usize) {
    i.state.start_node(SyntaxKind::StructField.into());
    if raw_name(&item) {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = declaration_item_with_pipe_lexical_normalized(
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
        declaration_field_missing(&mut i, &item, item_origin);
    }

    if item.payload_view().is_boundary() {
        declaration_field_missing(&mut i, &item, item_origin);
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        declaration_field_missing(&mut i, &item, item_origin);
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }
    if token_kind(&item) == Some(TokenKind::Colon)
        && indentation_after_newline(item.leading_view()).is_none()
        && !is_active_stop(i.rb(), &item, stops)
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
            ambient,
        );
    }

    if indentation_after_newline(item.leading_view()).is_some() {
        declaration_field_missing(&mut i, &item, item_origin);
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }

    if type_starter(&item) && !is_active_stop(i.rb(), &item, stops) {
        item.emit_all_remaining_leading(&mut *i.state);
        declaration_field_missing(&mut i, &item, item_origin);
        let (exit, item_origin) = named_type_normalized(
            i.rb(),
            item,
            baseline,
            delimited,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        i.state.finish_node();
        return (exit, item_origin);
    }

    if field_boundary(i.rb(), &item, baseline, stops, delimited) {
        item.emit_all_remaining_leading(&mut *i.state);
        declaration_field_missing(&mut i, &item, item_origin);
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    let (item, item_origin, line_entry, exit) = declaration_field_error_run(
        i.rb(),
        item,
        FieldErrorSlot::Colon,
        baseline,
        stops,
        delimited,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    match exit {
        FieldErrorExit::Colon => {
            emit_token_item(&mut i, item);
            named_field_rhs_normalized(
                i,
                baseline,
                delimited,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        FieldErrorExit::Type => {
            let (exit, item_origin) = named_type_normalized(
                i.rb(),
                item,
                baseline,
                delimited,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            i.state.finish_node();
            (exit, item_origin)
        }
        FieldErrorExit::Other => {
            i.state.finish_node();
            (complete(handoff(item), line_entry), item_origin)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_named_field_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (NormalizedExit, usize) {
    i.state.start_node(SyntaxKind::StructField.into());
    let (item, item_origin, line_entry, exit) = declaration_field_error_run(
        i.rb(),
        item,
        FieldErrorSlot::Start,
        baseline,
        stops,
        delimited,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    if exit == FieldErrorExit::Colon {
        emit_token_item(&mut i, item);
        return named_field_rhs_normalized(
            i,
            baseline,
            delimited,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
    }
    i.state.finish_node();
    (complete(handoff(item), line_entry), item_origin)
}

#[allow(clippy::too_many_arguments)]
fn named_field_rhs_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (NormalizedExit, usize) {
    let (mut primary, item_origin, line_entry) = declaration_item_with_pipe_lexical_normalized(
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
        ambient,
    );
    i.state.finish_node();
    (exit, item_origin)
}

#[allow(clippy::too_many_arguments)]
fn named_type_normalized(
    mut i: SyntaxIn,
    primary: Item,
    baseline: usize,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
        ambient,
    );
    (exit, advanced_origin(item_origin, entry, i))
}

#[allow(clippy::too_many_arguments)]
fn tuple_field_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    (exit, item_origin)
}

#[allow(clippy::too_many_arguments)]
fn recover_separator_normalized(
    i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    field_sequence_error_run(
        i,
        item,
        baseline,
        stops,
        delimited,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        |item, delimited| {
            token_kind(item) == Some(TokenKind::Comma)
                || delimited.is_some_and(|list| token_kind(item) == Some(list.close()))
                || delimited.is_some_and(|list| mismatched_close(item, list.close()))
                || token_kind(item) == Some(TokenKind::Colon)
                || raw_name(item)
                || delimited == Some(FieldList::Tuple) && type_starter(item)
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn recover_close_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    // Only the Struct delimited Recover route reaches this owner. Keep one
    // transparent wrapper per maximal run, outside individual StructField nodes.
    i.state
        .start_node(SyntaxKind::StructFieldForeignClose.into());
    let exit = field_sequence_error_run(
        i.rb(),
        item,
        baseline,
        stops,
        delimited,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
        |item, delimited| {
            delimited.is_some_and(|list| token_kind(item) == Some(list.close()))
                || matches!(
                    token_kind(item),
                    Some(TokenKind::Comma | TokenKind::Semicolon | TokenKind::Colon)
                )
                || raw_name(item)
                || delimited == Some(FieldList::Tuple) && type_starter(item)
        },
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn field_sequence_error_run(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    retry: impl Fn(&Item, Option<FieldList>) -> bool,
) -> (Item, usize, LineEntry) {
    emit_recovery_error_run(i.rb(), |run| {
        loop {
            run.emit_item_as(item, item_origin);
            (item, item_origin, line_entry) = run.lexical(|lex| {
                scan_declaration_item_lexical(
                    lex,
                    item_origin,
                    line_entry,
                    fence,
                    baseline,
                    stops,
                    delimited != Some(FieldList::Tuple),
                    delimited == Some(FieldList::Tuple),
                    pipe_lexical,
                )
            });
            if item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || run.lexical(|lex| is_active_stop_lex(lex, &item, stops))
                || implicit_delimited_newline(baseline, item.leading_view())
                || retry(&item, delimited)
            {
                return (item, item_origin, line_entry);
            }
        }
    })
}

#[allow(clippy::too_many_arguments)]
fn field_item_normalized(
    i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
) -> (Item, usize, LineEntry) {
    match delimited {
        Some(FieldList::Tuple) => declaration_item_with_pipe_lexical_normalized(
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
        Some(FieldList::NamedBrace) | None => declaration_item_with_pipe_lexical_normalized(
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
pub(crate) fn named_declaration_fields_next_field_candidate(
    i: SyntaxIn,
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

fn indented_end(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_eof()
        || indentation_after_newline(item.leading_view()).is_some_and(|indent| indent < baseline)
        || is_active_stop(i.rb(), item, stops)
}

fn emit_missing_field_item(
    i: &mut SyntaxIn,
    item: &mut Item,
    item_origin: usize,
    tuple: bool,
    emit_leading: bool,
) {
    i.state.start_node(SyntaxKind::StructField.into());
    if tuple {
        i.state.start_node(SyntaxKind::TypeExpression.into());
    }
    if emit_leading && !item.payload_view().is_boundary() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
    declaration_field_missing(i, item, item_origin);
    if tuple {
        i.state.finish_node();
    }
    i.state.finish_node();
}

fn emit_missing_separator(i: &mut SyntaxIn, item: &Item, item_origin: usize) {
    declaration_field_missing(i, item, item_origin);
}

fn emit_missing_close(i: &mut SyntaxIn, item: &Item, item_origin: usize) {
    declaration_field_missing(i, item, item_origin);
}

#[allow(clippy::too_many_arguments)]
pub(super) fn declaration_item_normalized(
    i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    declaration_item_with_pipe_lexical_normalized(
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
pub(super) fn declaration_item_with_pipe_lexical_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
    pipe_lexical: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_declaration_item_lexical(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            raw_identifier,
            type_vocabulary,
            pipe_lexical,
        ))
    })
    .expect("declaration payload scanning is total")
}

#[allow(clippy::too_many_arguments)]
pub(super) fn scan_declaration_item_lexical(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
    pipe_lexical: bool,
) -> (Item, usize, LineEntry) {
    let (current, consumed) = i.with_str(|lex| {
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
        .expect("declaration payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("declaration coordinate fits usize"),
        current.next_line_entry,
    )
}

pub(super) fn field_boundary(
    mut i: SyntaxIn,
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

pub(super) fn type_starter(item: &Item) -> bool {
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

pub(super) fn mismatched_close(item: &Item, expected: TokenKind) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && token_kind(item) != Some(expected)
}

pub(super) fn raw_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}
