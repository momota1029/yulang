//! Direct canonical `struct` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
use crate::cst_output::RecoveryDraft;
use reborrow_generic::Reborrow as _;
use std::{cell::Cell, sync::Arc};

use crate::{
    recovery_record::{
        DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StructRole, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::emit::{
        emit_missing, emit_recovery_error_run, emit_recovery_missing, emit_token_item,
        token_syntax_kind,
    },
    cursor::{LexIn, SyntaxIn},
    declaration::{
        declaration_companion::declaration_companion_normalized,
        derives::{derives_clause_normalized, is_word},
    },
    expression::if_expr::active_statement_companion,
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_exact_pipe, scan_identifier,
            scan_statement_payload, scan_type_nud_payload, source_identifier,
        },
        observation::{
            delimited_baseline, implicit_delimited_newline, indentation_after_newline,
            is_active_stop, is_active_stop_lex, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_WITH, Stops},
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
    type_expr::{
        TypeApplyBoundary, TypeOuterBoundary, required_type_expr_with_boundary_normalized,
        with_type_outer_close,
    },
};

#[cfg(test)]
pub(crate) fn struct_declaration_selected_normalized(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(struct_declaration_selected_lexical(
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

pub(crate) fn struct_declaration_selected_lexical(
    source: &str,
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
    prefixed_struct_candidate_normalized(source, item_origin, fence, baseline)
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
pub(crate) fn struct_declaration_normalized(
    mut i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
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

    let exit = header_from_item_normalized(
        i.rb(),
        body,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn header_from_item_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if stops & STOP_WITH != 0 && is_word(&item, "with") {
        return complete(handoff(item), line_entry);
    }
    if derives_attachment_start(i.rb(), &item, baseline, stops, line_handoff) {
        let (next, next_origin, next_entry) = derives_clause_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            line_handoff,
            struct_header_role_boundary(),
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        return header_from_item_normalized(
            i,
            next,
            baseline,
            stops,
            line_handoff,
            next_origin,
            next_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if declaration_companion_start(i.rb(), &item, baseline, stops, line_handoff) {
        return declaration_companion_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    parse_body_item_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

/// `Ok(Some)` carries a local body starter. `Err` is an unchanged caller
/// boundary. An accepted raw name returns `Ok(None)` at the live suffix.
#[allow(clippy::too_many_arguments)]
fn required_name_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> Result<Option<Item>, Item> {
    if item.payload_view().is_boundary()
        || !gstruct_allowed(&item, baseline)
        || is_active_stop(i.rb(), &item, stops)
    {
        header_missing(&mut i, &item, *item_origin, StructRole::Name);
        return Err(item);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        header_missing(&mut i, &item, *item_origin, StructRole::Name);
        return Err(item);
    }
    if body_starter_item(&item) {
        header_missing(&mut i, &item, *item_origin, StructRole::Name);
        item.emit_all_remaining_leading(&mut *i.state);
        return Ok(Some(item));
    }
    if header_boundary(i.rb(), &item, baseline, stops) {
        header_missing(&mut i, &item, *item_origin, StructRole::Name);
        return Err(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if raw_name(&item) {
        emit_item_as(&mut i, item, SyntaxKind::Identifier);
        return Ok(None);
    }

    let (mut next, origin, line) = header_error_run(
        i.rb(),
        item,
        StructRole::Name,
        baseline,
        stops,
        *item_origin,
        *line_entry,
        fence,
    );
    *item_origin = origin;
    *line_entry = line;
    if next.payload_view().is_boundary()
        || next.payload_view().is_eof()
        || !gstruct_allowed(&next, baseline)
        || is_active_stop(i.rb(), &next, stops)
    {
        return Err(next);
    }
    if body_starter_item(&next) {
        return Ok(Some(next));
    }
    if header_boundary(i.rb(), &next, baseline, stops) {
        return Err(next);
    }
    next.emit_all_remaining_leading(&mut *i.state);
    emit_item_as(&mut i, next, SyntaxKind::Identifier);
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn parse_body_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary()
        || !gstruct_allowed(&item, baseline)
        || is_active_stop(i.rb(), &item, stops)
    {
        header_missing(&mut i, &item, item_origin, StructRole::BodyIntroducer);
        return complete(handoff(item), line_entry);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        header_missing(&mut i, &item, item_origin, StructRole::BodyIntroducer);
        return complete(handoff(item), line_entry);
    }
    if !body_starter_item(&item) && body_boundary(i.rb(), &item, baseline, stops) {
        header_missing(&mut i, &item, item_origin, StructRole::BodyIntroducer);
        return complete(handoff(item), line_entry);
    }
    let gap = item.extent(item_origin).recovery_range().start;
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
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        Some(TokenKind::LParen) => parse_delimited_fields_normalized(
            i,
            item,
            baseline,
            stops,
            FieldList::Tuple,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        Some(TokenKind::Colon) => {
            emit_token_item(&mut i, item);
            parse_indented_fields_normalized(
                i,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
                ambient,
            )
        }
        _ if body_boundary(i.rb(), &item, baseline, stops) || type_starter(&item) => {
            emit_recovery_missing(i.rb(), LeadingTrivia::default(), gap, |range| {
                header_draft(
                    StructRole::BodyIntroducer,
                    RecoveryKind::Missing,
                    range,
                    Arc::from([]),
                )
            });
            complete(handoff(item), line_entry)
        }
        _ => recover_body_introducer_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    (item, item_origin, line_entry) = header_error_run(
        i.rb(),
        item,
        StructRole::BodyIntroducer,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
    );
    if !item.payload_view().is_boundary()
        && !item.payload_view().is_eof()
        && gstruct_allowed(&item, baseline)
        && !is_active_stop(i.rb(), &item, stops)
        && body_starter_item(&item)
    {
        return parse_body_item_normalized(
            i,
            item,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    complete(handoff(item), line_entry)
}

fn header_draft(
    slot: StructRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Declaration(DeclarationRole::Struct(slot));
    let expected: &[ExpectedSyntax] = match slot {
        StructRole::Name => &[ExpectedSyntax::Identifier],
        StructRole::BodyIntroducer => &[
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Parenthesis)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ],
        _ => unreachable!("Struct header slot"),
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expected
            .iter()
            .map(|expected| SyntaxExpectation {
                role,
                expected: *expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .collect::<Vec<_>>()
            .into(),
        0,
    )
}

fn header_missing(i: &mut SyntaxIn, item: &Item, origin: usize, role: StructRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        header_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

#[allow(clippy::too_many_arguments)]
fn header_error_run(
    mut i: SyntaxIn,
    mut item: Item,
    role: StructRole,
    baseline: usize,
    stops: Stops,
    mut origin: usize,
    mut line: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let start = item.extent(origin).recovery_range().start;
    emit_recovery_error_run(
        i.rb(),
        |run| loop {
            let kind = token_kind(&item)
                .map(token_syntax_kind)
                .unwrap_or(SyntaxKind::Operator);
            let end = run.emit_item_as(item, origin, kind).recovery_range().end;
            (item, origin, line) = run.lexical(|lex| {
                scan_struct_item_lexical(
                    lex,
                    origin,
                    line,
                    fence,
                    baseline,
                    stops,
                    role == StructRole::Name,
                    role != StructRole::Name,
                    false,
                )
            });
            let boundary = item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || !gstruct_allowed(&item, baseline)
                || run.lexical(|lex| {
                    crate::lexical::observation::is_active_stop_lex(lex, &item, stops)
                })
                || matches!(
                    token_kind(&item),
                    Some(
                        TokenKind::Comma
                            | TokenKind::RParen
                            | TokenKind::RBracket
                            | TokenKind::RBrace
                    )
                );
            if boundary
                || body_starter_item(&item)
                || (if role == StructRole::Name {
                    raw_name(&item)
                } else {
                    type_starter(&item)
                })
            {
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: start..end,
                    category: UnexpectedCategory::OtherCharacter,
                });
                return (item, origin, line);
            }
        },
        |range, unexpected| header_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn declaration_field_draft(
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

fn declaration_field_missing(
    i: &mut SyntaxIn,
    item: &Item,
    origin: usize,
    role: GrammarRole,
    expected: ExpectedSyntax,
) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i.rb(), LeadingTrivia::default(), at, |range| {
        declaration_field_draft(role, expected, RecoveryKind::Missing, range, Arc::from([]))
    });
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
    roles: DeclarationFieldRoles,
    slot: FieldErrorSlot,
    baseline: usize,
    stops: Stops,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry, FieldErrorExit) {
    let role = Cell::new(roles.field);
    let expected = Cell::new(ExpectedSyntax::Identifier);
    let (item, item_origin, line_entry, exit) = emit_recovery_error_run(
        i.rb(),
        |run| {
            let exit = loop {
                let kind = token_kind(&item)
                    .map(token_syntax_kind)
                    .unwrap_or(SyntaxKind::Operator);
                let range = run.emit_item_as(item, item_origin, kind).recovery_range();
                run.append_unexpected(UnexpectedSyntax::Token {
                    range,
                    category: UnexpectedCategory::OtherCharacter,
                });
                (item, item_origin, line_entry) = run.lexical(|lex| {
                    scan_struct_item_lexical(
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
                    if slot == FieldErrorSlot::Colon {
                        role.set(roles.field_colon);
                        expected.set(ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
                    }
                    break FieldErrorExit::Other;
                }
                let stop = match slot {
                    FieldErrorSlot::Start => colon || raw_name(&item),
                    FieldErrorSlot::Colon => colon || type_retry,
                };
                if stop {
                    if slot == FieldErrorSlot::Start && colon {
                        role.set(roles.field_name);
                        expected.set(ExpectedSyntax::Identifier);
                        break FieldErrorExit::Colon;
                    }
                    if slot == FieldErrorSlot::Colon {
                        role.set(roles.field_colon);
                        expected.set(ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
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
        },
        |range, unexpected| {
            declaration_field_draft(
                role.get(),
                expected.get(),
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    );
    (item, item_origin, line_entry, exit)
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum FieldList {
    NamedBrace,
    Tuple,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum FieldOuterClose {
    Recover,
    Borrow,
}

/// Finite recovery identities supplied by a declaration that reuses the
/// canonical field driver. Nested Type recovery remains Type-owned.
#[derive(Clone, Copy)]
pub(crate) struct DeclarationFieldRoles {
    pub(crate) field: GrammarRole,
    pub(crate) field_name: GrammarRole,
    pub(crate) field_colon: GrammarRole,
    pub(crate) field_type: GrammarRole,
}

fn struct_field_roles() -> DeclarationFieldRoles {
    let role = |slot| GrammarRole::Declaration(DeclarationRole::Struct(slot));
    DeclarationFieldRoles {
        field: role(StructRole::Field),
        field_name: role(StructRole::FieldName),
        field_colon: role(StructRole::FieldColon),
        field_type: role(StructRole::FieldType),
    }
}

pub(crate) struct DeclarationFieldExit {
    pub(crate) exit: NormalizedExit,
    pub(crate) item_origin: usize,
}

impl FieldList {
    fn close(self) -> TokenKind {
        match self {
            Self::NamedBrace => TokenKind::RBrace,
            Self::Tuple => TokenKind::RParen,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_delimited_fields_normalized(
    mut i: SyntaxIn,
    open: Item,
    owner_baseline: usize,
    stops: Stops,
    list: FieldList,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let result = declaration_fields_normalized(
        i.rb(),
        struct_field_roles(),
        open,
        owner_baseline,
        stops,
        list,
        FieldOuterClose::Recover,
        false,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    match result.exit {
        NormalizedExit::Complete(Ok(()), line_entry) => trailing_normalized(
            i,
            owner_baseline,
            stops,
            line_handoff,
            result.item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        exit => exit,
    }
}

/// Shared direct named/tuple declaration-field owner.  It consumes exactly
/// its own matching close; the enclosing declaration owner decides how to
/// acquire the successor after `Ok(())`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn declaration_fields_normalized(
    mut i: SyntaxIn,
    roles: DeclarationFieldRoles,
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
        roles,
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
fn parse_indented_fields_normalized(
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
        struct_field_roles(),
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
    roles: DeclarationFieldRoles,
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
                    roles,
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
                    roles.field_type,
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
                    roles,
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
    roles: DeclarationFieldRoles,
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
        declaration_field_missing(
            &mut i,
            &item,
            item_origin,
            roles.field_name,
            ExpectedSyntax::Identifier,
        );
    }

    if item.payload_view().is_boundary() {
        declaration_field_missing(
            &mut i,
            &item,
            item_origin,
            roles.field_colon,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        );
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        declaration_field_missing(
            &mut i,
            &item,
            item_origin,
            roles.field_colon,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        );
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
            roles.field_type,
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
        declaration_field_missing(
            &mut i,
            &item,
            item_origin,
            roles.field_colon,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        );
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }

    if type_starter(&item) && !is_active_stop(i.rb(), &item, stops) {
        item.emit_all_remaining_leading(&mut *i.state);
        declaration_field_missing(
            &mut i,
            &item,
            item_origin,
            roles.field_colon,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        );
        let (exit, item_origin) = named_type_normalized(
            i.rb(),
            roles.field_type,
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
        declaration_field_missing(
            &mut i,
            &item,
            item_origin,
            roles.field_colon,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        );
        i.state.finish_node();
        return (complete(handoff(item), line_entry), item_origin);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    let (item, item_origin, line_entry, exit) = declaration_field_error_run(
        i.rb(),
        item,
        roles,
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
                roles.field_type,
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
                roles.field_type,
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
    roles: DeclarationFieldRoles,
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
        roles,
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
            roles.field_type,
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
    missing_type_role: GrammarRole,
    baseline: usize,
    delimited: Option<FieldList>,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
        missing_type_role,
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
    missing_type_role: GrammarRole,
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
        missing_type_role,
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
    missing_type_role: GrammarRole,
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
        missing_type_role,
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
    mut i: SyntaxIn,
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

fn emit_missing_field(i: &mut SyntaxIn, leading: LeadingTrivia, tuple: bool) {
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

fn emit_missing_field_item(i: &mut SyntaxIn, item: &mut Item, tuple: bool) {
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
    i: SyntaxIn,
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
fn trailing_normalized(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = struct_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        false,
    );
    trailing_from_item_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn trailing_from_item_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if derives_attachment_start(i.rb(), &item, baseline, stops, line_handoff) {
        let (next, next_origin, next_entry) = derives_clause_normalized(
            i.rb(),
            item,
            baseline,
            stops,
            line_handoff,
            struct_trailing_role_boundary(),
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        return trailing_from_item_normalized(
            i,
            next,
            baseline,
            stops,
            line_handoff,
            next_origin,
            next_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if declaration_companion_start(i.rb(), &item, baseline, stops, line_handoff) {
        return declaration_companion_normalized(
            i,
            item,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn struct_item_normalized(
    i: SyntaxIn,
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
        Some(scan_struct_item_lexical(
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
    .expect("Struct payload scanning is total")
}

#[allow(clippy::too_many_arguments)]
fn scan_struct_item_lexical(
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
        .expect("Struct payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("Struct coordinate fits usize"),
        current.next_line_entry,
    )
}

fn header_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
}

fn body_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
}

fn derives_attachment_start(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    !item.payload_view().is_boundary()
        && is_word(item, "derives")
        && attachment_gap_continues(i.rb(), item, baseline, stops, line_handoff)
}

fn declaration_companion_start(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    is_word(item, "with")
        && item.leading_view().has_ordinary_trivia()
        && attachment_gap_continues(i.rb(), item, baseline, stops, line_handoff)
}

fn attachment_gap_continues(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    !item.payload_view().is_boundary()
        && !is_active_stop(i.rb(), item, stops)
        && !(stops & STOP_WITH != 0 && is_word(item, "with"))
        && active_statement_companion(i.rb(), item, baseline, stops).is_none()
        && indentation_after_newline(item.leading_view()).is_none_or(|indentation| {
            matches!(line_handoff, StatementLineHandoff::OrdinaryLayout) && indentation > baseline
        })
}

fn struct_header_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
        .with(TypeOuterBoundary::STRUCT_BODY)
}

fn struct_trailing_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
}

fn field_boundary(
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

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Struct visibility was selected from exact words"),
    };
    emit_item_as(i, item, kind);
}
