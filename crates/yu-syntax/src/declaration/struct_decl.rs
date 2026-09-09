//! Direct canonical `struct` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
use crate::cursor::recovery::RecoveryDraft;
use std::sync::Arc;

use crate::{
    recovery_record::{
        ConstructRole, DeclarationRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StructRole, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cursor::SyntaxIn,
    cursor::recovery::emit::{
        emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
    },
    declaration::{
        declaration_companion::declaration_companion_normalized,
        derives::{derives_clause_normalized, is_word},
        fields::{
            DeclarationFieldRoles, FieldList, FieldOuterClose, declaration_fields_normalized,
            declaration_item_normalized, parse_indented_fields_normalized, raw_name,
            scan_declaration_item_lexical, type_starter,
        },
    },
    expression::if_expr::active_statement_companion,
    handoff::{NormalizedExit, complete, handoff},
    lexical::{
        current_item::LineEntry,
        item::{Item, LeadingTrivia, TokenKind},
        lexer::source_identifier,
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop, token_kind,
        },
        stops::{STOP_WITH, Stops},
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
    type_expr::TypeOuterBoundary,
};

#[cfg(test)]
use crate::cursor::LexIn;

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
        let (mut keyword, next_origin, next_entry) = declaration_item_normalized(
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

    let (first, next_origin, next_entry) = declaration_item_normalized(
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
            let (body, next_origin, next_entry) = declaration_item_normalized(
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
                struct_field_roles(FieldList::NamedBrace),
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
                scan_declaration_item_lexical(
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

fn struct_field_roles(list: FieldList) -> DeclarationFieldRoles {
    let role = |slot| GrammarRole::Declaration(DeclarationRole::Struct(slot));
    DeclarationFieldRoles {
        field: role(StructRole::Field),
        field_name: role(StructRole::FieldName),
        field_colon: role(StructRole::FieldColon),
        field_type: role(StructRole::FieldType),
        field_separator: role(StructRole::FieldSeparator),
        close: GrammarRole::ClosingDelimiter {
            owner: match list {
                FieldList::NamedBrace => ConstructRole::StructNamedFields,
                FieldList::Tuple => ConstructRole::StructTupleFields,
            },
            delimiter: list.delimiter(),
        },
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
        struct_field_roles(list),
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

fn after_completed_normalized(
    i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = declaration_item_normalized(
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
    let (item, item_origin, line_entry) = declaration_item_normalized(
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

fn gstruct_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn body_starter_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::LParen | TokenKind::Colon)
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
