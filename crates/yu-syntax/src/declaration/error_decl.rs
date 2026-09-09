//! Private direct `error` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;
use crate::cursor::LexIn;
use crate::recovery_record::{
    DeclarationRole, ErrorDeclarationRole, ExpectationSources, ExpectedSyntax, GrammarRole,
    PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
    UnexpectedSyntax,
};
use std::sync::Arc;

use crate::syntax_kind::SyntaxKind;

use crate::{
    cursor::SyntaxIn,
    cursor::recovery::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    declaration::{
        declaration_companion::declaration_companion_normalized,
        declaration_variant::{VariantSequenceForm, declaration_variant_sequence_normalized},
        derives::{derives_clause_normalized, is_word},
    },
    expression::if_expr::active_statement_companion,
    handoff::{NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, is_declaration_starter_word,
            scan_declaration_type_parameter, scan_identifier, scan_statement_payload,
            scan_type_nud_payload, source_declaration_head, source_identifier,
        },
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop,
            is_active_stop_lex, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_WITH, Stops},
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
    type_expr::TypeOuterBoundary,
};

type NameResult = Result<Option<Item>, Item>;

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn error_declaration_witness(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !error_source_selected_normalized(i.rb(), baseline, stops, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = error_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        false,
    );
    error_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        error_declaration_normalized(
            i,
            intro,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            Some(AmbientClaimView::root_statement(baseline)).into(),
            Some(crate::sequence::SequenceOwner::RootStatement),
        )
    })
}

#[cfg(test)]
fn error_source_selected_normalized(
    i: SyntaxIn,
    baseline: usize,
    _stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            let source = lex.remainder();
            let TriviaObservation::Visible(observed) =
                observe_fenced_trivia(source, item_origin, line_entry, fence)
            else {
                return Some(false);
            };
            let Some((word, suffix)) = source_identifier(observed.source) else {
                return Some(false);
            };
            if word == "error" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_error_candidate_normalized(
                suffix,
                item_origin + leading_len + word.len(),
                fence,
                baseline,
                word == "my",
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

#[cfg(test)]
pub(crate) fn error_declaration_selected_normalized(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(error_declaration_selected_lexical(
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

pub(crate) fn error_declaration_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("error") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_error_candidate_normalized(
        source,
        item_origin,
        fence,
        baseline,
        item_word(item) == Some("my"),
    )
}

fn prefixed_error_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    require_head: bool,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
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
    let Some((word, after_keyword)) = source_identifier(observed.source) else {
        return false;
    };
    if word != "error" {
        return false;
    }
    if !require_head {
        return true;
    }
    let leading_len = source.len() - observed.source.len();
    let after_keyword_origin = item_origin + leading_len + word.len();
    let TriviaObservation::Visible(head) = observe_fenced_trivia(
        after_keyword,
        after_keyword_origin,
        LineEntry::InLine,
        fence,
    ) else {
        return false;
    };
    head.indentation
        .is_none_or(|indentation| indentation > baseline)
        && source_declaration_head(head.source)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn error_declaration_normalized(
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
    i.state.start_node(SyntaxKind::ErrorDeclaration.into());
    if item_word(&intro) == Some("error") {
        emit_item_as(&mut i, intro, SyntaxKind::ErrorKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = error_item_normalized(
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
        debug_assert!(declaration_gap_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("error"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::ErrorKw);
    }

    let (first, next_origin, next_entry) = error_item_normalized(
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
    let exit = match required_name_normalized(
        i.rb(),
        first,
        baseline,
        stops,
        &mut item_origin,
        &mut line_entry,
        fence,
    ) {
        Ok(None) => {
            parameters_normalized(i.rb(), &mut item_origin, &mut line_entry, fence);
            let (item, item_origin, line_entry) = error_item_normalized(
                i.rb(),
                item_origin,
                line_entry,
                fence,
                baseline,
                stops,
                false,
                true,
            );
            header_from_item_normalized(
                i.rb(),
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
        Ok(Some(body)) => parse_body_item_normalized(
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
        ),
        Err(boundary) => complete(handoff(boundary), line_entry),
    };
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn required_name_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> NameResult {
    if item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || !declaration_gap_allowed(&item, baseline)
        || (!body_starter(&item) && header_boundary(i.rb(), &item, baseline, stops))
    {
        emit_header_missing(i.rb(), &mut item, *item_origin);
        return Err(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if body_starter(&item) {
        emit_header_missing(i.rb(), &mut item, *item_origin);
        return Ok(Some(item));
    }
    if raw_name(&item) {
        emit_token_item(&mut i, item);
        return Ok(None);
    }
    (item, *item_origin, *line_entry) = retry_header(
        i.rb(),
        item,
        *item_origin,
        *line_entry,
        baseline,
        stops,
        fence,
        ErrorDeclarationRole::Name,
    );
    if header_boundary(i.rb(), &item, baseline, stops)
        || !declaration_gap_allowed(&item, baseline)
        || body_starter(&item)
    {
        if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
            item.emit_eof_leading(&mut *i.state);
        }
        return Err(item);
    }
    debug_assert!(raw_name(&item));
    emit_token_item(&mut i, item);
    Ok(None)
}

fn parameters_normalized(
    mut i: SyntaxIn,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) {
    let Some((parameter, next_origin, next_entry)) =
        parameter_item_normalized(i.rb(), *item_origin, *line_entry, fence)
    else {
        return;
    };
    *item_origin = next_origin;
    *line_entry = next_entry;
    i.state
        .start_node(SyntaxKind::DeclarationTypeParameterList.into());
    emit_parameter(&mut i, parameter);
    while let Some((parameter, next_origin, next_entry)) =
        parameter_item_normalized(i.rb(), *item_origin, *line_entry, fence)
    {
        *item_origin = next_origin;
        *line_entry = next_entry;
        emit_parameter(&mut i, parameter);
    }
    i.state.finish_node();
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
            header_role_boundary(),
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
    if implicit_bodyless_boundary(i.rb(), &item, baseline, stops) {
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    match token_kind(&item) {
        Some(TokenKind::Semicolon) => {
            emit_token_item(&mut i, item);
            after_completed_normalized(i, baseline, stops, item_origin, line_entry, fence)
        }
        Some(TokenKind::LBrace) => parse_variant_body_normalized(
            i,
            item,
            VariantSequenceForm::Braced,
            false,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        Some(TokenKind::Colon) => parse_variant_body_normalized(
            i,
            item,
            VariantSequenceForm::ColonIndented,
            false,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        ),
        Some(TokenKind::Equals) => {
            let form =
                if introduced_body_indentation_normalized(i.rb(), item_origin, fence).is_some() {
                    VariantSequenceForm::EqualsIndented
                } else {
                    VariantSequenceForm::EqualsInline
                };
            parse_variant_body_normalized(
                i,
                item,
                form,
                form == VariantSequenceForm::EqualsInline,
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
fn parse_variant_body_normalized(
    mut i: SyntaxIn,
    introducer: Item,
    form: VariantSequenceForm,
    yield_with: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = declaration_variant_sequence_normalized(
        i.rb(),
        crate::declaration::declaration_variant::VariantOwner::Error,
        form,
        introducer,
        yield_with,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match (form, exit) {
        (VariantSequenceForm::Braced, NormalizedExit::Complete(Ok(()), line_entry)) => {
            trailing_normalized(
                i,
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
        (_, exit) => exit,
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
    (item, item_origin, line_entry) = retry_header(
        i.rb(),
        item,
        item_origin,
        line_entry,
        baseline,
        stops,
        fence,
        ErrorDeclarationRole::BodyIntroducer,
    );
    if implicit_bodyless_boundary(i.rb(), &item, baseline, stops) {
        if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
            item.emit_eof_leading(&mut *i.state);
        }
        return complete(handoff(item), line_entry);
    }
    debug_assert!(body_starter(&item));
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
    let (item, item_origin, line_entry) = error_item_normalized(
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
            trailing_role_boundary(),
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

fn after_completed_normalized(
    i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = error_item_normalized(
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

fn header_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
        .with(TypeOuterBoundary::EQUALS)
        .with(TypeOuterBoundary::VARIANT_BODY)
}

fn trailing_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
}

fn implicit_bodyless_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || active_statement_companion(i, item, baseline, stops).is_some()
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn header_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn declaration_gap_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

fn body_starter(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Semicolon | TokenKind::LBrace | TokenKind::Colon | TokenKind::Equals)
    )
}

fn raw_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn parameter_spelling(parameter: &Item) -> bool {
    if token_kind(parameter) == Some(TokenKind::SigilIdentifier) {
        return true;
    }
    debug_assert_eq!(token_kind(parameter), Some(TokenKind::Identifier));
    let spelling = parameter
        .payload_view()
        .spelling()
        .expect("declaration parameter scanner returns identifiers");
    !is_declaration_starter_word(spelling)
        && !matches!(
            spelling,
            "for"
                | "realm"
                | "band"
                | "as"
                | "without"
                | "with"
                | "if"
                | "case"
                | "catch"
                | "where"
                | "elsif"
                | "else"
                | "derives"
        )
}

fn parameter_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<(Item, usize, LineEntry)> {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i.token(|lex| {
        let current = current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |mut lex, _, _, _, _| {
                let parameter = lex.token(scan_declaration_type_parameter)?;
                Some(AcceptedPayload {
                    payload: CurrentPayload::Token(parameter),
                    next_line_entry: LineEntry::InLine,
                })
            },
        )?;
        (!current.item.payload_view().is_boundary()
            && !current.item.payload_view().is_eof()
            && !current.item.leading_view().is_grammar_empty()
            && !current.item.leading_view().contains_line_break()
            && parameter_spelling(&current.item))
        .then_some(current)
    })?;
    Some((
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    ))
}

#[allow(clippy::too_many_arguments)]
fn error_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(error_item_lexical(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            raw_identifier,
            type_vocabulary,
        ))
    })
    .expect("header scan is total")
}

#[allow(clippy::too_many_arguments)]
fn error_item_lexical(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    let (
        CurrentItem {
            item,
            next_line_entry,
        },
        consumed,
    ) = i.with_str(|lex| {
        current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |mut lex, leading, origin, fence, _| {
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
        .expect("Error declaration payload scanning is total")
    });
    (item, item_origin + consumed.len(), next_line_entry)
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_parameter(i: &mut SyntaxIn, parameter: Item) {
    let kind = match token_kind(&parameter) {
        Some(TokenKind::Identifier) => SyntaxKind::Identifier,
        Some(TokenKind::SigilIdentifier) => SyntaxKind::SigilIdentifier,
        _ => unreachable!("declaration parameter scanner returns identifiers"),
    };
    parameter.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Error visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}

fn emit_header_missing(i: SyntaxIn, item: &mut Item, origin: usize) {
    if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
        item.emit_eof_leading(&mut *i.state);
    }
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        header_draft(
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            range,
            Arc::from([]),
        )
    });
}

fn header_draft(
    role: ErrorDeclarationRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected: &[ExpectedSyntax] = match role {
        ErrorDeclarationRole::Name => &[ExpectedSyntax::Identifier],
        ErrorDeclarationRole::BodyIntroducer => &[
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(
                crate::recovery_record::Delimiter::Brace,
            )),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Equals),
        ],
        _ => unreachable!("header recovery has two roles"),
    };
    let role = GrammarRole::Declaration(DeclarationRole::Error(role));
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

#[allow(clippy::too_many_arguments)]
fn retry_header(
    i: SyntaxIn,
    mut item: Item,
    mut origin: usize,
    mut line: LineEntry,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
    role: ErrorDeclarationRole,
) -> (Item, usize, LineEntry) {
    let name = role == ErrorDeclarationRole::Name;
    emit_recovery_error_run(
        i,
        |run| loop {
            let kind = match token_kind(&item).expect("header Error owns lexical Items") {
                TokenKind::Operator => SyntaxKind::Operator,
                kind => token_syntax_kind(kind),
            };
            let range = run.emit_item_as(item, origin, kind).recovery_range();
            run.append_unexpected(UnexpectedSyntax::Token {
                range,
                category: UnexpectedCategory::OtherCharacter,
            });
            (item, origin, line) = run.lexical(|lex| {
                error_item_lexical(lex, origin, line, fence, baseline, stops, name, true)
            });
            if item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || run.lexical(|lex| is_active_stop_lex(lex, &item, stops))
                || implicit_delimited_newline(baseline, item.leading_view())
                || matches!(
                    token_kind(&item),
                    Some(
                        TokenKind::Comma
                            | TokenKind::RParen
                            | TokenKind::RBracket
                            | TokenKind::RBrace
                    )
                )
                || (name && (!declaration_gap_allowed(&item, baseline) || raw_name(&item)))
                || body_starter(&item)
            {
                return (item, origin, line);
            }
        },
        |range, unexpected| header_draft(role, RecoveryKind::Error, range, unexpected),
    )
}
