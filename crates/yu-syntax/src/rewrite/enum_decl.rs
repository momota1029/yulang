//! Private direct `enum` declaration construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    declaration_companion::declaration_companion_normalized,
    declaration_variant::{VariantSequenceForm, declaration_variant_sequence_normalized},
    derives::{derives_clause_normalized, is_word},
    driver::{
        Either, NormalizedExit, advanced_origin, complete, handoff, implicit_delimited_newline,
        indentation_after_newline, is_active_stop, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    if_expr::active_statement_companion,
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, is_declaration_starter_word,
        scan_declaration_type_parameter, scan_identifier, scan_statement_payload,
        scan_type_nud_payload, source_declaration_head, source_identifier,
    },
    operator::{STOP_WITH, TriviaObservation, observe_fenced_trivia},
    statement::StatementLineHandoff,
    type_expr::TypeOuterBoundary,
    yumark::FenceBoundary,
};

type NameResult = Result<Option<Item>, Item>;

#[allow(clippy::too_many_arguments)]
pub(super) fn enum_declaration_witness(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !enum_source_selected_normalized(i.rb(), baseline, stops, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = enum_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        false,
    );
    enum_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        enum_declaration_normalized(
            i,
            intro,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
        )
    })
}

fn enum_source_selected_normalized(
    i: RewriteIn,
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
            if word == "enum" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_enum_candidate_normalized(
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

pub(super) fn enum_declaration_selected_normalized(
    i: RewriteIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("enum") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    observes(i, |source| {
        prefixed_enum_candidate_normalized(
            source,
            item_origin,
            fence,
            baseline,
            item_word(item) == Some("my"),
        )
    })
}

fn prefixed_enum_candidate_normalized(
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
    if word != "enum" {
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
pub(super) fn enum_declaration_normalized(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::EnumDeclaration.into());
    if item_word(&intro) == Some("enum") {
        emit_item_as(&mut i, intro, SyntaxKind::EnumKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = enum_item_normalized(
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
        debug_assert_eq!(item_word(&keyword), Some("enum"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::EnumKw);
    }

    let (first, next_origin, next_entry) = enum_item_normalized(
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
            let (item, item_origin, line_entry) = enum_item_normalized(
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
        ),
        Err(boundary) => complete(handoff(boundary), line_entry),
    };
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn required_name_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    item_origin: &mut usize,
    line_entry: &mut LineEntry,
    fence: Option<&FenceBoundary>,
) -> NameResult {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    if item.payload_view().is_eof() {
        item.emit_eof_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    if !declaration_gap_allowed(&item, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if body_starter(&item) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Ok(Some(item));
    }
    if header_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return Err(item);
    }
    if raw_name(&item) {
        emit_token_item(&mut i, item);
        return Ok(None);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let (mut next, next_origin, next_entry) = enum_item_normalized(
            i.rb(),
            *item_origin,
            *line_entry,
            fence,
            baseline,
            stops,
            true,
            true,
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
        if !declaration_gap_allowed(&next, baseline)
            || header_boundary(i.rb(), &next, baseline, stops)
        {
            i.state.finish_node();
            return Err(next);
        }
        if body_starter(&next) {
            i.state.finish_node();
            return Err(next);
        }
        if raw_name(&next) {
            next.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            emit_token_item(&mut i, next);
            return Ok(None);
        }
        item = next;
    }
}

fn parameters_normalized(
    mut i: RewriteIn,
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
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
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
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_body_item_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
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
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn parse_variant_body_normalized(
    mut i: RewriteIn,
    introducer: Item,
    form: VariantSequenceForm,
    yield_with: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = declaration_variant_sequence_normalized(
        i.rb(),
        form,
        introducer,
        yield_with,
        baseline,
        stops,
        item_origin,
        line_entry,
        fence,
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
            )
        }
        (
            VariantSequenceForm::EqualsInline,
            NormalizedExit::Complete(Err(Either::Left(item)), line_entry),
        ) if declaration_companion_start(i.rb(), &item, baseline, stops, line_handoff) => {
            declaration_companion_normalized(
                i,
                item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            )
        }
        (
            VariantSequenceForm::EqualsInline,
            NormalizedExit::Complete(Err(Either::Right(end)), line_entry),
        ) if declaration_companion_start(i.rb(), &end.item, baseline, stops, line_handoff) => {
            declaration_companion_normalized(
                i,
                end.item,
                baseline,
                stops,
                item_origin,
                line_entry,
                fence,
            )
        }
        (_, exit) => exit,
    }
}

#[allow(clippy::too_many_arguments)]
fn recover_body_introducer_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = enum_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            false,
            true,
        );
        if implicit_bodyless_boundary(i.rb(), &item, baseline, stops) {
            if item.payload_view().is_eof() {
                item.emit_eof_leading(&mut *i.state);
            }
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if body_starter(&item) {
            i.state.finish_node();
            return parse_body_item_normalized(
                i,
                item,
                baseline,
                stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn trailing_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = enum_item_normalized(
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
    )
}

#[allow(clippy::too_many_arguments)]
fn trailing_from_item_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
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
        );
    }
    complete(handoff(item), line_entry)
}

fn after_completed_normalized(
    i: RewriteIn,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, _, line_entry) = enum_item_normalized(
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
    mut i: RewriteIn,
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
    mut i: RewriteIn,
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
    mut i: RewriteIn,
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

fn implicit_bodyless_boundary(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
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

fn header_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
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
    mut i: RewriteIn,
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
fn enum_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
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
        .expect("Enum declaration payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn emit_item_as(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_parameter(i: &mut RewriteIn, parameter: Item) {
    let kind = match token_kind(&parameter) {
        Some(TokenKind::Identifier) => SyntaxKind::Identifier,
        Some(TokenKind::SigilIdentifier) => SyntaxKind::SigilIdentifier,
        _ => unreachable!("declaration parameter scanner returns identifiers"),
    };
    parameter.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Enum visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}

fn observes<F>(i: RewriteIn, predicate: F) -> bool
where
    F: FnOnce(&str) -> bool,
{
    i.map(
        |lex: LexIn| Some(predicate(lex.remainder())),
        |observed| observed,
    )
    .expect("source observation is total")
}
