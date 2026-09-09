//! Direct canonical equality-form `type` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
use crate::recovery_record::{
    DeclarationRole, ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence,
    RecoveryKind, RecoverySiteKey, SyntaxExpectation, TypeDeclarationRole, UnexpectedCategory,
    UnexpectedSyntax,
};
use std::sync::Arc;

use crate::syntax_kind::SyntaxKind;

use crate::{
    cursor::recovery::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    cursor::{LexIn, SyntaxIn},
    declaration::{
        declaration_companion::declaration_companion_normalized,
        derives::{derives_clause_normalized, is_word},
    },
    expression::if_expr::{ActiveStatementCompanion, active_statement_companion},
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            is_declaration_starter_word, scan_declaration_type_parameter, scan_identifier,
            scan_type_nud_payload, source_identifier,
        },
        observation::{
            implicit_delimited_newline, indentation_after_newline, is_active_stop,
            is_active_stop_lex, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_SEMICOLON, Stops},
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
    type_expr::{
        TypeOuterBoundary, is_type_caller_boundary,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
};

type NameResult = Result<Option<Item>, Item>;

pub(crate) fn type_declaration_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("type") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_type_candidate_normalized(source, item_origin, fence, baseline)
}

fn prefixed_type_candidate_normalized(
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
    observed.present
        && observed
            .indentation
            .is_none_or(|indentation| indentation > baseline)
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "type")
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn type_declaration_normalized(
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
    i.state.start_node(SyntaxKind::TypeDeclaration.into());
    if item_word(&intro) == Some("type") {
        emit_intro(&mut i, intro, SyntaxKind::TypeKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) =
            type_item_normalized(i.rb(), item_origin, line_entry, fence, true);
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(gtype_item_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("type"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_intro(&mut i, keyword, SyntaxKind::TypeKw);
    }

    let (first, next_origin, next_entry) =
        type_item_normalized(i.rb(), item_origin, line_entry, fence, true);
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
            definition_normalized(
                i.rb(),
                None,
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
        Ok(Some(equals)) => definition_normalized(
            i.rb(),
            Some(equals),
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

/// `Some(equals)` means the incomplete name slot reached a literal `=` and
/// the definition/RHS slots may continue without a second name diagnostic.
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
    if header_boundary(i.rb(), &item, baseline, stops)
        || item.leading_view().is_grammar_empty()
        || !gtype_item_allowed(&item, baseline)
    {
        emit_header_missing(i.rb(), &mut item, *item_origin, TypeDeclarationRole::Name);
        return Err(item);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if token_kind(&item) == Some(TokenKind::Equals) {
        emit_header_missing(i.rb(), &mut item, *item_origin, TypeDeclarationRole::Name);
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
        TypeDeclarationRole::Name,
    );
    if header_boundary(i.rb(), &item, baseline, stops) || !gtype_item_allowed(&item, baseline) {
        if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
            item.emit_eof_leading(&mut *i.state);
        }
        return Err(item);
    }
    emit_item_leading(&mut i, &mut item);
    if token_kind(&item) == Some(TokenKind::Equals) {
        return Ok(Some(item));
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
fn definition_normalized(
    mut i: SyntaxIn,
    pending: Option<Item>,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let name_was_incomplete = pending.is_some();
    let item = match pending {
        Some(item) => item,
        None => {
            let (item, next_origin, next_entry) =
                type_item_normalized(i.rb(), item_origin, line_entry, fence, false);
            item_origin = next_origin;
            line_entry = next_entry;
            item
        }
    };
    definition_from_item_normalized(
        i,
        item,
        name_was_incomplete,
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
fn definition_from_item_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    name_was_incomplete: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if !name_was_incomplete
        && derives_attachment_start(i.rb(), &item, baseline, stops, line_handoff)
    {
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
        return definition_from_item_normalized(
            i,
            next,
            false,
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
    if !name_was_incomplete
        && is_word(&item, "impl")
        && attachment_gap_continues(i.rb(), &item, baseline, stops, line_handoff)
    {
        return complete(handoff(item), line_entry);
    }
    if !name_was_incomplete
        && declaration_companion_start(i.rb(), &item, baseline, stops, line_handoff)
    {
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
    let companion = (!name_was_incomplete)
        .then(|| active_statement_companion(i.rb(), &item, baseline, stops))
        .flatten();
    match type_form(
        i.rb(),
        &item,
        baseline,
        stops,
        line_handoff,
        companion,
        name_was_incomplete,
    ) {
        TypeDeclarationForm::Equality => {
            emit_token_item(&mut i, item);
            return rhs_normalized(
                i,
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
        TypeDeclarationForm::Nominal(boundary) => {
            if boundary.type_owns_leading() {
                emit_item_leading(&mut i, &mut item);
            }
            return complete(handoff(item), line_entry);
        }
        TypeDeclarationForm::EqualityRecovery => {}
    }
    if !name_was_incomplete && !gtype_item_allowed(&item, baseline) {
        emit_header_missing(
            i.rb(),
            &mut item,
            item_origin,
            TypeDeclarationRole::DefinitionIntroducer,
        );
        return complete(handoff(item), line_entry);
    }
    if definition_boundary(i.rb(), &item, baseline, stops) {
        emit_header_missing(
            i.rb(),
            &mut item,
            item_origin,
            TypeDeclarationRole::DefinitionIntroducer,
        );
        return complete(handoff(item), line_entry);
    }
    item.emit_all_remaining_leading(&mut *i.state);
    if type_starter(&item) {
        emit_header_missing(
            i.rb(),
            &mut item,
            item_origin,
            TypeDeclarationRole::DefinitionIntroducer,
        );
        return rhs_item_normalized(
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

    (item, item_origin, line_entry) = retry_header(
        i.rb(),
        item,
        item_origin,
        line_entry,
        baseline,
        stops,
        fence,
        TypeDeclarationRole::DefinitionIntroducer,
    );
    if !gtype_item_allowed(&item, baseline) || definition_boundary(i.rb(), &item, baseline, stops) {
        if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
            item.emit_eof_leading(&mut *i.state);
        }
        return complete(handoff(item), line_entry);
    }
    emit_item_leading(&mut i, &mut item);
    if token_kind(&item) == Some(TokenKind::Equals) {
        emit_token_item(&mut i, item);
        return rhs_normalized(
            i,
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
    debug_assert!(type_starter(&item));
    rhs_item_normalized(
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
fn rhs_normalized(
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
    let (primary, item_origin, line_entry) =
        type_item_normalized(i.rb(), item_origin, line_entry, fence, false);
    rhs_item_normalized(
        i,
        primary,
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
fn rhs_item_normalized(
    mut i: SyntaxIn,
    mut primary: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    let caller_stops = stops | STOP_SEMICOLON;
    if !primary.payload_view().is_boundary()
        && !is_word(&primary, "derives")
        && !rhs_gap_is_outer_owned(&primary, baseline, caller_stops)
    {
        emit_item_leading(&mut i, &mut primary);
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
        i.rb(),
        primary,
        GrammarRole::Declaration(DeclarationRole::Type(TypeDeclarationRole::Rhs)),
        baseline,
        caller_stops,
        TypeOuterBoundary::DERIVES.with(TypeOuterBoundary::WITH),
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    trailing_after_type_normalized(
        i,
        exit,
        baseline,
        caller_stops,
        line_handoff,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
fn trailing_after_type_normalized(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            let (item, item_origin, line_entry) =
                type_item_normalized(i.rb(), item_origin, line_entry, fence, false);
            trailing_from_item_normalized(
                i,
                item,
                baseline,
                caller_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            trailing_from_item_normalized(
                i,
                item,
                baseline,
                caller_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            trailing_from_item_normalized(
                i,
                end.item,
                baseline,
                caller_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
                ambient,
                sequence,
            )
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer a declaration owner")
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn trailing_from_item_normalized(
    mut i: SyntaxIn,
    item: Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if declaration_companion_start(i.rb(), &item, baseline, caller_stops, line_handoff) {
        return declaration_companion_normalized(
            i,
            item,
            baseline,
            caller_stops,
            item_origin,
            line_entry,
            fence,
            ambient,
            sequence,
        );
    }
    if !derives_attachment_start(i.rb(), &item, baseline, caller_stops, line_handoff) {
        return complete(handoff(item), line_entry);
    }
    let (next, next_origin, next_entry) = derives_clause_normalized(
        i.rb(),
        item,
        baseline,
        caller_stops,
        line_handoff,
        trailing_role_boundary(),
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    trailing_from_item_normalized(
        i,
        next,
        baseline,
        caller_stops,
        line_handoff,
        next_origin,
        next_entry,
        fence,
        ambient,
        sequence,
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeDeclarationForm {
    Equality,
    Nominal(NominalBoundary),
    EqualityRecovery,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NominalBoundary {
    FencedBoundary,
    SameLineTerminal,
    EofOwnedTrivia,
    OrdinaryLayoutNewline,
    BracedStatementSequenceNewline,
    CatchArmSequenceNewlineThroughInlineCanonicalStatement,
    ActiveFixed,
    AmbientCompanion,
}

impl NominalBoundary {
    fn type_owns_leading(self) -> bool {
        matches!(self, Self::SameLineTerminal | Self::EofOwnedTrivia)
    }
}

fn type_form(
    mut i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    companion: Option<ActiveStatementCompanion>,
    name_was_incomplete: bool,
) -> TypeDeclarationForm {
    if name_was_incomplete {
        debug_assert_eq!(token_kind(item), Some(TokenKind::Equals));
        return TypeDeclarationForm::Equality;
    }
    if item.payload_view().is_boundary() {
        return TypeDeclarationForm::Nominal(NominalBoundary::FencedBoundary);
    }
    if companion.is_some() {
        return TypeDeclarationForm::Nominal(NominalBoundary::AmbientCompanion);
    }
    if token_kind(item) == Some(TokenKind::Equals) && gtype_item_allowed(item, baseline) {
        return TypeDeclarationForm::Equality;
    }
    if let Some(indentation) = indentation_after_newline(item.leading_view()) {
        return match line_handoff {
            StatementLineHandoff::OrdinaryLayout if indentation <= baseline => {
                TypeDeclarationForm::Nominal(NominalBoundary::OrdinaryLayoutNewline)
            }
            StatementLineHandoff::BracedStatementSequence => {
                TypeDeclarationForm::Nominal(NominalBoundary::BracedStatementSequenceNewline)
            }
            StatementLineHandoff::CatchArmSequenceThroughInlineCanonicalStatement => {
                TypeDeclarationForm::Nominal(
                    NominalBoundary::CatchArmSequenceNewlineThroughInlineCanonicalStatement,
                )
            }
            StatementLineHandoff::OrdinaryLayout if item.payload_view().is_eof() => {
                TypeDeclarationForm::Nominal(NominalBoundary::EofOwnedTrivia)
            }
            StatementLineHandoff::CatchBracedArm | StatementLineHandoff::OrdinaryLayout => {
                TypeDeclarationForm::EqualityRecovery
            }
        };
    }
    if item.payload_view().is_eof() || token_kind(item) == Some(TokenKind::Semicolon) {
        return TypeDeclarationForm::Nominal(NominalBoundary::SameLineTerminal);
    }
    if is_type_caller_boundary(item, stops)
        || (is_active_stop(i.rb(), item, stops)
            && matches!(
                token_kind(item),
                Some(
                    TokenKind::Comma | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
                )
            ))
    {
        return TypeDeclarationForm::Nominal(NominalBoundary::ActiveFixed);
    }
    TypeDeclarationForm::EqualityRecovery
}

fn rhs_gap_is_outer_owned(item: &Item, baseline: usize, caller_stops: Stops) -> bool {
    implicit_delimited_newline(baseline, item.leading_view())
        || is_word(item, "with")
        || (is_type_caller_boundary(item, caller_stops)
            && token_kind(item) != Some(TokenKind::Semicolon))
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
        && !is_type_caller_boundary(item, stops)
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
        && active_statement_companion(i.rb(), item, baseline, stops).is_none()
        && indentation_after_newline(item.leading_view()).is_none_or(|indentation| {
            matches!(line_handoff, StatementLineHandoff::OrdinaryLayout) && indentation > baseline
        })
}

fn header_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
        .with(TypeOuterBoundary::IMPL)
        .with(TypeOuterBoundary::EQUALS)
}

fn trailing_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
}

fn header_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    i.token(|lex| Some(header_boundary_lex(lex, item, baseline, stops)))
        .expect("header observation is total")
}

fn header_boundary_lex(i: LexIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || implicit_delimited_newline(baseline, item.leading_view())
        || is_active_stop_lex(i, item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn definition_boundary(mut i: SyntaxIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    header_boundary(i.rb(), item, baseline, stops)
        || item_word(item).is_some_and(|word| {
            matches!(word, "with" | "derives") || is_declaration_starter_word(word)
        })
}

fn gtype_item_allowed(item: &Item, baseline: usize) -> bool {
    !implicit_delimited_newline(baseline, item.leading_view())
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

fn emit_parameter(i: &mut SyntaxIn, parameter: Item) {
    let kind = match token_kind(&parameter) {
        Some(TokenKind::Identifier) => SyntaxKind::Identifier,
        Some(TokenKind::SigilIdentifier) => SyntaxKind::SigilIdentifier,
        _ => unreachable!("declaration parameter scanner returns identifiers"),
    };
    parameter.emit_remaining(&mut *i.state, kind);
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

fn raw_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
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

fn type_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    raw_identifier: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(type_item_lexical(
            lex,
            item_origin,
            line_entry,
            fence,
            raw_identifier,
        ))
    })
    .expect("header scanner is total")
}

fn type_item_lexical(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    raw_identifier: bool,
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
                scan_type_nud_payload(lex, leading, origin, fence)
            },
        )
        .expect("Type declaration payload scanning is total")
    });
    (
        item,
        item_origin
            .checked_add(consumed.len())
            .expect("header coordinate fits usize"),
        next_line_entry,
    )
}

fn emit_header_missing(i: SyntaxIn, item: &mut Item, origin: usize, role: TypeDeclarationRole) {
    if item.payload_view().is_eof() && !item.payload_view().is_boundary() {
        item.emit_eof_leading(&mut *i.state);
    }
    let at = item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        header_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn header_draft(
    role: TypeDeclarationRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        TypeDeclarationRole::Name => ExpectedSyntax::Identifier,
        TypeDeclarationRole::DefinitionIntroducer => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Equals)
        }
        _ => unreachable!("header recovery has two roles"),
    };
    let role = GrammarRole::Declaration(DeclarationRole::Type(role));
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

#[allow(clippy::too_many_arguments)]
fn retry_header(
    i: SyntaxIn,
    mut item: Item,
    mut origin: usize,
    mut line: LineEntry,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
    role: TypeDeclarationRole,
) -> (Item, usize, LineEntry) {
    let name = role == TypeDeclarationRole::Name;
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
            (item, origin, line) =
                run.lexical(|lex| type_item_lexical(lex, origin, line, fence, name));
            if run.lexical(|lex| header_boundary_lex(lex, &item, baseline, stops))
                || (!name
                    && item_word(&item).is_some_and(|word| {
                        matches!(word, "with" | "derives") || is_declaration_starter_word(word)
                    }))
                || token_kind(&item) == Some(TokenKind::Equals)
                || if name {
                    raw_name(&item)
                } else {
                    type_starter(&item)
                }
            {
                return (item, origin, line);
            }
        },
        |range, unexpected| header_draft(role, RecoveryKind::Error, range, unexpected),
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn emit_intro(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.payload_view().token_kind().is_some());
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Type visibility uses exact declaration words"),
    };
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_item_leading(i: &mut SyntaxIn, item: &mut Item) {
    item.emit_all_remaining_leading(&mut *i.state);
}
