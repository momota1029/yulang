//! Direct canonical equality-form `type` declaration construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn, Stops,
    derives::{derives_clause, is_word},
    driver::{
        Either, TailExit, handoff, implicit_delimited_newline, indentation_after_newline,
        is_active_stop, token_kind,
    },
    emit::{emit_leading_trivia, emit_missing, emit_token_item},
    if_expr::{ActiveStatementCompanion, active_statement_companion},
    item::{Item, LeadingTrivia, Payload, Token, TokenKind},
    lexer::{
        declaration_type_header_item_after_trivia, is_declaration_starter_word,
        scan_declaration_type_parameter, scan_identifier, scan_trivia, source_identifier,
        statement_item_after_trivia, type_nud_item_after_trivia,
    },
    operator::{STOP_SEMICOLON, STOP_WITH, source_after_trivia},
    statement::StatementLineHandoff,
    type_expr::{
        TypeOuterBoundary, is_type_caller_boundary,
        required_type_expr_with_caller_stops_and_outer_boundary,
    },
};

type NameResult = Result<Option<Item>, Item>;

pub(super) fn type_declaration_selected(i: RewriteIn, item: &Item, baseline: usize) -> bool {
    if item_word(item) == Some("type") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    observes(i, |source| prefixed_type_candidate(source, baseline))
}

pub(super) fn type_declaration(
    mut i: RewriteIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    debug_assert!(type_declaration_selected(i.rb(), &intro, baseline));
    i.state.start_node(SyntaxKind::TypeDeclaration.into());
    if item_word(&intro) == Some("type") {
        emit_intro(&mut i, intro, SyntaxKind::TypeKw);
    } else {
        emit_visibility(&mut i, intro);
        let accepted = emit_gtype(i.rb(), baseline, true);
        debug_assert!(accepted);
        let keyword = i
            .token(|lex| scan_exact_identifier(lex, "type"))
            .expect("visibility-led selection proved exact `type`");
        i.state.token(SyntaxKind::TypeKw.into(), &keyword.text);
    }

    let exit = if !emit_gtype(i.rb(), baseline, true) {
        emit_missing(&mut i, LeadingTrivia::default());
        handoff(scan_pending_item(i.rb(), baseline, stops))
    } else {
        match required_name(i.rb(), baseline, stops) {
            Ok(None) => {
                parameters(i.rb());
                definition(i.rb(), None, baseline, stops, line_handoff)
            }
            Ok(Some(equals)) => definition(i.rb(), Some(equals), baseline, stops, line_handoff),
            Err(boundary) => handoff(boundary),
        }
    };
    i.state.finish_node();
    exit
}

/// `Some(equals)` means the incomplete name slot reached a literal `=` and
/// the definition/RHS slots may continue without a second name diagnostic.
fn required_name(mut i: RewriteIn, baseline: usize, stops: Stops) -> NameResult {
    let item = declaration_type_header_item_after_trivia(i.rb(), LeadingTrivia::default());
    if token_kind(&item) == Some(TokenKind::Equals) {
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
    let mut item = item;
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = declaration_type_header_item_after_trivia(i.rb(), leading);
        if !gtype_item_allowed(&item, baseline) || header_boundary(i.rb(), &item, baseline, stops) {
            i.state.finish_node();
            return Err(item);
        }
        if token_kind(&item) == Some(TokenKind::Equals) {
            emit_item_leading(&mut i, &mut item);
            i.state.finish_node();
            return Ok(Some(item));
        }
        if raw_name(&item) {
            emit_item_leading(&mut i, &mut item);
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return Ok(None);
        }
    }
}

fn parameters(mut i: RewriteIn) {
    let Some((leading, parameter)) = i.token(scan_parameter) else {
        return;
    };
    i.state
        .start_node(SyntaxKind::DeclarationTypeParameterList.into());
    emit_parameter(&mut i, leading, parameter);
    while let Some((leading, parameter)) = i.token(scan_parameter) {
        emit_parameter(&mut i, leading, parameter);
    }
    i.state.finish_node();
}

fn definition(
    mut i: RewriteIn,
    pending: Option<Item>,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let name_was_incomplete = pending.is_some();
    let item = pending.unwrap_or_else(|| definition_item(i.rb()));
    definition_from_item(
        i,
        item,
        name_was_incomplete,
        false,
        baseline,
        stops,
        line_handoff,
    )
}

fn definition_from_item(
    mut i: RewriteIn,
    mut item: Item,
    name_was_incomplete: bool,
    header_clause_seen: bool,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if !name_was_incomplete
        && derives_attachment_start(i.rb(), &item, baseline, stops, line_handoff)
    {
        let next = derives_clause(
            i.rb(),
            item,
            baseline,
            stops,
            line_handoff,
            header_role_boundary(),
        );
        return definition_from_item(i, next, false, true, baseline, stops, line_handoff);
    }
    if header_clause_seen
        && (is_word(&item, "with") || is_word(&item, "impl"))
        && attachment_gap_continues(i.rb(), &item, baseline, stops, line_handoff)
    {
        return handoff(item);
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
            return rhs(i, baseline, stops, line_handoff);
        }
        TypeDeclarationForm::Nominal(boundary) => {
            if boundary.type_owns_leading() {
                emit_item_leading(&mut i, &mut item);
            }
            return handoff(item);
        }
        TypeDeclarationForm::EqualityRecovery => {}
    }
    if !name_was_incomplete && gtype_item_allowed(&item, baseline) {
        emit_item_leading(&mut i, &mut item);
    }
    if !name_was_incomplete && !gtype_item_allowed(&item, baseline) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    if definition_boundary(i.rb(), &item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    if type_starter(&item) {
        emit_missing(&mut i, std::mem::take(&mut item.leading));
        return rhs_item(i, item, baseline, stops, line_handoff);
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if !gtype_item_allowed(&item, baseline)
            || definition_boundary(i.rb(), &item, baseline, stops)
        {
            i.state.finish_node();
            return handoff(item);
        }
        if token_kind(&item) == Some(TokenKind::Equals) {
            emit_item_leading(&mut i, &mut item);
            i.state.finish_node();
            emit_token_item(&mut i, item);
            return rhs(i, baseline, stops, line_handoff);
        }
        if type_starter(&item) {
            emit_item_leading(&mut i, &mut item);
            i.state.finish_node();
            return rhs_item(i, item, baseline, stops, line_handoff);
        }
    }
}

fn rhs(
    mut i: RewriteIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let mut primary = type_nud_item_after_trivia(i.rb(), leading);
    let caller_stops = stops | STOP_SEMICOLON | STOP_WITH;
    if !is_word(&primary, "derives") && !rhs_gap_is_outer_owned(&primary, baseline, caller_stops) {
        emit_item_leading(&mut i, &mut primary);
    }
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary(
        i.rb(),
        primary,
        baseline,
        caller_stops,
        TypeOuterBoundary::DERIVES,
    );
    trailing_after_type(i, exit, baseline, caller_stops, line_handoff)
}

fn rhs_item(
    mut i: RewriteIn,
    mut primary: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    let caller_stops = stops | STOP_SEMICOLON | STOP_WITH;
    if !is_word(&primary, "derives") && !rhs_gap_is_outer_owned(&primary, baseline, caller_stops) {
        emit_item_leading(&mut i, &mut primary);
    }
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary(
        i.rb(),
        primary,
        baseline,
        caller_stops,
        TypeOuterBoundary::DERIVES,
    );
    trailing_after_type(i, exit, baseline, caller_stops, line_handoff)
}

fn trailing_after_type(
    i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    match exit {
        Ok(()) => Ok(()),
        Err(Either::Left(item)) => {
            trailing_from_item(i, item, baseline, caller_stops, line_handoff)
        }
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

fn trailing_from_item(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    if !derives_attachment_start(i.rb(), &item, baseline, caller_stops, line_handoff) {
        return handoff(item);
    }
    let next = derives_clause(
        i.rb(),
        item,
        baseline,
        caller_stops & !STOP_WITH,
        line_handoff,
        trailing_role_boundary(),
    );
    trailing_from_item(i, next, baseline, caller_stops, line_handoff)
}

fn definition_item(mut i: RewriteIn) -> Item {
    let leading = scan_trivia(i.rb());
    type_nud_item_after_trivia(i.rb(), leading)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeDeclarationForm {
    Equality,
    Nominal(NominalBoundary),
    EqualityRecovery,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NominalBoundary {
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
    mut i: RewriteIn,
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
    if companion.is_some() {
        return TypeDeclarationForm::Nominal(NominalBoundary::AmbientCompanion);
    }
    if token_kind(item) == Some(TokenKind::Equals) && gtype_item_allowed(item, baseline) {
        return TypeDeclarationForm::Equality;
    }
    if let Some(indentation) = indentation_after_newline(&item.leading) {
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
            StatementLineHandoff::OrdinaryLayout if matches!(item.payload, Payload::Eof) => {
                TypeDeclarationForm::Nominal(NominalBoundary::EofOwnedTrivia)
            }
            StatementLineHandoff::CatchBracedArm | StatementLineHandoff::OrdinaryLayout => {
                TypeDeclarationForm::EqualityRecovery
            }
        };
    }
    if matches!(item.payload, Payload::Eof) || token_kind(item) == Some(TokenKind::Semicolon) {
        return TypeDeclarationForm::Nominal(NominalBoundary::SameLineTerminal);
    }
    if is_active_stop(i.rb(), item, stops)
        && matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
    {
        return TypeDeclarationForm::Nominal(NominalBoundary::ActiveFixed);
    }
    TypeDeclarationForm::EqualityRecovery
}

fn rhs_gap_is_outer_owned(item: &Item, baseline: usize, caller_stops: Stops) -> bool {
    implicit_delimited_newline(baseline, &item.leading)
        || (is_type_caller_boundary(item, caller_stops)
            && token_kind(item) != Some(TokenKind::Semicolon))
}

fn derives_attachment_start(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    is_word(item, "derives")
        && attachment_gap_continues(i.rb(), item, baseline, stops, line_handoff)
}

fn attachment_gap_continues(
    mut i: RewriteIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    !is_active_stop(i.rb(), item, stops)
        && active_statement_companion(i.rb(), item, baseline, stops).is_none()
        && indentation_after_newline(&item.leading).is_none_or(|indentation| {
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

fn header_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    matches!(item.payload, Payload::Eof)
        || implicit_delimited_newline(baseline, &item.leading)
        || is_active_stop(i.rb(), item, stops)
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::Semicolon)
        )
}

fn definition_boundary(mut i: RewriteIn, item: &Item, baseline: usize, stops: Stops) -> bool {
    header_boundary(i.rb(), item, baseline, stops)
        || item_word(item).is_some_and(|word| {
            matches!(word, "with" | "derives") || is_declaration_starter_word(word)
        })
}

fn emit_gtype(mut i: RewriteIn, baseline: usize, required: bool) -> bool {
    let allowed = observes(i.rb(), |source| {
        let (_, present, indentation) = source_after_trivia(source);
        (!required || present) && indentation.is_none_or(|indentation| indentation > baseline)
    });
    if !allowed {
        return false;
    }
    let trivia = scan_trivia(i.rb());
    emit_leading_trivia(&mut i, &trivia);
    true
}

fn gtype_item_allowed(item: &Item, baseline: usize) -> bool {
    !implicit_delimited_newline(baseline, &item.leading)
}

fn scan_parameter(mut i: LexIn) -> Option<(LeadingTrivia, Token)> {
    let leading = scan_trivia(i.rb());
    if leading.0.is_empty()
        || leading
            .0
            .iter()
            .any(|trivia| trivia.text.contains(['\r', '\n']))
    {
        return None;
    }
    let parameter = scan_declaration_type_parameter(i.rb())?;
    parameter_spelling(&parameter).then_some((leading, parameter))
}

fn parameter_spelling(parameter: &Token) -> bool {
    if parameter.kind == TokenKind::SigilIdentifier {
        return true;
    }
    debug_assert_eq!(parameter.kind, TokenKind::Identifier);
    !is_declaration_starter_word(&parameter.text)
        && !matches!(
            &*parameter.text,
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

fn emit_parameter(i: &mut RewriteIn, leading: LeadingTrivia, parameter: Token) {
    emit_leading_trivia(i, &leading);
    let kind = match parameter.kind {
        TokenKind::Identifier => SyntaxKind::Identifier,
        TokenKind::SigilIdentifier => SyntaxKind::SigilIdentifier,
        _ => unreachable!("declaration parameter scanner returns identifiers"),
    };
    i.state.token(kind.into(), &parameter.text);
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

fn scan_pending_item(mut i: RewriteIn, baseline: usize, stops: Stops) -> Item {
    let leading = scan_trivia(i.rb());
    statement_item_after_trivia(i, leading, baseline, stops)
}

fn prefixed_type_candidate(source: &str, baseline: usize) -> bool {
    let (source, present, indentation) = source_after_trivia(source);
    present
        && indentation.is_none_or(|indentation| indentation > baseline)
        && source_identifier(source).is_some_and(|(word, _)| word == "type")
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
        _ => None,
    }
}

fn emit_intro(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let Payload::Token(token) = item.payload else {
        unreachable!("accepted Type intro is lexical")
    };
    emit_leading_trivia(i, &item.leading);
    i.state.token(kind.into(), &token.text);
}

fn emit_visibility(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("accepted Type visibility is lexical")
    };
    emit_leading_trivia(i, &item.leading);
    let kind = match &*token.text {
        "my" => SyntaxKind::MyKw,
        "our" => SyntaxKind::OurKw,
        "pub" => SyntaxKind::PubKw,
        _ => unreachable!("Type visibility uses exact declaration words"),
    };
    i.state.token(kind.into(), &token.text);
}

fn emit_item_leading(i: &mut RewriteIn, item: &mut Item) {
    let leading = std::mem::take(&mut item.leading);
    emit_leading_trivia(i, &leading);
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
