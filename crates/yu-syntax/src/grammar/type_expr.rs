//! Standalone fixed-precedence grammar for Yulang type expressions.
//!
//! The module deliberately owns no declaration or pattern use-site.  Future
//! grammar owners call its canonical entry after establishing their own stops.

use std::{marker::PhantomData, ops::Range, sync::Arc};

use chasa::{Back as _, ErrorSink, Input as _, error::std::{Unexpected, UnexpectedEndOfInput}, prelude::from_fn};

use crate::{
    grammar::{declaration::Recovered, expression::parse_integer_literal},
    scan::{
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::{TriviaRun, scan_trivia},
        word::{WordSpan, scan_path_segment, scan_word},
    },
    session::{CommitOutput, Committed, CommittedRecoveryRecord, ConstructRole, Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole, IndentationBaseline, IndentationBaselineKind, LayoutDelimitedBoundary, LayoutDelimitedFrame, PunctuationEvidence, RecoveryKind, RecoverySiteKey, StopKind, StopSet, SynIn, SyntaxExpectation, TypeDelimitedOwner, TypeRole, UnexpectedCategory, UnexpectedSyntax},
    syntax_kind::SyntaxKind,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeExpression<'source> {
    primary: TypePrimary<'source>,
    postfix: Vec<TypePostfixTail<'source>>,
    arrow: Option<TypeArrowTail<'source>>,
    range: Range<usize>,
}

impl TypeExpression<'_> {
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
    pub(crate) fn postfix(&self) -> &[TypePostfixTail<'_>] { &self.postfix }
    pub(crate) fn arrow(&self) -> Option<&TypeArrowTail<'_>> { self.arrow.as_ref() }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypePrimary<'source> {
    Atom(TypeAtom<'source>),
    Parenthesized(ParenthesizedTypeGroup<'source>),
    Record(NamedRecordType<'source>),
    Forall(ForallType<'source>),
    EffectRow(EffectRowType<'source>),
    PolymorphicVariant(PolymorphicVariantType<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypeAtom<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
    Number(TypeNumberAtom<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeNumberAtom<'source> {
    text: &'source str,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypePostfixTail<'source> {
    Path(TypePathTail<'source>),
    Call(TypeCallTail<'source>),
    Apply(TypeApplyArgument<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypePathTail<'source> {
    separator: Range<usize>,
    segment: Recovered<TypePathSegment<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypePathSegment<'source> {
    Identifier(WordSpan<'source>),
    SigilIdentifier(WordSpan<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeCallTail<'source> {
    open: Range<usize>,
    arguments: Vec<Recovered<TypeExpression<'source>>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeApplyArgument<'source> {
    boundary: Range<usize>,
    argument: Box<TypeExpression<'source>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeArrowTail<'source> {
    arrow: Range<usize>,
    rhs: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParenthesizedTypeGroup<'source> {
    open: Range<usize>,
    elements: Vec<Recovered<TypeExpression<'source>>>,
    trailing_explicit_separator: Option<TypeExplicitSeparator>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NamedRecordType<'source> {
    open: Range<usize>,
    fields: Vec<Recovered<TypeRecordField<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeRecordField<'source> {
    name: Recovered<WordSpan<'source>>,
    colon: Recovered<Range<usize>>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForallType<'source> {
    keyword: Range<usize>,
    binders: Vec<Recovered<ForallTypeBinder<'source>>>,
    colon: Recovered<Range<usize>>,
    body: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForallTypeBinder<'source> {
    boundary: Recovered<Range<usize>>,
    name: WordSpan<'source>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EffectRowType<'source> {
    apostrophe: Range<usize>,
    open: Range<usize>,
    items: Vec<Recovered<TypeExpression<'source>>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PolymorphicVariantType<'source> {
    colon: Range<usize>,
    open: Range<usize>,
    tags: Vec<Recovered<PolymorphicVariantTag<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PolymorphicVariantTag<'source> {
    name: Recovered<WordSpan<'source>>,
    payloads: Vec<Recovered<PolymorphicVariantPayload<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PolymorphicVariantPayload<'source> {
    boundary: Recovered<Range<usize>>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypeExplicitSeparator {
    Comma(Range<usize>),
    Semicolon(Range<usize>),
}

/// Parses one optional standalone type expression.  It neither needs nor
/// accepts an operator table.
pub(crate) fn parse_type_expression<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeExpression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_expression_with_outer_missing_role(None, i)
}

/// The outer missing role is intentionally retained at this standalone entry.
/// The AST path has no committed diagnostic record; direct CST will use it for
/// its one completely-missing-primary site.
pub(crate) fn parse_type_expression_with_outer_missing_role<'source, E>(
    _outer_missing_role: Option<crate::session::GrammarRole>,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeExpression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_expression_in_context(true, i)
}

fn parse_type_expression_in_context<'source, E>(
    allow_forall: bool,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeExpression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let primary = parse_type_primary_in_context(allow_forall, &mut i)?;
    if matches!(primary, TypePrimary::Forall(_)) {
        let end = primary_range(&primary).end;
        return Some(TypeExpression { primary, postfix: Vec::new(), arrow: None, range: start..end });
    }
    let mut postfix = Vec::new();
    let mut arrow = None;
    loop {
        let checkpoint = i.checkpoint();
        let boundary_start = i.pos();
        let trivia = consume_trivia(&mut i);
        if is_outer_newline_boundary(&i, &trivia) {
            i.rollback(checkpoint);
            break;
        }
        if type_active_tail_stop_pending(&mut i) {
            i.rollback(checkpoint);
            break;
        }

        if trivia.is_empty() {
            if let Some(arrow_range) = scan_exact_arrow(&mut i) {
                arrow = Some(parse_type_arrow_tail(arrow_range, &mut i));
                break;
            }
            if let Some(open) = scan_open_parenthesis(&mut i) {
                postfix.push(TypePostfixTail::Call(parse_type_call_tail(open, &mut i)));
                continue;
            }
            if let Some(separator) = scan_exact_colon_colon(&mut i) {
                postfix.push(TypePostfixTail::Path(parse_type_path_tail(separator, &mut i)));
                continue;
            }
        }

        if i.local.type_ml_arg() && !trivia.is_empty() {
            i.rollback(checkpoint);
            break;
        }
        if !type_chain_trivia(&i, &trivia) {
            i.rollback(checkpoint);
            break;
        }
        if let Some(arrow_range) = scan_exact_arrow(&mut i) {
            arrow = Some(parse_type_arrow_tail(arrow_range, &mut i));
            break;
        }
        if let Some(separator) = scan_exact_colon_colon(&mut i) {
            postfix.push(TypePostfixTail::Path(parse_type_path_tail(separator, &mut i)));
            continue;
        }
        if named_record_next_field_candidate(&mut i, &trivia) {
            i.rollback(checkpoint);
            break;
        }
        if !trivia.is_empty() && type_primary_candidate_in_context(false, &mut i) {
            let boundary = boundary_start..i.pos();
            let saved_ml = i.local.type_ml_arg();
            i.local.set_type_ml_arg(true);
            let argument = i.run(from_fn(|i| parse_type_expression_in_context(false, i)))
                .expect("the TypeApply candidate probe accepted a primary");
            i.local.set_type_ml_arg(saved_ml);
            let end = argument.range.end;
            postfix.push(TypePostfixTail::Apply(TypeApplyArgument {
                boundary: boundary.clone(),
                argument: Box::new(argument),
                range: boundary.start..end,
            }));
            continue;
        }
        i.rollback(checkpoint);
        break;
    }
    let end = arrow.as_ref().map_or_else(
        || postfix.last().map_or_else(|| primary_range(&primary).end, postfix_range_end),
        |tail| tail.range.end,
    );
    Some(TypeExpression { primary, postfix, arrow, range: start..end })
}

/// Mandatory AST entry matching the direct-CST outer-slot contract.  AST
/// values retain `Recovered::Incomplete`; only the direct path owns committed
/// recovery diagnostics and therefore consumes the optional caller role.
pub(crate) fn parse_required_type_expression_with_outer_missing_role<'source, E>(
    outer_missing_role: Option<crate::session::GrammarRole>,
    i: SynIn<'_, 'source, '_, E>,
) -> Recovered<TypeExpression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_expression_with_outer_missing_role(outer_missing_role, i)
        .map(Recovered::Complete)
        .unwrap_or(Recovered::Incomplete)
}

/// Direct-CST counterpart of [`parse_type_expression`].  This intentionally
/// shares the lexical recognizers with the AST path and emits source ranges as
/// they are accepted; it never replays an AST into a CST.
pub(crate) fn commit_direct_type_expression<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedTypeExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_direct_type_expression_in_context(true, committed)
}

fn commit_direct_type_expression_in_context<'parse, 'source, 'local, E, O>(
    allow_forall: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<ParsedTypeExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed.probe(|probe| probe.input().pos());
    committed.start_node(SyntaxKind::TypeExpression);
    let primary = match commit_direct_type_primary(allow_forall, committed) {
        Some(primary) => primary,
        None => {
            committed.finish_node();
            return None;
        }
    };
    if primary == DirectTypePrimary::TerminalForall {
        committed.finish_node();
        let end = committed.probe(|probe| probe.input().pos());
        return Some(ParsedTypeExpression { range: start..end, marker: PhantomData });
    }
    loop {
        let Some(tail) = committed.probe(|probe| recognize_direct_type_tail(probe.input())) else { break; };
        match tail {
            DirectTypeTail::Path { leading, separator } => {
                committed.emit_trivia(&leading);
                committed.start_node(SyntaxKind::TypePathTail);
                committed.token(SyntaxKind::ColonColon, separator);
                let rhs_trivia = consume_direct_type_chain_trivia(committed);
                if let Some(rhs_trivia) = rhs_trivia.as_ref() {
                    committed.emit_trivia(rhs_trivia);
                }
                if rhs_trivia.is_none() {
                    emit_type_missing(committed, GrammarRole::Type(TypeRole::PathSegment), ExpectedSyntax::TypePathSegment);
                    committed.finish_node();
                    continue;
                }
                if let Some(name) = committed.probe(|probe| scan_type_name(probe.input())) {
                    committed.token(type_name_kind(name), type_name_range(name));
                } else if let Some(range) = committed.probe(|probe| consume_type_path_invalid_run(probe.input())) {
                    emit_type_error(committed, TypeRole::PathSegment, range, ExpectedSyntax::TypePathSegment);
                    if let Some(name) = committed.probe(|probe| scan_type_name(probe.input())) {
                        committed.token(type_name_kind(name), type_name_range(name));
                    }
                } else {
                    emit_type_missing(committed, GrammarRole::Type(TypeRole::PathSegment), ExpectedSyntax::TypePathSegment);
                }
                committed.finish_node();
            }
            DirectTypeTail::Call { leading, open } => {
                committed.emit_trivia(&leading);
                commit_direct_type_delimited(TypeDelimitedOwner::Call, TypeDelimitedShape::Parenthesis, SyntaxKind::TypeCallTail, None, open, committed);
            }
            DirectTypeTail::Apply { boundary } => {
                committed.start_node(SyntaxKind::TypeApplyArgument);
                committed.emit_trivia(&boundary);
                let saved = committed.probe(|probe| probe.input().local.type_ml_arg());
                committed.probe(|probe| probe.input().local.set_type_ml_arg(true));
                commit_direct_type_expression_in_context(false, committed).expect("accepted TypeApply owns a type primary");
                committed.probe(|probe| probe.input().local.set_type_ml_arg(saved));
                committed.finish_node();
            }
            DirectTypeTail::Arrow { leading, arrow } => {
                committed.emit_trivia(&leading);
                committed.start_node(SyntaxKind::TypeArrowTail);
                committed.token(SyntaxKind::Arrow, arrow);
                let rhs_trivia = consume_direct_type_chain_trivia(committed);
                if let Some(rhs_trivia) = rhs_trivia.as_ref() {
                    committed.emit_trivia(rhs_trivia);
                }
                if rhs_trivia.is_none() {
                    emit_type_missing(committed, GrammarRole::Type(TypeRole::ArrowRhs), ExpectedSyntax::TypeExpression);
                } else if commit_direct_type_expression(committed).is_none() {
                    if direct_type_item_error_retry(committed, TypeRole::ArrowRhs) {
                        if commit_direct_type_expression(committed).is_none() {
                            emit_type_missing(committed, GrammarRole::Type(TypeRole::ArrowRhs), ExpectedSyntax::TypeExpression);
                        }
                    } else {
                        emit_type_missing(committed, GrammarRole::Type(TypeRole::ArrowRhs), ExpectedSyntax::TypeExpression);
                    }
                }
                committed.finish_node();
                break;
            }
        }
    }
    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    Some(ParsedTypeExpression { range: start..end, marker: PhantomData })
}

/// Mandatory direct entry whose optional role override affects exactly the
/// single completely-missing outer primary slot.
pub(crate) fn commit_direct_type_expression_with_outer_missing_role<'parse, 'source, 'local, E, O>(
    outer_missing_role: Option<GrammarRole>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedTypeExpression<O::Checkpoint>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| direct_type_primary_candidate(probe.input())) {
        return commit_direct_type_expression(committed)
            .expect("the sink-free type primary probe accepted a primary");
    }
    if direct_type_item_error_retry(committed, TypeRole::Primary) {
        return commit_direct_type_expression(committed)
            .expect("the primary recovery retry stopped at a valid primary");
    }
    let at = committed.probe(|probe| probe.input().pos());
    committed.start_node(SyntaxKind::TypeExpression);
    emit_type_missing(
        committed,
        outer_missing_role.unwrap_or(GrammarRole::Type(TypeRole::Primary)),
        ExpectedSyntax::TypeExpression,
    );
    committed.finish_node();
    ParsedTypeExpression { range: at..at, marker: PhantomData }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ParsedTypeExpression<C> {
    range: Range<usize>,
    marker: PhantomData<C>,
}

impl<C> ParsedTypeExpression<C> {
    pub(crate) fn range(&self) -> Range<usize> { self.range.clone() }
}

#[derive(Clone)]
enum DirectTypeTail {
    Path { leading: TriviaRun, separator: Range<usize> },
    Call { leading: TriviaRun, open: Range<usize> },
    Apply { boundary: TriviaRun },
    Arrow { leading: TriviaRun, arrow: Range<usize> },
}

fn recognize_direct_type_tail<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<DirectTypeTail>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let leading = consume_trivia(i);
    if is_outer_newline_boundary(i, &leading) {
        i.rollback(checkpoint);
        return None;
    }
    if type_active_tail_stop_pending(i) {
        i.rollback(checkpoint);
        return None;
    }
    if leading.is_empty() {
        if let Some(arrow) = scan_exact_arrow(i) { return Some(DirectTypeTail::Arrow { leading, arrow }); }
        if let Some(open) = scan_open_parenthesis(i) { return Some(DirectTypeTail::Call { leading, open }); }
        if let Some(separator) = scan_exact_colon_colon(i) { return Some(DirectTypeTail::Path { leading, separator }); }
    }
    if i.local.type_ml_arg() && !leading.is_empty() {
        i.rollback(checkpoint);
        return None;
    }
    if !type_chain_trivia(i, &leading) {
        i.rollback(checkpoint);
        return None;
    }
    if let Some(arrow) = scan_exact_arrow(i) { return Some(DirectTypeTail::Arrow { leading, arrow }); }
    if let Some(separator) = scan_exact_colon_colon(i) { return Some(DirectTypeTail::Path { leading, separator }); }
    if named_record_next_field_candidate(i, &leading) {
        i.rollback(checkpoint);
        return None;
    }
    if !leading.is_empty() && type_primary_candidate_in_context(false, i) {
        return Some(DirectTypeTail::Apply { boundary: leading });
    }
    i.rollback(checkpoint);
    None
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DirectTypePrimary {
    Ordinary,
    TerminalForall,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeDelimitedShape {
    Parenthesis,
    Bracket,
}

impl TypeDelimitedShape {
    fn delimiter(self) -> Delimiter {
        match self {
            Self::Parenthesis => Delimiter::Parenthesis,
            Self::Bracket => Delimiter::Bracket,
        }
    }

    fn close_stop(self) -> StopKind {
        match self {
            Self::Parenthesis => StopKind::RightParenthesis,
            Self::Bracket => StopKind::RightBracket,
        }
    }

    fn open_kind(self) -> SyntaxKind {
        match self {
            Self::Parenthesis => SyntaxKind::LParen,
            Self::Bracket => SyntaxKind::LBracket,
        }
    }

    fn close_kind(self) -> SyntaxKind {
        match self {
            Self::Parenthesis => SyntaxKind::RParen,
            Self::Bracket => SyntaxKind::RBracket,
        }
    }
}

fn commit_direct_type_primary<'parse, 'source, 'local, E, O>(
    allow_forall: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<DirectTypePrimary>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if allow_forall {
        if let Some(keyword) = committed.probe(|probe| scan_forall_keyword(probe.input())) {
            commit_direct_forall_type(keyword, committed);
            return Some(DirectTypePrimary::TerminalForall);
        }
    }
    if let Some((apostrophe, open)) = committed.probe(|probe| scan_effect_row_open(probe.input())) {
        commit_direct_type_delimited(
            TypeDelimitedOwner::EffectRow,
            TypeDelimitedShape::Bracket,
            SyntaxKind::EffectRowType,
            Some((SyntaxKind::Apostrophe, apostrophe)),
            open,
            committed,
        );
        return Some(DirectTypePrimary::Ordinary);
    }
    if let Some((colon, open)) = committed.probe(|probe| scan_polymorphic_variant_open(probe.input())) {
        commit_direct_polymorphic_variant_type(colon, open, committed);
        return Some(DirectTypePrimary::Ordinary);
    }
    if let Some(name) = committed.probe(|probe| scan_type_name(probe.input())) {
        committed.token(type_name_kind(name), type_name_range(name));
        return Some(DirectTypePrimary::Ordinary);
    }
    if let Some(integer) = committed.probe(|probe| {
        probe.input().input.remainder().chars().next().is_some_and(|character| character.is_ascii_digit())
            .then(|| probe.input().run(parse_integer_literal))
            .flatten()
    }) {
        committed.token(SyntaxKind::Integer, integer.range());
        return Some(DirectTypePrimary::Ordinary);
    }
    if let Some(open) = committed.probe(|probe| scan_open_parenthesis(probe.input())) {
        commit_direct_type_delimited(
            TypeDelimitedOwner::ParenthesizedGroup,
            TypeDelimitedShape::Parenthesis,
            SyntaxKind::ParenthesizedTypeGroup,
            None,
            open,
            committed,
        );
        return Some(DirectTypePrimary::Ordinary);
    }
    let open = committed.probe(|probe| scan_open_brace(probe.input()))?;
    commit_direct_named_record_type(open, committed);
    Some(DirectTypePrimary::Ordinary)
}

/// Direct-CST realization of the non-delimited forall binder sequence.  The
/// gap following a binder is held until its successor is known: it belongs to
/// the next binder when that successor is apostrophe-sigil, and otherwise to
/// the forall node's colon/body transition.
fn commit_direct_forall_type<'parse, 'source, 'local, E, O>(
    keyword: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ForallType);
    committed.token(SyntaxKind::ForKw, keyword);

    let mut accepted_binder = false;
    loop {
        let required_boundary = !accepted_binder;
        let trivia = consume_direct_forall_trivia(committed, required_boundary);

        if let Some(name) = committed.probe(|probe| scan_forall_binder(probe.input())) {
            committed.start_node(SyntaxKind::ForallTypeBinder);
            if let Some(trivia) = trivia.as_ref().filter(|trivia| !trivia.is_empty()) {
                committed.emit_trivia(trivia);
            } else {
                emit_type_missing(
                    committed,
                    GrammarRole::Type(TypeRole::ForallBinderBoundary),
                    ExpectedSyntax::TypeBinderBoundary,
                );
            }
            committed.token(SyntaxKind::SigilIdentifier, name.range());
            committed.finish_node();
            accepted_binder = true;
            continue;
        }

        if !accepted_binder {
            let mut recovered_malformed = false;
            if let Some(trivia) = trivia.as_ref() {
                // A first-binder boundary is owned by its recovery item too.
                committed.start_node(SyntaxKind::ForallTypeBinder);
                committed.emit_trivia(trivia);
                if let Some(range) = direct_forall_invalid_run(committed) {
                    emit_type_error(committed, TypeRole::ForallBinder, range, ExpectedSyntax::ForallTypeBinder);
                    recovered_malformed = true;
                } else {
                    emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBinder), ExpectedSyntax::ForallTypeBinder);
                }
                committed.finish_node();
            } else if direct_forall_colon_pending(committed) {
                committed.start_node(SyntaxKind::ForallTypeBinder);
                emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBinder), ExpectedSyntax::ForallTypeBinder);
                committed.finish_node();
            } else if let Some(range) = direct_forall_invalid_run(committed) {
                committed.start_node(SyntaxKind::ForallTypeBinder);
                emit_type_error(committed, TypeRole::ForallBinder, range, ExpectedSyntax::ForallTypeBinder);
                committed.finish_node();
                recovered_malformed = true;
            } else {
                committed.start_node(SyntaxKind::ForallTypeBinder);
                emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBinder), ExpectedSyntax::ForallTypeBinder);
                committed.finish_node();
                break;
            }

            if direct_forall_colon_pending(committed) {
                commit_direct_forall_colon_and_body(committed);
            } else if recovered_malformed {
                continue;
            }
            break;
        }

        if let Some(trivia) = trivia.as_ref() {
            committed.emit_trivia(trivia);
        }
        if direct_forall_colon_pending(committed) {
            commit_direct_forall_colon_and_body(committed);
            break;
        }
        if committed.probe(|probe| type_primary_candidate(probe.input())) {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallColon), ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
            commit_direct_forall_body(committed);
            break;
        }
        if let Some(separator) = direct_forall_unowned_separator(committed) {
            emit_type_error(
                committed,
                TypeRole::ForallBinderBoundary,
                separator,
                ExpectedSyntax::TypeBinderBoundary,
            );
            continue;
        }
        if let Some(range) = direct_forall_invalid_run(committed) {
            let role = if direct_forall_binder_after_invalid_pending(committed) {
                TypeRole::ForallBinder
            } else {
                TypeRole::ForallColon
            };
            emit_type_error(committed, role, range, ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
            continue;
        }
        emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallColon), ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
        break;
    }
    committed.finish_node();
}

fn direct_forall_unowned_separator<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let separator = scan_separator(i);
        let owned = match &separator {
            Some(TypeExplicitSeparator::Comma(_)) => active_stop_set(i).contains(StopKind::Comma),
            Some(TypeExplicitSeparator::Semicolon(_)) => active_stop_set(i).contains(StopKind::Semicolon),
            None => false,
        };
        if owned {
            i.rollback(checkpoint);
            None
        } else {
            separator.map(|separator| separator_range(&separator))
        }
    })
}

fn commit_direct_forall_colon_and_body<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let colon = committed.probe(|probe| scan_exact_colon(probe.input()))
        .expect("forall colon probe accepted a literal colon");
    committed.token(SyntaxKind::Colon, colon);
    commit_direct_forall_body(committed);
}

fn commit_direct_forall_body<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = consume_direct_forall_trivia(committed, false);
    if let Some(trivia) = trivia.as_ref() {
        committed.emit_trivia(trivia);
    } else {
        emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBody), ExpectedSyntax::TypeExpression);
        return;
    }
    if commit_direct_type_expression(committed).is_none() {
        if let Some(range) = direct_forall_invalid_run(committed) {
            emit_type_error(committed, TypeRole::ForallBody, range, ExpectedSyntax::TypeExpression);
            if commit_direct_type_expression(committed).is_none() {
                emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBody), ExpectedSyntax::TypeExpression);
            }
        } else {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::ForallBody), ExpectedSyntax::TypeExpression);
        }
    }
}

fn consume_direct_forall_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    required: bool,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = consume_trivia(i);
        if type_chain_trivia(i, &trivia) && (!required || !trivia.is_empty()) {
            Some(trivia)
        } else {
            i.rollback(checkpoint);
            None
        }
    })
}

fn direct_forall_colon_pending<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let pending = scan_exact_colon(i).is_some();
        i.rollback(checkpoint);
        pending
    })
}

fn direct_forall_binder_after_invalid_pending<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = consume_forall_trivia(i, false);
        let pending = trivia.is_some() && scan_forall_binder(i).is_some();
        i.rollback(checkpoint);
        pending
    })
}

fn direct_forall_invalid_run<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let start = i.pos();
        let mut end = start;
        let sigil_like_non_binder = matches!(i.input.remainder().chars().next(), Some('$' | '&' | '_'));
        loop {
            if end > start && !sigil_like_non_binder {
                let checkpoint = i.checkpoint();
                let retry = scan_forall_binder(i).is_some()
                    || scan_exact_colon(i).is_some()
                    || type_primary_candidate(i);
                i.rollback(checkpoint);
                if retry { return Some(start..end); }
            }
            if type_recovery_boundary_pending(i) || i.input.remainder().starts_with(':') {
                return (start < end).then_some(start..end);
            }
            let Some(character) = i.input.remainder().chars().next() else { return (start < end).then_some(start..end); };
            if character.is_whitespace() { return (start < end).then_some(start..end); }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })
}

fn commit_direct_type_delimited<'parse, 'source, 'local, E, O>(
    owner: TypeDelimitedOwner,
    shape: TypeDelimitedShape,
    kind: SyntaxKind,
    prefix: Option<(SyntaxKind, Range<usize>)>,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(kind);
    if let Some((kind, range)) = prefix { committed.token(kind, range); }
    committed.token(shape.open_kind(), open);
    let incoming = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::Semicolon).with(shape.close_stop()));
    committed.probe(|probe| {
        probe.input().local.push_delimiter(shape.delimiter());
        probe.input().local.push_stop_set(stops);
        probe.input().local.push_type_delimited_owner(owner);
    });
    let opening = consume_direct_trivia(committed);
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, probe.input().local.line().line_indent));
    committed.probe(|probe| push_layout(layout, probe.input()));
    if !direct_type_close_pending(shape, committed) {
        loop {
            if direct_type_separator_pending(committed) {
                emit_type_missing(
                    committed,
                    GrammarRole::Type(match owner {
                        TypeDelimitedOwner::Call => TypeRole::CallArgument,
                        TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedItem,
                        TypeDelimitedOwner::NamedRecord => TypeRole::RecordField,
                        TypeDelimitedOwner::EffectRow => TypeRole::EffectRowItem,
                        TypeDelimitedOwner::PolymorphicVariant => TypeRole::PolymorphicVariantPayload,
                    }),
                    ExpectedSyntax::TypeExpression,
                );
                let separator = committed
                    .probe(|probe| scan_separator(probe.input()))
                    .expect("the separator pending probe accepted a literal separator");
                committed.token(separator_kind(&separator), separator_range(&separator));
                let trailing = consume_direct_trivia(committed);
                committed.emit_trivia(&trailing);
                if direct_type_close_pending(shape, committed) { break; }
                continue;
            }
            if commit_direct_type_expression(committed).is_none() {
                let role = match owner {
                    TypeDelimitedOwner::Call => TypeRole::CallArgument,
                    TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedItem,
                    TypeDelimitedOwner::NamedRecord => TypeRole::RecordField,
                    TypeDelimitedOwner::EffectRow => TypeRole::EffectRowItem,
                    TypeDelimitedOwner::PolymorphicVariant => TypeRole::PolymorphicVariantPayload,
                };
                match direct_type_delimited_item_error_retry(committed, role) {
                    Some(TypeDelimitedItemRecovery::Retry) => continue,
                    // The malformed run reached a delimiter or a caller-owned
                    // stop.  It is already represented by its Error node;
                    // leave the boundary for the close/outer owner instead of
                    // manufacturing a second missing item at that cause.
                    Some(TypeDelimitedItemRecovery::Boundary) => break,
                    None => {
                        emit_type_missing(committed, GrammarRole::Type(role), ExpectedSyntax::TypeExpression);
                        break;
                    }
                }
            }
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            if let Some(separator) = committed.probe(|probe| scan_separator(probe.input())) {
                committed.token(separator_kind(&separator), separator_range(&separator));
                let trailing = consume_direct_trivia(committed);
                committed.emit_trivia(&trailing);
                if direct_type_close_pending(shape, committed) { break; }
                continue;
            }
            if direct_type_close_pending(shape, committed) { break; }
            if committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)) == LayoutDelimitedBoundary::ImplicitNewline { continue; }
            if committed.probe(|probe| direct_type_primary_candidate(probe.input())) {
                emit_type_missing(
                    committed,
                    GrammarRole::Type(match owner {
                        TypeDelimitedOwner::Call => TypeRole::CallArgumentSeparator,
                        TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedSeparator,
                        TypeDelimitedOwner::NamedRecord => TypeRole::RecordFieldSeparator,
                        TypeDelimitedOwner::EffectRow => TypeRole::EffectRowSeparator,
                        TypeDelimitedOwner::PolymorphicVariant => TypeRole::PolymorphicVariantTagSeparator,
                    }),
                    ExpectedSyntax::DelimitedSequenceSeparator,
                );
                continue;
            }
            break;
        }
    }
    let close_role = GrammarRole::ClosingDelimiter {
        owner: match owner {
            TypeDelimitedOwner::Call => ConstructRole::TypeCall,
            TypeDelimitedOwner::ParenthesizedGroup => ConstructRole::ParenthesizedTypeGroup,
            TypeDelimitedOwner::NamedRecord => ConstructRole::NamedRecordType,
            TypeDelimitedOwner::EffectRow => ConstructRole::EffectRowType,
            TypeDelimitedOwner::PolymorphicVariant => ConstructRole::PolymorphicVariantType,
        },
        delimiter: shape.delimiter(),
    };
    loop {
        if let Some(close) = committed.probe(|probe| scan_close_delimiter(shape, probe.input())) {
            committed.token(shape.close_kind(), close);
            break;
        }
        let mismatched = committed.probe(|probe| scan_mismatched_close_for(shape.delimiter(), probe.input()));
        if let Some(range) = mismatched {
            emit_error_with_role(
                committed,
                close_role,
                range,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(shape.delimiter())),
            );
            continue;
        }
        emit_type_missing(
            committed,
            close_role,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(shape.delimiter())),
        );
        break;
    }
    committed.probe(|probe| {
        pop_layout(layout, probe.input());
        assert_eq!(probe.input().local.pop_type_delimited_owner(), Some(owner));
        assert_eq!(probe.input().local.pop_stop_set(), Some(stops));
        assert_eq!(probe.input().local.pop_delimiter(), Some(shape.delimiter()));
    });
    committed.finish_node();
}

fn commit_direct_polymorphic_variant_type<'parse, 'source, 'local, E, O>(
    colon: Range<usize>,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::PolymorphicVariantType);
    committed.token(SyntaxKind::Colon, colon);
    committed.token(SyntaxKind::LBrace, open);
    let incoming = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::RightBrace));
    committed.probe(|probe| {
        probe.input().local.push_delimiter(Delimiter::Brace);
        probe.input().local.push_stop_set(stops);
        probe.input().local.push_type_delimited_owner(TypeDelimitedOwner::PolymorphicVariant);
    });
    let opening = consume_direct_trivia(committed);
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, probe.input().local.line().line_indent));
    committed.probe(|probe| push_layout(layout, probe.input()));

    let mut required_tag = false;
    let mut after_tag = false;
    let mut closed = false;
    loop {
        if let Some(close) = committed.probe(|probe| scan_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            closed = true;
            break;
        }
        if let Some(mismatched) = committed.probe(|probe| scan_mismatched_record_close(probe.input())) {
            emit_error_with_role(
                committed,
                GrammarRole::ClosingDelimiter { owner: ConstructRole::PolymorphicVariantType, delimiter: Delimiter::Brace },
                mismatched,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            );
            continue;
        }
        if let Some(comma) = committed.probe(|probe| scan_record_comma(probe.input())) {
            if required_tag || !after_tag {
                committed.start_node(SyntaxKind::PolymorphicVariantTag);
                emit_type_missing(committed, GrammarRole::Type(TypeRole::PolymorphicVariantTag), ExpectedSyntax::Identifier);
                committed.finish_node();
            }
            committed.token(SyntaxKind::Comma, comma);
            required_tag = true;
            after_tag = false;
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_record_semicolon(probe.input())) {
            if active_stop_set_probe(committed, StopKind::Semicolon) { break; }
            emit_type_error(committed, TypeRole::PolymorphicVariantTagSeparator, semicolon, ExpectedSyntax::DelimitedSequenceSeparator);
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(name) = committed.probe(|probe| scan_plain_type_identifier(probe.input())) {
            commit_direct_polymorphic_variant_tag(name, committed);
            required_tag = false;
            after_tag = true;
        } else if let Some(range) = committed.probe(|probe| parse_type_primary_in_context(true, probe.input()).map(|primary| primary_range(&primary))) {
            committed.start_node(SyntaxKind::PolymorphicVariantTag);
            emit_type_error(committed, TypeRole::PolymorphicVariantTagName, range, ExpectedSyntax::Identifier);
            commit_direct_polymorphic_variant_payloads(committed);
            committed.finish_node();
            required_tag = false;
            after_tag = true;
        } else if let Some(range) = committed.probe(|probe| consume_polymorphic_variant_invalid_run(probe.input(), false)) {
            emit_type_error(committed, TypeRole::PolymorphicVariantTag, range, ExpectedSyntax::Identifier);
            required_tag = false;
            after_tag = true;
        } else {
            if required_tag {
                committed.start_node(SyntaxKind::PolymorphicVariantTag);
                emit_type_missing(committed, GrammarRole::Type(TypeRole::PolymorphicVariantTag), ExpectedSyntax::Identifier);
                committed.finish_node();
            }
            break;
        }

        let trivia = consume_direct_trivia(committed);
        let newline_boundary = trivia_has_newline(&trivia).then(|| {
            committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent))
        });
        if matches!(newline_boundary, Some(LayoutDelimitedBoundary::DeeperNewline)) {
            committed.emit_trivia(&trivia);
            break;
        }
        committed.emit_trivia(&trivia);
        if matches!(newline_boundary, Some(LayoutDelimitedBoundary::ImplicitNewline)) && after_tag {
            required_tag = true;
            after_tag = false;
        }
    }
    if !closed {
        loop {
            if let Some(close) = committed.probe(|probe| scan_close_brace(probe.input())) {
                committed.token(SyntaxKind::RBrace, close);
                break;
            }
            if let Some(mismatched) = committed.probe(|probe| scan_mismatched_record_close(probe.input())) {
                emit_error_with_role(
                    committed,
                    GrammarRole::ClosingDelimiter { owner: ConstructRole::PolymorphicVariantType, delimiter: Delimiter::Brace },
                    mismatched,
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                );
                continue;
            }
            emit_type_missing(
                committed,
                GrammarRole::ClosingDelimiter { owner: ConstructRole::PolymorphicVariantType, delimiter: Delimiter::Brace },
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            );
            break;
        }
    }
    committed.probe(|probe| {
        pop_layout(layout, probe.input());
        assert_eq!(probe.input().local.pop_type_delimited_owner(), Some(TypeDelimitedOwner::PolymorphicVariant));
        assert_eq!(probe.input().local.pop_stop_set(), Some(stops));
        assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Brace));
    });
    committed.finish_node();
}

fn active_stop_set_probe<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    stop: StopKind,
) -> bool
where E: ErrorSink<usize>, O: CommitOutput<'source> {
    committed.probe(|probe| active_stop_set(probe.input()).contains(stop))
}

fn commit_direct_polymorphic_variant_tag<'parse, 'source, 'local, E, O>(
    name: WordSpan<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::PolymorphicVariantTag);
    committed.token(SyntaxKind::Identifier, name.range());
    commit_direct_polymorphic_variant_payloads(committed);
    committed.finish_node();
}

fn commit_direct_polymorphic_variant_payloads<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>, O: CommitOutput<'source>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error>,
{
    loop {
        let (trivia, candidate, boundary) = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = consume_trivia(i);
            let boundary = trivia_has_newline(&trivia) || polymorphic_variant_outer_boundary(i);
            let candidate = !boundary && type_primary_candidate(i);
            i.rollback(checkpoint);
            (trivia, candidate, boundary)
        });
        if boundary { break; }
        if candidate {
            committed.start_node(SyntaxKind::PolymorphicVariantPayload);
            if trivia.is_empty() {
                emit_type_missing(committed, GrammarRole::Type(TypeRole::PolymorphicVariantPayloadBoundary), ExpectedSyntax::TypePayloadBoundary);
            } else {
                let consumed = consume_direct_trivia(committed);
                committed.emit_trivia(&consumed);
            }
            let saved = committed.probe(|probe| probe.input().local.type_ml_arg());
            committed.probe(|probe| probe.input().local.set_type_ml_arg(true));
            commit_direct_type_expression_in_context(false, committed)
                .expect("accepted polymorphic-variant payload owns a type primary");
            committed.probe(|probe| probe.input().local.set_type_ml_arg(saved));
            committed.finish_node();
            continue;
        }
        if trivia.is_empty() { break; }
        let range = committed.probe(|probe| {
            let i = probe.input();
            let _ = consume_trivia(i);
            consume_polymorphic_variant_invalid_run(i, true)
        });
        let Some(range) = range else { break; };
        committed.start_node(SyntaxKind::PolymorphicVariantPayload);
        let consumed = consume_direct_trivia(committed);
        committed.emit_trivia(&consumed);
        emit_type_error(committed, TypeRole::PolymorphicVariantPayload, range, ExpectedSyntax::TypeExpression);
        if committed.probe(|probe| type_primary_candidate(probe.input())) {
            let saved = committed.probe(|probe| probe.input().local.type_ml_arg());
            committed.probe(|probe| probe.input().local.set_type_ml_arg(true));
            commit_direct_type_expression_in_context(false, committed)
                .expect("polymorphic-variant payload recovery retries its type slot");
            committed.probe(|probe| probe.input().local.set_type_ml_arg(saved));
        }
        committed.finish_node();
    }
}

fn commit_direct_named_record_type<'parse, 'source, 'local, E, O>(
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::NamedRecordType);
    committed.token(SyntaxKind::LBrace, open);
    let incoming = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::RightBrace));
    committed.probe(|probe| {
        probe.input().local.push_delimiter(Delimiter::Brace);
        probe.input().local.push_stop_set(stops);
        probe.input().local.push_type_delimited_owner(TypeDelimitedOwner::NamedRecord);
    });
    let opening = consume_direct_trivia(committed);
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, probe.input().local.line().line_indent));
    committed.probe(|probe| push_layout(layout, probe.input()));
    let mut closed = false;
    loop {
        if let Some(close) = committed.probe(|probe| scan_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            closed = true;
            break;
        }
        if let Some(comma) = committed.probe(|probe| scan_record_comma(probe.input())) {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordField), ExpectedSyntax::Identifier);
            committed.token(SyntaxKind::Comma, comma);
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_record_semicolon(probe.input())) {
            emit_type_error(
                committed,
                TypeRole::RecordFieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            continue;
        }
        if !commit_direct_type_record_field(committed) {
            if let Some(range) = committed.probe(|probe| consume_record_invalid_run(probe.input())) {
                emit_type_error(committed, TypeRole::RecordField, range, ExpectedSyntax::Identifier);
                let trivia = consume_direct_trivia(committed);
                committed.emit_trivia(&trivia);
                continue;
            }
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordField), ExpectedSyntax::Identifier);
            break;
        }
        let trivia = consume_direct_trivia(committed);
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_record_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = consume_direct_trivia(committed);
            committed.emit_trivia(&post);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_record_semicolon(probe.input())) {
            emit_type_error(
                committed,
                TypeRole::RecordFieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            let post = consume_direct_trivia(committed);
            committed.emit_trivia(&post);
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            closed = true;
            break;
        }
        if committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)) == LayoutDelimitedBoundary::ImplicitNewline {
            continue;
        }
        if committed.probe(|probe| named_record_next_field_candidate(probe.input(), &trivia)) {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldSeparator), ExpectedSyntax::DelimitedSequenceSeparator);
            continue;
        }
        break;
    }
    let close_role = GrammarRole::ClosingDelimiter { owner: ConstructRole::NamedRecordType, delimiter: Delimiter::Brace };
    if !closed {
        loop {
            if let Some(close) = committed.probe(|probe| scan_close_brace(probe.input())) {
                committed.token(SyntaxKind::RBrace, close);
                break;
            }
            if let Some(mismatched) = committed.probe(|probe| scan_mismatched_record_close(probe.input())) {
                emit_error_with_role(
                    committed,
                    close_role,
                    mismatched,
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                );
                continue;
            }
            emit_type_missing(committed, close_role, ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)));
            break;
        }
    }
    committed.probe(|probe| {
        pop_layout(layout, probe.input());
        assert_eq!(probe.input().local.pop_type_delimited_owner(), Some(TypeDelimitedOwner::NamedRecord));
        assert_eq!(probe.input().local.pop_stop_set(), Some(stops));
        assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Brace));
    });
    committed.finish_node();
}

fn commit_direct_type_record_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name = committed.probe(|probe| scan_plain_type_identifier(probe.input()));
    // This is a consuming direct-CST probe.  Retain the colon rather than
    // probing it as a boolean and trying to scan it again after the input has
    // advanced; the latter would turn `{: A}` into a stranded `A`.
    let missing_name_colon = if name.is_none() {
        committed.probe(|probe| scan_exact_colon(probe.input()))
    } else {
        None
    };
    let malformed_name = if name.is_none() && missing_name_colon.is_none() {
        committed.probe(|probe| scan_malformed_record_name_colon(probe.input()))
    } else {
        None
    };
    if name.is_none() && missing_name_colon.is_none() && malformed_name.is_none() { return false; }
    committed.start_node(SyntaxKind::TypeRecordField);
    let type_expected;
    if let Some(name) = name {
        committed.token(SyntaxKind::Identifier, name.range());
        let trivia = consume_direct_trivia(committed);
        committed.emit_trivia(&trivia);
        if let Some(colon) = committed.probe(|probe| scan_exact_colon(probe.input())) {
            committed.token(SyntaxKind::Colon, colon);
            type_expected = true;
        } else if let Some(equals) = committed.probe(|probe| scan_exact_equals(probe.input())) {
            emit_type_error(
                committed,
                TypeRole::RecordFieldColon,
                equals,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            );
            type_expected = true;
        } else if let Some(range) = committed.probe(|probe| consume_record_colon_invalid_run(probe.input())) {
            emit_type_error(
                committed,
                TypeRole::RecordFieldColon,
                range,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            );
            let recovered_colon = committed.probe(|probe| scan_exact_colon(probe.input()));
            let has_recovered_colon = recovered_colon.is_some();
            if let Some(colon) = recovered_colon {
                committed.token(SyntaxKind::Colon, colon);
            }
            type_expected = has_recovered_colon
                || committed.probe(|probe| type_primary_candidate(probe.input()));
        } else {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldColon), ExpectedSyntax::Punctuation(PunctuationEvidence::Colon));
            type_expected = committed.probe(|probe| type_primary_candidate(probe.input()));
        }
    } else {
        if let Some((range, colon)) = malformed_name {
            emit_type_error(committed, TypeRole::RecordFieldName, range, ExpectedSyntax::Identifier);
            committed.token(SyntaxKind::Colon, colon);
        } else {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldName), ExpectedSyntax::Identifier);
            let colon = missing_name_colon.expect("missing-name field accepted a colon");
            committed.token(SyntaxKind::Colon, colon);
        }
        type_expected = true;
    }
    let trivia = consume_direct_trivia(committed);
    committed.emit_trivia(&trivia);
    if type_expected && commit_direct_type_expression(committed).is_none() {
        if direct_type_item_error_retry(committed, TypeRole::RecordFieldType) {
            if commit_direct_type_expression(committed).is_none() {
                emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldType), ExpectedSyntax::TypeExpression);
            }
        } else {
            emit_type_missing(committed, GrammarRole::Type(TypeRole::RecordFieldType), ExpectedSyntax::TypeExpression);
        }
    }
    committed.finish_node();
    true
}

fn direct_type_close_pending<'parse, 'source, 'local, E, O>(
    shape: TypeDelimitedShape,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let pending = scan_close_delimiter(shape, i).is_some();
        i.rollback(checkpoint);
        pending
    })
}

fn direct_type_separator_pending<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let pending = scan_separator(i).is_some();
        i.rollback(checkpoint);
        pending
    })
}

fn parse_type_primary_in_context<'source, E>(
    allow_forall: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypePrimary<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if allow_forall {
        if let Some(keyword) = scan_forall_keyword(i) {
            return Some(TypePrimary::Forall(parse_forall_type(keyword, i)));
        }
    }
    if let Some((apostrophe, open)) = scan_effect_row_open(i) {
        return Some(TypePrimary::EffectRow(parse_effect_row_type(apostrophe, open, i)));
    }
    if let Some((colon, open)) = scan_polymorphic_variant_open(i) {
        return Some(TypePrimary::PolymorphicVariant(parse_polymorphic_variant_type(colon, open, i)));
    }
    if let Some(name) = scan_type_name(i) {
        return Some(TypePrimary::Atom(match name {
            TypeName::Identifier(word) => TypeAtom::Identifier(word),
            TypeName::SigilIdentifier(word) => TypeAtom::SigilIdentifier(word),
        }));
    }
    if i.input.remainder().chars().next().is_some_and(|character| character.is_ascii_digit()) {
        if let Some(integer) = i.run(parse_integer_literal) {
            let range = integer.range();
            return Some(TypePrimary::Atom(TypeAtom::Number(TypeNumberAtom { text: integer.text(), range })));
        }
    }
    if let Some(open) = scan_open_parenthesis(i) {
        return Some(TypePrimary::Parenthesized(parse_parenthesized_type_group(open, i)));
    }
    scan_open_brace(i).map(|open| TypePrimary::Record(parse_named_record_type(open, i)))
}

fn parse_forall_type<'source, E>(keyword: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> ForallType<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = keyword.start;
    let mut binders = Vec::new();
    let mut colon = Recovered::Incomplete;
    let mut body = Recovered::Incomplete;

    let first_boundary = consume_forall_trivia(i, true);
    if let Some(name) = scan_forall_binder(i) {
        let boundary = first_boundary.map_or(Recovered::Incomplete, |trivia| Recovered::Complete(trivia.range()));
        let end = name.range().end;
        let binder_start = match &boundary { Recovered::Complete(range) => range.start, Recovered::Incomplete => name.range().start };
        binders.push(Recovered::Complete(ForallTypeBinder { boundary, name, range: binder_start..end }));
    } else if let Some(found_colon) = scan_exact_colon(i) {
        binders.push(Recovered::Incomplete);
        colon = Recovered::Complete(found_colon);
        body = parse_forall_body_for_ast(i);
        let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
        return ForallType { keyword, binders, colon, body, range: start..end };
    } else if recover_forall_for_ast(i) {
        binders.push(Recovered::Incomplete);
        let gap = consume_forall_trivia(i, true);
        if let Some(name) = scan_forall_binder(i) {
            let boundary = gap.map_or(Recovered::Incomplete, |trivia| Recovered::Complete(trivia.range()));
            let end = name.range().end;
            let binder_start = match &boundary { Recovered::Complete(range) => range.start, Recovered::Incomplete => name.range().start };
            binders.push(Recovered::Complete(ForallTypeBinder { boundary, name, range: binder_start..end }));
        } else if let Some(found_colon) = scan_exact_colon(i) {
            colon = Recovered::Complete(found_colon);
            body = parse_forall_body_for_ast(i);
            let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
            return ForallType { keyword, binders, colon, body, range: start..end };
        } else {
            let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
            return ForallType { keyword, binders, colon, body, range: start..end };
        }
    } else {
        binders.push(Recovered::Incomplete);
        let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
        return ForallType { keyword, binders, colon, body, range: start..end };
    }

    loop {
        let checkpoint = i.checkpoint();
        let gap = consume_forall_trivia(i, false);
        if gap.is_none() {
            i.rollback(checkpoint);
            break;
        }
        if let Some(found_colon) = scan_exact_colon(i) {
            colon = Recovered::Complete(found_colon);
            body = parse_forall_body_for_ast(i);
            break;
        }
        if let Some(name) = scan_forall_binder(i) {
            let binder_start = gap.as_ref().filter(|trivia| !trivia.is_empty())
                .map_or_else(|| name.range().start, |trivia| trivia.range().start);
            let boundary = gap.filter(|trivia| !trivia.is_empty())
                .map_or(Recovered::Incomplete, |trivia| Recovered::Complete(trivia.range()));
            let end = name.range().end;
            binders.push(Recovered::Complete(ForallTypeBinder { boundary, name, range: binder_start..end }));
            continue;
        }
        if type_primary_candidate(i) {
            colon = Recovered::Incomplete;
            body = parse_forall_body_for_ast(i);
            break;
        }
        if consume_forall_unowned_separator_ast(i) {
            continue;
        }
        if !recover_forall_for_ast(i) {
            break;
        }
    }
    let end = forall_end(&keyword, &binders, &colon, &body, i.pos());
    ForallType { keyword, binders, colon, body, range: start..end }
}

fn consume_forall_unowned_separator_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let separator = scan_separator(i);
    let owned = match &separator {
        Some(TypeExplicitSeparator::Comma(_)) => active_stop_set(i).contains(StopKind::Comma),
        Some(TypeExplicitSeparator::Semicolon(_)) => active_stop_set(i).contains(StopKind::Semicolon),
        None => false,
    };
    if separator.is_some() && !owned {
        true
    } else {
        i.rollback(checkpoint);
        false
    }
}

fn parse_forall_body_for_ast<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let _ = consume_forall_trivia(i, false);
    i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
        .or_else(|| recover_forall_for_ast(i).then(|| i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))).flatten())
        .map(|value| Recovered::Complete(Box::new(value)))
        .unwrap_or(Recovered::Incomplete)
}

fn forall_end(
    keyword: &Range<usize>,
    binders: &[Recovered<ForallTypeBinder<'_>>],
    colon: &Recovered<Range<usize>>,
    body: &Recovered<Box<TypeExpression<'_>>>,
    fallback: usize,
) -> usize {
    match body {
        Recovered::Complete(value) => value.range.end,
        Recovered::Incomplete => match colon {
            Recovered::Complete(range) => range.end,
            Recovered::Incomplete => binders.last().and_then(|binder| match binder {
                Recovered::Complete(binder) => Some(binder.range.end),
                Recovered::Incomplete => None,
            }).unwrap_or(keyword.end).max(fallback),
        },
    }
}

fn consume_forall_trivia<E>(i: &mut SynIn<E>, required: bool) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if type_chain_trivia(i, &trivia) && (!required || !trivia.is_empty()) {
        Some(trivia)
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn scan_forall_keyword<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let Some(word) = i.run(scan_word) else { return None; };
    if word.text() == "for" { Some(word.range()) } else { i.rollback(checkpoint); None }
}

fn scan_forall_binder<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    match scan_type_name(i) {
        Some(TypeName::SigilIdentifier(word)) => Some(word),
        Some(TypeName::Identifier(_)) | None => {
            i.rollback(checkpoint);
            None
        }
    }
}

fn recover_forall_for_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if i.pos() > start {
            let checkpoint = i.checkpoint();
            let retry = scan_forall_binder(i).is_some()
                || scan_exact_colon(i).is_some()
                || type_primary_candidate(i);
            i.rollback(checkpoint);
            if retry { return true; }
        }
        if type_recovery_boundary_pending(i) { return i.pos() > start; }
        let Some(character) = i.input.remainder().chars().next() else { return i.pos() > start; };
        if character.is_whitespace() { return i.pos() > start; }
        i.input.next();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn parse_type_path_tail<'source, E>(separator: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> TypePathTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if !type_chain_trivia(i, &trivia) { i.rollback(checkpoint); }
    let segment = scan_type_name(i)
        .or_else(|| recover_type_path_for_ast(i).then(|| scan_type_name(i)).flatten())
        .map(|name| Recovered::Complete(match name {
            TypeName::Identifier(word) => TypePathSegment::Identifier(word),
            TypeName::SigilIdentifier(word) => TypePathSegment::SigilIdentifier(word),
        }))
        .unwrap_or(Recovered::Incomplete);
    let end = match &segment {
        Recovered::Complete(segment) => match segment {
            TypePathSegment::Identifier(word) | TypePathSegment::SigilIdentifier(word) => word.range().end,
        },
        Recovered::Incomplete => separator.end,
    };
    TypePathTail { separator: separator.clone(), segment, range: separator.start..end }
}

fn parse_type_arrow_tail<'source, E>(arrow: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> TypeArrowTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if !type_chain_trivia(i, &trivia) { i.rollback(checkpoint); }
    let rhs = i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
        .or_else(|| {
            recover_type_item_for_ast(i)
                .then(|| i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i))))
                .flatten()
        })
        .map(|value| Recovered::Complete(Box::new(value)))
        .unwrap_or(Recovered::Incomplete);
    let end = match &rhs { Recovered::Complete(rhs) => rhs.range.end, Recovered::Incomplete => arrow.end };
    TypeArrowTail { arrow: arrow.clone(), rhs, range: arrow.start..end }
}

fn parse_type_call_tail<'source, E>(open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> TypeCallTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (arguments, _, close) = parse_type_delimited_items(TypeDelimitedOwner::Call, TypeDelimitedShape::Parenthesis, i);
    let end = match &close { Recovered::Complete(close) => close.end, Recovered::Incomplete => i.pos() };
    TypeCallTail { open: open.clone(), arguments, close, range: open.start..end }
}

fn parse_parenthesized_type_group<'source, E>(open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> ParenthesizedTypeGroup<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (elements, trailing_explicit_separator, close) = parse_type_delimited_items(TypeDelimitedOwner::ParenthesizedGroup, TypeDelimitedShape::Parenthesis, i);
    let end = match &close { Recovered::Complete(close) => close.end, Recovered::Incomplete => i.pos() };
    ParenthesizedTypeGroup { open: open.clone(), elements, trailing_explicit_separator, close, range: open.start..end }
}

fn parse_effect_row_type<'source, E>(
    apostrophe: Range<usize>,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EffectRowType<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (items, _, close) = parse_type_delimited_items(TypeDelimitedOwner::EffectRow, TypeDelimitedShape::Bracket, i);
    let end = match &close { Recovered::Complete(close) => close.end, Recovered::Incomplete => i.pos() };
    EffectRowType { apostrophe: apostrophe.clone(), open, items, close, range: apostrophe.start..end }
}

/// Parse the two-level polymorphic-variant primary.  The outer loop is the
/// sole owner of commas and qualifying newlines; the inner loop deliberately
/// leaves every physical newline for that outer judge.
fn parse_polymorphic_variant_type<'source, E>(
    colon: Range<usize>,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> PolymorphicVariantType<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::RightBrace);
    i.local.push_delimiter(Delimiter::Brace);
    i.local.push_stop_set(stops);
    i.local.push_type_delimited_owner(TypeDelimitedOwner::PolymorphicVariant);
    let opening = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent);
    push_layout(layout, i);

    let mut tags = Vec::new();
    let mut trailing_comma = None;
    let mut tag_required = false;
    let mut required_filled = false;
    let mut after_tag = false;
    let mut last_comma = None;
    let close;
    loop {
        // NT-1 / NT-2.
        if let Some(range) = scan_close_brace(i) {
            if tag_required && !required_filled { trailing_comma = last_comma.take(); }
            close = Recovered::Complete(range);
            break;
        }
        if scan_mismatched_record_close(i).is_some() { continue; }

        // NT-3 / NT-4.
        if let Some(comma) = scan_record_comma(i) {
            if tag_required || !after_tag {
                tags.push(Recovered::Incomplete);
                required_filled = true;
            } else {
                required_filled = false;
            }
            tag_required = true;
            after_tag = false;
            last_comma = Some(comma);
            let _ = consume_trivia(i);
            continue;
        }
        if scan_record_semicolon(i).is_some() {
            if active_stop_set(i).contains(StopKind::Semicolon) { close = Recovered::Incomplete; break; }
            let _ = consume_trivia(i);
            continue;
        }

        // NT-5.  Unlike the payload scanner, outer layout owns a qualifying
        // newline.  Same-line trivia is merely leading trivia for a tag.
        let checkpoint = i.checkpoint();
        let gap = consume_trivia(i);
        if trivia_has_newline(&gap) {
            if layout.boundary_after_trivia(&gap, i.local.line().line_indent) != LayoutDelimitedBoundary::ImplicitNewline {
                i.rollback(checkpoint);
                close = Recovered::Incomplete;
                break;
            }
            // The newline itself is an outer boundary.  Re-enter NT so a
            // matching close gets NT-1 priority over the generic boundary.
            if after_tag {
                tag_required = true;
                required_filled = false;
                after_tag = false;
                last_comma = None;
            }
            continue;
        } else if !gap.is_empty() {
            // The AST has no trivia slots at this level; retain the consumed
            // gap exactly as the direct CST does.
        }

        // NT-6: only a plain identifier is a normal tag head.  Other valid
        // primaries consume one recovered tag skeleton rather than becoming a
        // malformed-byte run.
        if let Some(name) = scan_plain_type_identifier(i) {
            tags.push(Recovered::Complete(parse_polymorphic_variant_tag(name, i)));
            tag_required = false;
            required_filled = false;
            after_tag = true;
            continue;
        }
        if let Some(primary) = parse_type_primary_in_context(true, i) {
            let start = primary_range(&primary).start;
            let payloads = parse_polymorphic_variant_payloads(i);
            let end = payloads.last().and_then(|payload| match payload {
                Recovered::Complete(payload) => Some(payload.range.end),
                Recovered::Incomplete => None,
            }).unwrap_or_else(|| primary_range(&primary).end);
            tags.push(Recovered::Complete(PolymorphicVariantTag {
                name: Recovered::Incomplete,
                payloads,
                range: start..end,
            }));
            tag_required = false;
            required_filled = false;
            after_tag = true;
            continue;
        }
        if i.input.remainder().is_empty() || type_recovery_boundary_pending(i) {
            if tag_required && !required_filled { tags.push(Recovered::Incomplete); }
            close = Recovered::Incomplete;
            break;
        }
        // NT-8: consume a maximal non-boundary prefix, then retry at the same
        // tag slot on a primary candidate.
        if consume_polymorphic_variant_invalid_run(i, false).is_some() {
            tags.push(Recovered::Incomplete);
            tag_required = false;
            required_filled = false;
            after_tag = true;
            continue;
        }
        close = Recovered::Incomplete;
        break;
    }
    pop_layout(layout, i);
    assert_eq!(i.local.pop_type_delimited_owner(), Some(TypeDelimitedOwner::PolymorphicVariant));
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    let end = match &close { Recovered::Complete(range) => range.end, Recovered::Incomplete => i.pos() };
    PolymorphicVariantType { colon: colon.clone(), open, tags, trailing_comma, close, range: colon.start..end }
}

fn parse_polymorphic_variant_tag<'source, E>(
    name: WordSpan<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> PolymorphicVariantTag<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = name.range().start;
    let payloads = parse_polymorphic_variant_payloads(i);
    let end = payloads.last().and_then(|payload| match payload {
        Recovered::Complete(payload) => Some(payload.range.end),
        Recovered::Incomplete => None,
    }).unwrap_or_else(|| name.range().end);
    PolymorphicVariantTag { name: Recovered::Complete(name), payloads, range: start..end }
}

fn parse_polymorphic_variant_payloads<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<Recovered<PolymorphicVariantPayload<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut payloads = Vec::new();
    loop {
        let checkpoint = i.checkpoint();
        let boundary_start = i.pos();
        let trivia = consume_trivia(i);
        // IT-1 / IT-2 leave their gap for the outer judge.
        if trivia_has_newline(&trivia) || polymorphic_variant_outer_boundary(i) {
            i.rollback(checkpoint);
            break;
        }
        if type_primary_candidate(i) {
            let boundary = if trivia.is_empty() { Recovered::Incomplete } else { Recovered::Complete(boundary_start..i.pos()) };
            let start = match &boundary { Recovered::Complete(range) => range.start, Recovered::Incomplete => i.pos() };
            let saved_ml = i.local.type_ml_arg();
            i.local.set_type_ml_arg(true);
            let type_expr = i.run(from_fn(|i| parse_type_expression_in_context(false, i)));
            i.local.set_type_ml_arg(saved_ml);
            let end = type_expr.as_ref().map_or(i.pos(), |value| value.range.end);
            payloads.push(Recovered::Complete(PolymorphicVariantPayload {
                boundary,
                type_expr: type_expr.map(|value| Recovered::Complete(Box::new(value))).unwrap_or(Recovered::Incomplete),
                range: start..end,
            }));
            continue;
        }
        if trivia.is_empty() {
            i.rollback(checkpoint);
            break;
        }
        if let Some(range) = consume_polymorphic_variant_invalid_run(i, true) {
            let saved_ml = i.local.type_ml_arg();
            i.local.set_type_ml_arg(true);
            let recovered = i.run(from_fn(|i| parse_type_expression_in_context(false, i)));
            i.local.set_type_ml_arg(saved_ml);
            let end = recovered.as_ref().map_or(range.end, |value| value.range.end);
            payloads.push(Recovered::Complete(PolymorphicVariantPayload {
                boundary: Recovered::Complete(boundary_start..range.start),
                type_expr: recovered.map(|value| Recovered::Complete(Box::new(value))).unwrap_or(Recovered::Incomplete),
                range: boundary_start..end,
            }));
            continue;
        }
        i.rollback(checkpoint);
        break;
    }
    payloads
}

fn polymorphic_variant_outer_boundary<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let remainder = i.input.remainder();
    remainder.is_empty() || matches!(remainder.chars().next(), Some(',' | ';' | '}' | ')' | ']')) || type_recovery_boundary_pending(i)
}

fn consume_polymorphic_variant_invalid_run<E>(i: &mut SynIn<E>, payload: bool) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let start = i.pos();
    let mut end = start;
    loop {
        if end > start && type_primary_candidate(i) { return Some(start..end); }
        if polymorphic_variant_outer_boundary(i) { return (start < end).then_some(start..end); }
        let Some(character) = i.input.remainder().chars().next() else { return (start < end).then_some(start..end); };
        if character.is_whitespace() { return (start < end).then_some(start..end); }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if payload && end > start && type_primary_candidate(i) { return Some(start..end); }
    }
}

fn parse_named_record_type<'source, E>(open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> NamedRecordType<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::RightBrace);
    i.local.push_delimiter(Delimiter::Brace);
    i.local.push_stop_set(stops);
    i.local.push_type_delimited_owner(TypeDelimitedOwner::NamedRecord);
    let opening = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent);
    push_layout(layout, i);
    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close;
    loop {
        if let Some(range) = scan_close_brace(i) { close = Recovered::Complete(range); break; }
        if scan_record_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = consume_trivia(i);
            if let Some(range) = scan_close_brace(i) { close = Recovered::Complete(range); break; }
            continue;
        }
        if scan_record_semicolon(i).is_some() {
            let _ = consume_trivia(i);
            continue;
        }
        if let Some(field) = parse_type_record_field(i) {
            fields.push(Recovered::Complete(field));
        } else if recover_record_item_for_ast(i) {
            fields.push(Recovered::Incomplete);
            let _ = consume_trivia(i);
            continue;
        } else {
            fields.push(Recovered::Incomplete);
            close = Recovered::Incomplete;
            break;
        }
        let trivia = consume_trivia(i);
        if let Some(comma) = scan_record_comma(i) {
            let post = consume_trivia(i);
            if let Some(range) = scan_close_brace(i) {
                trailing_comma = Some(comma);
                close = Recovered::Complete(range);
                break;
            }
            if post.is_empty() && i.input.remainder().is_empty() {
                fields.push(Recovered::Incomplete);
                close = Recovered::Incomplete;
                break;
            }
            continue;
        }
        if scan_record_semicolon(i).is_some() {
            let _ = consume_trivia(i);
            continue;
        }
        if let Some(range) = scan_close_brace(i) { close = Recovered::Complete(range); break; }
        match layout.boundary_after_trivia(&trivia, i.local.line().line_indent) {
            LayoutDelimitedBoundary::ImplicitNewline => continue,
            LayoutDelimitedBoundary::None if named_record_next_field_candidate(i, &trivia) => continue,
            _ => { close = Recovered::Incomplete; break; }
        }
    }
    pop_layout(layout, i);
    assert_eq!(i.local.pop_type_delimited_owner(), Some(TypeDelimitedOwner::NamedRecord));
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    let end = match &close { Recovered::Complete(range) => range.end, Recovered::Incomplete => i.pos() };
    NamedRecordType { open: open.clone(), fields, trailing_comma, close, range: open.start..end }
}

fn parse_type_record_field<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<TypeRecordField<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let (name, colon) = if let Some(name) = scan_plain_type_identifier(i) {
        let checkpoint = i.checkpoint();
        let trivia = consume_trivia(i);
        if !type_chain_trivia(i, &trivia) { i.rollback(checkpoint); }
        let colon = scan_exact_colon(i).map(Recovered::Complete).unwrap_or_else(|| {
            let _ = scan_exact_equals(i);
            Recovered::Incomplete
        });
        (Recovered::Complete(name), colon)
    } else if let Some(colon) = scan_exact_colon(i) {
        (Recovered::Incomplete, Recovered::Complete(colon))
    } else if let Some((_, colon)) = scan_malformed_record_name_colon(i) {
        (Recovered::Incomplete, Recovered::Complete(colon))
    } else {
        return None;
    };
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    if !type_chain_trivia(i, &trivia) { i.rollback(checkpoint); }
    let type_expr = i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
        .map(|value| Recovered::Complete(Box::new(value)))
        .unwrap_or(Recovered::Incomplete);
    let end = match &type_expr { Recovered::Complete(value) => value.range.end, Recovered::Incomplete => match &colon { Recovered::Complete(colon) => colon.end, Recovered::Incomplete => match &name { Recovered::Complete(name) => name.range().end, Recovered::Incomplete => start } } };
    Some(TypeRecordField { name, colon, type_expr, range: start..end })
}

fn parse_type_delimited_items<'source, E>(
    owner: TypeDelimitedOwner,
    shape: TypeDelimitedShape,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (Vec<Recovered<TypeExpression<'source>>>, Option<TypeExplicitSeparator>, Recovered<Range<usize>>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    i.local.push_delimiter(shape.delimiter());
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::Semicolon).with(shape.close_stop());
    i.local.push_stop_set(stops);
    i.local.push_type_delimited_owner(owner);
    let opening = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent);
    push_layout(layout, i);
    let mut items = Vec::new();
    let mut trailing = None;
    let close;
    loop {
        if let Some(range) = scan_close_delimiter(shape, i) { close = Recovered::Complete(range); break; }
        if scan_mismatched_close_for(shape.delimiter(), i).is_some() { close = Recovered::Incomplete; break; }
        if scan_separator(i).is_some() {
            items.push(Recovered::Incomplete);
            let _ = consume_trivia(i);
            if let Some(range) = scan_close_delimiter(shape, i) {
                close = Recovered::Complete(range);
                break;
            }
            continue;
        }
        if let Some(item) = i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i))) {
            items.push(Recovered::Complete(item));
        } else if recover_type_item_for_ast(i) {
            continue;
        } else {
            items.push(Recovered::Incomplete);
            let _ = scan_mismatched_close_for(shape.delimiter(), i);
            close = Recovered::Incomplete;
            break;
        }
        let trivia = consume_trivia(i);
        if let Some(separator) = scan_separator(i) {
            let post = consume_trivia(i);
            if let Some(range) = scan_close_delimiter(shape, i) {
                trailing = Some(separator);
                close = Recovered::Complete(range);
                break;
            }
            if post.is_empty() && i.input.remainder().is_empty() {
                items.push(Recovered::Incomplete);
                close = Recovered::Incomplete;
                break;
            }
            continue;
        }
        match layout.boundary_after_trivia(&trivia, i.local.line().line_indent) {
            LayoutDelimitedBoundary::ImplicitNewline => {
                if let Some(range) = scan_close_delimiter(shape, i) { close = Recovered::Complete(range); break; }
                continue;
            }
            LayoutDelimitedBoundary::DeeperNewline => {
                close = Recovered::Incomplete;
                break;
            }
            LayoutDelimitedBoundary::None => {
                if let Some(range) = scan_close_delimiter(shape, i) { close = Recovered::Complete(range); break; }
                if type_primary_candidate(i) {
                    // A nested ML argument may intentionally stop before this
                    // primary.  The direct path commits the separator Missing;
                    // the source-free AST retains the same next-item slot.
                    continue;
                }
                let _ = scan_mismatched_close_for(shape.delimiter(), i);
                close = Recovered::Incomplete;
                break;
            }
        }
    }
    pop_layout(layout, i);
    assert_eq!(i.local.pop_type_delimited_owner(), Some(owner));
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(shape.delimiter()));
    (items, trailing, close)
}

/// The AST is intentionally source-free: direct CST owns the Error node and
/// typed recovery record.  This counterpart only advances across the same
/// malformed non-empty prefix, then lets the normal item loop retry a valid
/// primary or observe its delimiter.
fn recover_type_item_for_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if i.pos() > start && type_primary_candidate(i) {
            return true;
        }
        if type_recovery_boundary_pending(i) {
            return i.pos() > start;
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return i.pos() > start;
        };
        if character.is_whitespace() || matches!(character, ':') {
            return i.pos() > start;
        }
        i.input.next();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn recover_record_item_for_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    consume_record_invalid_run(i).is_some()
}

fn recover_type_path_for_ast<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if i.pos() > start {
            let checkpoint = i.checkpoint();
            let retry = scan_type_name(i).is_some();
            i.rollback(checkpoint);
            if retry { return true; }
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return i.pos() > start;
        };
        if character.is_whitespace() || matches!(character, ':' | ')' | ']' | '}' | ',' | ';') {
            return i.pos() > start;
        }
        i.input.next();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

#[derive(Clone, Copy)]
enum TypeName<'source> { Identifier(WordSpan<'source>), SigilIdentifier(WordSpan<'source>) }

fn scan_type_name<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<TypeName<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(word) = i.run(scan_path_segment) else {
        i.rollback(checkpoint);
        return None;
    };
    match word.text().chars().next() {
        Some('\'') => Some(TypeName::SigilIdentifier(word)),
        Some('$' | '&') => { i.rollback(checkpoint); None }
        _ => Some(TypeName::Identifier(word)),
    }
}

fn type_name_kind(name: TypeName<'_>) -> SyntaxKind {
    match name {
        TypeName::Identifier(_) => SyntaxKind::Identifier,
        TypeName::SigilIdentifier(_) => SyntaxKind::SigilIdentifier,
    }
}

fn type_name_range(name: TypeName<'_>) -> Range<usize> {
    match name {
        TypeName::Identifier(word) | TypeName::SigilIdentifier(word) => word.range(),
    }
}

fn separator_kind(separator: &TypeExplicitSeparator) -> SyntaxKind {
    match separator {
        TypeExplicitSeparator::Comma(_) => SyntaxKind::Comma,
        TypeExplicitSeparator::Semicolon(_) => SyntaxKind::Semicolon,
    }
}

fn separator_range(separator: &TypeExplicitSeparator) -> Range<usize> {
    match separator {
        TypeExplicitSeparator::Comma(range) | TypeExplicitSeparator::Semicolon(range) => range.clone(),
    }
}

fn type_primary_candidate<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    type_primary_candidate_in_context(true, i)
}

fn type_primary_candidate_in_context<E>(allow_forall: bool, i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let candidate = parse_type_primary_in_context(allow_forall, i).is_some();
    i.rollback(checkpoint);
    candidate
}

fn direct_type_primary_candidate<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type_primary_candidate(i)
}

fn scan_open_parenthesis<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Open(Delimiter::Parenthesis) { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_open_brace<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Open(Delimiter::Brace) { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_effect_row_open<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, Range<usize>)>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let start = i.pos();
    if !i.input.remainder().starts_with("'[") {
        return None;
    }
    i.input.next()?;
    let middle = i.pos();
    i.input.next()?;
    let end = i.pos();
    if middle == start || end == middle {
        i.rollback(checkpoint);
        return None;
    }
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some((start..middle, middle..end))
}

/// The compound introducer is deliberately probed as one atomic spelling.
/// A bare colon remains available to the caller's structural grammar.
fn scan_polymorphic_variant_open<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, Range<usize>)>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let start = i.pos();
    if !i.input.remainder().starts_with(":{") { return None; }
    i.input.next()?;
    let middle = i.pos();
    i.input.next()?;
    let end = i.pos();
    if middle == start || end == middle { i.rollback(checkpoint); return None; }
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    Some((start..middle, middle..end))
}

fn scan_close_delimiter<'source, E>(shape: TypeDelimitedShape, i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Close(shape.delimiter()) { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_mismatched_close_for<'source, E>(delimiter: Delimiter, i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    let owned_by_outer = match punctuation.kind() {
        PunctuationKind::Close(Delimiter::Parenthesis) => active_stop_set(i).contains(StopKind::RightParenthesis),
        PunctuationKind::Close(Delimiter::Bracket) => active_stop_set(i).contains(StopKind::RightBracket),
        PunctuationKind::Close(Delimiter::Brace) => active_stop_set(i).contains(StopKind::RightBrace),
        _ => false,
    };
    if matches!(punctuation.kind(), PunctuationKind::Close(found) if found != delimiter) && !owned_by_outer {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn scan_close_brace<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Close(Delimiter::Brace) { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_record_comma<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Comma { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_record_semicolon<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Semicolon { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_exact_colon<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Colon { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_exact_equals<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let start = i.pos();
    if !i.input.remainder().starts_with('=') || i.input.remainder().starts_with("==") {
        return None;
    }
    i.input.next()?;
    let end = i.pos();
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);
    if end == start { i.rollback(checkpoint); None } else { Some(start..end) }
}

fn scan_plain_type_identifier<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<WordSpan<'source>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let TypeName::Identifier(word) = scan_type_name(i)? else {
        i.rollback(checkpoint);
        return None;
    };
    Some(word)
}

fn scan_malformed_record_name_colon<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, Range<usize>)>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let mut end = start;
    loop {
        if end > start && scan_exact_colon(i).is_some() {
            let colon_end = i.pos();
            return Some((start..end, end..colon_end));
        }
        let Some(character) = i.input.remainder().chars().next() else { i.rollback(checkpoint); return None; };
        if character.is_whitespace() || matches!(character, ',' | '}' | ':') {
            i.rollback(checkpoint);
            return None;
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn named_record_next_field_candidate<E>(i: &mut SynIn<E>, leading: &TriviaRun) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    if leading.is_empty() || trivia_has_newline(leading) || i.local.type_delimited_owner() != Some(TypeDelimitedOwner::NamedRecord) {
        return false;
    }
    let checkpoint = i.checkpoint();
    let candidate = scan_plain_type_identifier(i).is_some_and(|_| {
        let gap = consume_trivia(i);
        type_chain_trivia(i, &gap) && scan_exact_colon(i).is_some()
    });
    i.rollback(checkpoint);
    candidate
}

fn scan_mismatched_record_close<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    let outer_owned = match punctuation.kind() {
        PunctuationKind::Close(Delimiter::Parenthesis) => active_stop_set(i).contains(StopKind::RightParenthesis),
        PunctuationKind::Close(Delimiter::Bracket) => active_stop_set(i).contains(StopKind::RightBracket),
        _ => false,
    };
    if matches!(punctuation.kind(), PunctuationKind::Close(delimiter) if delimiter != Delimiter::Brace) && !outer_owned {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

fn scan_separator<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<TypeExplicitSeparator>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    match punctuation.kind() {
        PunctuationKind::Comma => Some(TypeExplicitSeparator::Comma(punctuation.range())),
        PunctuationKind::Semicolon => Some(TypeExplicitSeparator::Semicolon(punctuation.range())),
        _ => { i.rollback(checkpoint); None }
    }
}

fn scan_exact_colon_colon<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::ColonColon { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_exact_arrow<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let start = i.pos();
    if !i.input.remainder().starts_with("->") || i.input.remainder().starts_with("->>") { return None; }
    i.input.next()?; i.input.next()?;
    let end = i.pos();
    let mut line = i.local.line(); line.at_line_start = false; i.local.set_line(line);
    if end == start { i.rollback(checkpoint); None } else { Some(start..end) }
}

fn consume_trivia<E>(i: &mut SynIn<E>) -> TriviaRun
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> { i.run(scan_trivia).expect("trivia scanning is total") }

fn consume_direct_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> TriviaRun
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| consume_trivia(probe.input()))
}

/// Consume post-introducer trivia only when it remains inside this type
/// chain.  An equal-or-shallower newline belongs to the caller's layout
/// owner, so it must remain unread beside a missing path/arrow RHS.
fn consume_direct_type_chain_trivia<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = consume_trivia(i);
        if type_chain_trivia(i, &trivia) {
            Some(trivia)
        } else {
            i.rollback(checkpoint);
            None
        }
    })
}

fn emit_type_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: at..at },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

fn emit_type_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: TypeRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_error_with_role(committed, GrammarRole::Type(role), range, expected);
}

fn emit_error_with_role<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey { role, range: range.clone() },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeDelimitedItemRecovery {
    Retry,
    Boundary,
}

/// Recover one malformed call/group item without crossing a delimiter or an
/// active caller stop.  A non-empty Error run ending at a boundary is still a
/// committed recovery site, but it is not an item retry and must not make the
/// list synthesize a second Missing item from the same cause.
fn direct_type_delimited_item_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: TypeRole,
) -> Option<TypeDelimitedItemRecovery>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            if end > start && direct_type_primary_candidate(i) {
                return Some((start..end, TypeDelimitedItemRecovery::Retry));
            }
            if type_recovery_boundary_pending(i) {
                return (start < end).then_some((start..end, TypeDelimitedItemRecovery::Boundary));
            }
            let Some(_) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, TypeDelimitedItemRecovery::Boundary));
            };
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    let Some((range, recovery)) = recovered else { return None; };
    emit_type_error(committed, role, range, ExpectedSyntax::TypeExpression);
    Some(recovery)
}

/// Generic primary recovery used by the mandatory and arrow-RHS entries.
/// Delimited calls and groups use the boundary-aware variant above because
/// their close and separator slots need separate ownership.
fn direct_type_item_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: TypeRole,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some(start..end);
            };
            if matches!(character, ')' | ']' | '}' | ',' | ';') { return None; }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if direct_type_primary_candidate(i) { return Some(start..end); }
        }
    });
    let Some(range) = recovered else { return false; };
    emit_type_error(committed, role, range, ExpectedSyntax::TypeExpression);
    true
}

/// Boundaries are never consumed by a malformed item scanner.  Delimiter
/// closers are handled by the local close slot; an active stop is returned to
/// the caller that installed it.
fn type_recovery_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let remainder = i.input.remainder();
    let Some(character) = remainder.chars().next() else { return true; };
    if matches!(character, ')' | ']' | '}' | ',' | ';') {
        return true;
    }
    let stops = active_stop_set(i);
    (character == ':' && stops.contains(StopKind::Colon))
        || (character == '=' && stops.contains(StopKind::Equal))
        || (character == '\n' && stops.contains(StopKind::Newline))
        || (character == '\r' && stops.contains(StopKind::Newline))
        || (remainder.starts_with("->") && stops.contains(StopKind::Arrow))
}

/// A type parser may be nested beneath an owner that reserves an arrow.  The
/// structural tail judge must yield before accepting that arrow, just as its
/// malformed-item scanner does.
fn type_active_tail_stop_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !active_stop_set(i).contains(StopKind::Arrow) {
        return false;
    }
    let checkpoint = i.checkpoint();
    let pending = scan_exact_arrow(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn consume_type_path_invalid_run<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut end = start;
    loop {
        if start < end {
            let checkpoint = i.checkpoint();
            let retry = scan_type_name(i).is_some();
            i.rollback(checkpoint);
            if retry { return Some(start..end); }
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < end).then_some(start..end);
        };
        if character.is_whitespace() || matches!(character, ':' | ')' | ']' | '}' | ',' | ';') {
            return (start < end).then_some(start..end);
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn consume_record_invalid_run<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut end = start;
    loop {
        if end > start {
            let checkpoint = i.checkpoint();
            let retry = record_field_head_candidate(i);
            i.rollback(checkpoint);
            if retry { return Some(start..end); }
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < end).then_some(start..end);
        };
        if character.is_whitespace() || matches!(character, ',' | '}') {
            return (start < end).then_some(start..end);
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn consume_record_colon_invalid_run<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let start = i.pos();
    let mut end = start;
    loop {
        if end > start {
            let checkpoint = i.checkpoint();
            let retry = scan_exact_colon(i).is_some() || type_primary_candidate(i);
            i.rollback(checkpoint);
            if retry { return Some(start..end); }
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < end).then_some(start..end);
        };
        if character.is_whitespace() || matches!(character, ',' | '}') {
            return (start < end).then_some(start..end);
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

fn record_field_head_candidate<E>(i: &mut SynIn<E>) -> bool
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let candidate = scan_plain_type_identifier(i).is_some_and(|_| {
        let trivia = consume_trivia(i);
        type_chain_trivia(i, &trivia) && scan_exact_colon(i).is_some()
    });
    i.rollback(checkpoint);
    candidate
}

fn type_chain_trivia<E>(i: &SynIn<E>, trivia: &TriviaRun) -> bool where E: ErrorSink<usize> {
    !trivia_has_newline(trivia) || i.local.line().line_indent > i.local.indentation_baseline().map_or(0, |baseline| baseline.column)
}
fn is_outer_newline_boundary<E>(i: &SynIn<E>, trivia: &TriviaRun) -> bool where E: ErrorSink<usize> { trivia_has_newline(trivia) && !type_chain_trivia(i, trivia) }
fn trivia_has_newline(trivia: &TriviaRun) -> bool { trivia.parts().iter().any(|part| matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline)) }
fn active_stop_set<E>(i: &SynIn<E>) -> StopSet where E: ErrorSink<usize> { i.local.stop_set().unwrap_or_default() }
fn push_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>) where E: ErrorSink<usize> { i.local.push_indentation_baseline(IndentationBaseline { column: layout.base_indent(), kind: IndentationBaselineKind::Introducer }); }
fn pop_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>) where E: ErrorSink<usize> { assert_eq!(i.local.pop_indentation_baseline(), Some(IndentationBaseline { column: layout.base_indent(), kind: IndentationBaselineKind::Introducer })); }
fn primary_range(primary: &TypePrimary<'_>) -> Range<usize> { match primary { TypePrimary::Atom(atom) => match atom { TypeAtom::Identifier(word) | TypeAtom::SigilIdentifier(word) => word.range(), TypeAtom::Number(number) => number.range.clone() }, TypePrimary::Parenthesized(group) => group.range.clone(), TypePrimary::Record(record) => record.range.clone(), TypePrimary::Forall(forall) => forall.range.clone(), TypePrimary::EffectRow(row) => row.range.clone(), TypePrimary::PolymorphicVariant(variant) => variant.range.clone() } }
fn postfix_range_end(tail: &TypePostfixTail<'_>) -> usize { match tail { TypePostfixTail::Path(tail) => tail.range.end, TypePostfixTail::Call(tail) => tail.range.end, TypePostfixTail::Apply(tail) => tail.range.end } }
#[cfg(test)]
mod tests {
    use super::*;

    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxNode,
        input::SourceInput,
        session::{FullCstOutput, GrammarRole, ParseLocal, StopKind, StopSet, TypeRole},
    };

    fn parse<'source>(source: &'source str) -> TypeExpression<'source> {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let value = i.run(from_fn(parse_type_expression));
        assert!(value.is_some(), "type expression AST for {source:?}; remainder={:?}", i.input.remainder());
        let value = value.expect("asserted above");
        assert_eq!(i.input.remainder(), "", "complete type source");
        value
    }

    fn parse_prefix<'source>(source: &'source str) -> (&'source str, TypeExpression<'source>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let value = i.run(from_fn(parse_type_expression)).expect("type expression AST prefix");
        (i.input.remainder(), value)
    }

    fn parse_prefix_with_outer_stop<'source>(
        source: &'source str,
        stop: StopKind,
    ) -> (&'source str, TypeExpression<'source>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(StopSet::default().with(stop));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let value = i.run(from_fn(parse_type_expression)).expect("type expression AST prefix with outer stop");
        (i.input.remainder(), value)
    }

    fn primary_candidate(source: &str) -> bool {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        type_primary_candidate(&mut i)
    }

    fn parse_direct(source: &str) -> SyntaxNode {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression(&mut committed).expect("direct type expression");
        let remainder = committed.probe(|probe| probe.input().input.remainder());
        assert_eq!(remainder, "", "complete direct type source");
        committed.finish_node();
        SyntaxNode::new_root(committed.into_output().finish_complete())
    }

    fn parse_direct_mandatory_recovered(
        source: &str,
        outer_missing_role: Option<GrammarRole>,
    ) -> Vec<crate::session::CommittedRecoveryRecord> {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression_with_outer_missing_role(outer_missing_role, &mut committed);
        committed.finish_node();
        committed.into_output().committed_recoveries().to_vec()
    }

    fn parse_direct_recovered(source: &str) -> Vec<crate::session::CommittedRecoveryRecord> {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression(&mut committed).expect("direct type expression");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "");
        committed.finish_node();
        committed.into_output().committed_recoveries().to_vec()
    }

    fn parse_direct_prefix_with_outer_stop(
        source: &str,
        stop: StopKind,
    ) -> (String, Vec<crate::session::CommittedRecoveryRecord>) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(StopSet::default().with(stop));
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression(&mut committed).expect("direct type expression prefix with outer stop");
        let remainder = committed.probe(|probe| probe.input().input.remainder().to_owned());
        committed.finish_node();
        let output = committed.into_output();
        (remainder, output.committed_recoveries().to_vec())
    }

    #[test]
    fn type_apply_path_precedence_uses_the_ml_boundary() {
        let tight = parse("F A::B");
        assert!(matches!(tight.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.postfix.as_slice(), [TypePostfixTail::Path(_)])));

        let outer = parse("F A ::B");
        assert!(matches!(outer.postfix.as_slice(), [TypePostfixTail::Apply(_), TypePostfixTail::Path(_)]));
    }

    #[test]
    fn type_core_forms_keep_fixed_flat_structure() {
        let value = parse("List(Int)::Result Arg -> Out -> Final");
        assert!(matches!(value.primary, TypePrimary::Atom(TypeAtom::Identifier(_))));
        assert!(matches!(value.postfix.as_slice(), [
            TypePostfixTail::Call(_),
            TypePostfixTail::Path(_),
            TypePostfixTail::Apply(_),
        ]));
        assert!(matches!(value.arrow, Some(TypeArrowTail { rhs: Recovered::Complete(rhs), .. })
            if rhs.arrow.is_some()));
        assert_eq!(parse_direct("List(Int)::Result Arg -> Out -> Final").to_string(), "List(Int)::Result Arg -> Out -> Final");
    }

    #[test]
    fn type_arrow_is_right_associative_without_an_operator_table() {
        let value = parse("A -> B -> C");
        assert!(matches!(value.arrow, Some(TypeArrowTail { rhs: Recovered::Complete(rhs), .. })
            if matches!(rhs.arrow, Some(TypeArrowTail { rhs: Recovered::Complete(_), .. }))));
    }

    #[test]
    fn type_call_and_group_accept_comma_and_semicolon() {
        let call = parse("List(Int; String)");
        assert!(matches!(call.postfix.as_slice(), [TypePostfixTail::Call(tail)] if tail.arguments.len() == 2));
        let group = parse("(Int, String)");
        assert!(matches!(group.primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup { ref elements, .. }) if elements.len() == 2));
        assert_eq!(parse_direct("List(Int; String)").to_string(), "List(Int; String)");
        assert_eq!(parse_direct("(Int, String)").to_string(), "(Int, String)");
        let trailing = parse("List(Int,)");
        assert!(matches!(trailing.postfix.as_slice(), [TypePostfixTail::Call(tail)] if tail.arguments.len() == 1));
        assert_eq!(parse_direct("List(Int,)").to_string(), "List(Int,)");
    }

    #[test]
    fn type_groups_reuse_layout_boundaries_without_synthetic_separator_nodes() {
        let group = parse("(\n  A\n  B\n)");
        assert!(matches!(group.primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            ref elements, ..
        }) if elements.len() == 2));
        assert_eq!(parse_direct("(\n  A\n  B\n)").to_string(), "(\n  A\n  B\n)");
    }

    #[test]
    fn type_apply_uses_one_argument_per_nonempty_trivia_boundary() {
        let value = parse("Dict String Int");
        assert!(matches!(value.postfix.as_slice(), [
            TypePostfixTail::Apply(_),
            TypePostfixTail::Apply(_),
        ]));
        assert_eq!(parse_direct("Dict String Int").to_string(), "Dict String Int");
    }

    #[test]
    fn type_apply_respects_comment_and_newline_boundaries() {
        assert!(matches!(parse("List/* note */(Int)").postfix.as_slice(), [TypePostfixTail::Apply(_)]));
        assert!(matches!(parse("List\n  Int").postfix.as_slice(), [TypePostfixTail::Apply(_)]));
        let (remainder, value) = parse_prefix("List\nInt");
        assert!(value.postfix.is_empty());
        assert_eq!(remainder, "\nInt");
        assert_eq!(parse_direct("List/* note */(Int)").to_string(), "List/* note */(Int)");
        assert_eq!(parse_direct("List\n  Int").to_string(), "List\n  Int");
    }

    #[test]
    fn path_and_arrow_missing_rhs_leave_an_outer_layout_newline_unconsumed() {
        let (remainder, path) = parse_prefix("A::\nB");
        assert_eq!(remainder, "\nB");
        assert!(matches!(path.postfix.as_slice(), [TypePostfixTail::Path(TypePathTail {
            segment: Recovered::Incomplete, ..
        })]));

        let (remainder, arrow) = parse_prefix("A ->\nB");
        assert_eq!(remainder, "\nB");
        assert!(matches!(arrow.arrow, Some(TypeArrowTail {
            rhs: Recovered::Incomplete, ..
        })));
    }

    #[test]
    fn type_primary_and_path_segments_keep_their_own_surface_categories() {
        assert!(matches!(parse("'a").primary, TypePrimary::Atom(TypeAtom::SigilIdentifier(_))));
        assert!(matches!(parse("42").primary, TypePrimary::Atom(TypeAtom::Number(_))));
        let path = parse("A::'b");
        assert!(matches!(path.postfix.as_slice(), [TypePostfixTail::Path(TypePathTail {
            segment: Recovered::Complete(TypePathSegment::SigilIdentifier(_)), ..
        })]));
        assert_eq!(parse_direct("A::'b").to_string(), "A::'b");
    }

    #[test]
    fn mandatory_type_entry_keeps_the_outer_missing_primary_site_typed() {
        let recoveries = parse_direct_mandatory_recovered("", None);
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::Primary)
                && record.site.range == (0..0)));
    }

    #[test]
    fn mandatory_type_entry_allows_only_its_outer_missing_primary_role_to_be_overridden() {
        let recoveries = parse_direct_mandatory_recovered(
            "",
            Some(GrammarRole::Type(TypeRole::ArrowRhs)),
        );
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ArrowRhs)
                && record.site.range == (0..0)));
    }

    #[test]
    fn mandatory_type_entry_recovers_a_nonempty_primary_prefix_before_retrying() {
        let recoveries = parse_direct_mandatory_recovered("@A", None);
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::Primary)
                && record.site.range == (0..1)
                && record.kind == crate::session::RecoveryKind::Error));
    }

    #[test]
    fn type_call_missing_item_and_close_keep_distinct_typed_slots() {
        let recoveries = parse_direct_recovered("T(");
        assert!(recoveries.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::CallArgument)));
        assert!(recoveries.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: crate::session::ConstructRole::TypeCall,
            delimiter: crate::session::Delimiter::Parenthesis,
        })));
        let leading = parse_direct_recovered("T(,)");
        assert!(matches!(leading.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && record.site.range == (2..2)));
        let separator_at_eof = parse_direct_recovered("T(A;");
        assert!(separator_at_eof.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && record.kind == crate::session::RecoveryKind::Missing
                && record.site.range == (4..4)));
        assert!(separator_at_eof.iter().any(|record| matches!(record.site.role,
            GrammarRole::ClosingDelimiter { owner: crate::session::ConstructRole::TypeCall,
                delimiter: crate::session::Delimiter::Parenthesis }
        ) && record.kind == crate::session::RecoveryKind::Missing));
    }

    #[test]
    fn call_and_group_retry_a_same_line_item_after_a_nested_ml_argument_stops() {
        let call = parse("G T(F A)");
        assert!(matches!(call.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.postfix.as_slice(), [TypePostfixTail::Call(tail)]
                if tail.arguments.len() == 2)));
        let call_recoveries = parse_direct_recovered("G T(F A)");
        assert!(matches!(call_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::CallArgumentSeparator)
                && record.site.range == (6..6)
                && record.kind == crate::session::RecoveryKind::Missing));

        let group = parse("G (F A)");
        assert!(matches!(group.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
                ref elements, ..
            }) if elements.len() == 2)));
        let group_recoveries = parse_direct_recovered("G (F A)");
        assert!(matches!(group_recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ParenthesizedSeparator)
                && record.site.range == (5..5)
                && record.kind == crate::session::RecoveryKind::Missing));
    }

    #[test]
    fn call_and_group_recovery_leave_outer_owned_boundaries_unconsumed() {
        let (call_remainder, call_ast) = parse_prefix_with_outer_stop("T(@]", StopKind::RightBracket);
        assert_eq!(call_remainder, "]");
        assert!(matches!(call_ast.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Incomplete, ..
        })]));
        let (call_remainder, call_recoveries) = parse_direct_prefix_with_outer_stop("T(@]", StopKind::RightBracket);
        assert_eq!(call_remainder, "]");
        assert!(matches!(call_recoveries.as_slice(), [error, close]
            if error.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && error.site.range == (2..3)
                && error.kind == crate::session::RecoveryKind::Error
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::TypeCall,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (3..3)
                && close.kind == crate::session::RecoveryKind::Missing));

        let (group_remainder, group_ast) = parse_prefix_with_outer_stop("(@]", StopKind::RightBracket);
        assert_eq!(group_remainder, "]");
        assert!(matches!(group_ast.primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            close: Recovered::Incomplete, ..
        })));
        let (group_remainder, group_recoveries) = parse_direct_prefix_with_outer_stop("(@]", StopKind::RightBracket);
        assert_eq!(group_remainder, "]");
        assert!(matches!(group_recoveries.as_slice(), [error, close]
            if error.site.role == GrammarRole::Type(TypeRole::ParenthesizedItem)
                && error.site.range == (1..2)
                && error.kind == crate::session::RecoveryKind::Error
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::ParenthesizedTypeGroup,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (2..2)
                && close.kind == crate::session::RecoveryKind::Missing));

        let (arrow_remainder, arrow_ast) = parse_prefix_with_outer_stop("T(@->", StopKind::Arrow);
        assert_eq!(arrow_remainder, "->");
        assert!(matches!(arrow_ast.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Incomplete, ..
        })]));
        let (arrow_remainder, arrow_recoveries) = parse_direct_prefix_with_outer_stop("T(@->", StopKind::Arrow);
        assert_eq!(arrow_remainder, "->");
        assert!(matches!(arrow_recoveries.as_slice(), [error, close]
            if error.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && error.site.range == (2..3)
                && error.kind == crate::session::RecoveryKind::Error
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::TypeCall,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (3..3)
                && close.kind == crate::session::RecoveryKind::Missing));

        let (call_separator_remainder, call_separator_ast) = parse_prefix_with_outer_stop("T(A,]", StopKind::RightBracket);
        assert_eq!(call_separator_remainder, "]");
        assert!(matches!(call_separator_ast.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            arguments, close: Recovered::Incomplete, ..
        })] if matches!(arguments.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])));
        let (call_separator_remainder, call_separator_recoveries) = parse_direct_prefix_with_outer_stop("T(A,]", StopKind::RightBracket);
        assert_eq!(call_separator_remainder, "]");
        assert!(matches!(call_separator_recoveries.as_slice(), [item, close]
            if item.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && item.site.range == (4..4)
                && item.kind == crate::session::RecoveryKind::Missing
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::TypeCall,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (4..4)
                && close.kind == crate::session::RecoveryKind::Missing));

        let (group_separator_remainder, group_separator_ast) = parse_prefix_with_outer_stop("(A;]", StopKind::RightBracket);
        assert_eq!(group_separator_remainder, "]");
        assert!(matches!(group_separator_ast.primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            ref elements, close: Recovered::Incomplete, ..
        }) if matches!(elements.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])));
        let (group_separator_remainder, group_separator_recoveries) = parse_direct_prefix_with_outer_stop("(A;]", StopKind::RightBracket);
        assert_eq!(group_separator_remainder, "]");
        assert!(matches!(group_separator_recoveries.as_slice(), [item, close]
            if item.site.role == GrammarRole::Type(TypeRole::ParenthesizedItem)
                && item.site.range == (3..3)
                && item.kind == crate::session::RecoveryKind::Missing
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::ParenthesizedTypeGroup,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (3..3)
                && close.kind == crate::session::RecoveryKind::Missing));
    }

    #[test]
    fn call_and_group_delimited_recovery_rows_keep_ast_and_direct_slots_in_lockstep() {
        for source in ["T(A,)", "(A;)", "T(A,\n)", "(A;\n)"] {
            assert!(parse_direct_recovered(source).is_empty(), "valid trailing boundary: {source}");
        }
        assert!(matches!(parse("(A,)").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            trailing_explicit_separator: Some(TypeExplicitSeparator::Comma(_)), ..
        })));

        let call_leading = parse_direct_recovered("T(,,A)");
        assert!(matches!(call_leading.as_slice(), [first, second]
            if first.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && first.site.range == (2..2)
                && second.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && second.site.range == (3..3)));
        assert!(matches!(parse("T(,,A)").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            arguments, ..
        })] if matches!(arguments.as_slice(), [Recovered::Incomplete, Recovered::Incomplete, Recovered::Complete(_)])));

        let group_leading = parse_direct_recovered("(,,A)");
        assert!(matches!(group_leading.as_slice(), [first, second]
            if first.site.role == GrammarRole::Type(TypeRole::ParenthesizedItem)
                && first.site.range == (1..1)
                && second.site.role == GrammarRole::Type(TypeRole::ParenthesizedItem)
                && second.site.range == (2..2)));
        assert!(matches!(parse("(,,A)").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            ref elements, ..
        }) if matches!(elements.as_slice(), [Recovered::Incomplete, Recovered::Incomplete, Recovered::Complete(_)])));

        let call_eof = parse_direct_recovered("T(A,");
        assert!(matches!(call_eof.as_slice(), [item, close]
            if item.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && item.site.range == (4..4)
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::TypeCall,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (4..4)));
        assert!(matches!(parse("T(A,").postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            arguments, close: Recovered::Incomplete, ..
        })] if matches!(arguments.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])));

        let group_eof = parse_direct_recovered("(A;");
        assert!(matches!(group_eof.as_slice(), [item, close]
            if item.site.role == GrammarRole::Type(TypeRole::ParenthesizedItem)
                && item.site.range == (3..3)
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::ParenthesizedTypeGroup,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && close.site.range == (3..3)));
        assert!(matches!(parse("(A;").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            ref elements, close: Recovered::Incomplete, ..
        }) if matches!(elements.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])));

        let group_malformed = parse_direct_recovered("(@A)");
        assert!(matches!(group_malformed.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ParenthesizedItem)
                && record.site.range == (1..2)
                && record.kind == crate::session::RecoveryKind::Error));
        assert!(matches!(parse("(@A)").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            ref elements, ..
        }) if matches!(elements.as_slice(), [Recovered::Complete(_)])));

        let group_close = parse_direct_recovered("(A]");
        assert!(matches!(group_close.as_slice(), [error, missing]
            if matches!(error.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::ParenthesizedTypeGroup,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && error.site.range == (2..3)
                && error.kind == crate::session::RecoveryKind::Error
                && matches!(missing.site.role, GrammarRole::ClosingDelimiter {
                    owner: crate::session::ConstructRole::ParenthesizedTypeGroup,
                    delimiter: crate::session::Delimiter::Parenthesis,
                })
                && missing.site.range == (3..3)
                && missing.kind == crate::session::RecoveryKind::Missing));
        assert!(matches!(parse("(A]").primary, TypePrimary::Parenthesized(ParenthesizedTypeGroup {
            close: Recovered::Incomplete, ..
        })));
    }

    #[test]
    fn accepted_path_and_arrow_own_their_missing_rhs_slots() {
        let path = parse_direct_recovered("A::");
        assert!(matches!(path.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::PathSegment)
                && record.site.range == (3..3)));
        let arrow = parse_direct_recovered("A ->");
        assert!(matches!(arrow.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ArrowRhs)
                && record.site.range == (4..4)));

        let malformed_arrow = parse_direct_recovered("A ->@B");
        assert!(matches!(malformed_arrow.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ArrowRhs)
                && record.site.range == (4..5)
                && record.kind == crate::session::RecoveryKind::Error));
        assert!(matches!(parse("A ->@B").arrow, Some(TypeArrowTail {
            rhs: Recovered::Complete(_), ..
        })));
    }

    #[test]
    fn malformed_delimited_item_retries_at_the_next_type_primary() {
        let recoveries = parse_direct_recovered("T(@A)");
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::CallArgument)
                && record.site.range == (2..3)
                && record.kind == crate::session::RecoveryKind::Error));
    }

    #[test]
    fn ast_delimited_recovery_keeps_the_same_item_slots_as_direct_cst() {
        let malformed = parse("T(@A)");
        assert!(matches!(malformed.postfix.as_slice(), [TypePostfixTail::Call(tail)]
            if matches!(tail.arguments.as_slice(), [Recovered::Complete(_)])));

        let leading_separator = parse("T(,)");
        assert!(matches!(leading_separator.postfix.as_slice(), [TypePostfixTail::Call(tail)]
            if matches!(tail.arguments.as_slice(), [Recovered::Incomplete])));
    }

    #[test]
    fn type_delimited_close_recovery_keeps_a_mismatched_closer_local() {
        let recoveries = parse_direct_recovered("T(A]");
        assert!(recoveries.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: crate::session::ConstructRole::TypeCall,
            delimiter: crate::session::Delimiter::Parenthesis,
        }) && record.kind == crate::session::RecoveryKind::Error && record.site.range == (3..4)));
        assert!(recoveries.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: crate::session::ConstructRole::TypeCall,
            delimiter: crate::session::Delimiter::Parenthesis,
        }) && record.kind == crate::session::RecoveryKind::Missing && record.site.range == (4..4)));
        let ast = parse("T(A]");
        assert!(matches!(ast.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail {
            close: Recovered::Incomplete, ..
        })]));
    }

    #[test]
    fn numeric_path_rhs_is_an_error_not_a_path_segment() {
        let recoveries = parse_direct_recovered("A::123");
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::PathSegment)
                && record.site.range == (3..6)
                && record.kind == crate::session::RecoveryKind::Error));
    }

    #[test]
    fn malformed_path_segment_retries_at_the_next_segment_candidate() {
        let recoveries = parse_direct_recovered("A::@B");
        assert!(matches!(recoveries.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::PathSegment)
                && record.site.range == (3..4)
                && record.kind == crate::session::RecoveryKind::Error));
        let ast = parse("A::@B");
        assert!(matches!(ast.postfix.as_slice(), [TypePostfixTail::Path(TypePathTail {
            segment: Recovered::Complete(TypePathSegment::Identifier(_)), ..
        })]));
    }

    #[test]
    fn named_record_types_are_primary_fields_with_comma_or_newline_boundaries() {
        let single = parse("{a: A, b: B}");
        assert!(matches!(single.primary, TypePrimary::Record(NamedRecordType { ref fields, close: Recovered::Complete(_), .. })
            if fields.len() == 2 && fields.iter().all(|field| matches!(field, Recovered::Complete(_)))));
        let newline = parse("{\n  a: A\n  b: B\n}");
        assert!(matches!(newline.primary, TypePrimary::Record(NamedRecordType { ref fields, .. }) if fields.len() == 2));
        let direct = parse_direct("{a: A, b: B}");
        assert!(direct.descendants().any(|node| node.kind() == SyntaxKind::NamedRecordType));
        assert!(direct.descendants().filter(|node| node.kind() == SyntaxKind::TypeRecordField).count() == 2);
    }

    #[test]
    fn named_record_field_head_yields_before_type_apply() {
        let applied = parse("{a: F B}");
        assert!(matches!(applied.primary, TypePrimary::Record(NamedRecordType { ref fields, .. })
            if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField { type_expr: Recovered::Complete(value), .. })]
                if matches!(value.postfix.as_slice(), [TypePostfixTail::Apply(_)]))));
        let split = parse("{a: F b: B}");
        assert!(matches!(split.primary, TypePrimary::Record(NamedRecordType { ref fields, .. })
            if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField { type_expr: Recovered::Complete(value), .. }), Recovered::Complete(_)]
                if value.postfix.is_empty())));
        let recoveries = parse_direct_recovered("{a: F b: B}");
        assert!(recoveries.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::RecordFieldSeparator)));
    }

    #[test]
    fn named_record_missing_name_commits_the_field_owner() {
        let records = parse_direct_recovered("{@: A}");
        assert!(records.iter().any(|record| {
            record.site.role == GrammarRole::Type(TypeRole::RecordFieldName)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..2)
        }));
    }

    #[test]
    fn named_record_malformed_item_stays_at_sequence_scope() {
        let records = parse_direct_recovered("{@ a: A}");
        assert!(records.iter().any(|record| {
            record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..2)
        }));
    }

    #[test]
    fn named_record_rejects_spread_shorthand_and_default_field_forms() {
        let spread = parse_direct_recovered("{..Type}");
        assert!(matches!(spread.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Error
                && record.site.range == (1..7)));
        let spread_ast = parse("{..Type}");
        assert!(matches!(spread_ast.primary, TypePrimary::Record(NamedRecordType { ref fields, .. })
            if matches!(fields.as_slice(), [Recovered::Incomplete])));

        let shorthand = parse_direct_recovered("{name}");
        assert!(matches!(shorthand.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                && record.kind == RecoveryKind::Missing
                && record.site.range == (5..5)));

        let default = parse_direct_recovered("{name = Value}");
        assert!(matches!(default.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                && record.kind == RecoveryKind::Error
                && record.site.range == (6..7)));
        let ast = parse("{name = Value}");
        assert!(matches!(ast.primary, TypePrimary::Record(NamedRecordType { ref fields, .. })
            if matches!(fields.as_slice(), [Recovered::Complete(TypeRecordField {
                colon: Recovered::Incomplete,
                type_expr: Recovered::Complete(_),
                ..
            })])));
    }

    #[test]
    fn named_record_recovers_malformed_colon_and_type_slots() {
        let colon = parse_direct_recovered("{name @: A}");
        assert!(colon.iter().any(|record| {
            record.site.role == GrammarRole::Type(TypeRole::RecordFieldColon)
                && record.kind == RecoveryKind::Error
                && record.site.range == (6..7)
        }));

        let rhs = parse_direct_recovered("{name: @A}");
        assert!(rhs.iter().any(|record| {
            record.site.role == GrammarRole::Type(TypeRole::RecordFieldType)
                && record.kind == RecoveryKind::Error
                && record.site.range == (7..8)
        }));
    }

    #[test]
    fn named_record_comma_policy_and_close_recovery_are_typed() {
        let trailing = parse("{a: A,}");
        assert!(matches!(trailing.primary, TypePrimary::Record(NamedRecordType {
            trailing_comma: Some(_), close: Recovered::Complete(_), ..
        })));

        let incomplete = parse_direct_recovered("{a: A,");
        assert!(incomplete.iter().any(|record| {
            record.site.role == GrammarRole::Type(TypeRole::RecordField)
                && record.kind == RecoveryKind::Missing
        }));
        assert!(incomplete.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::NamedRecordType,
            delimiter: Delimiter::Brace,
        })));

        let semicolon = parse_direct_recovered("{a: A; b: B}");
        assert!(semicolon.iter().any(|record| {
            record.site.role == GrammarRole::Type(TypeRole::RecordFieldSeparator)
                && record.kind == RecoveryKind::Error
                && record.site.range == (5..6)
        }));

        let mismatch = parse_direct_recovered("{a: A]");
        assert!(mismatch.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::NamedRecordType,
            delimiter: Delimiter::Brace,
        }) && record.kind == RecoveryKind::Error && record.site.range == (5..6)));
        assert!(mismatch.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::NamedRecordType,
            delimiter: Delimiter::Brace,
        }) && record.kind == RecoveryKind::Missing && record.site.range == (6..6)));

        let (remainder, outer_owned) = parse_direct_prefix_with_outer_stop("{a: A]", StopKind::RightBracket);
        assert_eq!(remainder, "]");
        assert!(!outer_owned.iter().any(|record| record.kind == RecoveryKind::Error));
    }

    #[test]
    fn forall_type_primary_owns_a_non_delimited_binder_sequence_and_body() {
        let single = parse("for 'a: 'a -> 'a");
        assert!(matches!(single.primary, TypePrimary::Forall(ForallType {
            ref binders, colon: Recovered::Complete(_), body: Recovered::Complete(_), ..
        }) if binders.len() == 1));
        assert!(single.postfix.is_empty() && single.arrow.is_none());

        let multiple = parse("for 'a 'b 'c: T");
        assert!(matches!(multiple.primary, TypePrimary::Forall(ForallType { ref binders, .. })
            if binders.len() == 3 && binders.iter().all(|binder| matches!(binder, Recovered::Complete(ForallTypeBinder { boundary: Recovered::Complete(_), .. })) )));

        let direct = parse_direct("for 'a 'b: T");
        assert!(direct.descendants().any(|node| node.kind() == SyntaxKind::ForallType));
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::ForallTypeBinder).count(), 2);
    }

    #[test]
    fn forall_is_nud_only_apostrophe_only_and_terminal() {
        for source in ["for $a: T", "for &a: T", "for _a: T"] {
            let recoveries = parse_direct_recovered(source);
            assert!(recoveries.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::ForallBinder)));
        }
        let adjacent = parse_direct_recovered("for 'a'b: T");
        assert!(adjacent.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::ForallBinderBoundary)
            && record.kind == RecoveryKind::Missing));

        let grouped = parse("(for 'a: T)::Result");
        assert!(matches!(grouped.postfix.as_slice(), [TypePostfixTail::Path(_)]));
        let (_, led) = parse_prefix("F for 'a: T");
        assert!(!matches!(led.primary, TypePrimary::Forall(_)));
        assert!(matches!(led.postfix.first(), Some(TypePostfixTail::Apply(_))));
    }

    #[test]
    fn forall_recovery_keeps_its_phase_slots_non_cascading() {
        let bare = parse_direct_recovered("for");
        assert!(matches!(bare.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBinder)
                && record.kind == RecoveryKind::Missing && record.site.range == (3..3)));
        let colon = parse_direct_recovered("for 'a");
        assert!(matches!(colon.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallColon)
                && record.kind == RecoveryKind::Missing && record.site.range == (6..6)));
        let body = parse_direct_recovered("for 'a:");
        assert!(matches!(body.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallBody)
                && record.kind == RecoveryKind::Missing && record.site.range == (7..7)));
        let malformed = parse_direct_recovered("for 'a: @T");
        assert!(malformed.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::ForallBody)
            && record.kind == RecoveryKind::Error && record.site.range == (8..9)), "{malformed:#?}");

        let missing_colon = parse_direct_recovered("for 'a T");
        assert!(matches!(missing_colon.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallColon)
                && record.kind == RecoveryKind::Missing && record.site.range == (7..7)));
        assert!(matches!(parse("for 'a T").primary, TypePrimary::Forall(ForallType {
            colon: Recovered::Incomplete, body: Recovered::Complete(_), ..
        })));

        let comma = parse_direct_recovered("for 'a, 'b: T");
        assert!(comma.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::ForallBinderBoundary)
            && record.kind == RecoveryKind::Error && record.site.range == (6..7)));
        assert!(matches!(parse("for 'a, 'b: T").primary, TypePrimary::Forall(ForallType { ref binders, .. }) if binders.len() == 2));

        let (remainder, outer_comma) = parse_direct_prefix_with_outer_stop("for 'a, T", StopKind::Comma);
        assert_eq!(remainder, ", T");
        assert!(matches!(outer_comma.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::ForallColon)
                && record.kind == RecoveryKind::Missing && record.site.range == (6..6)));
        let (newline_remainder, _) = parse_prefix("for 'a\nT");
        assert_eq!(newline_remainder, "\nT");
    }

    #[test]
    fn effect_row_primary_is_adjacent_semantically_blind_and_composes_normally() {
        let empty = parse("'[]");
        assert!(matches!(empty.primary, TypePrimary::EffectRow(EffectRowType {
            ref items, close: Recovered::Complete(_), ..
        }) if items.is_empty()));

        let ordinary = parse("'[e]");
        assert!(matches!(ordinary.primary, TypePrimary::EffectRow(EffectRowType {
            ref items, ..
        }) if matches!(items.as_slice(), [Recovered::Complete(TypeExpression {
            primary: TypePrimary::Atom(TypeAtom::Identifier(_)), ..
        })])));

        let sigil = parse("'['e]");
        assert!(matches!(sigil.primary, TypePrimary::EffectRow(EffectRowType {
            ref items, ..
        }) if matches!(items.as_slice(), [Recovered::Complete(TypeExpression {
            primary: TypePrimary::Atom(TypeAtom::SigilIdentifier(_)), ..
        })])));

        let multi = parse("'[A, B; C]");
        assert!(matches!(multi.primary, TypePrimary::EffectRow(EffectRowType { ref items, .. }) if items.len() == 3));
        let direct = parse_direct("'[A, B; C]");
        assert_eq!(direct.to_string(), "'[A, B; C]");
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::EffectRowType).count(), 1);
        let newline = parse("'[\n  A\n  B\n]");
        assert!(matches!(newline.primary, TypePrimary::EffectRow(EffectRowType { ref items, .. }) if items.len() == 2));
        assert_eq!(parse_direct("'[\n  A\n  B\n]").to_string(), "'[\n  A\n  B\n]");

        let applied = parse("Foo '['e]");
        assert!(matches!(applied.postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.primary, TypePrimary::EffectRow(_))));
        let called = parse("F('[e])");
        assert!(matches!(called.postfix.as_slice(), [TypePostfixTail::Call(TypeCallTail { arguments, .. })]
            if matches!(arguments.as_slice(), [Recovered::Complete(TypeExpression { primary: TypePrimary::EffectRow(_), .. })])));
        let path = parse("'[e]::Result");
        assert!(matches!(path.postfix.as_slice(), [TypePostfixTail::Path(_)]));
        assert!(parse("'[e] -> Out").arrow.is_some());

        assert!(!primary_candidate("'"));
        assert!(!primary_candidate("' [e]"));
        assert!(!primary_candidate("'/*c*/[e]"));
        assert!(matches!(parse("'e").primary, TypePrimary::Atom(TypeAtom::SigilIdentifier(_))));
    }

    #[test]
    fn effect_row_reuses_type_call_delimited_recovery_slots() {
        for source in ["'[A,]", "'[A;]", "'[A,\n]"] {
            assert!(parse_direct_recovered(source).is_empty(), "valid trailing boundary: {source}");
        }
        let leading = parse_direct_recovered("'[,;A]");
        assert!(matches!(leading.as_slice(), [first, second]
            if first.site.role == GrammarRole::Type(TypeRole::EffectRowItem)
                && first.site.range == (2..2)
                && second.site.role == GrammarRole::Type(TypeRole::EffectRowItem)
                && second.site.range == (3..3)));
        assert!(matches!(parse("'[,;A]").primary, TypePrimary::EffectRow(EffectRowType { ref items, .. })
            if matches!(items.as_slice(), [Recovered::Incomplete, Recovered::Incomplete, Recovered::Complete(_)])));

        let missing_separator = parse_direct_recovered("'[A{}]");
        assert!(matches!(missing_separator.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::EffectRowSeparator)
                && record.site.range == (3..3)
                && record.kind == RecoveryKind::Missing));
        assert!(matches!(parse("'[A{}]").primary, TypePrimary::EffectRow(EffectRowType { ref items, .. }) if items.len() == 2));

        let malformed = parse_direct_recovered("'[@A]");
        assert!(matches!(malformed.as_slice(), [record]
            if record.site.role == GrammarRole::Type(TypeRole::EffectRowItem)
                && record.site.range == (2..3)
                && record.kind == RecoveryKind::Error));
        assert!(matches!(parse("'[@A]").primary, TypePrimary::EffectRow(EffectRowType { ref items, .. })
            if matches!(items.as_slice(), [Recovered::Complete(_)])));

        let eof = parse_direct_recovered("'[A,");
        assert!(matches!(eof.as_slice(), [item, close]
            if item.site.role == GrammarRole::Type(TypeRole::EffectRowItem)
                && item.site.range == (4..4)
                && matches!(close.site.role, GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::EffectRowType,
                    delimiter: Delimiter::Bracket,
                })
                && close.site.range == (4..4)));
        assert!(matches!(parse("'[A,").primary, TypePrimary::EffectRow(EffectRowType {
            ref items, close: Recovered::Incomplete, ..
        }) if matches!(items.as_slice(), [Recovered::Complete(_), Recovered::Incomplete])));

        let mismatch = parse_direct_recovered("'[A)");
        assert!(mismatch.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EffectRowType,
            delimiter: Delimiter::Bracket,
        }) && record.kind == RecoveryKind::Error && record.site.range == (3..4)));
        assert!(mismatch.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EffectRowType,
            delimiter: Delimiter::Bracket,
        }) && record.kind == RecoveryKind::Missing && record.site.range == (4..4)));

        let (remainder, records) = parse_direct_prefix_with_outer_stop("'[@)", StopKind::RightParenthesis);
        assert_eq!(remainder, ")");
        assert!(records.iter().any(|record| record.site.role == GrammarRole::Type(TypeRole::EffectRowItem)
            && record.kind == RecoveryKind::Error));
        assert!(records.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EffectRowType,
            delimiter: Delimiter::Bracket,
        }) && record.kind == RecoveryKind::Missing));
    }

    #[test]
    fn polymorphic_variant_type_is_a_two_level_primary() {
        let paired = parse(":{A Int, B}");
        assert!(matches!(paired.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType {
            ref tags, close: Recovered::Complete(_), ..
        }) if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag { payloads, .. }), Recovered::Complete(PolymorphicVariantTag { payloads: empty, .. })]
            if payloads.len() == 1 && empty.is_empty())));

        let siblings = parse(":{A Int Bool}");
        assert!(matches!(siblings.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. })
            if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag { payloads, .. })] if payloads.len() == 2)));

        let newline = parse(":{A Int\nB}");
        assert!(matches!(newline.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. }) if tags.len() == 2));

        let direct = parse_direct(":{A Int, B}");
        assert_eq!(direct.to_string(), ":{A Int, B}");
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::PolymorphicVariantType).count(), 1);
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag).count(), 2);
        assert_eq!(direct.descendants().filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload).count(), 1);
    }

    #[test]
    fn polymorphic_variant_type_preserves_primary_and_ml_payload_boundaries() {
        assert!(matches!(parse(":{}").primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. }) if tags.is_empty()));
        assert!(matches!(parse(":{A,}").primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { trailing_comma: Some(_), close: Recovered::Complete(_), .. })));
        let nested = parse(":{\n  A Pair(\n    Int,\n    Bool\n  )\n  B\n}");
        assert!(matches!(nested.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. }) if tags.len() == 2));
        let ml = parse(":{A Pair(Int, Bool) B}");
        assert!(matches!(ml.primary, TypePrimary::PolymorphicVariant(PolymorphicVariantType { ref tags, .. })
            if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag { payloads, .. })] if payloads.len() == 2)));
        assert!(matches!(parse("F :{A}").postfix.as_slice(), [TypePostfixTail::Apply(argument)]
            if matches!(argument.argument.primary, TypePrimary::PolymorphicVariant(_))));
        assert!(matches!(parse(":{A}::Result").postfix.as_slice(), [TypePostfixTail::Path(_)]));
        assert!(!primary_candidate(": {A}"));
    }

    #[test]
    fn polymorphic_variant_type_uses_phase_specific_recovery_roles() {
        let leading = parse_direct_recovered(":{,,A}");
        assert_eq!(leading.iter().filter(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Missing).count(), 2);

        let semicolon = parse_direct_recovered(":{;A}");
        assert!(semicolon.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagSeparator)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..3)));

        let wrong_name = parse_direct_recovered(":{123 Int}");
        assert!(wrong_name.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTagName)
                && record.kind == RecoveryKind::Error
                && record.site.range == (2..5)));

        let malformed = parse_direct_recovered(":{A@,B}");
        assert!(malformed.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantTag)
                && record.kind == RecoveryKind::Error
                && record.site.range == (3..4)));

        let payload = parse_direct_recovered(":{A @Int}");
        assert!(payload.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayload)
                && record.kind == RecoveryKind::Error
                && record.site.range == (4..5)));
        assert!(!payload.iter().any(|record|
            record.site.role == GrammarRole::Type(TypeRole::PolymorphicVariantPayloadBoundary)
                && record.kind == RecoveryKind::Missing));

        let missing = parse_direct_recovered(":{A");
        assert!(missing.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::PolymorphicVariantType,
            delimiter: Delimiter::Brace,
        }) && record.kind == RecoveryKind::Missing));

        let mismatched = parse_direct_recovered(":{A]}");
        assert!(mismatched.iter().any(|record| matches!(record.site.role, GrammarRole::ClosingDelimiter {
            owner: ConstructRole::PolymorphicVariantType,
            delimiter: Delimiter::Brace,
        }) && record.kind == RecoveryKind::Error && record.site.range == (3..4)));
    }

}
