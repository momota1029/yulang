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
        word::{WordSpan, scan_path_segment},
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
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeExpression<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let primary = parse_type_primary(&mut i)?;
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
        if !trivia.is_empty() && type_primary_candidate(&mut i) {
            let boundary = boundary_start..i.pos();
            let saved_ml = i.local.type_ml_arg();
            i.local.set_type_ml_arg(true);
            let argument = i.run(from_fn(|i| parse_type_expression_with_outer_missing_role(None, i)))
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
    let start = committed.probe(|probe| probe.input().pos());
    committed.start_node(SyntaxKind::TypeExpression);
    if commit_direct_type_primary(committed).is_none() {
        committed.finish_node();
        return None;
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
                commit_direct_type_delimited(TypeDelimitedOwner::Call, SyntaxKind::TypeCallTail, open, false, committed);
            }
            DirectTypeTail::Apply { boundary } => {
                committed.start_node(SyntaxKind::TypeApplyArgument);
                committed.emit_trivia(&boundary);
                let saved = committed.probe(|probe| probe.input().local.type_ml_arg());
                committed.probe(|probe| probe.input().local.set_type_ml_arg(true));
                commit_direct_type_expression(committed).expect("accepted TypeApply owns a type primary");
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
    if !leading.is_empty() && type_primary_candidate(i) {
        return Some(DirectTypeTail::Apply { boundary: leading });
    }
    i.rollback(checkpoint);
    None
}

fn commit_direct_type_primary<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(name) = committed.probe(|probe| scan_type_name(probe.input())) {
        committed.token(type_name_kind(name), type_name_range(name));
        return Some(());
    }
    if let Some(integer) = committed.probe(|probe| {
        probe.input().input.remainder().chars().next().is_some_and(|character| character.is_ascii_digit())
            .then(|| probe.input().run(parse_integer_literal))
            .flatten()
    }) {
        committed.token(SyntaxKind::Integer, integer.range());
        return Some(());
    }
    let open = committed.probe(|probe| scan_open_parenthesis(probe.input()))?;
    commit_direct_type_delimited(
        TypeDelimitedOwner::ParenthesizedGroup,
        SyntaxKind::ParenthesizedTypeGroup,
        open,
        true,
        committed,
    );
    Some(())
}

fn commit_direct_type_delimited<'parse, 'source, 'local, E, O>(
    owner: TypeDelimitedOwner,
    kind: SyntaxKind,
    open: Range<usize>,
    _is_group: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(kind);
    committed.token(SyntaxKind::LParen, open);
    let incoming = committed.probe(|probe| probe.input().local.indentation_baseline().map_or(0, |baseline| baseline.column));
    let stops = committed.probe(|probe| active_stop_set(probe.input()).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightParenthesis));
    committed.probe(|probe| {
        probe.input().local.push_delimiter(Delimiter::Parenthesis);
        probe.input().local.push_stop_set(stops);
        probe.input().local.push_type_delimited_owner(owner);
    });
    let opening = consume_direct_trivia(committed);
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, probe.input().local.line().line_indent));
    committed.probe(|probe| push_layout(layout, probe.input()));
    if !direct_type_close_pending(committed) {
        loop {
            if direct_type_separator_pending(committed) {
                emit_type_missing(
                    committed,
                    GrammarRole::Type(match owner {
                        TypeDelimitedOwner::Call => TypeRole::CallArgument,
                        TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedItem,
                    }),
                    ExpectedSyntax::TypeExpression,
                );
                let separator = committed
                    .probe(|probe| scan_separator(probe.input()))
                    .expect("the separator pending probe accepted a literal separator");
                committed.token(separator_kind(&separator), separator_range(&separator));
                let trailing = consume_direct_trivia(committed);
                committed.emit_trivia(&trailing);
                if direct_type_close_pending(committed) { break; }
                continue;
            }
            if commit_direct_type_expression(committed).is_none() {
                let role = match owner {
                    TypeDelimitedOwner::Call => TypeRole::CallArgument,
                    TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedItem,
                };
                if direct_type_item_error_retry(committed, role) {
                    continue;
                }
                emit_type_missing(committed, GrammarRole::Type(role), ExpectedSyntax::TypeExpression);
                break;
            }
            let trivia = consume_direct_trivia(committed);
            committed.emit_trivia(&trivia);
            if let Some(separator) = committed.probe(|probe| scan_separator(probe.input())) {
                committed.token(separator_kind(&separator), separator_range(&separator));
                let trailing = consume_direct_trivia(committed);
                committed.emit_trivia(&trailing);
                if direct_type_close_pending(committed) { break; }
                continue;
            }
            if direct_type_close_pending(committed) { break; }
            if committed.probe(|probe| layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)) == LayoutDelimitedBoundary::ImplicitNewline { continue; }
            if committed.probe(|probe| direct_type_primary_candidate(probe.input())) {
                emit_type_missing(
                    committed,
                    GrammarRole::Type(match owner {
                        TypeDelimitedOwner::Call => TypeRole::CallArgumentSeparator,
                        TypeDelimitedOwner::ParenthesizedGroup => TypeRole::ParenthesizedSeparator,
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
        },
        delimiter: Delimiter::Parenthesis,
    };
    loop {
        if let Some(close) = committed.probe(|probe| scan_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        let mismatched = committed.probe(|probe| scan_mismatched_close(probe.input()));
        if let Some(range) = mismatched {
            emit_error_with_role(
                committed,
                close_role,
                range,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
            );
            continue;
        }
        emit_type_missing(
            committed,
            close_role,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
        );
        break;
    }
    committed.probe(|probe| {
        pop_layout(layout, probe.input());
        assert_eq!(probe.input().local.pop_type_delimited_owner(), Some(owner));
        assert_eq!(probe.input().local.pop_stop_set(), Some(stops));
        assert_eq!(probe.input().local.pop_delimiter(), Some(Delimiter::Parenthesis));
    });
    committed.finish_node();
}

fn direct_type_close_pending<'parse, 'source, 'local, E, O>(committed: &mut Committed<'parse, 'source, 'local, E, O>) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let pending = scan_close_parenthesis(i).is_some();
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

fn parse_type_primary<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<TypePrimary<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
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
    scan_open_parenthesis(i).map(|open| TypePrimary::Parenthesized(parse_parenthesized_type_group(open, i)))
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
    let (arguments, _, close) = parse_type_delimited_items(TypeDelimitedOwner::Call, i);
    let end = match &close { Recovered::Complete(close) => close.end, Recovered::Incomplete => i.pos() };
    TypeCallTail { open: open.clone(), arguments, close, range: open.start..end }
}

fn parse_parenthesized_type_group<'source, E>(open: Range<usize>, i: &mut SynIn<'_, 'source, '_, E>) -> ParenthesizedTypeGroup<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (elements, trailing_explicit_separator, close) = parse_type_delimited_items(TypeDelimitedOwner::ParenthesizedGroup, i);
    let end = match &close { Recovered::Complete(close) => close.end, Recovered::Incomplete => i.pos() };
    ParenthesizedTypeGroup { open: open.clone(), elements, trailing_explicit_separator, close, range: open.start..end }
}

fn parse_type_delimited_items<'source, E>(
    owner: TypeDelimitedOwner,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (Vec<Recovered<TypeExpression<'source>>>, Option<TypeExplicitSeparator>, Recovered<Range<usize>>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = i.local.indentation_baseline().map_or(0, |baseline| baseline.column);
    i.local.push_delimiter(Delimiter::Parenthesis);
    let stops = active_stop_set(i).with(StopKind::Comma).with(StopKind::Semicolon).with(StopKind::RightParenthesis);
    i.local.push_stop_set(stops);
    i.local.push_type_delimited_owner(owner);
    let opening = consume_trivia(i);
    let layout = LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent);
    push_layout(layout, i);
    let mut items = Vec::new();
    let mut trailing = None;
    let close;
    loop {
        if let Some(range) = scan_close_parenthesis(i) { close = Recovered::Complete(range); break; }
        if scan_mismatched_close(i).is_some() { close = Recovered::Incomplete; break; }
        if scan_separator(i).is_some() {
            items.push(Recovered::Incomplete);
            let _ = consume_trivia(i);
            if let Some(range) = scan_close_parenthesis(i) {
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
            let _ = scan_mismatched_close(i);
            close = Recovered::Incomplete;
            break;
        }
        let trivia = consume_trivia(i);
        if let Some(separator) = scan_separator(i) {
            let post = consume_trivia(i);
            if let Some(range) = scan_close_parenthesis(i) {
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
                if let Some(range) = scan_close_parenthesis(i) { close = Recovered::Complete(range); break; }
                continue;
            }
            LayoutDelimitedBoundary::DeeperNewline => {
                close = Recovered::Incomplete;
                break;
            }
            LayoutDelimitedBoundary::None => {
                if let Some(range) = scan_close_parenthesis(i) { close = Recovered::Complete(range); break; }
                let _ = scan_mismatched_close(i);
                close = Recovered::Incomplete;
                break;
            }
        }
    }
    pop_layout(layout, i);
    assert_eq!(i.local.pop_type_delimited_owner(), Some(owner));
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
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
        let Some(character) = i.input.remainder().chars().next() else {
            return i.pos() > start;
        };
        if character.is_whitespace() || matches!(character, ')' | ']' | '}' | ',' | ';') {
            return i.pos() > start;
        }
        i.input.next();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
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
    let checkpoint = i.checkpoint();
    let candidate = parse_type_primary(i).is_some();
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

fn scan_close_parenthesis<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Close(Delimiter::Parenthesis) { Some(punctuation.range()) } else { i.rollback(checkpoint); None }
}

fn scan_mismatched_close<'source, E>(i: &mut SynIn<'_, 'source, '_, E>) -> Option<Range<usize>>
where E: ErrorSink<usize>, Unexpected<char>: Into<E::Error>, UnexpectedEndOfInput: Into<E::Error> {
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    let owned_by_outer = match punctuation.kind() {
        PunctuationKind::Close(Delimiter::Bracket) => active_stop_set(i).contains(StopKind::RightBracket),
        PunctuationKind::Close(Delimiter::Brace) => active_stop_set(i).contains(StopKind::RightBrace),
        _ => false,
    };
    if matches!(punctuation.kind(), PunctuationKind::Close(delimiter) if delimiter != Delimiter::Parenthesis)
        && !owned_by_outer
    {
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

fn type_chain_trivia<E>(i: &SynIn<E>, trivia: &TriviaRun) -> bool where E: ErrorSink<usize> {
    !trivia_has_newline(trivia) || i.local.line().line_indent > i.local.indentation_baseline().map_or(0, |baseline| baseline.column)
}
fn is_outer_newline_boundary<E>(i: &SynIn<E>, trivia: &TriviaRun) -> bool where E: ErrorSink<usize> { trivia_has_newline(trivia) && !type_chain_trivia(i, trivia) }
fn trivia_has_newline(trivia: &TriviaRun) -> bool { trivia.parts().iter().any(|part| matches!(part.kind(), crate::scan::trivia::TriviaPartKind::Newline)) }
fn active_stop_set<E>(i: &SynIn<E>) -> StopSet where E: ErrorSink<usize> { i.local.stop_set().unwrap_or_default() }
fn push_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>) where E: ErrorSink<usize> { i.local.push_indentation_baseline(IndentationBaseline { column: layout.base_indent(), kind: IndentationBaselineKind::Introducer }); }
fn pop_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>) where E: ErrorSink<usize> { assert_eq!(i.local.pop_indentation_baseline(), Some(IndentationBaseline { column: layout.base_indent(), kind: IndentationBaselineKind::Introducer })); }
fn primary_range(primary: &TypePrimary<'_>) -> Range<usize> { match primary { TypePrimary::Atom(atom) => match atom { TypeAtom::Identifier(word) | TypeAtom::SigilIdentifier(word) => word.range(), TypeAtom::Number(number) => number.range.clone() }, TypePrimary::Parenthesized(group) => group.range.clone() } }
fn postfix_range_end(tail: &TypePostfixTail<'_>) -> usize { match tail { TypePostfixTail::Path(tail) => tail.range.end, TypePostfixTail::Call(tail) => tail.range.end, TypePostfixTail::Apply(tail) => tail.range.end } }
#[cfg(test)]
mod tests {
    use super::*;

    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxNode,
        input::SourceInput,
        session::{FullCstOutput, GrammarRole, ParseLocal, TypeRole},
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
}
